/* ==========================================================================
   SQL NOLOCK / SET NOCOUNT Professional Auditor
   --------------------------------------------------------------------------
   Engine notes
   ------------
   The analyzer is not line based. It lexes the batch once to find comment and
   string-literal spans, then produces two documents of identical length so
   every character offset (and therefore every line number) stays exact:

     codeDoc : comments + string literals blanked  -> static T-SQL
     dynDoc  : comments blanked, literal quotes and concatenation glue
               ('+ @var +') blanked                -> dynamic T-SQL

   Both documents are tokenised and walked by the same FROM/JOIN/APPLY/USING
   source parser, so comma joins, hints written without WITH, hints written
   without a space, aliases before or after the hint, linked-server four part
   names, CTEs, derived tables and table valued functions are all handled.
   ========================================================================== */

/* ------------------------------- vocabulary ------------------------------- */

const HINT_WORDS = new Set([
    'NOLOCK', 'READUNCOMMITTED', 'READCOMMITTED', 'READCOMMITTEDLOCK', 'REPEATABLEREAD',
    'SERIALIZABLE', 'SNAPSHOT', 'HOLDLOCK', 'UPDLOCK', 'XLOCK', 'ROWLOCK', 'PAGLOCK',
    'TABLOCK', 'TABLOCKX', 'READPAST', 'NOWAIT', 'FORCESEEK', 'FORCESCAN', 'NOEXPAND',
    'INDEX', 'KEEPIDENTITY', 'KEEPDEFAULTS', 'IGNORE_CONSTRAINTS', 'IGNORE_TRIGGERS',
    'SPATIAL_WINDOW_MAX_CELLS'
]);

const NOLOCK_EQUIVALENT = new Set(['NOLOCK', 'READUNCOMMITTED']);

/* Words that can never be a table name or an alias. */
const RESERVED = new Set([
    'SELECT', 'INSERT', 'UPDATE', 'DELETE', 'MERGE', 'FROM', 'WHERE', 'GROUP', 'ORDER',
    'HAVING', 'UNION', 'EXCEPT', 'INTERSECT', 'OPTION', 'FOR', 'ON', 'SET', 'GO',
    'BEGIN', 'END', 'IF', 'ELSE', 'WHILE', 'RETURN', 'RETURNS', 'EXEC', 'EXECUTE',
    'DECLARE', 'PRINT', 'CREATE', 'ALTER', 'DROP', 'TRUNCATE', 'WITH', 'VALUES',
    'OUTPUT', 'INTO', 'PIVOT', 'UNPIVOT', 'TOP', 'DISTINCT', 'CASE', 'WHEN', 'THEN',
    'AS', 'INNER', 'LEFT', 'RIGHT', 'FULL', 'CROSS', 'OUTER', 'JOIN', 'APPLY', 'AND',
    'OR', 'NOT', 'NULL', 'IS', 'LIKE', 'IN', 'BETWEEN', 'EXISTS', 'USING', 'ASC',
    'DESC', 'TABLESAMPLE', 'GRANT', 'COMMIT', 'ROLLBACK', 'TRAN', 'TRANSACTION', 'TRY',
    'CATCH', 'RAISERROR', 'THROW', 'OPEN', 'CLOSE', 'FETCH', 'DEALLOCATE', 'USE',
    'WAITFOR', 'GOTO', 'BREAK', 'CONTINUE', 'ALL', 'ANY', 'SOME', 'PERCENT', 'TIES',
    'IDENTITY', 'NOCOUNT', 'OFF', 'PROCEDURE', 'PROC', 'FUNCTION', 'TRIGGER', 'VIEW'
]);

const NON_HINTABLE_FUNCS = new Set([
    'OPENQUERY', 'OPENROWSET', 'OPENDATASOURCE', 'OPENXML', 'OPENJSON', 'STRING_SPLIT',
    'CONTAINSTABLE', 'FREETEXTTABLE', 'CHANGETABLE', 'PREDICT', 'GENERATE_SERIES'
]);

/* Trigger pseudo tables - already read from the version store, cannot be hinted. */
const PSEUDO_TABLES = new Set(['INSERTED', 'DELETED']);

/* Tokens that turn a following FROM into a cursor fetch rather than a table source. */
const CURSOR_FETCH = new Set(['FETCH', 'NEXT', 'PRIOR', 'FIRST', 'LAST', 'ABSOLUTE', 'RELATIVE']);

/* Reported: a read source with no NOLOCK, a module body with no SET NOCOUNT ON,
   and the three security problems (injection, remote execution, credentials).
   Everything else stays silent. */
const RULES = {
    NL001: { cat: 'nolock',   msg: 'No NOLOCK on read source' },
    NL005: { cat: 'nolock',   msg: 'No NOLOCK inside dynamic SQL' },
    NC001: { cat: 'nocount',  msg: 'Module body missing SET NOCOUNT ON' },
    NC002: { cat: 'nocount',  msg: 'SET NOCOUNT turned OFF again' },
    NC004: { cat: 'nocount',  msg: 'Batch missing SET NOCOUNT ON' },
    SEC001: { cat: 'security', msg: 'String parameter concatenated into executed dynamic SQL' },
    SEC002: { cat: 'security', msg: 'Caller supplied identifier or predicate in dynamic SQL' },
    SEC003: { cat: 'security', msg: 'Dynamic SQL executed against a linked server' },
    SEC004: { cat: 'security', msg: 'Credential in plain text' },
    GO001: { cat: 'go', msg: 'Missing GO batch separator' }
};

/* ------------------------- security analysis vocabulary ------------------- */

const STRING_TYPES = new Set([
    'VARCHAR', 'NVARCHAR', 'CHAR', 'NCHAR', 'TEXT', 'NTEXT', 'SYSNAME', 'XML'
]);

/* Types that cannot carry an injection payload once concatenated. */
const SAFE_TYPES = new Set([
    'INT', 'INTEGER', 'BIGINT', 'SMALLINT', 'TINYINT', 'BIT', 'DECIMAL', 'NUMERIC',
    'MONEY', 'SMALLMONEY', 'FLOAT', 'REAL', 'DATE', 'DATETIME', 'DATETIME2',
    'SMALLDATETIME', 'DATETIMEOFFSET', 'TIME', 'UNIQUEIDENTIFIER', 'TIMESTAMP',
    'BINARY', 'VARBINARY', 'IMAGE'
]);

/* Parameter names that mean "caller hands us raw SQL" - the recurring design
   flaw found across the SIP procedures (@WhereClause, @TableName, ...). */
const IDENT_PARAM_RE = /(TABLE|COLUMN|FIELD|ORDER|SORT|WHERE|CLAUSE|CONDITION|PREDICATE|FILTER|CRITERIA|SQL|QUERY|STMT|SELECTLIST|GROUPBY|HAVING|JOIN)/;

const REMOTE_FUNCS = /\b(OPENQUERY|OPENROWSET|OPENDATASOURCE)\s*\(/gi;

/* Credential shapes: connection strings, linked-server logins, CREATE LOGIN,
   scoped credentials. Values are redacted before they are ever displayed.

   Deliberately quoted-literal-only ('...' / N'...') on the right of "=". This
   codebase's login procedures are full of `Password=(case when ... else
   @Password end)` and `Password=@Password` - a column compared against an
   expression or a passed-through parameter, not a hardcoded secret. Matching
   a bare unquoted token would flag "(case" as a credential on almost every
   login proc. Real hardcoded creds in these scripts are always a string
   literal, so requiring one keeps this to genuine hits. */
const SECRET_PATTERNS = [
    { re: /\b(pass\s*word|pwd|passwd)\s*=\s*(N?'[^']*')/gi, what: 'password' },
    { re: /@rmtpassword\s*=\s*(N?'[^']*')/gi, what: 'linked server remote password' },
    { re: /\b(secret)\s*=\s*(N?'[^']*')/gi, what: 'credential secret' }
];

/* "User ID=x;Password=y" connection-string idiom. Scoped to a single string
   literal (see analyzeSecurity) so it can never pair a "userid=" on one line
   with an unrelated "password" many lines later - T-SQL statements do not
   require a terminating ';', so an unbounded scan across the whole script
   would do exactly that. */
const CONN_STRING_RE = /\b(user\s*id|uid)\s*=\s*([^;'"]+)\s*;[^;]{0,120}?\b(pass\s*word|pwd)\s*=\s*([^;'"]*)/gi;

/* --------------------------- span lexer / masking -------------------------- */

function lexSpans(sql) {
    const comments = [], strings = [];
    const n = sql.length;
    let i = 0;
    while (i < n) {
        const c = sql[i], c2 = sql.substr(i, 2);
        if (c2 === '--') {
            let j = sql.indexOf('\n', i);
            if (j < 0) j = n;
            comments.push([i, j]);
            i = j;
        } else if (c2 === '/*') {
            let depth = 1, j = i + 2;
            while (j < n && depth > 0) {
                if (sql.substr(j, 2) === '/*') { depth++; j += 2; }
                else if (sql.substr(j, 2) === '*/') { depth--; j += 2; }
                else j++;
            }
            comments.push([i, j]);
            i = j;
        } else if (c === "'") {
            let j = i + 1;
            while (j < n) {
                if (sql[j] === "'") {
                    if (sql[j + 1] === "'") { j += 2; continue; }
                    j++;
                    break;
                }
                j++;
            }
            strings.push([i, j]);
            i = j;
        } else if (c === '[') {
            const j = sql.indexOf(']', i);
            i = j < 0 ? n : j + 1;
        } else {
            i++;
        }
    }
    return { comments: comments, strings: strings };
}

/* Blank spans, keeping length and newlines so every offset stays valid. */
function blankSpans(text, spans) {
    const buf = text.split('');
    spans.forEach(sp => {
        for (let i = sp[0]; i < sp[1] && i < buf.length; i++) {
            if (buf[i] !== '\n' && buf[i] !== '\r') buf[i] = ' ';
        }
    });
    return buf.join('');
}

function blankRanges(buf, ranges) {
    ranges.forEach(sp => {
        for (let i = sp[0]; i < sp[1] && i < buf.length; i++) {
            if (buf[i] !== '\n' && buf[i] !== '\r') buf[i] = ' ';
        }
    });
}

/* Glue between two adjacent literals: '+ @var +', '+CAST(@x AS VARCHAR)+' ... */
function isConcatGlue(text) {
    if (!text.length || text.length > 120) return false;
    if (text.indexOf('+') < 0) return false;
    if (!/^[\s+@\w.\[\](),$#]*$/.test(text)) return false;
    return !/\b(SELECT|FROM|WHERE|JOIN|UPDATE|INSERT|DELETE|EXEC|SET|VALUES)\b/i.test(text);
}

/* ------------------------------- tokenizer -------------------------------- */

const TOKEN_RE = /\[[^\]]*\]|"[^"]*"|[#@]{1,2}[A-Za-z0-9_$#]+|[A-Za-z_][A-Za-z0-9_$#]*|\d+(?:\.\d+)?|[(),.;]|\S/g;

function tokenize(doc) {
    const toks = [];
    let m;
    TOKEN_RE.lastIndex = 0;
    while ((m = TOKEN_RE.exec(doc)) !== null) {
        const v = m[0];
        toks.push({
            v: v,
            u: v.toUpperCase(),
            s: m.index,
            e: m.index + v.length,
            w: /^[[\"#@A-Za-z_]/.test(v)
        });
    }
    return toks;
}

function matchParen(toks, i) {
    let depth = 0;
    for (let k = i; k < toks.length; k++) {
        if (toks[k].v === '(') depth++;
        else if (toks[k].v === ')') { depth--; if (depth === 0) return k; }
    }
    return -1;
}

function unquote(s) {
    return String(s || '').replace(/[\[\]"]/g, '').trim().toUpperCase();
}

/* ---------------------------- name / tail parsing -------------------------- */

function readName(doc, toks, j) {
    let i = j;
    while (toks[i] && toks[i].v === '.') i++;                 /* .dbo.Fn  /  ..tbl */
    if (!toks[i] || !toks[i].w || RESERVED.has(toks[i].u)) return null;

    const start = toks[j].s;
    const parts = [toks[i].v];
    i++;
    while (toks[i] && toks[i].v === '.') {
        i++;
        if (toks[i] && toks[i].w && !RESERVED.has(toks[i].u)) { parts.push(toks[i].v); i++; }
        else parts.push('');
    }
    return {
        parts: parts,
        raw: doc.slice(start, toks[i - 1].e),
        s: start,
        e: toks[i - 1].e,
        next: i
    };
}

function parseHints(inner) {
    return inner.split(',')
        .map(p => (p.trim().split(/[\s=(]/)[0] || '').toUpperCase())
        .filter(Boolean);
}

function isHintList(inner) {
    if (!inner.trim()) return false;
    return inner.split(',').every(p => {
        const first = (p.trim().split(/[\s=(]/)[0] || '').toUpperCase();
        return first && HINT_WORDS.has(first);
    });
}

/* Consume alias / AS alias / WITH (hints) / (hints) in any order. */
function parseTail(doc, toks, i) {
    const out = {
        alias: null, aliasSpan: null, hints: null, hintSpan: null, hasWith: false,
        fnCall: false, next: i, endPos: toks[i - 1] ? toks[i - 1].e : 0
    };
    while (i < toks.length) {
        const t = toks[i];

        if (t.v === '(') {
            const close = matchParen(toks, i);
            if (close < 0) break;
            const inner = doc.slice(t.e, toks[close].s);
            if (isHintList(inner)) {
                out.hints = parseHints(inner);
                out.hintSpan = [t.s, toks[close].e];
            } else {
                out.fnCall = true;
            }
            out.endPos = toks[close].e;
            i = close + 1;
            continue;
        }
        if (t.u === 'WITH' && toks[i + 1] && toks[i + 1].v === '(') {
            const close = matchParen(toks, i + 1);
            if (close < 0) break;
            out.hints = parseHints(doc.slice(toks[i + 1].e, toks[close].s));
            out.hasWith = true;
            out.hintSpan = [t.s, toks[close].e];
            out.endPos = toks[close].e;
            i = close + 1;
            continue;
        }
        if (t.u === 'AS') {
            const nxt = toks[i + 1];
            if (nxt && nxt.w && !RESERVED.has(nxt.u)) {
                out.alias = nxt.v;
                out.aliasSpan = [t.s, nxt.e];
                out.endPos = nxt.e;
                i += 2;
                continue;
            }
            break;
        }
        if (t.u === 'TABLESAMPLE') {
            i++;
            if (toks[i] && toks[i].v === '(') {
                const c = matchParen(toks, i);
                if (c > 0) { out.endPos = toks[c].e; i = c + 1; }
            }
            continue;
        }
        if (t.w && !RESERVED.has(t.u) && !out.alias) {
            out.alias = t.v;
            out.aliasSpan = [t.s, t.e];
            out.endPos = t.e;
            i++;
            continue;
        }
        break;
    }
    out.next = i;
    return out;
}

/* ----------------------------- source scanning ----------------------------- */

function collectCteNames(doc) {
    const names = new Set();
    const re = /(?:\bWITH\s+|,\s*)((?:\[[^\]]*\]|[A-Za-z_][\w$#]*))\s*(?:\([^)]*\)\s*)?AS\s*\(/gi;
    let m;
    while ((m = re.exec(doc)) !== null) names.add(unquote(m[1]));
    return names;
}

function makeRef(doc, nm, tail, stmt, cteNames) {
    const base = unquote(nm.parts[nm.parts.length - 1]);
    const full = unquote(nm.raw.replace(/\s+/g, ''));
    const upperParts = nm.parts.map(unquote);

    let kind = 'read';
    if (NON_HINTABLE_FUNCS.has(base) || (tail.fnCall && !tail.hints)) kind = 'function';
    else if (nm.parts.length === 1 && PSEUDO_TABLES.has(base)) kind = 'pseudo';
    else if (/^#/.test(nm.parts[0])) kind = 'temp';
    else if (/^@/.test(nm.parts[0])) kind = 'tablevar';
    else if (nm.parts.length === 1 && cteNames.has(base)) kind = 'cte';
    else if (stmt.targets.has(base) || stmt.targets.has(full) ||
             (tail.alias && stmt.targets.has(unquote(tail.alias)))) kind = 'dml-target';
    else if (upperParts.indexOf('SYS') >= 0 || upperParts.indexOf('INFORMATION_SCHEMA') >= 0 ||
             /^SYS[A-Z]/.test(base)) kind = 'system';

    return {
        raw: nm.raw,
        disp: nm.raw.replace(/\s+/g, ' ').replace(/\[\s*\]/g, '[?]')
                    .replace(/\.\s+\./g, '.?.').replace(/\.\s+$/, '.?')
                    .replace(/^\s*\./, '?.'),
        base: base,
        alias: tail.alias,
        aliasSpan: tail.aliasSpan,
        kind: kind,
        hints: tail.hints,
        hintSpan: tail.hintSpan,
        hasWith: tail.hasWith,
        s: nm.s,
        e: nm.e,
        insertAt: tail.endPos,
        stmtType: stmt.type || 'SELECT',
        dynamic: false
    };
}

function scanRange(doc, toks, a, b, refs, cteNames, inherited, depth) {
    const stmt = { type: null, targets: new Set(inherited || []) };

    for (let i = a; i < b; i++) {
        const u = toks[i].u;

        if (u === 'SELECT') {
            stmt.type = 'SELECT';
            stmt.targets = new Set();
            continue;
        }

        if (u === 'INSERT' || u === 'UPDATE' || u === 'DELETE' || u === 'MERGE') {
            stmt.type = u;
            stmt.targets = new Set();
            let j = i + 1;
            if (toks[j] && toks[j].u === 'TOP') {
                j++;
                if (toks[j] && toks[j].v === '(') { const c = matchParen(toks, j); j = c > 0 ? c + 1 : j + 1; }
                else j++;
                if (toks[j] && toks[j].u === 'PERCENT') j++;
            }
            if (toks[j] && (toks[j].u === 'INTO' || toks[j].u === 'FROM')) j++;
            const nm = readName(doc, toks, j);
            if (nm) {
                stmt.targets.add(unquote(nm.parts[nm.parts.length - 1]));
                stmt.targets.add(unquote(nm.raw.replace(/\s+/g, '')));
                const tail = parseTail(doc, toks, nm.next);
                if (tail.alias) stmt.targets.add(unquote(tail.alias));
                if (tail.hints && tail.hints.some(h => NOLOCK_EQUIVALENT.has(h))) {
                    const ref = makeRef(doc, nm, tail, stmt, cteNames);
                    ref.kind = /^[#@]/.test(nm.parts[0]) ? 'temp-target' : 'dml-target-hinted';
                    refs.push(ref);
                }
            }
            continue;
        }

        /* FETCH NEXT FROM <cursor> is a cursor operation, not a table source */
        if (u === 'FROM' && i > a && CURSOR_FETCH.has(toks[i - 1].u)) continue;

        if (u === 'FROM' || u === 'JOIN' || u === 'APPLY' ||
            (u === 'USING' && stmt.type === 'MERGE')) {
            const after = parseSourceList(doc, toks, i + 1, u !== 'FROM', stmt, refs, cteNames, depth, b);
            i = Math.max(after - 1, i);
            continue;
        }
    }
}

function parseSourceList(doc, toks, i, single, stmt, refs, cteNames, depth, limit) {
    for (;;) {
        if (i >= toks.length || i >= limit) return i;

        if (toks[i].v === '(') {
            const close = matchParen(toks, i);
            if (close < 0) return i + 1;
            if (depth < 12) scanRange(doc, toks, i + 1, close, refs, cteNames, [], depth + 1);
            i = close + 1;
            if (toks[i] && toks[i].u === 'AS') i++;
            if (toks[i] && toks[i].w && !RESERVED.has(toks[i].u)) i++;
            if (toks[i] && toks[i].v === '(') { const c = matchParen(toks, i); if (c > 0) i = c + 1; }
        } else {
            const nm = readName(doc, toks, i);
            if (!nm) return i;
            const tail = parseTail(doc, toks, nm.next);
            refs.push(makeRef(doc, nm, tail, stmt, cteNames));
            i = tail.next;
        }

        if (!single && toks[i] && toks[i].v === ',') { i++; continue; }
        return i;
    }
}

function scanRefs(doc) {
    const toks = tokenize(doc);
    const refs = [];
    scanRange(doc, toks, 0, toks.length, refs, collectCteNames(doc), [], 0);
    return refs;
}

/* --------------------------------- helpers -------------------------------- */

function lineStartsOf(text) {
    const starts = [0];
    for (let i = 0; i < text.length; i++) if (text[i] === '\n') starts.push(i + 1);
    return starts;
}

function makeLineOf(starts) {
    return function (off) {
        let lo = 0, hi = starts.length - 1;
        while (lo < hi) {
            const mid = (lo + hi + 1) >> 1;
            if (starts[mid] <= off) lo = mid; else hi = mid - 1;
        }
        return lo + 1;
    };
}

function mkFinding(rule, line, obj, msg, ctx, fix) {
    const r = RULES[rule];
    return {
        rule: rule, cat: r.cat, line: line, obj: obj,
        msg: msg || r.msg, ctx: ctx || '', fix: fix || null, dynamic: false, off: 0
    };
}

function snipAt(text, off) {
    const from = text.lastIndexOf('\n', off) + 1;
    let to = text.indexOf('\n', off);
    if (to < 0) to = text.length;
    return text.slice(from, to).trim().slice(0, 120);
}

/* ------------------------- module (NOCOUNT) analysis ----------------------- */

function findModules(codeDoc) {
    const re = /\b(CREATE|ALTER)\s+(PROCEDURE|PROC|TRIGGER|FUNCTION)\s+((?:\[[^\]]*\]|[A-Za-z_][\w$#]*)(?:\s*\.\s*(?:\[[^\]]*\]|[A-Za-z_][\w$#]*))*)/gi;
    const mods = [];
    let m;
    while ((m = re.exec(codeDoc)) !== null) {
        mods.push({
            kind: m[2].toUpperCase(),
            name: m[3].replace(/\s+/g, ''),
            s: m.index,
            headerEnd: m.index + m[0].length,
            e: codeDoc.length
        });
    }
    mods.forEach((mod, k) => { if (mods[k + 1]) mod.e = mods[k + 1].s; });
    return mods;
}

/* First AS at paren depth 0 after the parameter list, then optional BEGIN. */
function bodyStart(codeDoc, mod) {
    let depth = 0;
    const re = /\[[^\]]*\]|[A-Za-z_][\w$#]*|[()]|\S/g;
    re.lastIndex = mod.headerEnd;
    let m;
    while ((m = re.exec(codeDoc)) !== null && m.index < mod.e) {
        const v = m[0];
        if (v === '(') depth++;
        else if (v === ')') depth--;
        else if (depth <= 0 && v.toUpperCase() === 'AS') {
            let pos = m.index + v.length;
            const beg = codeDoc.slice(pos, pos + 40).match(/^\s*BEGIN\b/i);
            if (beg) pos += beg[0].length;
            return pos;
        }
    }
    return mod.headerEnd;
}

function analyzeNoCount(sql, codeDoc, lineOf, findings) {
    const mods = findModules(codeDoc);
    const dataRe = /\b(SELECT|INSERT|UPDATE|DELETE|MERGE|EXEC|EXECUTE)\b/i;
    let missing = 0;

    function add(rule, off, obj, msg, fix) {
        const f = mkFinding(rule, lineOf(off), obj, msg, snipAt(sql, off), fix);
        f.off = off;
        findings.push(f);
    }

    if (!mods.length) {
        if (dataRe.test(codeDoc) && !/\bSET\s+NOCOUNT\s+ON\b/i.test(codeDoc)) {
            missing++;
            add('NC004', 0, '(ad-hoc batch)', 'SET NOCOUNT ON is not present in this batch',
                { s: 0, e: 0, text: 'SET NOCOUNT ON;\n' });
        }
        return { mods: mods, missing: missing };
    }

    mods.forEach(mod => {
        /* SET statements are not allowed inside a user defined function body */
        if (mod.kind === 'FUNCTION') return;

        const body = codeDoc.slice(mod.s, mod.e);
        const start = bodyStart(codeDoc, mod);
        const onMatch = /\bSET\s+NOCOUNT\s+ON\b/i.exec(body);
        const offMatch = /\bSET\s+NOCOUNT\s+OFF\b/i.exec(body);
        const kindLabel = mod.kind.charAt(0) + mod.kind.slice(1).toLowerCase();

        if (!onMatch) {
            missing++;
            add('NC001', mod.s, mod.name,
                kindLabel + ' ' + mod.name + ' has no SET NOCOUNT ON',
                { s: start, e: start, text: '\nSET NOCOUNT ON;' });
        } else if (offMatch && offMatch.index > onMatch.index) {
            missing++;
            add('NC002', mod.s + offMatch.index, mod.name,
                'SET NOCOUNT ON is cancelled by a later SET NOCOUNT OFF', null);
        }
    });

    return { mods: mods, missing: missing };
}

/* ============================ security analysis ============================
   Mirrors the review done on the SIP database: a dynamic SQL string that is
   executed is only a problem when a caller supplied value reaches it. Values
   that come from a config table (PMSSettings.SIPServer, pmsTradingMember ...)
   and values with a non-string type are not caller controlled, so they stay
   silent - that is what keeps this from firing on every EXEC(@Sql).
   ========================================================================== */

/* @name <type> pairs out of a parameter list or a DECLARE statement. */
function readDeclarations(text, isParam, into) {
    const re = /@(\w+)\s+(?:AS\s+)?([A-Za-z_]\w*)\s*(?:\(\s*([\w,\s]*)\s*\))?/g;
    let m;
    while ((m = re.exec(text)) !== null) {
        const name = m[1].toUpperCase();
        const type = m[2].toUpperCase();
        if (!STRING_TYPES.has(type) && !SAFE_TYPES.has(type) && type !== 'TABLE') continue;
        if (into.has(name)) continue;
        into.set(name, {
            name: m[1],
            type: type,
            size: m[3] || '',
            isParam: isParam,
            /* char(1) style parameters cannot hold a payload */
            tainted: isParam && STRING_TYPES.has(type) && !/^1$/.test((m[3] || '').trim()),
            fromTable: false,
            evidence: []
        });
    }
}

function collectVariables(sql, codeDoc) {
    const vars = new Map();

    /* module parameter lists */
    findModules(codeDoc).forEach(mod => {
        readDeclarations(codeDoc.slice(mod.headerEnd, bodyStart(codeDoc, mod)), true, vars);
    });

    /* DECLARE blocks */
    const re = /\bDECLARE\b/gi;
    let m;
    while ((m = re.exec(codeDoc)) !== null) {
        const rest = codeDoc.slice(m.index + 7, m.index + 4000);
        const stop = rest.search(/\n\s*(SET|SELECT|INSERT|UPDATE|DELETE|IF|BEGIN|END|EXEC|EXECUTE|PRINT|RETURN|WHILE|CREATE|DROP|FETCH|OPEN|CLOSE|DEALLOCATE|GO)\b/i);
        readDeclarations(stop < 0 ? rest : rest.slice(0, stop), false, vars);
    }
    return vars;
}

/* Split a statement body into `@var = expr` segments at top level commas -
   paren depth is tracked so a function call's own commas ("Fn(1,2)") don't
   split it. Shared by SET/SELECT assignments and DECLARE initializers, which
   both allow a comma separated list of the same shape. */
function splitTopLevel(body) {
    const toks = tokenize(body);
    let depth = 0, segStart = 0;
    const segs = [];
    for (let i = 0; i < toks.length; i++) {
        const t = toks[i];
        if (t.v === '(') depth++;
        else if (t.v === ')') depth--;
        else if (t.v === ',' && depth === 0) {
            segs.push(body.slice(segStart, t.s));
            segStart = t.e;
        }
    }
    segs.push(body.slice(segStart));
    return segs;
}

const ASSIGN_STOP_RE = /\n\s*(SET|SELECT|INSERT|UPDATE|DELETE|IF|ELSE|BEGIN|END|EXEC|EXECUTE|PRINT|RETURN|WHILE|CREATE|DROP|FETCH|OPEN|CLOSE|DEALLOCATE|DECLARE|GO)\b/i;

/* Every SET/SELECT assignment to a variable, with the right hand side kept
   intact so the quoting around a concatenated parameter can be inspected.

   The SIP procedures almost always read config values with a single
   multi-column statement: "Select @SIPServer=SIPServer, @SIPDb = SIPDb, ...
   From PMSSettings(nolock)". Treating that as one assignment (as a naive
   "SET|SELECT @x =" regex does) only ever catches the first column - every
   other variable in the list would look like it came from nowhere and get
   flagged "confirm where it is set" instead of "from a config table, safe".
   So each statement's column list is split into segments, and "reads from a
   real table" is judged once per statement and applied to every variable
   that statement assigns. */
function collectAssignments(noCmt) {
    const out = [];
    const headRe = /\b(?:SET|SELECT)\s+(?=@\w+\s*=)/gi;
    let hm;
    while ((hm = headRe.exec(noCmt)) !== null) {
        const from = hm.index + hm[0].length;
        const rest = noCmt.slice(from, from + 8000);
        const stop = rest.search(ASSIGN_STOP_RE);
        const body = stop < 0 ? rest : rest.slice(0, stop);
        const fromTable = /\bFROM\b/i.test(body) && !/\+/.test(body);

        let pos = 0;
        splitTopLevel(body).forEach(seg => {
            const am = /^\s*@(\w+)\s*=\s*/i.exec(seg);
            if (am) {
                out.push({
                    target: am[1].toUpperCase(),
                    s: from + pos + am[0].length,
                    rhs: seg.slice(am[0].length),
                    fromTable: fromTable
                });
            }
            pos += seg.length + 1;         /* +1 for the comma consumed between segments */
        });
    }
    return out;
}

/* `DECLARE @sql VARCHAR(MAX) = 'select ... ' + @param` initializes and
   concatenates in the same statement - a separate shape from SET/SELECT, but
   just as common a sink, and just as able to carry a tainted parameter
   straight into a variable that later gets executed. */
function collectDeclareInits(noCmt) {
    const out = [];
    const headRe = /\bDECLARE\s+/gi;
    let hm;
    while ((hm = headRe.exec(noCmt)) !== null) {
        const from = hm.index + hm[0].length;
        const rest = noCmt.slice(from, from + 8000);
        const stop = rest.search(ASSIGN_STOP_RE);
        const body = stop < 0 ? rest : rest.slice(0, stop);

        let pos = 0;
        splitTopLevel(body).forEach(seg => {
            const dm = /^\s*@(\w+)\s+(?:AS\s+)?[A-Za-z_][\w.]*\s*(?:\([^)]*\))?\s*=\s*/i.exec(seg);
            if (dm) {
                out.push({
                    target: dm[1].toUpperCase(),
                    s: from + pos + dm[0].length,
                    rhs: seg.slice(dm[0].length),
                    fromTable: /\bFROM\b/i.test(seg) && !/\+/.test(seg)
                });
            }
            pos += seg.length + 1;
        });
    }
    return out;
}

/* Is @param inside a quoted literal in the generated SQL, or bare?  The chunk
   of literal immediately before "'+@p" ends with an escaped quote ('') when the
   value lands inside quotes; anything else means it lands as raw SQL. */
function concatContext(rhs, at) {
    const before = rhs.slice(Math.max(0, at - 40), at);
    if (/''\s*'?\s*\+\s*$/.test(before) || /''\s*$/.test(before.replace(/\s*\+\s*$/, ''))) return 'quoted';
    if (/(=|,|\(|\bLIKE\b|\bIN\b|\bAND\b|\bOR\b|\bWHERE\b|\bVALUES\b)\s*'?\s*\+?\s*$/i.test(before)) return 'bare';
    return 'bare';
}

function isSanitized(rhs, at) {
    const before = rhs.slice(Math.max(0, at - 120), at);
    return /\b(QUOTENAME|REPLACE|CONVERT|CAST|STR|FORMAT|ISNUMERIC|TRY_CONVERT|TRY_CAST)\s*\([^()]*$/i.test(before);
}

function analyzeSecurity(sql, codeDoc, spans, lineOf, findings) {
    const noCmt = blankSpans(sql, spans.comments);      /* literals kept intact */
    const vars = collectVariables(sql, codeDoc);
    const assigns = collectAssignments(noCmt).concat(collectDeclareInits(noCmt))
        .sort((a, b) => a.s - b.s);

    function add(rule, off, obj, msg) {
        const f = mkFinding(rule, lineOf(off), obj, msg, snipAt(sql, off), null);
        f.off = off;
        findings.push(f);
    }

    /* ---- taint propagation over the assignments, in source order ----
       Only an actual parameter starts as tainted. Every var also carries
       `origin`, the parameter that first tainted it, so a flow reported many
       hops later (@sql2 = @sql1, ... EXEC(@sql2)) still names the real
       parameter instead of the intermediate accumulator variable. A line like
       `SET @sql = @sql + ... + @clientid` must not treat @sql-referencing-
       itself as a new taint source - that produced a bogus "parameter @sql"
       finding, since @sql is the accumulator being inspected, not a caller
       supplied value. */
    const flows = [];                       /* {target, param, off, ctx, ident} */
    for (let pass = 0; pass < 2; pass++) {
        assigns.forEach(a => {
            const v = vars.get(a.target);
            if (a.fromTable && v) v.fromTable = true;   /* read out of a table */
            const pre = /@(\w+)/g;
            let pm;
            while ((pm = pre.exec(a.rhs)) !== null) {
                const srcName = pm[1].toUpperCase();
                if (srcName === a.target) continue;      /* self accumulation, no new taint */
                const src = vars.get(srcName);
                if (!src || !src.tainted) continue;
                if (isSanitized(a.rhs, pm.index)) continue;
                const origin = src.origin || (src.isParam ? src : null);
                if (!origin) continue;
                if (v) { v.tainted = true; v.origin = v.origin || origin; }
                if (pass === 0) {
                    flows.push({
                        target: a.target,
                        param: origin,
                        off: a.s + pm.index,
                        ctx: concatContext(a.rhs, pm.index),
                        ident: origin.isParam && IDENT_PARAM_RE.test(origin.name.toUpperCase())
                    });
                }
            }
        });
    }

    /* ---- execution sinks ---- */
    const sinks = [];
    const execRe = /\b(?:EXEC|EXECUTE)\s*\(/gi;
    let m;
    while ((m = execRe.exec(noCmt)) !== null) {
        const toks = tokenize(noCmt.slice(m.index));
        const open = toks.findIndex(t => t.v === '(');
        const close = open >= 0 ? matchParen(toks, open) : -1;
        const inner = close > 0 ? noCmt.slice(m.index + toks[open].e, m.index + toks[close].s) : '';
        sinks.push({ off: m.index, inner: inner, how: 'EXEC()' });
    }
    const spRe = /\bsp_executesql\b/gi;
    while ((m = spRe.exec(noCmt)) !== null) {
        const rest = noCmt.slice(m.index, m.index + 400);
        /* a real parameter list means the statement is parameterised */
        const parameterised = /,\s*N?'\s*@/.test(rest);
        sinks.push({ off: m.index, inner: rest.split(/\n/)[0], how: 'sp_executesql', parameterised: parameterised });
    }
    /* OPENQUERY / OPENROWSET / OPENDATASOURCE also run their query text
       verbatim on the remote server - a tainted parameter reaching the query
       argument is just as much an injection sink as EXEC(). */
    REMOTE_FUNCS.lastIndex = 0;
    while ((m = REMOTE_FUNCS.exec(noCmt)) !== null) {
        const toks = tokenize(noCmt.slice(m.index));
        const open = toks.findIndex(t => t.v === '(');
        const close = open >= 0 ? matchParen(toks, open) : -1;
        const inner = close > 0 ? noCmt.slice(m.index + toks[open].e, m.index + toks[close].s) : '';
        sinks.push({ off: m.index, inner: inner, how: m[1].toUpperCase() + '(...)' });
    }

    const reported = new Set();

    sinks.forEach(sink => {
        const used = new Set();
        let vm;
        const vre = /@(\w+)/g;
        while ((vm = vre.exec(sink.inner)) !== null) used.add(vm[1].toUpperCase());

        /* inline payload: EXEC('... ' + @param + ' ...') with no variable */
        used.forEach(u => {
            const v = vars.get(u);
            if (v && v.tainted && v.isParam && !sink.parameterised) {
                const key = 'inline:' + u + ':' + sink.off;
                if (!reported.has(key)) {
                    reported.add(key);
                    add(v.isParam && IDENT_PARAM_RE.test(v.name.toUpperCase()) ? 'SEC002' : 'SEC001',
                        sink.off, '@' + v.name,
                        'CRITICAL: parameter @' + v.name + ' (' + v.type.toLowerCase() +
                        ') is concatenated straight into ' + sink.how + ' - SQL injection');
                }
            }
        });

        if (sink.parameterised) return;

        flows.forEach(fl => {
            if (!used.has(fl.target)) return;
            const key = fl.param.name + ':' + fl.off;
            if (reported.has(key)) return;
            reported.add(key);

            const where = 'built into @' + fl.target + ', executed by ' + sink.how +
                          ' on line ' + lineOf(sink.off);
            if (fl.ident) {
                add('SEC002', fl.off, '@' + fl.param.name,
                    'CRITICAL: parameter @' + fl.param.name +
                    ' is a caller supplied identifier or predicate - ' + where +
                    '. Whitelist it or use QUOTENAME, sp_executesql cannot bind an object name');
            } else if (fl.ctx === 'bare') {
                add('SEC001', fl.off, '@' + fl.param.name,
                    'CRITICAL: parameter @' + fl.param.name + ' (' + fl.param.type.toLowerCase() +
                    ') is concatenated UNQUOTED - ' + where + '. Any SQL passed in runs as is');
            } else {
                add('SEC001', fl.off, '@' + fl.param.name,
                    'HIGH: parameter @' + fl.param.name + ' (' + fl.param.type.toLowerCase() +
                    ') is concatenated inside a quoted literal - ' + where +
                    ". A single quote in the value breaks out. Bind it with sp_executesql");
            }
        });
    });

    /* ---- remote execution surface ---- */
    const fourPart = /\[\s*'\s*\+\s*@(\w+)\s*\+\s*'\s*\]\s*\./g;
    const seenRemote = new Set();
    while ((m = fourPart.exec(noCmt)) !== null) {
        const v = vars.get(m[1].toUpperCase());
        const line = lineOf(m.index);
        if (seenRemote.has(line)) continue;
        seenRemote.add(line);
        const src = v && v.tainted ? 'a PARAMETER - the remote target is caller controlled'
                  : v && v.fromTable ? 'a config table, not caller controlled'
                  : 'a variable - confirm where it is set';
        add('SEC003', m.index, '@' + m[1],
            (v && v.tainted ? 'CRITICAL' : 'REVIEW') +
            ': dynamic SQL builds a linked server four part name from @' + m[1] +
            ' and executes it. Server name comes from ' + src);
    }

    const atRe = /\bEXEC(?:UTE)?\s*\([\s\S]{0,4000}?\)\s*AT\s+([\w\[\]\.]+)/gi;
    while ((m = atRe.exec(noCmt)) !== null) {
        add('SEC003', m.index, m[1],
            'REVIEW: pass through query executed on linked server ' + m[1] +
            ' with EXEC ... AT - the text is run by the remote server, not parsed locally');
    }

    /* Only flag OPENQUERY/OPENROWSET/OPENDATASOURCE when the query text is
       actually built by concatenation - a hardcoded literal query is not a
       "dynamic query" risk and would just be noise. */
    REMOTE_FUNCS.lastIndex = 0;
    while ((m = REMOTE_FUNCS.exec(noCmt)) !== null) {
        const head = noCmt.slice(m.index, m.index + 300);
        if (!/'\s*\+|\+\s*@/.test(head)) continue;
        add('SEC003', m.index, m[1].toUpperCase(),
            'REVIEW: ' + m[1].toUpperCase() + ' runs a dynamically built query on the remote server' +
            ' - check the tainted parameter finding above for this line');
    }

    if (/\bsp_addlinkedserver\b|\bsp_addlinkedsrvlogin\b/i.test(noCmt)) {
        const mm = /\bsp_addlinkedserver\b|\bsp_addlinkedsrvlogin\b/i.exec(noCmt);
        add('SEC003', mm.index, mm[0],
            'REVIEW: script creates or configures a linked server login at runtime');
    }

    /* ---- credentials in plain text (value redacted) ---- */
    SECRET_PATTERNS.forEach(p => {
        p.re.lastIndex = 0;
        let sm;
        while ((sm = p.re.exec(noCmt)) !== null) {
            const val = sm[sm.length - 1] || '';
            if (/^N?''$/.test(val.trim())) continue;             /* empty */
            const f = mkFinding('SEC004', lineOf(sm.index), p.what,
                'CRITICAL: ' + p.what + ' is hard coded in the script. Move it to a credential ' +
                'or integrated auth, then rotate the value - it is in source control history',
                redactSecrets(snipAt(sql, sm.index)), null);
            f.off = sm.index;
            findings.push(f);
        }
    });

    /* Connection-string idiom, checked one literal at a time so "user id" on
       one line can never be paired with an unrelated "password" elsewhere. */
    spans.strings.forEach(sp => {
        const lit = sql.slice(sp[0], sp[1]);
        if (lit.length > 4000) return;
        CONN_STRING_RE.lastIndex = 0;
        const cm = CONN_STRING_RE.exec(lit);
        if (!cm) return;
        const off = sp[0] + cm.index;
        const f = mkFinding('SEC004', lineOf(off), 'connection string',
            'CRITICAL: connection string with user id and password hard coded in the script. ' +
            'Move it to a credential or integrated auth, then rotate the value - it is in source control history',
            redactSecrets(snipAt(sql, off)), null);
        f.off = off;
        findings.push(f);
    });
}

/* Never echo a secret back into the UI or the CSV. */
function redactSecrets(line) {
    return line
        .replace(/\b(pass\s*word|pwd|passwd|secret)(\s*=\s*)(N?'[^']*'|[^\s;'")]+)/gi, '$1$2********')
        .replace(/(@rmtpassword\s*=\s*)(N?'[^']*'|[^\s;'")]+)/gi, '$1********')
        .replace(/\b(user\s*id|uid)(\s*=\s*)[^;'"]+/gi, '$1$2********');
}

/* -------------------------------- analyzer -------------------------------- */

function analyze(sql) {
    const spans = lexSpans(sql);
    const lineOf = makeLineOf(lineStartsOf(sql));

    /* codeDoc: comments + literals blanked */
    const codeDoc = blankSpans(blankSpans(sql, spans.comments), spans.strings);

    /* dynDoc: comments blanked, literal delimiters + concat glue blanked */
    const dynBuf = blankSpans(sql, spans.comments).split('');
    spans.strings.forEach(sp => {
        dynBuf[sp[0]] = ' ';
        if (sp[1] - 1 > sp[0]) dynBuf[sp[1] - 1] = ' ';
        for (let i = sp[0] + 1; i < sp[1] - 1; i++) if (dynBuf[i] === "'") dynBuf[i] = ' ';
    });

    /* merge adjacent literals whose glue is pure string concatenation */
    const chains = [];
    let cur = null;
    spans.strings.forEach((sp, idx) => {
        if (!cur) cur = { s: sp[0], e: sp[1] };
        else cur.e = sp[1];
        const nxt = spans.strings[idx + 1];
        if (nxt && isConcatGlue(sql.slice(sp[1], nxt[0]))) {
            blankRanges(dynBuf, [[sp[1], nxt[0]]]);
            return;
        }
        chains.push(cur);
        cur = null;
    });
    if (cur) chains.push(cur);

    /* a chain only counts as dynamic SQL if it really looks like a statement */
    const dynBlocks = chains.filter(ch => {
        const txt = sql.slice(ch.s, ch.e);
        return txt.length >= 20 &&
               /\b(FROM|JOIN)\b/i.test(txt) &&
               /\b(SELECT|UPDATE|DELETE|INSERT|MERGE)\b/i.test(txt);
    });

    /* comments that only exist inside literal text must be masked in dynDoc */
    let dynDoc = dynBuf.join('');
    const dynComments = [];
    dynBlocks.forEach(ch => {
        const seg = dynDoc.slice(ch.s, ch.e);
        const re = /--[^\n]*|\/\*[\s\S]*?\*\//g;
        let m;
        while ((m = re.exec(seg)) !== null) dynComments.push([ch.s + m.index, ch.s + m.index + m[0].length]);
    });
    if (dynComments.length) {
        const b2 = dynDoc.split('');
        blankRanges(b2, dynComments);
        dynDoc = b2.join('');
    }

    const inDynBlock = off => dynBlocks.some(ch => off > ch.s && off < ch.e);
    const inAnyLiteral = off => spans.strings.some(sp => off > sp[0] && off < sp[1]);

    /* READ UNCOMMITTED isolation scopes */
    const ruOffsets = [];
    const ruRe = /\bSET\s+TRANSACTION\s+ISOLATION\s+LEVEL\s+READ\s+UNCOMMITTED\b/gi;
    let ruM;
    while ((ruM = ruRe.exec(codeDoc)) !== null) ruOffsets.push(ruM.index);

    /* pass A static, pass B dynamic */
    const staticRefs = scanRefs(codeDoc);
    const seen = new Set(staticRefs.map(r => r.s));
    const dynRefs = scanRefs(dynDoc).filter(r =>
        !seen.has(r.s) && inDynBlock(r.s) && inAnyLiteral(r.insertAt));
    dynRefs.forEach(r => { r.dynamic = true; });

    const refs = staticRefs.concat(dynRefs).sort((x, y) => x.s - y.s);

    const findings = [];
    const stats = { sources: 0, covered: 0, missing: 0, dynamic: dynBlocks.length, procs: 0, nocount: 0, security: 0 };

    function add(rule, ref, msg, fix) {
        const f = mkFinding(rule, lineOf(ref.s), ref.disp + (ref.alias ? ' ' + ref.alias : ''),
                            msg, snipAt(sql, ref.s), fix);
        f.off = ref.s;
        f.dynamic = ref.dynamic;
        if (ruOffsets.some(o => o < ref.s)) f.msg += ' (batch sets READ UNCOMMITTED isolation)';
        findings.push(f);
    }

    refs.forEach(ref => {
        const hints = ref.hints || [];

        /* Nothing that cannot carry a table hint is ever reported: temp tables,
           table variables, CTEs, derived tables, TVFs, OPENQUERY, trigger
           pseudo tables and the target of an INSERT/UPDATE/DELETE/MERGE. */
        if (ref.kind !== 'read' && ref.kind !== 'system') return;

        stats.sources++;

        if (hints.some(h => NOLOCK_EQUIVALENT.has(h))) {
            stats.covered++;                       /* hinted - silent, WITH or not */
            return;
        }

        stats.missing++;
        /* A source that already carries a hint gets no auto fix: a second WITH
           clause is a syntax error and NOLOCK conflicts with UPDLOCK / TABLOCK. */
        const fix = hints.length ? null : { s: ref.insertAt, e: ref.insertAt, text: ' WITH (NOLOCK)' };
        const extra = hints.length ? ' (has ' + hints.join(', ') + ' but no NOLOCK - fix by hand)' : '';
        if (ref.dynamic) add('NL005', ref, 'Dynamic SQL source ' + ref.disp + ' has no NOLOCK' + extra, fix);
        else add('NL001', ref, ref.stmtType + ' source ' + ref.disp + ' has no NOLOCK' + extra, fix);
    });

    const nc = analyzeNoCount(sql, codeDoc, lineOf, findings);
    stats.procs = nc.mods.length;
    stats.nocount = nc.missing;

    analyzeSecurity(sql, codeDoc, spans, lineOf, findings);
    stats.security = findings.filter(f => f.cat === 'security').length;

    findings.sort((a, b) => (a.line - b.line) || (a.off - b.off));
    return { findings: findings, stats: stats };
}

/* --------------------------------- autofix -------------------------------- */

function applyFixes(sql, findings) {
    const edits = findings.filter(f => f.fix).map(f => f.fix);
    edits.sort((a, b) => b.s - a.s || b.e - a.e);
    let out = sql;
    let n = 0;
    let lastStart = Infinity;
    edits.forEach(ed => {
        if (ed.e > lastStart) return;                     /* overlapping edit, skip */
        out = out.slice(0, ed.s) + ed.text + out.slice(ed.e);
        lastStart = ed.s;
        n++;
    });
    return { sql: out, count: n };
}

/* ================================ SCRIPT CHECK ==============================
   For a whole script dump (many CREATE/ALTER PROCEDURE|FUNCTION|TRIGGER|VIEW
   batches back to back), not a single pasted proc: reuses analyze() as-is for
   NOLOCK/NOCOUNT/security (unchanged, zero regression risk to the audit view),
   adds a check for a missing GO batch separator between objects, and counts
   each object kind. Deliberately a separate object scanner from findModules()
   above rather than extending it - findModules() is also used by the NOCOUNT
   and security engines, which have their own tested assumptions (e.g. a
   FUNCTION body can't contain SET, so it's skipped there); teaching it about
   VIEW as well would need matching guards added in three places for no
   benefit here, since this check only needs header positions. ========== */

function findScriptObjects(codeDoc) {
    const re = /\b(CREATE|ALTER)\s+(PROCEDURE|PROC|FUNCTION|TRIGGER|VIEW)\s+((?:\[[^\]]*\]|[A-Za-z_][\w$#]*)(?:\s*\.\s*(?:\[[^\]]*\]|[A-Za-z_][\w$#]*))*)/gi;
    const objs = [];
    let m;
    while ((m = re.exec(codeDoc)) !== null) {
        const kind = m[2].toUpperCase() === 'PROC' ? 'PROCEDURE' : m[2].toUpperCase();
        objs.push({ kind: kind, name: m[3].replace(/\s+/g, ''), s: m.index, e: codeDoc.length });
    }
    objs.forEach((o, k) => { if (objs[k + 1]) o.e = objs[k + 1].s; });
    return objs;
}

/* A standalone GO on its own line (optionally "GO 5" to repeat the batch,
   per real T-SQL batch syntax) anywhere between one object and the next
   counts as present - this checks presence, not exact placement. Comments
   are already blanked in codeDoc, so a comment-only line reads as blank and
   never false-matches. */
const STANDALONE_GO_RE = /^[ \t]*GO(?:[ \t]+\d+)?[ \t]*$/im;

function analyzeGo(sql, codeDoc, lineOf, objs, findings) {
    objs.forEach((obj, i) => {
        const isLast = i === objs.length - 1;
        const gapEnd = isLast ? codeDoc.length : objs[i + 1].s;
        const gap = codeDoc.slice(obj.s, gapEnd);
        if (STANDALONE_GO_RE.test(gap)) return;
        const kindLabel = obj.kind.charAt(0) + obj.kind.slice(1).toLowerCase();
        const msg = isLast
            ? kindLabel + ' ' + obj.name + ' has no trailing GO before end of script'
            : kindLabel + ' ' + obj.name + ' has no GO before the next batch (' + objs[i + 1].name + ')';
        const f = mkFinding('GO001', lineOf(obj.s), obj.name, msg, snipAt(sql, obj.s), null);
        f.off = obj.s;
        findings.push(f);
    });
}

/* Runs the full existing audit (unchanged) plus the GO check, and counts each
   object kind for the summary ribbon. */
function analyzeScript(sql) {
    const result = analyze(sql);
    const spans = lexSpans(sql);
    const codeDoc = blankSpans(blankSpans(sql, spans.comments), spans.strings);
    const lineOf = makeLineOf(lineStartsOf(sql));
    const objs = findScriptObjects(codeDoc);

    analyzeGo(sql, codeDoc, lineOf, objs, result.findings);
    result.findings.sort((a, b) => (a.line - b.line) || (a.off - b.off));

    const counts = { PROCEDURE: 0, FUNCTION: 0, TRIGGER: 0, VIEW: 0 };
    objs.forEach(o => { counts[o.kind]++; });
    result.objectCounts = counts;
    result.goMissing = result.findings.filter(f => f.rule === 'GO001').length;
    return result;
}

/* --------------------------------- format ---------------------------------
   vendor/sql-formatter.min.js (github.com/sql-formatter-org/sql-formatter, MIT).
   Two T-SQL things it doesn't know about:
   (1) "GO" is an SSMS/sqlcmd client directive, not part of SQL grammar, so
       left alone it glues "END GO CREATE PROCEDURE..." onto one line, which
       no longer parses as separate batches. Split on real standalone GO
       lines first (codeDoc-based, so a GO inside a string/comment is
       correctly ignored - same check as analyzeGo above), format each batch
       independently, then rejoin with GO.
   (2) a table hint - "WITH (NOLOCK)" etc, the whole reason this tool exists -
       gets misread as a CTE's WITH clause and split apart ("Users u\nWITH\n
       (NOLOCK)"). Protected per batch: every "WITH (...)" span is swapped
       for a plain-word placeholder token before formatting (a CTE never
       matches this - CTE syntax is always "WITH name AS (", never "WITH ("
       directly) and restored, uppercased, straight after. */
function protectTableHints(sql) {
    const map = [];
    const text = sql.replace(/\bWITH\s*(\([^()]*\))/gi, full => {
        const token = 'ZzHINTzZ' + map.length + 'ZzEND';
        map.push(full.toUpperCase());
        return token;
    });
    return { text, map };
}

function restoreTableHints(text, map) {
    return text.replace(/ZzHINTzZ(\d+)ZzEND/g, (m, i) => map[Number(i)]);
}

function formatSql(sql) {
    const spans = lexSpans(sql);
    const codeDoc = blankSpans(blankSpans(sql, spans.comments), spans.strings);
    const lines = sql.split('\n');
    const codeLines = codeDoc.split('\n');
    const batches = [];
    let start = 0;
    for (let i = 0; i < codeLines.length; i++) {
        if (STANDALONE_GO_RE.test(codeLines[i])) {
            batches.push(lines.slice(start, i).join('\n'));
            start = i + 1;
        }
    }
    batches.push(lines.slice(start).join('\n'));

    return batches.map(batch => {
        const trimmed = batch.trim();
        if (!trimmed) return '';
        try {
            const protected_ = protectTableHints(trimmed);
            const formatted = sqlFormatter.format(protected_.text, { language: 'tsql', keywordCase: 'upper' });
            return restoreTableHints(formatted, protected_.map);
        } catch (e) {
            return batch;   /* formatter choked on this batch - leave it untouched rather than losing text */
        }
    }).join('\nGO\n');
}

/* ================================ SQL COMPARE ==============================
   Line diff comes from jsdiff (vendor/diff.min.js, BSD-3-Clause). Rows are
   aligned into a side by side view here, and paired changed lines get a word
   level diff so the exact edit inside the line is visible.
   ========================================================================== */

function escHtml(s) {
    return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

/* Normalisation used only for comparison - the rendered text stays original. */
function cmpKey(line, opt) {
    let t = line;
    if (opt.ignoreComments) t = t.replace(/--.*$/, '').replace(/\/\*[\s\S]*?\*\//g, ' ');
    if (opt.ignoreWhitespace) t = t.replace(/\s+/g, ' ').trim();
    if (opt.ignoreCase) t = t.toLowerCase();
    return t;
}

/* Word overlap ratio, used to decide whether a removed line and an added line
   are the same line edited or two unrelated lines. */
function simRatio(a, b) {
    const ta = a.toLowerCase().match(/[a-z0-9_#@$.]+/g) || [];
    const tb = b.toLowerCase().match(/[a-z0-9_#@$.]+/g) || [];
    if (!ta.length && !tb.length) return 1;
    if (!ta.length || !tb.length) return 0;
    const bag = new Map();
    ta.forEach(t => bag.set(t, (bag.get(t) || 0) + 1));
    let common = 0;
    tb.forEach(t => {
        const c = bag.get(t);
        if (c) { common++; bag.set(t, c - 1); }
    });
    return 2 * common / (ta.length + tb.length);
}

const PAIR_THRESHOLD = 0.4;

/* Align a removed block against an added block so only genuinely related lines
   sit side by side; the rest stay as pure add or pure remove rows. */
function alignBlock(dels, ins) {
    const n = dels.length, m = ins.length;
    if (!n) return ins.slice();
    if (!m) return dels.slice();

    const pair = (d, i) => ({ t: 'mod', ln: d.ln, rn: i.rn, left: d.left, right: i.right });

    if (n * m > 40000) {                       /* huge block - pair positionally */
        const out = [];
        const k = Math.min(n, m);
        for (let i = 0; i < k; i++) out.push(pair(dels[i], ins[i]));
        for (let i = k; i < n; i++) out.push(dels[i]);
        for (let i = k; i < m; i++) out.push(ins[i]);
        return out;
    }

    const score = [], from = [];
    for (let i = 0; i <= n; i++) {
        score.push(new Float64Array(m + 1));
        from.push(new Uint8Array(m + 1));
    }
    for (let i = 1; i <= n; i++) from[i][0] = 1;            /* 1 = unpaired removal */
    for (let j = 1; j <= m; j++) from[0][j] = 2;            /* 2 = unpaired addition */

    for (let i = 1; i <= n; i++) {
        for (let j = 1; j <= m; j++) {
            const s = simRatio(dels[i - 1].left, ins[j - 1].right);
            const match = s >= PAIR_THRESHOLD ? score[i - 1][j - 1] + s : -1;
            const skipD = score[i - 1][j];
            const skipI = score[i][j - 1];
            if (match >= skipD && match >= skipI) { score[i][j] = match; from[i][j] = 3; }
            else if (skipD >= skipI) { score[i][j] = skipD; from[i][j] = 1; }
            else { score[i][j] = skipI; from[i][j] = 2; }
        }
    }

    const out = [];
    let i = n, j = m;
    while (i > 0 || j > 0) {
        const dir = from[i][j];
        if (dir === 3) { i--; j--; out.push(pair(dels[i], ins[j])); }
        else if (j === 0 || (dir === 1 && i > 0)) { i--; out.push(dels[i]); }
        else { j--; out.push(ins[j]); }
    }
    return out.reverse();
}

/* jsdiff over normalised lines, then map back to the original text. */
function diffSql(leftText, rightText, opt) {
    const L = leftText.replace(/\r\n/g, '\n').split('\n');
    const R = rightText.replace(/\r\n/g, '\n').split('\n');
    const parts = Diff.diffArrays(L.map(l => cmpKey(l, opt)), R.map(l => cmpKey(l, opt)));

    const rows = [];
    let li = 0, ri = 0, pending = [];

    function flush() {
        if (!pending.length) return;
        alignBlock(pending.filter(p => p.t === 'del'), pending.filter(p => p.t === 'ins'))
            .forEach(r => rows.push(r));
        pending = [];
    }

    parts.forEach(part => {
        const n = part.count === undefined ? part.value.length : part.count;
        if (part.added) {
            for (let k = 0; k < n; k++) pending.push({ t: 'ins', ln: 0, rn: ri + 1, left: '', right: R[ri++] });
        } else if (part.removed) {
            for (let k = 0; k < n; k++) pending.push({ t: 'del', ln: li + 1, rn: 0, left: L[li++], right: '' });
        } else {
            flush();
            for (let k = 0; k < n; k++) {
                rows.push({ t: 'same', ln: li + 1, rn: ri + 1, left: L[li++], right: R[ri++] });
            }
        }
    });
    flush();
    return rows;
}

/* Word level highlight for a changed line pair, applied as CodeMirror
   markText ranges (not HTML strings - there is no separate render surface
   to build HTML for any more, the editor IS the display). */
function markWordDiff(leftCm, li, rightCm, ri, a, b) {
    if (a.length > 4000 || b.length > 4000) return;      /* pathological line - skip, stay responsive */
    const parts = Diff.diffWordsWithSpace(a, b);
    let lch = 0, rch = 0;
    parts.forEach(p => {
        const len = p.value.length;
        if (p.added) {
            rightCm.markText({ line: ri, ch: rch }, { line: ri, ch: rch + len }, { className: 'chg-ins' });
            rch += len;
        } else if (p.removed) {
            leftCm.markText({ line: li, ch: lch }, { line: li, ch: lch + len }, { className: 'chg-del' });
            lch += len;
        } else {
            lch += len;
            rch += len;
        }
    });
}

/* ----------------------------------- UI ----------------------------------- */

/* CodeMirror's stock T-SQL mode (vendor/codemirror, MIT) already covers
   keywords/strings/comments/numbers/@variables; the only tool-specific
   addition is a thin overlay mode that re-tags NOLOCK & co with their own
   style, since that is this tool's whole point. */
CodeMirror.defineMode('sql-hints', function (config) {
    const base = CodeMirror.getMode(config, 'text/x-mssql');
    const hintRe = new RegExp('^(' + Array.from(HINT_WORDS).join('|') + ')\\b', 'i');
    const overlay = {
        token: function (stream) {
            if (stream.match(hintRe)) return 'hint-nolock';
            while (stream.next() != null && !stream.match(hintRe, false)) { /* advance to next candidate */ }
            return null;
        }
    };
    return CodeMirror.overlayMode(base, overlay);
});
CodeMirror.defineMIME('text/x-sql-hints', 'sql-hints');

const CM_OPTIONS = {
    mode: 'text/x-sql-hints',
    lineNumbers: true,
    tabSize: 4,
    indentUnit: 4,
    lineWrapping: false
};

/* Script Check only: folds a CREATE/ALTER PROCEDURE|FUNCTION|TRIGGER|VIEW
   header down to its matching GO (or the next such header, or end of file)
   - "collapse the SPs like SSMS". Combined with the vendored generic
   brace-paren folder, so a plain "CREATE TABLE #tmp (...)" also folds on its
   own parens, same as the SSMS screenshot this was built from. Written
   against cm.getLine() directly rather than the audit engine's codeDoc, so
   it stays simple and self-contained; it is a fold trigger, not an audit
   finding, so it does not need comment/string-aware masking to be useful. */
function sqlBatchFold(cm, start) {
    const HEADER_RE = /^\s*(CREATE|ALTER)\s+(PROCEDURE|PROC|FUNCTION|TRIGGER|VIEW)\b/i;
    const line = start.line;
    const lineText = cm.getLine(line);
    if (!HEADER_RE.test(lineText)) return null;

    const lastLine = cm.lastLine();
    for (let i = line + 1; i <= lastLine; i++) {
        const text = cm.getLine(i);
        if (/^[ \t]*GO(?:[ \t]+\d+)?[ \t]*$/i.test(text) || HEADER_RE.test(text)) {
            if (i - 1 <= line) return null;
            return { from: CodeMirror.Pos(line, lineText.length), to: CodeMirror.Pos(i - 1, cm.getLine(i - 1).length) };
        }
    }
    if (lastLine > line) {
        return { from: CodeMirror.Pos(line, lineText.length), to: CodeMirror.Pos(lastLine, cm.getLine(lastLine).length) };
    }
    return null;
}

const CM_OPTIONS_SCRIPT = Object.assign({}, CM_OPTIONS, {
    foldGutter: true,
    gutters: ['CodeMirror-linenumbers', 'CodeMirror-foldgutter'],
    foldOptions: {
        widget: '…',
        rangeFinder: CodeMirror.fold.combine(sqlBatchFold, CodeMirror.fold['brace-paren']),
        foldOnChangeTimeSpan: 150   /* addon default is 600ms - too sluggish after pasting a big script */
    }
});

document.addEventListener('DOMContentLoaded', () => {
    const $ = id => document.getElementById(id);

    /* One scrollbar-annotation track per severity colour, so the scrollbar
       itself previews where each kind of finding sits before you scroll -
       same colours as the line/gutter/tag marks, via addon/scroll. 'go' is
       only ever produced in Script Check, but it's harmless (always empty)
       on the audit editor, so one shared list keeps both in step. */
    const SEVERITY_CLASSES = ['critical', 'high', 'nolock', 'nocount', 'review', 'go'];

    const toast = $('toast');

    /* compare */
    let leftCm = CodeMirror.fromTextArea($('leftInput'), CM_OPTIONS);
    let rightCm = CodeMirror.fromTextArea($('rightInput'), CM_OPTIONS);
    const leftScrollAnn = leftCm.annotateScrollbar('cm-scrollmark-del');
    const rightScrollAnn = rightCm.annotateScrollbar('cm-scrollmark-ins');
    const diffSummary = $('diffSummary');

    /* script check */
    let scriptCm = CodeMirror.fromTextArea($('scriptInput'), CM_OPTIONS_SCRIPT);
    const scriptScrollAnns = {};
    SEVERITY_CLASSES.forEach(c => { scriptScrollAnns[c] = scriptCm.annotateScrollbar('cm-scrollmark-' + c); });
    const scriptResultsBody = $('scriptResultsBody');
    const scriptResultsTableContainer = $('scriptResultsTableContainer');
    const scriptEmptyState = $('scriptEmptyState');
    const scriptAllClearState = $('scriptAllClearState');
    const scriptIssueCountBadge = $('scriptIssueCount');
    const scriptSummaryText = $('scriptSummaryText');
    const scriptSearchBox = $('scriptSearchBox');
    const scriptMeta = $('scriptMeta');

    let diffMarks = [];
    let markPos = -1;
    let currentScript = null;
    let scriptUndoBuffer = null;
    let scriptTab = 'all';
    let scriptSortKey = 'line';
    let scriptSortDir = 1;

    /* ------------------------------ mode switch ---------------------------- */

    function setMode(mode) {
        const cms = { compare: leftCm, script: scriptCm };
        ['compare', 'script'].forEach(m => {
            $(m + 'View').classList.toggle('hidden', m !== mode);
        });
        $('compareActions').classList.toggle('hidden', mode !== 'compare');
        $('scriptActions').classList.toggle('hidden', mode !== 'script');
        document.querySelectorAll('.mode').forEach(b =>
            b.classList.toggle('active', b.dataset.mode === mode));
        /* the pane was hidden (display:none) while inactive, so CodeMirror's
           cached measurements are stale until it is visible again */
        cms[mode].refresh();
        if (mode === 'compare') rightCm.refresh();
        cms[mode].focus();
    }

    $('modeSwitch').addEventListener('click', e => {
        const b = e.target.closest('.mode');
        if (b) setMode(b.dataset.mode);
    });

    function activeMode() {
        return $('compareView').classList.contains('hidden') ? 'script' : 'compare';
    }

    /* -------------------------------- helpers ------------------------------ */

    function flash(msg) {
        toast.textContent = msg;
        toast.classList.remove('hidden');
        clearTimeout(flash._t);
        flash._t = setTimeout(() => toast.classList.add('hidden'), 2600);
    }

    function copyText(text, label) {
        if (!text) { flash('Nothing to copy.'); return; }
        if (navigator.clipboard && navigator.clipboard.writeText) {
            navigator.clipboard.writeText(text).then(() => flash(label), () => flash('Copy blocked by browser.'));
        } else {
            const ta = document.createElement('textarea');
            ta.value = text;
            document.body.appendChild(ta);
            ta.select();
            document.execCommand('copy');
            document.body.removeChild(ta);
            flash(label);
        }
    }

    /* A security finding carries its own CRITICAL/HIGH/REVIEW prefix in the
       message; NOLOCK/NOCOUNT findings don't have a severity of their own.
       Shared by the results table and the editor's line/gutter marking so
       the two never disagree about what colour a finding gets. */
    function findingStyle(f) {
        const sev = f.cat === 'security' ? (/^(CRITICAL|HIGH|REVIEW)\b/.exec(f.msg) || [, 'REVIEW'])[1] : null;
        const cls = sev ? sev.toLowerCase() : f.cat;
        const accent = sev ? (sev === 'REVIEW' ? 'var(--purple)' : 'var(--red)')
                     : f.cat === 'nolock' ? 'var(--amber)'
                     : f.cat === 'go' ? 'var(--teal)'
                     : 'var(--blue)';
        const tagLabel = sev || (f.cat === 'nolock' ? 'NOLOCK' : f.cat === 'go' ? 'MISSING GO' : 'NOCOUNT');
        return { sev: sev, cls: cls, tagLabel: tagLabel, accent: accent };
    }

    /* -------------------------------- drag & drop --------------------------- */

    /* Wire a drop zone: dragging a .sql/.txt file over `zoneEl` shows the dashed
       overlay, dropping it loads the text via `setText`. Any other drag (text,
       an image, a browser tab) is ignored so it does not swallow normal text
       drag-select-and-drop inside the editor. */
    function setupDropZone(zoneEl, setText, onLoaded) {
        const overlay = zoneEl.querySelector('.drop-overlay');
        let depth = 0;

        function isFileDrag(e) {
            return e.dataTransfer && Array.prototype.indexOf.call(e.dataTransfer.types || [], 'Files') >= 0;
        }

        zoneEl.addEventListener('dragenter', e => {
            if (!isFileDrag(e)) return;
            e.preventDefault();
            depth++;
            overlay.classList.remove('hidden');
        });
        zoneEl.addEventListener('dragover', e => {
            if (!isFileDrag(e)) return;
            e.preventDefault();
        });
        zoneEl.addEventListener('dragleave', () => {
            depth = Math.max(0, depth - 1);
            if (depth === 0) overlay.classList.add('hidden');
        });
        zoneEl.addEventListener('drop', e => {
            if (!isFileDrag(e)) return;
            e.preventDefault();
            depth = 0;
            overlay.classList.add('hidden');
            const file = e.dataTransfer.files && e.dataTransfer.files[0];
            if (!file) return;
            if (file.size > 15 * 1024 * 1024) { flash('File too large (' + Math.round(file.size / 1048576) + ' MB).'); return; }
            const reader = new FileReader();
            reader.onload = () => {
                setText(String(reader.result || '').replace(/^﻿/, ''));
                flash('Loaded ' + file.name + '.');
                if (onLoaded) onLoaded();
            };
            reader.onerror = () => flash('Could not read ' + file.name + '.');
            reader.readAsText(file);
        });
    }

    setupDropZone($('leftDrop'), text => leftCm.setValue(text), refreshCompare);
    setupDropZone($('rightDrop'), text => rightCm.setValue(text), refreshCompare);

    /* -------------------------------- resizing ------------------------------
       Drag the divider to resize the two panes in either view. The left
       track gets an explicit pixel width via a CSS custom property; the
       right track stays 1fr and just takes whatever is left, so the divider
       never has to know the container's total width up front. CodeMirror
       caches its own layout measurements, so anything it is displaying needs
       an explicit refresh() after the container's width actually changes. */
    function makeResizable(container, resizer, varName, storageKey, onResize) {
        const MIN = 200;

        function apply(px) {
            const max = Math.max(MIN, container.clientWidth - MIN - resizer.offsetWidth);
            px = Math.max(MIN, Math.min(px, max));
            container.style.setProperty(varName, px + 'px');
            if (onResize) onResize();
            return px;
        }

        function currentPx() {
            const stored = parseFloat(getComputedStyle(container).getPropertyValue(varName));
            return stored || container.clientWidth / 2;
        }

        function persist(px) {
            if (!storageKey) return;
            try { localStorage.setItem(storageKey, px); } catch (e) { /* private mode / quota - fine to skip */ }
        }

        if (storageKey) {
            let saved = null;
            try { saved = localStorage.getItem(storageKey); } catch (e) { /* ignore */ }
            if (saved) apply(parseFloat(saved));
        }

        let dragging = false;
        resizer.addEventListener('mousedown', e => {
            dragging = true;
            resizer.classList.add('dragging');
            document.body.style.cursor = 'col-resize';
            document.body.style.userSelect = 'none';
            e.preventDefault();
        });
        window.addEventListener('mousemove', e => {
            if (!dragging) return;
            persist(apply(e.clientX - container.getBoundingClientRect().left));
        });
        window.addEventListener('mouseup', () => {
            if (!dragging) return;
            dragging = false;
            resizer.classList.remove('dragging');
            document.body.style.cursor = '';
            document.body.style.userSelect = '';
        });

        resizer.addEventListener('keydown', e => {
            if (e.key === 'ArrowLeft') { persist(apply(currentPx() - 20)); e.preventDefault(); }
            else if (e.key === 'ArrowRight') { persist(apply(currentPx() + 20)); e.preventDefault(); }
        });
        resizer.addEventListener('dblclick', () => {
            container.style.removeProperty(varName);
            if (onResize) onResize();
            if (storageKey) { try { localStorage.removeItem(storageKey); } catch (e) { /* ignore */ } }
        });
    }

    makeResizable(document.querySelector('.compare-inputs'), $('cmpResizer'), '--cmp-split', 'sqltools-cmp-split',
        () => { leftCm.refresh(); rightCm.refresh(); });

    /* -------------------------------- compare ------------------------------
       One live pane per side: the editor IS the diff output, not a separate
       result view below it. Every real line of each side gets its own
       CodeMirror line/gutter class per its diff role, and changed-line pairs
       additionally get word-level markText spans - paste, type, or drop a
       file and the colouring updates as you go, with no explicit Compare
       step. Cross-pane row alignment after an insertion or deletion is only
       approximate by design: nothing pads one side to match the other, since
       that would mean showing lines that don't actually exist in the pasted
       text. Each pane's own line numbers (CodeMirror's real gutter now, not
       a hand-built one) stay exact regardless. ------------------------- */

    function cmpOpts() {
        return {
            ignoreCase: $('optCase').checked,
            ignoreWhitespace: $('optWs').checked,
            ignoreComments: $('optCmt').checked
        };
    }

    function clearCompareMarks() {
        [leftCm, rightCm].forEach(cm => {
            cm.operation(() => {
                for (let i = 0; i < cm.lineCount(); i++) {
                    cm.removeLineClass(i, 'background');
                    cm.removeLineClass(i, 'gutter');
                    cm.removeLineClass(i, 'wrap');
                }
            });
            cm.getAllMarks().forEach(m => m.clear());
        });
        leftScrollAnn.update([]);
        rightScrollAnn.update([]);
    }

    /* Walks jsdiff's row list once, applying line/gutter classes and word
       level marks directly via the CodeMirror API - no HTML is built at all.
       Also feeds the same positions to each pane's scrollbar annotation
       (addon/scroll/annotatescrollbar) so the red/green marks on the
       scrollbar itself preview where every change sits before you scroll.
       Returns the list of changed-row positions for the Prev/Next nav. */
    function applyCompareMarks(rows) {
        clearCompareMarks();
        const marks = [];
        const leftScroll = [], rightScroll = [];
        let li = 0, ri = 0;
        leftCm.operation(() => {
            rightCm.operation(() => {
                rows.forEach(r => {
                    if (r.t === 'same') { li++; ri++; return; }
                    if (r.t === 'del') {
                        leftCm.addLineClass(li, 'background', 'hl-del');
                        leftCm.addLineClass(li, 'gutter', 'cm-gutter-del');
                        leftScroll.push({ from: { line: li, ch: 0 }, to: { line: li, ch: 0 } });
                        marks.push({ lline: li, rline: null });
                        li++;
                    } else if (r.t === 'ins') {
                        rightCm.addLineClass(ri, 'background', 'hl-ins');
                        rightCm.addLineClass(ri, 'gutter', 'cm-gutter-ins');
                        rightScroll.push({ from: { line: ri, ch: 0 }, to: { line: ri, ch: 0 } });
                        marks.push({ lline: null, rline: ri });
                        ri++;
                    } else {
                        leftCm.addLineClass(li, 'background', 'hl-mod-del');
                        leftCm.addLineClass(li, 'gutter', 'cm-gutter-del');
                        rightCm.addLineClass(ri, 'background', 'hl-mod-ins');
                        rightCm.addLineClass(ri, 'gutter', 'cm-gutter-ins');
                        markWordDiff(leftCm, li, rightCm, ri, r.left, r.right);
                        leftScroll.push({ from: { line: li, ch: 0 }, to: { line: li, ch: 0 } });
                        rightScroll.push({ from: { line: ri, ch: 0 }, to: { line: ri, ch: 0 } });
                        marks.push({ lline: li, rline: ri });
                        li++;
                        ri++;
                    }
                });
            });
        });
        leftScrollAnn.update(leftScroll);
        rightScrollAnn.update(rightScroll);
        return marks;
    }

    let compareTimer = null;

    function refreshCompare() {
        clearTimeout(compareTimer);
        const leftText = leftCm.getValue(), rightText = rightCm.getValue();
        $('leftMeta').textContent = leftCm.lineCount() + ' LINES';
        $('rightMeta').textContent = rightCm.lineCount() + ' LINES';

        if (!leftText.trim() && !rightText.trim()) {
            clearCompareMarks();
            diffSummary.textContent = 'Paste SQL into both panes';
            diffSummary.className = 'diff-summary';
            diffMarks = [];
            markPos = -1;
            $('prevDiffBtn').disabled = true;
            $('nextDiffBtn').disabled = true;
            return;
        }

        const rows = diffSql(leftText, rightText, cmpOpts());
        diffMarks = applyCompareMarks(rows);
        markPos = -1;
        $('prevDiffBtn').disabled = !diffMarks.length;
        $('nextDiffBtn').disabled = !diffMarks.length;

        const counts = { ins: 0, del: 0, mod: 0 };
        rows.forEach(r => { if (r.t !== 'same') counts[r.t]++; });
        const total = counts.ins + counts.del + counts.mod;
        diffSummary.textContent = total
            ? total + ' difference' + (total === 1 ? '' : 's') + ' · ' +
              counts.mod + ' changed / ' + counts.ins + ' added / ' + counts.del + ' removed'
            : 'Both sides are identical';
        diffSummary.className = 'diff-summary' + (total ? '' : ' identical');
    }

    function scheduleCompareRefresh() {
        clearTimeout(compareTimer);
        compareTimer = setTimeout(refreshCompare, 150);
    }

    leftCm.on('change', scheduleCompareRefresh);
    rightCm.on('change', scheduleCompareRefresh);

    /* Scroll one pane, the other follows - by fraction, so it still lines up
       when the two files have a different number of lines. A guard flag
       stops the mirrored scroll event from bouncing back and forth forever.
       Nothing else needs syncing: CodeMirror is the only rendering surface
       for each pane, so there is nothing left that could drift apart from
       it. */
    let syncingScroll = false;
    function linkScroll(a, b) {
        a.on('scroll', () => {
            if (syncingScroll) return;
            syncingScroll = true;
            const infoA = a.getScrollInfo(), infoB = b.getScrollInfo();
            const rangeA = infoA.height - infoA.clientHeight;
            const rangeB = infoB.height - infoB.clientHeight;
            b.scrollTo(infoA.left, rangeA > 0 ? (infoA.top / rangeA) * rangeB : 0);
            syncingScroll = false;
        });
    }
    linkScroll(leftCm, rightCm);
    linkScroll(rightCm, leftCm);

    function clearFocusedLines() {
        [leftCm, rightCm].forEach(cm => {
            for (let i = 0; i < cm.lineCount(); i++) cm.removeLineClass(i, 'wrap', 'cm-focused-line');
        });
    }

    /* Both sides' exact line are known for every mark, so - unlike ordinary
       free scrolling, which only has each side's fraction-of-total-height to
       go on - navigating to a specific difference can position each pane
       precisely instead of leaving the other to its usual approximation. */
    function gotoMark(step) {
        if (!diffMarks.length) return;
        markPos = (markPos + step + diffMarks.length) % diffMarks.length;
        clearFocusedLines();
        const mark = diffMarks[markPos];
        if (mark.lline != null) {
            leftCm.addLineClass(mark.lline, 'wrap', 'cm-focused-line');
            leftCm.scrollIntoView({ line: mark.lline, ch: 0 }, 100);
        }
        if (mark.rline != null) {
            rightCm.addLineClass(mark.rline, 'wrap', 'cm-focused-line');
            rightCm.scrollIntoView({ line: mark.rline, ch: 0 }, 100);
        }
    }

    $('nextDiffBtn').addEventListener('click', () => gotoMark(1));
    $('prevDiffBtn').addEventListener('click', () => gotoMark(-1));

    $('swapBtn').addEventListener('click', () => {
        const t = leftCm.getValue();
        leftCm.setValue(rightCm.getValue());
        rightCm.setValue(t);
        refreshCompare();
    });

    $('clearCmpBtn').addEventListener('click', () => {
        leftCm.setValue('');
        rightCm.setValue('');
        refreshCompare();
    });

    ['optCase', 'optWs', 'optCmt'].forEach(id => $(id).addEventListener('change', refreshCompare));

    /* ------------------------------ script check ----------------------------
       For a whole script dump, not one pasted proc: reuses analyzeScript()
       (itself a thin wrapper over the unchanged analyze()) so NOLOCK/NOCOUNT/
       security work exactly as in the Audit view, plus a missing-GO check and
       object counts. The editor also gets a fold gutter (SSMS-style outlining)
       via CM_OPTIONS_SCRIPT, set up once above. -------------------------- */

    function clearScriptIssueMarks() {
        scriptCm.operation(() => {
            for (let i = 0; i < scriptCm.lineCount(); i++) {
                scriptCm.removeLineClass(i, 'background');
                scriptCm.removeLineClass(i, 'gutter');
            }
        });
        SEVERITY_CLASSES.forEach(c => scriptScrollAnns[c].update([]));
    }

    function markScriptIssues() {
        clearScriptIssueMarks();
        if (!currentScript) return;
        const bySeverity = {};
        SEVERITY_CLASSES.forEach(c => { bySeverity[c] = []; });
        scriptCm.operation(() => {
            currentScript.findings.forEach(f => {
                const style = findingStyle(f);
                scriptCm.addLineClass(f.line - 1, 'background', 'cm-issue-' + style.cls);
                scriptCm.addLineClass(f.line - 1, 'gutter', 'cm-gutter-' + style.cls);
                bySeverity[style.cls].push({ from: { line: f.line - 1, ch: 0 }, to: { line: f.line - 1, ch: 0 } });
            });
        });
        SEVERITY_CLASSES.forEach(c => scriptScrollAnns[c].update(bySeverity[c]));
    }

    function updateScriptMeta() {
        scriptMeta.textContent = scriptCm.lineCount() + ' LINES / ' + scriptCm.getValue().length + ' CHARS';
    }

    scriptCm.on('change', () => {
        updateScriptMeta();
        if (currentScript) {
            currentScript = null;
            clearScriptIssueMarks();
            scriptResultsBody.innerHTML = '';
            scriptIssueCountBadge.textContent = '0 Errors';
            scriptIssueCountBadge.className = 'badge';
            scriptSummaryText.textContent = 'Edited - Run Check again';
            $('fixScriptBtn').disabled = true;
            $('exportScriptBtn').disabled = true;
            scriptShowState('empty');
        }
    });

    function scriptShowState(state) {
        scriptEmptyState.classList.add('hidden');
        scriptResultsTableContainer.classList.add('hidden');
        scriptAllClearState.classList.add('hidden');
        if (state === 'results') scriptResultsTableContainer.classList.remove('hidden');
        else if (state === 'clear') scriptAllClearState.classList.remove('hidden');
        else scriptEmptyState.classList.remove('hidden');
    }

    function scriptRun() {
        const sql = scriptCm.getValue();
        if (!sql.trim()) { flash('Nothing to check.'); return; }

        currentScript = analyzeScript(sql);
        markScriptIssues();

        const security = currentScript.findings.filter(f => f.cat === 'security').length;
        const nolock = currentScript.findings.filter(f => f.cat === 'nolock').length;
        const nocount = currentScript.findings.filter(f => f.cat === 'nocount').length;
        const total = security + nolock + nocount + currentScript.goMissing;

        scriptIssueCountBadge.textContent = total
            ? total + ' ERROR' + (total === 1 ? '' : 'S') +
              (security ? ' · ' + security + ' SECURITY' : '') +
              ' · ' + nolock + ' NOLOCK / ' + nocount + ' NOCOUNT / ' + currentScript.goMissing + ' GO'
            : '0 Errors';
        scriptIssueCountBadge.className = total ? (security ? 'badge danger' : 'badge') : 'badge success';
        scriptSummaryText.textContent = security ? 'Security Risk Found' : total ? 'Errors Found' : 'All Clear';

        $('fixScriptBtn').disabled = !currentScript.findings.some(f => f.fix);
        $('exportScriptBtn').disabled = !currentScript.findings.length;
        scriptRenderResults();
    }

    function scriptVisibleRows() {
        if (!currentScript) return [];
        const q = scriptSearchBox.value.trim().toLowerCase();
        let rows = currentScript.findings.filter(f => scriptTab === 'all' || f.cat === scriptTab);
        if (q) {
            rows = rows.filter(f =>
                (f.line + ' ' + f.obj + ' ' + f.rule + ' ' + f.msg + ' ' + f.ctx).toLowerCase().indexOf(q) >= 0);
        }
        rows.sort((a, b) => {
            let d = 0;
            if (scriptSortKey === 'line') d = a.line - b.line;
            else if (scriptSortKey === 'type') d = a.cat < b.cat ? -1 : a.cat > b.cat ? 1 : 0;
            else if (scriptSortKey === 'obj') d = a.obj.toLowerCase() < b.obj.toLowerCase() ? -1 : 1;
            return d * scriptSortDir || a.off - b.off;
        });
        return rows;
    }

    function scriptRenderResults() {
        const rows = scriptVisibleRows();
        if (!rows.length) {
            scriptResultsBody.innerHTML = '';
            if (!currentScript) { scriptShowState('empty'); return; }
            const filtered = scriptSearchBox.value.trim() || scriptTab !== 'all';
            scriptAllClearState.querySelector('h3').textContent = filtered ? 'Nothing In This View' : 'All Clear';
            scriptAllClearState.querySelector('p').textContent = filtered
                ? 'No errors match the current tab or filter text.'
                : 'Every read source has NOLOCK, every module sets NOCOUNT ON, every batch has a GO, and no security issues found.';
            scriptShowState('clear');
            return;
        }
        scriptShowState('results');
        scriptResultsBody.innerHTML = rows.map(f => {
            const style = findingStyle(f);
            return '<tr data-line="' + f.line + '"' + (style.sev ? ' class="sev-' + style.cls + '"' : '') +
                ' style="--row-accent:' + style.accent + '">' +
                '<td class="line-cell">' + f.line + '</td>' +
                '<td><span class="tag tag-' + style.cls + '">' + style.tagLabel + '</span>' +
                (f.dynamic ? '<span class="tag tag-dyn">DYN</span>' : '') +
                (f.fix ? '<span class="fixable" title="auto fixable">&#9670;</span>' : '') + '</td>' +
                '<td class="obj-cell"><b>' + escHtml(f.obj) + '</b></td>' +
                '<td class="issue-cell">' + escHtml(f.msg) + '</td>' +
                '<td class="snippet-cell">' + escHtml(f.ctx) + '</td>' +
                '</tr>';
        }).join('');
    }

    function scriptJumpToLine(num) {
        if (num < 1 || num > scriptCm.lineCount()) return;
        /* jumping to a line inside a folded batch must open it first, or the
           line silently stays hidden inside the collapsed widget */
        scriptCm.findMarksAt(CodeMirror.Pos(num - 1, 0)).forEach(m => { if (m.__isFold) m.clear(); });
        const lineLen = scriptCm.getLine(num - 1).length;
        scriptCm.setSelection({ line: num - 1, ch: 0 }, { line: num - 1, ch: lineLen });
        scriptCm.scrollIntoView({ line: num - 1, ch: 0 }, 120);
        scriptCm.focus();
    }

    scriptResultsBody.addEventListener('click', e => {
        const tr = e.target.closest('tr');
        if (tr && tr.dataset.line) scriptJumpToLine(parseInt(tr.dataset.line, 10));
    });

    $('scriptTabs').addEventListener('click', e => {
        const b = e.target.closest('.tab');
        if (!b) return;
        document.querySelectorAll('#scriptTabs .tab').forEach(x => x.classList.remove('active'));
        b.classList.add('active');
        scriptTab = b.dataset.tab;
        scriptRenderResults();
    });

    document.querySelectorAll('#scriptResultsTable th.sortable').forEach(th => {
        th.addEventListener('click', () => {
            const k = th.dataset.sort;
            scriptSortDir = (k === scriptSortKey) ? -scriptSortDir : 1;
            scriptSortKey = k;
            document.querySelectorAll('#scriptResultsTable th.sortable').forEach(x => x.classList.remove('sorted'));
            th.classList.add('sorted');
            scriptRenderResults();
        });
    });

    scriptSearchBox.addEventListener('input', scriptRenderResults);
    $('checkScriptBtn').addEventListener('click', scriptRun);

    $('clearScriptBtn').addEventListener('click', () => {
        scriptCm.setValue('');
        currentScript = null;
        scriptUndoBuffer = null;
        clearScriptIssueMarks();
        scriptResultsBody.innerHTML = '';
        scriptIssueCountBadge.textContent = '0 Errors';
        scriptIssueCountBadge.className = 'badge';
        scriptSummaryText.textContent = 'Ready to Check';
        $('fixScriptBtn').disabled = true;
        $('undoScriptBtn').disabled = true;
        $('exportScriptBtn').disabled = true;
        scriptShowState('empty');
    });

    $('fixScriptBtn').addEventListener('click', () => {
        if (!currentScript) return;
        scriptUndoBuffer = scriptCm.getValue();
        const res = applyFixes(scriptUndoBuffer, currentScript.findings);
        scriptCm.setValue(res.sql);
        $('undoScriptBtn').disabled = false;
        scriptRun();
        flash('Applied ' + res.count + ' fix' + (res.count === 1 ? '' : 'es') + '. Review before deploying.');
    });

    $('formatScriptBtn').addEventListener('click', () => {
        const sql = scriptCm.getValue();
        if (!sql.trim()) { flash('Nothing to format.'); return; }
        scriptUndoBuffer = sql;
        scriptCm.setValue(formatSql(sql));
        $('undoScriptBtn').disabled = false;
        flash('SQL formatted.');
    });

    $('undoScriptBtn').addEventListener('click', () => {
        if (scriptUndoBuffer === null) return;
        scriptCm.setValue(scriptUndoBuffer);
        scriptUndoBuffer = null;
        $('undoScriptBtn').disabled = true;
        if (scriptCm.getValue().trim()) scriptRun();
        flash('Reverted.');
    });

    $('copyScriptBtn').addEventListener('click', () => copyText(scriptCm.getValue(), 'SQL copied.'));

    $('exportScriptBtn').addEventListener('click', () => {
        if (!currentScript || !currentScript.findings.length) return;
        const rows = scriptVisibleRows();
        const q = v => '"' + String(v).replace(/"/g, '""') + '"';
        const csv = [['Line', 'Type', 'Rule', 'Object', 'Error', 'Context'].join(',')].concat(
            rows.map(f => [f.line, f.cat.toUpperCase(), f.rule, f.obj, f.msg, f.ctx].map(q).join(','))
        ).join('\r\n');
        const a = document.createElement('a');
        a.href = URL.createObjectURL(new Blob(['﻿' + csv], { type: 'text/csv;charset=utf-8;' }));
        a.download = 'script_check.csv';
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        flash('Exported ' + rows.length + ' rows.');
    });

    $('collapseAllBtn').addEventListener('click', () => {
        CodeMirror.commands.foldAll(scriptCm);
        flash('Collapsed every batch.');
    });
    $('expandAllBtn').addEventListener('click', () => CodeMirror.commands.unfoldAll(scriptCm));

    setupDropZone($('scriptDrop'), text => scriptCm.setValue(text), scriptRun);
    makeResizable($('scriptView'), $('scriptResizer'), '--script-split', 'sqltools-script-split',
        () => scriptCm.refresh());

    document.addEventListener('keydown', e => {
        if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
            e.preventDefault();
            const mode = activeMode();
            if (mode === 'compare') refreshCompare();
            else scriptRun();
        }
    });

    updateScriptMeta();
    refreshCompare();
});
