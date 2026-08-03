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

/* Only two things are reported: a read source with no NOLOCK, and a module
   body with no SET NOCOUNT ON. Everything else stays silent. */
const RULES = {
    NL001: { cat: 'nolock',  msg: 'No NOLOCK on read source' },
    NL005: { cat: 'nolock',  msg: 'No NOLOCK inside dynamic SQL' },
    NC001: { cat: 'nocount', msg: 'Module body missing SET NOCOUNT ON' },
    NC002: { cat: 'nocount', msg: 'SET NOCOUNT turned OFF again' },
    NC004: { cat: 'nocount', msg: 'Batch missing SET NOCOUNT ON' }
};

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
    const stats = { sources: 0, covered: 0, missing: 0, dynamic: dynBlocks.length, procs: 0, nocount: 0 };

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

/* Word level highlight for a changed pair. */
function inlineDiff(a, b) {
    if (a.length > 4000 || b.length > 4000) return [escHtml(a), escHtml(b)];
    const parts = Diff.diffWordsWithSpace(a, b);
    let left = '', right = '';
    parts.forEach(p => {
        const html = escHtml(p.value);
        if (p.added) right += '<span class="chg">' + html + '</span>';
        else if (p.removed) left += '<span class="chg">' + html + '</span>';
        else { left += html; right += html; }
    });
    return [left, right];
}

/* ----------------------------------- UI ----------------------------------- */

document.addEventListener('DOMContentLoaded', () => {
    const $ = id => document.getElementById(id);

    /* audit */
    const sqlInput = $('sqlInput');
    const lineNumbers = $('lineNumbers');
    const resultsBody = $('resultsBody');
    const resultsTableContainer = $('resultsTableContainer');
    const emptyState = $('emptyState');
    const allClearState = $('allClearState');
    const issueCountBadge = $('issueCount');
    const summaryText = $('summaryText');
    const filterBar = $('filterBar');
    const searchBox = $('searchBox');
    const editorMeta = $('editorMeta');
    const toast = $('toast');

    /* compare */
    const leftInput = $('leftInput');
    const rightInput = $('rightInput');
    const diffContainer = $('diffContainer');
    const diffSummary = $('diffSummary');

    let current = null;
    let tab = 'all';
    let sortKey = 'line';
    let sortDir = 1;
    let undoBuffer = null;
    let issueLines = new Set();
    let diffRows = null;
    let diffMarks = [];
    let markPos = -1;

    /* ------------------------------ mode switch ---------------------------- */

    function setMode(mode) {
        const audit = mode === 'audit';
        $('auditView').classList.toggle('hidden', !audit);
        $('compareView').classList.toggle('hidden', audit);
        $('auditActions').classList.toggle('hidden', !audit);
        $('compareActions').classList.toggle('hidden', audit);
        document.querySelectorAll('.mode').forEach(b =>
            b.classList.toggle('active', b.dataset.mode === mode));
        (audit ? sqlInput : leftInput).focus();
    }

    $('modeSwitch').addEventListener('click', e => {
        const b = e.target.closest('.mode');
        if (b) setMode(b.dataset.mode);
    });

    function activeMode() {
        return $('auditView').classList.contains('hidden') ? 'compare' : 'audit';
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

    /* ------------------------------ audit editor --------------------------- */

    function updateLineNumbers() {
        const count = sqlInput.value.split('\n').length;
        const html = [];
        for (let i = 1; i <= count; i++) {
            html.push('<div' + (issueLines.has(i) ? ' class="issue"' : '') + '>' + i + '</div>');
        }
        lineNumbers.innerHTML = html.join('');
        lineNumbers.scrollTop = sqlInput.scrollTop;
        editorMeta.textContent = count + ' LINES / ' + sqlInput.value.length + ' CHARS';
    }

    sqlInput.addEventListener('input', () => { issueLines = new Set(); updateLineNumbers(); });
    sqlInput.addEventListener('scroll', () => { lineNumbers.scrollTop = sqlInput.scrollTop; });

    function showState(state) {
        emptyState.classList.add('hidden');
        resultsTableContainer.classList.add('hidden');
        allClearState.classList.add('hidden');
        if (state === 'results') resultsTableContainer.classList.remove('hidden');
        else if (state === 'clear') allClearState.classList.remove('hidden');
        else emptyState.classList.remove('hidden');
    }

    /* --------------------------------- audit ------------------------------- */

    function run() {
        const sql = sqlInput.value;
        if (!sql.trim()) { flash('Nothing to analyze.'); return; }

        current = analyze(sql);
        issueLines = new Set(current.findings.map(f => f.line));
        updateLineNumbers();
        filterBar.classList.remove('hidden');

        const nolock = current.findings.filter(f => f.cat === 'nolock').length;
        const nocount = current.findings.filter(f => f.cat === 'nocount').length;
        const total = nolock + nocount;

        issueCountBadge.textContent = total
            ? total + ' ERROR' + (total === 1 ? '' : 'S') + ' · ' + nolock + ' NOLOCK / ' + nocount + ' NOCOUNT'
            : '0 Errors';
        issueCountBadge.className = total ? 'badge' : 'badge success';
        summaryText.textContent = total ? 'Errors Found' : 'All Clear';

        $('fixBtn').disabled = !current.findings.some(f => f.fix);
        $('exportBtn').disabled = !current.findings.length;
        render();
    }

    function visibleRows() {
        if (!current) return [];
        const q = searchBox.value.trim().toLowerCase();
        let rows = current.findings.filter(f => tab === 'all' || f.cat === tab);
        if (q) {
            rows = rows.filter(f =>
                (f.line + ' ' + f.obj + ' ' + f.rule + ' ' + f.msg + ' ' + f.ctx).toLowerCase().indexOf(q) >= 0);
        }
        rows.sort((a, b) => {
            let d = 0;
            if (sortKey === 'line') d = a.line - b.line;
            else if (sortKey === 'type') d = a.cat < b.cat ? -1 : a.cat > b.cat ? 1 : 0;
            else if (sortKey === 'obj') d = a.obj.toLowerCase() < b.obj.toLowerCase() ? -1 : 1;
            return d * sortDir || a.off - b.off;
        });
        return rows;
    }

    function render() {
        const rows = visibleRows();
        if (!rows.length) {
            resultsBody.innerHTML = '';
            if (!current) { showState('empty'); return; }
            const filtered = searchBox.value.trim() || tab !== 'all';
            allClearState.querySelector('h3').textContent = filtered ? 'Nothing In This View' : 'All Clear';
            allClearState.querySelector('p').textContent = filtered
                ? 'No errors match the current tab or filter text.'
                : 'Every read source has NOLOCK and every module sets NOCOUNT ON.';
            showState('clear');
            return;
        }
        showState('results');
        resultsBody.innerHTML = rows.map(f =>
            '<tr data-line="' + f.line + '">' +
            '<td class="line-cell">' + f.line + '</td>' +
            '<td><span class="tag tag-' + f.cat + '">' + (f.cat === 'nolock' ? 'NOLOCK' : 'NOCOUNT') + '</span>' +
            (f.dynamic ? '<span class="tag tag-dyn">DYN</span>' : '') +
            (f.fix ? '<span class="fixable" title="auto fixable">&#9670;</span>' : '') + '</td>' +
            '<td class="obj-cell"><b>' + escHtml(f.obj) + '</b></td>' +
            '<td class="issue-cell">' + escHtml(f.msg) + '</td>' +
            '<td class="snippet-cell">' + escHtml(f.ctx) + '</td>' +
            '</tr>').join('');
    }

    function jumpToLine(num) {
        const lines = sqlInput.value.split('\n');
        if (num < 1 || num > lines.length) return;
        sqlInput.focus();
        let startPos = 0;
        for (let i = 0; i < num - 1; i++) startPos += lines[i].length + 1;
        setTimeout(() => {
            sqlInput.setSelectionRange(startPos, startPos + lines[num - 1].length);
            sqlInput.scrollTop = Math.max(0, (num - 1) * 22.4 - sqlInput.clientHeight / 3);
            lineNumbers.scrollTop = sqlInput.scrollTop;
        }, 0);
    }

    resultsBody.addEventListener('click', e => {
        const tr = e.target.closest('tr');
        if (tr && tr.dataset.line) jumpToLine(parseInt(tr.dataset.line, 10));
    });

    $('tabs').addEventListener('click', e => {
        const b = e.target.closest('.tab');
        if (!b) return;
        document.querySelectorAll('#tabs .tab').forEach(x => x.classList.remove('active'));
        b.classList.add('active');
        tab = b.dataset.tab;
        render();
    });

    document.querySelectorAll('th.sortable').forEach(th => {
        th.addEventListener('click', () => {
            const k = th.dataset.sort;
            sortDir = (k === sortKey) ? -sortDir : 1;
            sortKey = k;
            document.querySelectorAll('th.sortable').forEach(x => x.classList.remove('sorted'));
            th.classList.add('sorted');
            render();
        });
    });

    searchBox.addEventListener('input', render);
    $('analyzeBtn').addEventListener('click', run);

    $('clearBtn').addEventListener('click', () => {
        sqlInput.value = '';
        current = null;
        undoBuffer = null;
        issueLines = new Set();
        updateLineNumbers();
        filterBar.classList.add('hidden');
        resultsBody.innerHTML = '';
        issueCountBadge.textContent = '0 Errors';
        issueCountBadge.className = 'badge';
        summaryText.textContent = 'Ready to Analyze';
        $('fixBtn').disabled = true;
        $('exportBtn').disabled = true;
        $('undoBtn').classList.add('hidden');
        showState('empty');
    });

    $('fixBtn').addEventListener('click', () => {
        if (!current) return;
        undoBuffer = sqlInput.value;
        const res = applyFixes(sqlInput.value, current.findings);
        sqlInput.value = res.sql;
        $('undoBtn').classList.remove('hidden');
        run();
        flash('Applied ' + res.count + ' fix' + (res.count === 1 ? '' : 'es') + '. Review before deploying.');
    });

    $('undoBtn').addEventListener('click', () => {
        if (undoBuffer === null) return;
        sqlInput.value = undoBuffer;
        undoBuffer = null;
        $('undoBtn').classList.add('hidden');
        run();
        flash('Auto fix reverted.');
    });

    $('copyBtn').addEventListener('click', () => copyText(sqlInput.value, 'SQL copied.'));

    $('exportBtn').addEventListener('click', () => {
        if (!current || !current.findings.length) return;
        const rows = visibleRows();
        const q = v => '"' + String(v).replace(/"/g, '""') + '"';
        const csv = [['Line', 'Type', 'Rule', 'Object', 'Error', 'Context'].join(',')].concat(
            rows.map(f => [f.line, f.cat.toUpperCase(), f.rule, f.obj, f.msg, f.ctx].map(q).join(','))
        ).join('\r\n');
        const a = document.createElement('a');
        a.href = URL.createObjectURL(new Blob(['﻿' + csv], { type: 'text/csv;charset=utf-8;' }));
        a.download = 'nolock_nocount_errors.csv';
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        flash('Exported ' + rows.length + ' rows.');
    });

    /* -------------------------------- compare ------------------------------ */

    function cmpOpts() {
        return {
            ignoreCase: $('optCase').checked,
            ignoreWhitespace: $('optWs').checked,
            ignoreComments: $('optCmt').checked,
            diffsOnly: $('optOnly').checked
        };
    }

    function updateCmpMeta() {
        $('leftMeta').textContent = leftInput.value.split('\n').length + ' LINES';
        $('rightMeta').textContent = rightInput.value.split('\n').length + ' LINES';
    }

    leftInput.addEventListener('input', updateCmpMeta);
    rightInput.addEventListener('input', updateCmpMeta);

    function compare() {
        if (!leftInput.value.trim() && !rightInput.value.trim()) {
            flash('Paste SQL into both panes first.');
            return;
        }
        const opt = cmpOpts();
        diffRows = diffSql(leftInput.value, rightInput.value, opt);
        renderDiff(opt);
    }

    /* keep 2 lines of context around every change when hiding identical lines */
    function isNear(rows, i) {
        for (let k = Math.max(0, i - 2); k <= Math.min(rows.length - 1, i + 2); k++) {
            if (rows[k].t !== 'same') return true;
        }
        return false;
    }

    function renderDiff(opt) {
        const rows = diffRows;
        const counts = { ins: 0, del: 0, mod: 0 };
        rows.forEach(r => { if (r.t !== 'same') counts[r.t]++; });
        const total = counts.ins + counts.del + counts.mod;

        diffSummary.textContent = total
            ? total + ' difference' + (total === 1 ? '' : 's') + ' · ' +
              counts.mod + ' changed / ' + counts.ins + ' added / ' + counts.del + ' removed'
            : 'Both sides are identical';
        diffSummary.className = 'diff-summary' + (total ? '' : ' identical');

        const html = [];
        let skipped = 0;
        let diffIndex = 0;

        function spacer() {
            if (!skipped) return;
            html.push('<tr class="d-skip"><td colspan="6">' + skipped +
                      ' identical line' + (skipped === 1 ? '' : 's') + ' hidden</td></tr>');
            skipped = 0;
        }

        rows.forEach((r, i) => {
            if (r.t === 'same') {
                if (opt.diffsOnly && !isNear(rows, i)) { skipped++; return; }
                spacer();
                html.push('<tr class="d-same">' +
                    '<td class="dl">' + r.ln + '</td><td class="dm"></td><td class="dt">' + escHtml(r.left) + '</td>' +
                    '<td class="dl">' + r.rn + '</td><td class="dm"></td><td class="dt">' + escHtml(r.right) + '</td></tr>');
                return;
            }
            spacer();
            let lh = escHtml(r.left), rh = escHtml(r.right);
            if (r.t === 'mod') { const pair = inlineDiff(r.left, r.right); lh = pair[0]; rh = pair[1]; }
            const lMark = r.t === 'ins' ? '' : r.t === 'mod' ? '~' : '-';
            const rMark = r.t === 'del' ? '' : r.t === 'mod' ? '~' : '+';
            html.push('<tr class="d-' + r.t + '" data-diff="' + (diffIndex++) + '">' +
                '<td class="dl">' + (r.ln || '') + '</td><td class="dm">' + lMark + '</td>' +
                '<td class="dt">' + lh + '</td>' +
                '<td class="dl">' + (r.rn || '') + '</td><td class="dm">' + rMark + '</td>' +
                '<td class="dt">' + rh + '</td></tr>');
        });
        spacer();

        diffContainer.innerHTML =
            '<table class="diff-table"><colgroup><col class="c-ln"><col class="c-mk"><col>' +
            '<col class="c-ln"><col class="c-mk"><col></colgroup>' +
            '<thead><tr><th colspan="3">Original</th><th colspan="3">Modified</th></tr></thead>' +
            '<tbody>' + html.join('') + '</tbody></table>';

        diffMarks = Array.prototype.slice.call(diffContainer.querySelectorAll('[data-diff]'));
        markPos = -1;
        $('prevDiffBtn').disabled = !diffMarks.length;
        $('nextDiffBtn').disabled = !diffMarks.length;
    }

    function gotoMark(step) {
        if (!diffMarks.length) return;
        markPos = (markPos + step + diffMarks.length) % diffMarks.length;
        diffMarks.forEach(el => el.classList.remove('focused'));
        const el = diffMarks[markPos];
        el.classList.add('focused');
        el.scrollIntoView({ block: 'center' });
    }

    $('compareBtn').addEventListener('click', compare);
    $('nextDiffBtn').addEventListener('click', () => gotoMark(1));
    $('prevDiffBtn').addEventListener('click', () => gotoMark(-1));

    $('swapBtn').addEventListener('click', () => {
        const t = leftInput.value;
        leftInput.value = rightInput.value;
        rightInput.value = t;
        updateCmpMeta();
        if (diffRows) compare();
    });

    $('clearCmpBtn').addEventListener('click', () => {
        leftInput.value = '';
        rightInput.value = '';
        diffRows = null;
        diffMarks = [];
        updateCmpMeta();
        diffSummary.textContent = 'Not compared';
        diffSummary.className = 'diff-summary';
        $('prevDiffBtn').disabled = true;
        $('nextDiffBtn').disabled = true;
        diffContainer.innerHTML =
            '<div class="empty-state"><h3>Nothing Compared Yet</h3>' +
            '<p>Paste SQL into both panes and click Compare.</p></div>';
    });

    ['optCase', 'optWs', 'optCmt', 'optOnly'].forEach(id =>
        $(id).addEventListener('change', () => { if (diffRows) compare(); }));

    document.addEventListener('keydown', e => {
        if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
            e.preventDefault();
            if (activeMode() === 'audit') run(); else compare();
        }
    });

    updateLineNumbers();
    updateCmpMeta();
});
