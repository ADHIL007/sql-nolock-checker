document.addEventListener('DOMContentLoaded', () => {
    const sqlInput = document.getElementById('sqlInput');
    const lineNumbers = document.getElementById('lineNumbers');
    const analyzeBtn = document.getElementById('analyzeBtn');
    const clearBtn = document.getElementById('clearBtn');
    const resultsBody = document.getElementById('resultsBody');
    const resultsTableContainer = document.getElementById('resultsTableContainer');
    const emptyState = document.getElementById('emptyState');
    const allClearState = document.getElementById('allClearState');
    const issueCountBadge = document.getElementById('issueCount');
    const summaryText = document.getElementById('summaryText');

    // Update line numbers as user types
    sqlInput.addEventListener('input', updateLineNumbers);
    sqlInput.addEventListener('scroll', () => {
        lineNumbers.scrollTop = sqlInput.scrollTop;
    });

    function updateLineNumbers() {
        const lines = sqlInput.value.split('\n').length;
        lineNumbers.innerHTML = Array.from({length: lines}, (_, i) => `<div>${i + 1}</div>`).join('');
    }

    updateLineNumbers();

    analyzeBtn.addEventListener('click', () => {
        const sql = sqlInput.value;
        if (!sql.trim()) return;
        
        showState('loading');
        setTimeout(() => {
            const results = performDeepScan(sql);
            displayResults(results);
        }, 100);
    });

    clearBtn.addEventListener('click', () => {
        sqlInput.value = '';
        updateLineNumbers();
        showState('empty');
    });

    function showState(state) {
        emptyState.classList.add('hidden');
        resultsTableContainer.classList.add('hidden');
        allClearState.classList.add('hidden');

        if (state === 'results') resultsTableContainer.classList.remove('hidden');
        else if (state === 'clear') allClearState.classList.remove('hidden');
        else if (state === 'empty') emptyState.classList.remove('hidden');
    }

    function performDeepScan(sql) {
        const lines = sql.split('\n');
        const results = [];
        
        // Comprehensive Parser Logic
        // We first strip comments but maintain line placement for accurate reporting
        const cleanLines = lines.map(line => line.replace(/--.*$/, '').replace(/\/\*[\s\S]*?\*\//g, ' '));
        
        let inCteBlock = false;
        const cteNames = new Set();
        
        // Preliminary pass to identify CTE names to ignore them as table references
        const cteRegex = /\bWITH\s+([\[\]\w]+)\s+AS\s*\(/gi;
        const fullSql = cleanLines.join('\n');
        let cteMatch;
        while ((cteMatch = cteRegex.exec(fullSql)) !== null) {
            cteNames.add(cteMatch[1].toUpperCase());
        }

        // Main parser loop
        cleanLines.forEach((line, index) => {
            const lineNum = index + 1;
            
            // Regex for Table references in FROM or JOIN
            // Handles schema, aliases, newlines (within same line context)
            // Excludes #temp, @vars
            const tableRefRegex = /\b(FROM|JOIN)\s+((?![#@])([\[\]\w\.]+))(?:\s+(?:AS\s+)?([\[\]\w]+))?/gi;
            
            let match;
            while ((match = tableRefRegex.exec(line)) !== null) {
                const keyword = match[1];
                const fullName = match[2];
                const tableName = match[3];
                const alias = match[4];
                
                // Ignore if it's a CTE name
                if (cteNames.has(fullName.toUpperCase()) || cteNames.has(tableName.toUpperCase())) continue;

                // Look ahead for (NOLOCK)
                // We check the rest of the line and the next few lines for context
                const lookAhead = cleanLines.slice(index).join('\n').substring(match.index + match[0].length);
                
                // Terminate search at next statement/clause
                const terminatorRegex = /\b(WHERE|JOIN|GROUP|ORDER|UNION|SELECT|INSERT|UPDATE|DELETE|BEGIN|END|IF|GO)\b/i;
                const termMatch = lookAhead.match(terminatorRegex);
                const context = termMatch ? lookAhead.substring(0, termMatch.index) : lookAhead;
                
                const hasNoLock = /(?:WITH\s*)?\(NOLOCK\)/i.test(context);
                
                if (!hasNoLock) {
                    results.push({
                        line: lineNum,
                        table: fullName,
                        snippet: (match[0] + context).substring(0, 60).trim() + '...',
                        issue: 'Missing Hint'
                    });
                }
            }
        });

        return results;
    }

    function displayResults(results) {
        resultsBody.innerHTML = '';
        
        if (results.length === 0) {
            showState('clear');
            issueCountBadge.textContent = '0 Issues';
            issueCountBadge.className = 'badge success';
            summaryText.textContent = 'All Clear';
        } else {
            showState('results');
            issueCountBadge.textContent = `${results.length} Issue${results.length > 1 ? 's' : ''}`;
            issueCountBadge.className = 'badge';
            summaryText.textContent = 'Audit Results';

            results.forEach(res => {
                const tr = document.createElement('tr');
                tr.innerHTML = `
                    <td class="line-cell" onclick="jumpToLine(${res.line})">${res.line}</td>
                    <td><b>${res.table}</b></td>
                    <td class="snippet-cell">${res.snippet}</td>
                    <td class="issue-cell">${res.issue}</td>
                `;
                resultsBody.appendChild(tr);
            });
        }
    }

    window.jumpToLine = (num) => {
        const lines = sqlInput.value.split('\n');
        if (num < 1 || num > lines.length) return;

        // Ensure editor is focused first
        sqlInput.focus();

        // Calculate exact byte positions
        let startPos = 0;
        for (let i = 0; i < num - 1; i++) {
            startPos += lines[i].length + 1; // +1 for the newline character
        }
        const endPos = startPos + lines[num - 1].length;

        // Set selection and scroll in next tick to ensure focus is stable
        setTimeout(() => {
            sqlInput.setSelectionRange(startPos, endPos);
            
            // Smoother scroll to line
            const lineHeight = 1.4 * 13.6; // Based on CSS 1.4rem line-height and 0.85rem (13.6px) font
            const targetScroll = (num - 1) * 22.4; // Calculated 1.4 * 16px (1rem) = 22.4 approx
            sqlInput.scrollTop = targetScroll - (sqlInput.clientHeight / 4); // Center it a bit
        }, 0);
    };
});
