/**
 * LL(1) Grammar Analyzer & Parser — ll1.js
 * Features: Grammar parsing, FIRST, FOLLOW, Parse Table,
 *           String Parsing, Parse Tree, Left Recursion Elimination,
 *           Left Factoring, Ambiguity/Conflict detection, Export.
 */

'use strict';

/* ═══════════════════════════════════════════════════════════════
   CONSTANTS & GLOBALS
═══════════════════════════════════════════════════════════════ */
const EPSILON = 'ε';
const DOLLAR  = '$';

let G = null;          // Current grammar object
let parseTableData = null;
let traceSteps     = [];
let traceIndex     = 0;
let traceTimer     = null;
let parseTreeRoot  = null;

/* ═══════════════════════════════════════════════════════════════
   SAMPLE GRAMMARS
═══════════════════════════════════════════════════════════════ */
const SAMPLES = [
  {
    name: 'Expression Grammar (Arithmetic)',
    desc: 'Classic LL(1) grammar for arithmetic expressions',
    grammar: `E -> T E'
E' -> + T E' | eps
T -> F T'
T' -> * F T' | eps
F -> ( E ) | id`,
    sampleInput: 'id + id * id'
  },
  {
    name: 'Simple Statement Grammar',
    desc: 'Assignment, if-else and while statements',
    grammar: `S -> id = E | if ( E ) S L | while ( E ) S | { SL }
L -> else S | eps
SL -> S SL | eps
E -> id | num`,
    sampleInput: 'id = id'
  },
  {
    name: 'Balanced Parentheses',
    desc: 'Grammar recognizing balanced parentheses',
    grammar: `S -> ( S ) S | eps`,
    sampleInput: '( ( ) )'
  },
  {
    name: 'Simple Type Declarations',
    desc: 'Variable declarations with type',
    grammar: `D -> T id L
L -> , id L | ;
T -> int | float | bool`,
    sampleInput: 'int id ;'
  },
  {
    name: 'Left-Recursive (needs elimination)',
    desc: 'Grammar with direct left recursion',
    grammar: `E -> E + T | T
T -> T * F | F
F -> ( E ) | id`,
    sampleInput: 'id + id'
  },
  {
    name: 'Needs Left Factoring',
    desc: 'Grammar that requires left factoring',
    grammar: `S -> a b | a c d | b e
A -> a b c | a b d | a b e`,
    sampleInput: 'a b'
  },
];

/* ═══════════════════════════════════════════════════════════════
   1. GRAMMAR PARSER
═══════════════════════════════════════════════════════════════ */
function parseGrammar(text) {
  const lines = text.split('\n').map(l => l.trim()).filter(l => l && !l.startsWith('//') && !l.startsWith('#'));
  if (!lines.length) throw new Error('Grammar is empty.');

  const productions = [];  // { lhs: 'A', rhs: ['a','B'] }[]
  const nonTerminals = [];
  const terminalSet = new Set();

  for (const line of lines) {
    // Support → and ->
    const parts = line.split(/→|->/).map(p => p.trim());
    if (parts.length < 2) throw new Error(`Invalid production: "${line}"`);
    const lhs = parts[0].trim();
    if (!lhs) throw new Error(`Empty LHS in: "${line}"`);
    if (!nonTerminals.includes(lhs)) nonTerminals.push(lhs);

    const alts = parts[1].split('|').map(a => a.trim());
    for (const alt of alts) {
      const rhs = tokenizeRhs(alt);
      productions.push({ lhs, rhs });
    }
  }

  // Identify terminals: symbols that appear in RHS but not in NT list
  for (const { rhs } of productions) {
    for (const sym of rhs) {
      if (sym !== EPSILON && !nonTerminals.includes(sym)) {
        terminalSet.add(sym);
      }
    }
  }

  const terminals = [...terminalSet].sort();

  return {
    nonTerminals,
    terminals,
    productions,
    start: nonTerminals[0],
    first: null,
    follow: null,
    table: null,
  };
}

function tokenizeRhs(str) {
  str = str.trim();
  if (!str || str === 'eps' || str === 'epsilon' || str === EPSILON || str === 'ε') return [EPSILON];
  // Split by spaces (symbols are space-separated)
  return str.split(/\s+/).filter(Boolean).map(normalizeSymbol);
}

function normalizeSymbol(s) {
  if (s === 'eps' || s === 'epsilon' || s === 'ε') return EPSILON;
  // Keep → as-is for display but it shouldn't appear in rhs
  return s;
}

/* ═══════════════════════════════════════════════════════════════
   2. FIRST SETS
═══════════════════════════════════════════════════════════════ */
function computeFirst(g) {
  const first = {};
  for (const nt of g.nonTerminals) first[nt] = new Set();

  let changed = true;
  while (changed) {
    changed = false;
    for (const { lhs, rhs } of g.productions) {
      const before = first[lhs].size;

      if (rhs[0] === EPSILON) {
        if (!first[lhs].has(EPSILON)) { first[lhs].add(EPSILON); changed = true; }
      } else {
        let allDeriveEps = true;
        for (const sym of rhs) {
          if (!g.nonTerminals.includes(sym)) {
            // terminal
            first[lhs].add(sym);
            allDeriveEps = false;
            break;
          } else {
            for (const t of first[sym]) {
              if (t !== EPSILON) first[lhs].add(t);
            }
            if (!first[sym].has(EPSILON)) { allDeriveEps = false; break; }
          }
        }
        if (allDeriveEps) first[lhs].add(EPSILON);
      }
      if (first[lhs].size !== before) changed = true;
    }
  }

  return first;
}

function firstOfSequence(seq, first, nonTerminals) {
  const result = new Set();
  let allDeriveEps = true;
  for (const sym of seq) {
    if (sym === EPSILON) { result.add(EPSILON); break; }
    if (!nonTerminals.includes(sym)) {
      result.add(sym);
      allDeriveEps = false;
      break;
    } else {
      for (const t of first[sym]) {
        if (t !== EPSILON) result.add(t);
      }
      if (!first[sym].has(EPSILON)) { allDeriveEps = false; break; }
    }
  }
  if (allDeriveEps) result.add(EPSILON);
  return result;
}

/* ═══════════════════════════════════════════════════════════════
   3. FOLLOW SETS
═══════════════════════════════════════════════════════════════ */
function computeFollow(g) {
  const follow = {};
  for (const nt of g.nonTerminals) follow[nt] = new Set();
  follow[g.start].add(DOLLAR);

  let changed = true;
  while (changed) {
    changed = false;
    for (const { lhs, rhs } of g.productions) {
      for (let i = 0; i < rhs.length; i++) {
        const sym = rhs[i];
        if (!g.nonTerminals.includes(sym)) continue;
        const before = follow[sym].size;

        const beta = rhs.slice(i + 1);
        const firstBeta = beta.length ? firstOfSequence(beta, g.first, g.nonTerminals) : new Set([EPSILON]);

        for (const t of firstBeta) {
          if (t !== EPSILON) follow[sym].add(t);
        }
        if (firstBeta.has(EPSILON) || beta.length === 0) {
          for (const t of follow[lhs]) follow[sym].add(t);
        }
        if (follow[sym].size !== before) changed = true;
      }
    }
  }
  return follow;
}

/* ═══════════════════════════════════════════════════════════════
   4. LL(1) PARSE TABLE & CONFLICT DETECTION
═══════════════════════════════════════════════════════════════ */
function buildParseTable(g) {
  // M[A][a] = list of productions (for conflict detection)
  const table = {};
  for (const nt of g.nonTerminals) table[nt] = {};

  const conflictMap = new Map();

  for (const prod of g.productions) {
    const { lhs, rhs } = prod;
    const firstRhs = firstOfSequence(rhs, g.first, g.nonTerminals);

    for (const term of firstRhs) {
      if (term === EPSILON) continue;
      if (!table[lhs][term]) table[lhs][term] = [];
      if (table[lhs][term].length > 0) {
        const key = `${lhs}|${term}`;
        const existing = conflictMap.get(key) || { nt: lhs, term, prods: [...table[lhs][term]], type: 'FIRST/FIRST' };
        existing.prods.push(prod);
        conflictMap.set(key, existing);
      }
      table[lhs][term].push(prod);
    }

    if (firstRhs.has(EPSILON)) {
      for (const term of g.follow[lhs]) {
        if (!table[lhs][term]) table[lhs][term] = [];
        if (table[lhs][term].length > 0) {
          const key = `${lhs}|${term}`;
          const existing = conflictMap.get(key) || { nt: lhs, term, prods: [...table[lhs][term]], type: 'FIRST/FOLLOW' };
          existing.prods.push(prod);
          conflictMap.set(key, existing);
        }
        table[lhs][term].push(prod);
      }
    }
  }

  return { table, conflicts: Array.from(conflictMap.values()) };
}

function detectLeftRecursion(g) {
  const directRules = [];
  for (const prod of g.productions) {
    if (prod.rhs[0] === prod.lhs) {
      directRules.push(`${prod.lhs} → ${prod.rhs.join(' ')}`);
    }
  }
  return directRules;
}

function detectNeedsLeftFactoring(g) {
  const needsFactoring = [];
  for (const nt of g.nonTerminals) {
    const prods = g.productions.filter(p => p.lhs === nt);
    const prefixes = {};
    for (const p of prods) {
      const first = p.rhs[0];
      if (!prefixes[first]) prefixes[first] = [];
      prefixes[first].push(p);
    }
    for (const [sym, pList] of Object.entries(prefixes)) {
      if (pList.length > 1 && sym !== EPSILON) {
        needsFactoring.push(`${nt} (shared prefix "${sym}")`);
      }
    }
  }
  return needsFactoring;
}

/* ═══════════════════════════════════════════════════════════════
   5. SMART TOKENIZER & PARSING (TRACE & TREE)
═══════════════════════════════════════════════════════════════ */
function tokenizeInput(raw, terminals) {
  raw = (raw || '').trim();
  if (!raw) return [];
  const spaceTokens = raw.split(/\s+/).filter(t => t && t !== DOLLAR);
  // If user separated by spaces and all are known terminals, accept immediately
  if (spaceTokens.length > 0 && spaceTokens.every(t => terminals.includes(t))) {
    return spaceTokens;
  }

  // Greedy tokenizer fallback (handles id+id, (id+id), etc.)
  const sorted = [...terminals].sort((a, b) => b.length - a.length);
  const result = [];
  let s = raw.replace(/\s+/g, '');
  let i = 0;
  while (i < s.length) {
    let matched = false;
    for (const t of sorted) {
      if (s.startsWith(t, i)) {
        result.push(t);
        i += t.length;
        matched = true;
        break;
      }
    }
    if (!matched) {
      // Return space tokens so standard parser error message can report unknown token
      return spaceTokens;
    }
  }
  return result;
}

function deriveParseTree(g, tokens) {
  function matchSymbol(sym, index, depth) {
    if (depth > 45) return null; // Avoid infinite recursion
    if (!g.nonTerminals.includes(sym)) {
      if (sym === EPSILON) {
        return [{ node: { symbol: EPSILON, children: [] }, nextIndex: index }];
      }
      if (index < tokens.length && tokens[index] === sym) {
        return [{ node: { symbol: sym, children: [] }, nextIndex: index + 1 }];
      }
      return null;
    }

    const prods = g.productions.filter(p => p.lhs === sym);
    // Sort productions: prefer non-left-recursive productions first
    const sortedProds = [...prods].sort((a, b) => (a.rhs[0] === sym) - (b.rhs[0] === sym));

    const results = [];
    for (const prod of sortedProds) {
      const rhsMatches = matchSequence(prod.rhs, index, depth + 1);
      for (const m of rhsMatches) {
        results.push({
          node: { symbol: sym, children: m.children },
          nextIndex: m.nextIndex
        });
      }
    }
    return results.length ? results : null;
  }

  function matchSequence(rhs, index, depth) {
    if (rhs.length === 0 || rhs[0] === EPSILON) {
      return [{ children: [{ symbol: EPSILON, children: [] }], nextIndex: index }];
    }
    let states = [{ children: [], nextIndex: index }];
    for (const sym of rhs) {
      const nextStates = [];
      for (const state of states) {
        const matches = matchSymbol(sym, state.nextIndex, depth);
        if (matches) {
          for (const m of matches) {
            nextStates.push({
              children: [...state.children, m.node],
              nextIndex: m.nextIndex
            });
          }
        }
      }
      states = nextStates;
      if (states.length === 0) break;
    }
    return states;
  }

  const allMatches = matchSymbol(g.start, 0, 0);
  if (allMatches) {
    const fullMatch = allMatches.find(m => m.nextIndex === tokens.length);
    if (fullMatch) return fullMatch.node;
  }
  return null;
}

function parseString(inputTokens, g) {
  // inputTokens: array of terminal strings
  const tokens = [...inputTokens, DOLLAR];
  const steps  = [];
  const stack  = [DOLLAR, g.start];
  let ip = 0; // input pointer

  // Build parse tree
  const rootNode = { symbol: g.start, children: [] };
  const nodeStack = [null, rootNode]; // parallel to stack

  let stepCount = 0;
  const MAX_STEPS = 500;

  while (true) {
    if (++stepCount > MAX_STEPS) {
      steps.push({
        stack: [...stack].reverse().join(' '),
        input: tokens.slice(ip).join(' '),
        action: `Execution halted: Loop detected (${MAX_STEPS} steps). Left recursion or conflicts in table prevented deterministic LL(1) parse.`,
        actionType: 'error'
      });
      return { steps, accepted: false, root: null, conflictHalted: true };
    }

    const top       = stack[stack.length - 1];
    const topNode   = nodeStack[nodeStack.length - 1];
    const lookahead = tokens[ip];

    const stackStr = [...stack].reverse().join(' ');
    const inputStr = tokens.slice(ip).join(' ');

    if (top === DOLLAR && lookahead === DOLLAR) {
      steps.push({ stack: stackStr, input: inputStr, action: 'accept', actionType: 'accept' });
      return { steps, accepted: true, root: rootNode };
    }

    if (top === DOLLAR) {
      steps.push({ stack: stackStr, input: inputStr, action: `Error: stack empty but input "${lookahead}" remains`, actionType: 'error' });
      return { steps, accepted: false, root: null };
    }

    if (top === lookahead) {
      // Match
      steps.push({ stack: stackStr, input: inputStr, action: `Match "${top}"`, actionType: 'match' });
      stack.pop();
      nodeStack.pop();
      ip++;
    } else if (!g.nonTerminals.includes(top)) {
      // Terminal mismatch
      steps.push({ stack: stackStr, input: inputStr, action: `Error: expected "${top}", got "${lookahead}"`, actionType: 'error' });
      return { steps, accepted: false, root: null };
    } else {
      // Non-terminal
      const entry = g.table.table[top] && g.table.table[top][lookahead];
      if (!entry || entry.length === 0) {
        steps.push({ stack: stackStr, input: inputStr, action: `Error: no rule for M[${top},${lookahead}]`, actionType: 'error' });
        return { steps, accepted: false, root: null };
      }

      // If cell has conflict, pick non-recursive production if possible to avoid immediate self-loop
      let prod = entry[0];
      const isConflict = entry.length > 1;
      if (isConflict) {
        const nonRec = entry.find(p => p.rhs[0] !== top);
        if (nonRec) prod = nonRec;
      }

      const rhsStr = prod.rhs[0] === EPSILON ? EPSILON : prod.rhs.join(' ');
      const actionMsg = isConflict
        ? `[Conflict in M[${top},${lookahead}]] Chose ${top} → ${rhsStr}`
        : `Expand: ${top} → ${rhsStr}`;

      steps.push({ stack: stackStr, input: inputStr, action: actionMsg, actionType: isConflict ? 'error' : 'expand', prod });
      stack.pop();
      nodeStack.pop();

      if (prod.rhs[0] !== EPSILON) {
        const children = prod.rhs.map(s => ({ symbol: s, children: [] }));
        if (topNode) topNode.children = children;
        for (let i = prod.rhs.length - 1; i >= 0; i--) {
          stack.push(prod.rhs[i]);
          nodeStack.push(children[i]);
        }
      } else {
        const epsChild = { symbol: EPSILON, children: [] };
        if (topNode) topNode.children = [epsChild];
      }
    }
  }
}

/* ═══════════════════════════════════════════════════════════════
   6. LEFT RECURSION ELIMINATION
═══════════════════════════════════════════════════════════════ */
function eliminateLeftRecursion(g) {
  const nts = [...g.nonTerminals];
  let productions = g.productions.map(p => ({ ...p, rhs: [...p.rhs] }));
  const newProductions = [];
  const newNTs = [...nts];

  for (let i = 0; i < nts.length; i++) {
    const Ai = nts[i];

    // Step 1: substitute Aj (j < i) in Ai-productions
    for (let j = 0; j < i; j++) {
      const Aj = nts[j];
      const AjProds = productions.filter(p => p.lhs === Aj);
      const AiProds = productions.filter(p => p.lhs === Ai);
      productions = productions.filter(p => p.lhs !== Ai);

      for (const prod of AiProds) {
        if (prod.rhs[0] === Aj) {
          for (const ajProd of AjProds) {
            if (ajProd.rhs[0] === EPSILON) {
              productions.push({ lhs: Ai, rhs: prod.rhs.slice(1).length ? prod.rhs.slice(1) : [EPSILON] });
            } else {
              productions.push({ lhs: Ai, rhs: [...ajProd.rhs, ...prod.rhs.slice(1)] });
            }
          }
        } else {
          productions.push(prod);
        }
      }
    }

    // Step 2: eliminate direct left recursion from Ai
    const aiProds = productions.filter(p => p.lhs === Ai);
    const recursive    = aiProds.filter(p => p.rhs[0] === Ai);
    const nonRecursive = aiProds.filter(p => p.rhs[0] !== Ai);

    if (recursive.length > 0) {
      const Ai_prime = Ai + "'";
      if (!newNTs.includes(Ai_prime)) newNTs.push(Ai_prime);
      productions = productions.filter(p => p.lhs !== Ai);

      for (const p of nonRecursive) {
        const newRhs = p.rhs[0] === EPSILON ? [Ai_prime] : [...p.rhs, Ai_prime];
        productions.push({ lhs: Ai, rhs: newRhs });
      }
      if (nonRecursive.length === 0) productions.push({ lhs: Ai, rhs: [Ai_prime] });

      for (const p of recursive) {
        productions.push({ lhs: Ai_prime, rhs: [...p.rhs.slice(1), Ai_prime] });
      }
      productions.push({ lhs: Ai_prime, rhs: [EPSILON] });
    }
  }

  return formatProductions(productions, newNTs);
}

/* ═══════════════════════════════════════════════════════════════
   7. LEFT FACTORING
═══════════════════════════════════════════════════════════════ */
function leftFactor(g) {
  let productions = g.productions.map(p => ({ ...p, rhs: [...p.rhs] }));
  const allNTs = [...g.nonTerminals];
  let changed = true;
  let iteration = 0;

  while (changed && iteration++ < 20) {
    changed = false;
    const currentNTs = [...new Set(productions.map(p => p.lhs))];
    for (const A of currentNTs) {
      const AProds = productions.filter(p => p.lhs === A);
      if (AProds.length < 2) continue;

      // Group by first symbol
      const groups = {};
      for (const p of AProds) {
        const first = p.rhs[0];
        if (!groups[first]) groups[first] = [];
        groups[first].push(p);
      }

      for (const [alpha, prods] of Object.entries(groups)) {
        if (prods.length < 2) continue;
        if (alpha === EPSILON) continue;

        // Find longest common prefix
        const lcp = longestCommonPrefix(prods.map(p => p.rhs));
        if (lcp.length === 0) continue;

        changed = true;
        const ANew = A + '_f' + Object.keys(groups).indexOf(alpha);
        if (!allNTs.includes(ANew)) allNTs.push(ANew);

        productions = productions.filter(p => !prods.includes(p));
        productions.push({ lhs: A, rhs: [...lcp, ANew] });

        for (const p of prods) {
          const rest = p.rhs.slice(lcp.length);
          productions.push({ lhs: ANew, rhs: rest.length ? rest : [EPSILON] });
        }
        break; // restart for this NT
      }
    }
  }

  return formatProductions(productions, allNTs);
}

function longestCommonPrefix(arrays) {
  if (!arrays.length) return [];
  let prefix = [...arrays[0]];
  for (let i = 1; i < arrays.length; i++) {
    let len = 0;
    while (len < prefix.length && len < arrays[i].length && prefix[len] === arrays[i][len]) len++;
    prefix = prefix.slice(0, len);
  }
  return prefix;
}

function formatProductions(productions, nts) {
  const lines = [];
  const seen = new Set();
  for (const nt of nts) {
    const prods = productions.filter(p => p.lhs === nt);
    if (!prods.length) continue;
    const key = nt;
    if (seen.has(key)) continue;
    seen.add(key);
    const rhs = prods.map(p => p.rhs.join(' ')).join(' | ');
    lines.push(`${nt} -> ${rhs}`);
  }
  return lines.join('\n');
}

/* ═══════════════════════════════════════════════════════════════
   8. PARSE TREE SVG RENDERER
═══════════════════════════════════════════════════════════════ */
function renderParseTree(root) {
  if (!root) return '<p style="color:var(--text-muted)">No parse tree available.</p>';

  const NODE_W = 64, NODE_H = 32, H_GAP = 16, V_GAP = 56;

  // Compute layout with post-order widths
  function computeLayout(node, depth = 0) {
    node.depth = depth;
    if (!node.children || node.children.length === 0) {
      node.width = NODE_W + H_GAP;
      node.x = 0;
      return;
    }
    for (const c of node.children) computeLayout(c, depth + 1);
    node.width = node.children.reduce((s, c) => s + c.width, 0);
  }

  function assignX(node, startX = 0) {
    node.x = startX + node.width / 2 - NODE_W / 2;
    let cx = startX;
    for (const c of (node.children || [])) {
      assignX(c, cx);
      cx += c.width;
    }
  }

  function maxDepth(node) {
    if (!node.children || !node.children.length) return node.depth;
    return Math.max(...node.children.map(maxDepth));
  }

  function collectNodes(node, list = []) {
    list.push(node);
    for (const c of (node.children || [])) collectNodes(c, list);
    return list;
  }

  function collectEdges(node, edges = []) {
    for (const c of (node.children || [])) {
      edges.push({ from: node, to: c });
      collectEdges(c, edges);
    }
    return edges;
  }

  computeLayout(root);
  assignX(root);

  const allNodes = collectNodes(root);
  const allEdges = collectEdges(root);
  const maxD = maxDepth(root);

  const svgW = root.width + 40;
  const svgH = (maxD + 1) * (NODE_H + V_GAP) + 40;

  const px = n => n.x + 20 + NODE_W / 2;
  const py = n => n.depth * (NODE_H + V_GAP) + 20 + NODE_H / 2;

  let svgContent = `<svg id="tree-svg" width="${svgW}" height="${svgH}" viewBox="0 0 ${svgW} ${svgH}" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <linearGradient id="nodeGrad" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#E6CDBA"/>
      <stop offset="100%" stop-color="#D9BBA3"/>
    </linearGradient>
    <linearGradient id="leafGrad" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#8A9A7B"/>
      <stop offset="100%" stop-color="#758567"/>
    </linearGradient>
    <linearGradient id="epsGrad" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#C9923A"/>
      <stop offset="100%" stop-color="#B57E28"/>
    </linearGradient>
    <filter id="softShadow" x="-10%" y="-10%" width="125%" height="130%">
      <feDropShadow dx="0" dy="2" stdDeviation="2.5" flood-color="#1C1512" flood-opacity="0.08"/>
    </filter>
  </defs>`;

  // Edges
  for (const { from, to } of allEdges) {
    svgContent += `<line x1="${px(from)}" y1="${py(from) + NODE_H/2}" x2="${px(to)}" y2="${py(to) - NODE_H/2}"
      stroke="#1C1512" stroke-width="1.2" stroke-linecap="round"/>`;
  }

  // Nodes
  for (const node of allNodes) {
    const isLeaf = !node.children || node.children.length === 0;
    const isEps  = node.symbol === EPSILON;
    const fill   = isEps ? 'url(#epsGrad)' : (isLeaf ? 'url(#leafGrad)' : 'url(#nodeGrad)');
    const textColor = isLeaf || isEps ? '#FFFFFF' : '#1C1512';
    const nx = node.x + 20;
    const ny = node.depth * (NODE_H + V_GAP) + 20;
    const label = node.symbol;

    svgContent += `<rect x="${nx}" y="${ny}" width="${NODE_W}" height="${NODE_H}" rx="10"
      fill="${fill}" opacity="${isEps ? 0.95 : 1}" filter="url(#softShadow)" stroke="#1C1512" stroke-width="1"/>`;
    svgContent += `<text x="${nx + NODE_W/2}" y="${ny + NODE_H/2 + 5}"
      text-anchor="middle" font-family="'JetBrains Mono', monospace" font-size="12" font-weight="600"
      fill="${textColor}">${escHtml(label)}</text>`;
  }

  svgContent += '</svg>';
  return svgContent;
}

function escHtml(str) {
  return String(str).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
}

/* ═══════════════════════════════════════════════════════════════
   9. UI HELPERS
═══════════════════════════════════════════════════════════════ */
function showToast(msg, type = 'info') {
  let container = document.querySelector('.toast-container');
  if (!container) {
    container = document.createElement('div');
    container.className = 'toast-container';
    document.body.appendChild(container);
  }
  const toast = document.createElement('div');
  toast.className = `toast toast-${type}`;
  const icon = type === 'success' ? '✓' : type === 'error' ? '✕' : 'ℹ';
  toast.innerHTML = `<span>${icon}</span> ${escHtml(msg)}`;
  container.appendChild(toast);
  setTimeout(() => { toast.style.opacity = '0'; toast.style.transition = 'opacity 0.3s'; setTimeout(() => toast.remove(), 300); }, 3000);
}

function switchTab(name) {
  document.querySelectorAll('.tab-btn-arch').forEach(b => { b.classList.toggle('active', b.dataset.tab === name); b.setAttribute('aria-selected', b.dataset.tab === name); });
  document.querySelectorAll('.tab-pane').forEach(p => p.classList.toggle('active', p.id === `pane-${name}`));
}

function setStatus(cls, text) {
  const badge = document.getElementById('ll1-status-badge');
  badge.className = `status-badge status-${cls}`;
  document.getElementById('status-text').textContent = text;
}

function updateLineNumbers() {
  const ta = document.getElementById('grammar-input');
  const ln = document.getElementById('line-numbers');
  const lines = ta.value.split('\n').length;
  ln.innerHTML = Array.from({length: lines}, (_,i) => `<div>${i+1}</div>`).join('');
}

/* ═══════════════════════════════════════════════════════════════
   10. RENDER: FIRST / FOLLOW
═══════════════════════════════════════════════════════════════ */
function renderSetTable(containerId, setData, nonTerminals) {
  const container = document.getElementById(containerId);
  let html = `<table class="sets-table">
    <thead><tr><th>Non-Terminal</th><th>Set</th></tr></thead><tbody>`;

  for (const nt of nonTerminals) {
    const items = [...(setData[nt] || [])].sort((a,b) => {
      if (a === EPSILON) return 1;
      if (b === EPSILON) return -1;
      if (a === DOLLAR)  return 1;
      if (b === DOLLAR)  return -1;
      return a.localeCompare(b);
    });
    const tokens = items.map(t => {
      if (t === EPSILON) return `<span class="token token-epsilon">${EPSILON}</span>`;
      if (t === DOLLAR)  return `<span class="token token-dollar">$</span>`;
      return `<span class="token token-terminal">${escHtml(t)}</span>`;
    }).join('');
    html += `<tr><td class="nt-cell">${escHtml(nt)}</td><td><div class="token-list">${tokens}</div></td></tr>`;
  }
  html += '</tbody></table>';
  container.innerHTML = html;
}

/* ═══════════════════════════════════════════════════════════════
   11. RENDER: PARSE TABLE
═══════════════════════════════════════════════════════════════ */
function renderParseTableHTML(g) {
  const { table, conflicts } = g.table;
  const terminals = [...g.terminals, DOLLAR].sort((a,b) => {
    if (a === DOLLAR) return 1; if (b === DOLLAR) return -1; return a.localeCompare(b);
  });

  let html = `<table class="parse-table"><thead><tr><th>NT \\ T</th>`;
  for (const t of terminals) {
    html += `<th class="${t === DOLLAR ? 'col-dollar' : ''}">${escHtml(t)}</th>`;
  }
  html += '</tr></thead><tbody>';

  for (const nt of g.nonTerminals) {
    html += `<tr><td class="row-header">${escHtml(nt)}</td>`;
    for (const t of terminals) {
      const entry = table[nt] && table[nt][t];
      if (!entry || entry.length === 0) {
        html += `<td class="cell-empty">—</td>`;
      } else if (entry.length > 1) {
        const prods = entry.map(p => `${p.lhs}→${p.rhs.join(' ')}`).join(' / ');
        html += `<td class="cell-conflict" title="CONFLICT">${escHtml(prods)}</td>`;
      } else {
        const p = entry[0];
        const rhsStr = p.rhs[0] === EPSILON ? EPSILON : p.rhs.join(' ');
        html += `<td class="cell-production">${escHtml(p.lhs)} → ${escHtml(rhsStr)}</td>`;
      }
    }
    html += '</tr>';
  }
  html += '</tbody></table>';
  return html;
}

/* ═══════════════════════════════════════════════════════════════
   12. RENDER: TRACE TABLE
═══════════════════════════════════════════════════════════════ */
function renderTraceTable(steps, currentIdx) {
  let html = `<table class="trace-table">
    <thead><tr>
      <th>#</th>
      <th>Stack (top →)</th>
      <th>Input</th>
      <th>Action</th>
    </tr></thead><tbody>`;

  for (let i = 0; i < steps.length; i++) {
    const s = steps[i];
    const isCurrent = i === currentIdx;
    const tagClass = `action-tag-${s.actionType}`;
    html += `<tr class="${isCurrent ? 'row-current' : ''}">
      <td class="trace-step-num">${i + 1}</td>
      <td class="trace-stack">${escHtml(s.stack)}</td>
      <td class="trace-input-cell">${escHtml(s.input)}</td>
      <td class="trace-action-cell"><span class="${tagClass}">${escHtml(s.action)}</span></td>
    </tr>`;
  }
  html += '</tbody></table>';
  return html;
}

/* ═══════════════════════════════════════════════════════════════
   13. TRACE VISUALIZATION (stack + input area)
═══════════════════════════════════════════════════════════════ */
function renderTraceVisual(step, allTokens) {
  if (!step) return;
  const visual = document.getElementById('trace-visual');
  const stackSyms = step.stack.split(' ').filter(Boolean).reverse();
  const inputSyms  = step.input.split(' ').filter(Boolean);

  let stackHtml = '<div class="trace-panel"><div class="trace-panel-label">Stack (top)</div><div class="trace-tokens">';
  stackHtml += stackSyms.map((s,i) =>
    `<span class="trace-token ${i===0 ? 'trace-token-active' : 'trace-token-normal'}">${escHtml(s)}</span>`
  ).join('');
  stackHtml += '</div></div>';

  let inputHtml = '<div class="trace-panel"><div class="trace-panel-label">Input Buffer</div><div class="trace-tokens">';
  inputHtml += inputSyms.map((s,i) =>
    `<span class="trace-token ${i===0 ? 'trace-token-active' : 'trace-token-normal'}">${escHtml(s)}</span>`
  ).join('');
  inputHtml += '</div></div>';

  const tagClass = `action-${step.actionType}`;
  const actionHtml = `<div class="trace-panel" style="flex:none;width:100%">
    <div class="trace-panel-label">Action</div>
    <div class="trace-action-box"><span class="${tagClass}">${escHtml(step.action)}</span></div>
  </div>`;

  visual.innerHTML = `<div style="display:flex;gap:24px;flex-wrap:wrap;width:100%">${stackHtml}${inputHtml}</div>${actionHtml}`;
}

function updateTraceUI() {
  const step = traceSteps[traceIndex];
  if (!step) return;
  renderTraceVisual(step, []);
  document.getElementById('trace-counter').textContent = `Step ${traceIndex + 1} / ${traceSteps.length}`;
  document.getElementById('btn-trace-prev').disabled = traceIndex === 0;
  document.getElementById('btn-trace-next').disabled = traceIndex === traceSteps.length - 1;
  document.getElementById('trace-table-container').innerHTML = renderTraceTable(traceSteps, traceIndex);
  // Scroll current row into view
  const cur = document.querySelector('.trace-table .row-current');
  if (cur) cur.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
}

/* ═══════════════════════════════════════════════════════════════
   14. EXPORT
═══════════════════════════════════════════════════════════════ */
function exportCSV(type) {
  if (!G) return showToast('Analyze a grammar first.', 'error');
  let csv = '', filename = '';

  if (type === 'first') {
    csv = 'Non-Terminal,FIRST Set\n';
    for (const nt of G.nonTerminals) {
      csv += `"${nt}","${[...G.first[nt]].join(', ')}"\n`;
    }
    filename = 'first_sets.csv';
  } else if (type === 'follow') {
    csv = 'Non-Terminal,FOLLOW Set\n';
    for (const nt of G.nonTerminals) {
      csv += `"${nt}","${[...G.follow[nt]].join(', ')}"\n`;
    }
    filename = 'follow_sets.csv';
  } else if (type === 'table') {
    const terms = [...G.terminals, DOLLAR];
    csv = 'NT,' + terms.map(t => `"${t}"`).join(',') + '\n';
    for (const nt of G.nonTerminals) {
      csv += `"${nt}",` + terms.map(t => {
        const e = G.table.table[nt] && G.table.table[nt][t];
        if (!e || !e.length) return '""';
        return `"${e.map(p => p.lhs + ' -> ' + p.rhs.join(' ')).join(' | ')}"`;
      }).join(',') + '\n';
    }
    filename = 'parse_table.csv';
  } else if (type === 'trace') {
    csv = '#,Stack,Input,Action\n';
    traceSteps.forEach((s,i) => {
      csv += `${i+1},"${s.stack}","${s.input}","${s.action}"\n`;
    });
    filename = 'parse_trace.csv';
  }

  const blob = new Blob([csv], { type: 'text/csv' });
  const url  = URL.createObjectURL(blob);
  const a    = document.createElement('a');
  a.href = url; a.download = filename; a.click();
  URL.revokeObjectURL(url);
  showToast(`Exported ${filename}`, 'success');
}

function exportTreeSVG() {
  const svg = document.getElementById('tree-svg');
  if (!svg) return showToast('No parse tree to export.', 'error');
  const data = new XMLSerializer().serializeToString(svg);
  const blob = new Blob([data], { type: 'image/svg+xml' });
  const url  = URL.createObjectURL(blob);
  const a    = document.createElement('a');
  a.href = url; a.download = 'parse_tree.svg'; a.click();
  URL.revokeObjectURL(url);
  showToast('Exported parse_tree.svg', 'success');
}

/* ═══════════════════════════════════════════════════════════════
   15. MAIN ANALYZE HANDLER
═══════════════════════════════════════════════════════════════ */
function analyzeGrammar() {
  const text = document.getElementById('grammar-input').value.trim();
  if (!text) return showToast('Please enter a grammar first.', 'error');

  try {
    G = parseGrammar(text);
    G.first  = computeFirst(G);
    G.follow = computeFollow(G);
    G.table  = buildParseTable(G);

    const conflicts = G.table.conflicts;
    const hasConflict = conflicts.length > 0;
    const lrRules = detectLeftRecursion(G);
    const lfRules = detectNeedsLeftFactoring(G);

    // Status badge
    setStatus(hasConflict ? 'conflict' : 'valid', hasConflict ? `Conflicts (${conflicts.length})` : 'LL(1) Valid');

    // Enable parse button and transform buttons
    document.getElementById('btn-parse').disabled = false;
    document.getElementById('btn-elim-lr').disabled = false;
    document.getElementById('btn-left-factor').disabled = false;

    // ── Overview stats ──
    const statsGrid = document.getElementById('stats-grid');
    if (statsGrid) {
      statsGrid.innerHTML = [
        { label: 'Non-Terminals', value: G.nonTerminals.length },
        { label: 'Terminals',     value: G.terminals.length },
        { label: 'Productions',   value: G.productions.length },
        { label: 'Start Symbol',  value: G.start },
        { label: 'Conflicts',     value: conflicts.length },
        { label: 'LL(1) Valid',   value: hasConflict ? 'No' : 'Yes' },
      ].map(s => `
        <div class="stat-item">
          <div class="stat-value">${escHtml(String(s.value))}</div>
          <div class="stat-label">${escHtml(s.label)}</div>
        </div>
      `).join('');
    }

    // Show dashboard content
    const dashEmpty = document.getElementById('dashboard-empty');
    if (dashEmpty) dashEmpty.style.display = 'none';
    const dashContent = document.getElementById('dashboard-content');
    if (dashContent) dashContent.style.display = 'block';

    // ── FIRST sets ──
    document.getElementById('first-empty').style.display = 'none';
    document.getElementById('first-content').style.display = 'block';
    renderSetTable('first-table-container', G.first, G.nonTerminals);
    if (document.getElementById('dashboard-first-container')) {
      renderSetTable('dashboard-first-container', G.first, G.nonTerminals);
    }

    // ── FOLLOW sets ──
    document.getElementById('follow-empty').style.display = 'none';
    document.getElementById('follow-content').style.display = 'block';
    renderSetTable('follow-table-container', G.follow, G.nonTerminals);
    if (document.getElementById('dashboard-follow-container')) {
      renderSetTable('dashboard-follow-container', G.follow, G.nonTerminals);
    }

    // ── Parse Table ──
    document.getElementById('table-empty').style.display = 'none';
    document.getElementById('table-content').style.display = 'block';

    // Build explanatory verdict banner
    let verdictHTML = '';
    if (hasConflict) {
      const conflictList = conflicts.map(c => `<code>M[${escHtml(c.nt)}, ${escHtml(c.term)}]</code>`).join(', ');
      let fixButtons = '';
      if (lrRules.length > 0) {
        fixButtons += `<button class="btn-conflict-fix" onclick="quickEliminateLeftRecursion()">⚡ ELIMINATE LEFT RECURSION</button>`;
      }
      if (lfRules.length > 0) {
        fixButtons += `<button class="btn-conflict-fix" onclick="quickLeftFactor()">⚡ APPLY LEFT FACTORING</button>`;
      }

      verdictHTML = `
        <div class="conflict-details-wrap">
          <div class="conflict-heading-row">
            <span>⚠</span>
            <span><strong>NOT LL(1)</strong> — ${conflicts.length} conflict(s) detected in parse table: ${conflictList}</span>
          </div>
          <div class="conflict-msg-body">
            ${lrRules.length ? `<p><strong>Direct Left Recursion:</strong> Found in <code>${lrRules.map(escHtml).join(', ')}</code>. Left recursion causes multiple rules per table cell.</p>` : ''}
            ${lfRules.length ? `<p><strong>Needs Left Factoring:</strong> Common prefix found for ${lfRules.map(escHtml).join(', ')}.</p>` : ''}
            <p>An LL(1) parser requires deterministic tables (1 rule per cell). Click below to resolve automatically:</p>
          </div>
          ${fixButtons ? `<div class="conflict-actions-row">${fixButtons}</div>` : ''}
        </div>
      `;
    } else {
      verdictHTML = '✓ <strong>Grammar is LL(1)</strong>: No conflicts detected. The predictive parse table is completely deterministic.';
    }

    const verdictEl = document.getElementById('ll1-verdict');
    if (verdictEl) {
      verdictEl.className = hasConflict ? 'verdict-pill verdict-conflict' : 'verdict-pill verdict-valid';
      verdictEl.innerHTML = verdictHTML;
    }
    const dashVerdict = document.getElementById('dashboard-ll1-verdict');
    if (dashVerdict) {
      dashVerdict.className = `verdict-pill ${hasConflict ? 'verdict-conflict' : 'verdict-valid'}`;
      dashVerdict.innerHTML = verdictHTML;
    }

    const tableHTML = renderParseTableHTML(G);
    document.getElementById('parse-table-container').innerHTML = tableHTML;
    if (document.getElementById('dashboard-table-container')) {
      document.getElementById('dashboard-table-container').innerHTML = tableHTML;
    }

    // Default tree-empty placeholder
    const treeEmptyEl = document.getElementById('tree-empty');
    if (treeEmptyEl) {
      if (hasConflict) {
        treeEmptyEl.innerHTML = `
          <div class="tree-empty-card">
            <div class="tree-notice-badge">⚠ Conflicts Detected in Parse Table</div>
            <h3 style="font-family:var(--font-serif);margin-bottom:8px;">Grammar is not LL(1)</h3>
            <p style="font-size:0.86rem;color:var(--text-muted);margin-bottom:14px;">The table has multiple productions for some cells. You can auto-resolve conflicts, or click Parse to derive a tree anyway.</p>
            <div style="display:flex;gap:8px;justify-content:center;flex-wrap:wrap;">
              ${lrRules.length ? '<button class="btn-conflict-fix" onclick="quickEliminateLeftRecursion()">⚡ ELIMINATE LEFT RECURSION</button>' : ''}
              ${lfRules.length ? '<button class="btn-conflict-fix" onclick="quickLeftFactor()">⚡ APPLY LEFT FACTORING</button>' : ''}
              <button class="btn-conflict-fix" style="background:var(--accent-copper);" onclick="document.getElementById('btn-parse').click()">⚡ PARSE & VIEW TREE</button>
            </div>
          </div>
        `;
      } else {
        treeEmptyEl.innerHTML = `
          <div class="tree-empty-card">
            <h3 style="font-family:var(--font-serif);margin-bottom:8px;">Ready to View Derivation Tree</h3>
            <p style="font-size:0.86rem;color:var(--text-muted);margin-bottom:14px;">Parse an input sentence on the left to render the visual syntax derivation tree.</p>
            <button class="btn-conflict-fix" style="background:var(--accent-copper);" onclick="document.getElementById('btn-parse').click()">⚡ GENERATE PARSE TREE →</button>
          </div>
        `;
      }
    }

    // Reset trace & tree
    traceSteps = [];
    document.getElementById('trace-content').style.display = 'none';
    document.getElementById('trace-empty').style.display   = 'flex';
    document.getElementById('tree-content').style.display  = 'none';
    if (treeEmptyEl) treeEmptyEl.style.display             = 'flex';

    showToast('Grammar analyzed successfully!', 'success');

  } catch (e) {
    setStatus('invalid', 'Parse Error');
    showToast(e.message, 'error');
  }
}

/* ═══════════════════════════════════════════════════════════════
   16. PARSE STRING HANDLER
═══════════════════════════════════════════════════════════════ */
function handleParse() {
  if (!G) return showToast('Analyze grammar first.', 'error');

  const raw = document.getElementById('parse-string-input').value.trim();
  if (!raw && raw !== '') {
    showToast('Enter an input string.', 'error');
    return;
  }

  const tokens = tokenizeInput(raw, G.terminals);

  const result = parseString(tokens, G);
  traceSteps = result.steps;
  traceIndex = 0;
  parseTreeRoot = result.root;

  let derivedViaFallback = false;
  // If LL(1) table parse didn't find an accepted tree, try top-down derivation search
  if (!result.accepted || !parseTreeRoot) {
    const fallbackTree = deriveParseTree(G, tokens);
    if (fallbackTree) {
      parseTreeRoot = fallbackTree;
      derivedViaFallback = true;
    }
  }

  const isAccepted = result.accepted || derivedViaFallback;

  // Show banner
  const banner = document.getElementById('parse-result-banner');
  if (result.accepted) {
    banner.className = 'banner-accept';
    banner.innerHTML = `<span>✓</span> <strong>Accepted!</strong> String "<code>${escHtml(raw)}</code>" is valid according to LL(1) grammar.`;
  } else if (derivedViaFallback) {
    banner.className = 'banner-warning';
    banner.innerHTML = `<span>✓</span> <strong>Accepted (Top-Down Derivation Tree Generated):</strong> String "<code>${escHtml(raw)}</code>" derived successfully. <em>(Note: Parse table contains conflicts because grammar is not strictly LL(1)).</em>`;
  } else {
    banner.className = 'banner-reject';
    banner.innerHTML = `<span>✕</span> <strong>Rejected.</strong> String "<code>${escHtml(raw)}</code>" cannot be derived by the grammar.`;
  }

  // Update dashboard parse summary card
  const dashParseSec = document.getElementById('dashboard-parse-section');
  const dashParseBanner = document.getElementById('dashboard-parse-banner');
  if (dashParseSec && dashParseBanner) {
    dashParseSec.style.display = 'block';
    dashParseBanner.className = isAccepted ? (result.accepted ? 'banner-accept' : 'banner-warning') : 'banner-reject';
    dashParseBanner.innerHTML = isAccepted
      ? `<span>✓</span> <strong>Accepted!</strong> String "<code>${escHtml(raw)}</code>" derived successfully.`
      : `<span>✕</span> <strong>Rejected.</strong> String "<code>${escHtml(raw)}</code>" could not be derived.`;
  }

  // Show trace pane
  document.getElementById('trace-empty').style.display = 'none';
  document.getElementById('trace-content').style.display = 'block';

  document.getElementById('btn-trace-prev').disabled = traceIndex === 0;
  document.getElementById('btn-trace-next').disabled = traceSteps.length <= 1;

  updateTraceUI();

  // Tab management: preserve tree tab if user is currently looking at tree
  const activeTabBtn = document.querySelector('.tab-btn-arch.active');
  const activeTab = activeTabBtn ? activeTabBtn.dataset.tab : 'overview';
  if (activeTab !== 'tree' && activeTab !== 'overview') {
    switchTab('trace');
  }

  // Parse Tree Rendering
  if (isAccepted && parseTreeRoot) {
    document.getElementById('tree-empty').style.display = 'none';
    document.getElementById('tree-content').style.display = 'block';
    document.getElementById('parse-tree-svg-container').innerHTML = renderParseTree(parseTreeRoot);
  } else {
    document.getElementById('tree-content').style.display = 'none';
    document.getElementById('tree-empty').style.display = 'flex';
  }
}

/* Quick Action Handlers (One-Click Conflict Resolution) */
function quickEliminateLeftRecursion() {
  if (!G) return;
  try {
    const result = eliminateLeftRecursion(G);
    document.getElementById('grammar-input').value = result;
    updateLineNumbers();
    analyzeGrammar();
    handleParse();
    switchTab('tree');
    showToast('Left recursion eliminated! Grammar is now LL(1).', 'success');
  } catch(e) {
    showToast('Error: ' + e.message, 'error');
  }
}
if (typeof window !== 'undefined') {
  window.quickEliminateLeftRecursion = quickEliminateLeftRecursion;
}

function quickLeftFactor() {
  if (!G) return;
  try {
    const result = leftFactor(G);
    document.getElementById('grammar-input').value = result;
    updateLineNumbers();
    analyzeGrammar();
    handleParse();
    switchTab('tree');
    showToast('Left factoring applied! Grammar is now LL(1).', 'success');
  } catch(e) {
    showToast('Error: ' + e.message, 'error');
  }
}
if (typeof window !== 'undefined') {
  window.quickLeftFactor = quickLeftFactor;
}

/* ═══════════════════════════════════════════════════════════════
   17. EVENT LISTENERS
═══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  // Line numbers
  const ta = document.getElementById('grammar-input');
  ta.addEventListener('input', updateLineNumbers);
  ta.addEventListener('keydown', (e) => {
    // Tab -> insert spaces
    if (e.key === 'Tab') {
      e.preventDefault();
      const s = ta.selectionStart, end = ta.selectionEnd;
      ta.value = ta.value.substring(0, s) + '  ' + ta.value.substring(end);
      ta.selectionStart = ta.selectionEnd = s + 2;
      updateLineNumbers();
    }
  });
  updateLineNumbers();

  // Analyze
  document.getElementById('btn-analyze').addEventListener('click', analyzeGrammar);

  // Reset
  document.getElementById('btn-reset').addEventListener('click', () => {
    G = null; traceSteps = []; parseTreeRoot = null;
    document.getElementById('grammar-input').value = '';
    document.getElementById('parse-string-input').value = '';
    updateLineNumbers();
    setStatus('idle', 'Awaiting Input');
    document.getElementById('btn-parse').disabled = true;
    document.getElementById('btn-elim-lr').disabled = true;
    document.getElementById('btn-left-factor').disabled = true;
    ['first','follow','table','trace','tree'].forEach(t => {
      const emptyEl = document.getElementById(`${t}-empty`);
      if (emptyEl) emptyEl.style.display = 'flex';
      const c = document.getElementById(`${t}-content`);
      if (c) c.style.display = 'none';
    });
    // Also hide the dashboard content and show empty state
    const dashEmpty2 = document.getElementById('dashboard-empty');
    if (dashEmpty2) dashEmpty2.style.display = '';
    const dashContent2 = document.getElementById('dashboard-content');
    if (dashContent2) dashContent2.style.display = 'none';
    const transResult = document.getElementById('transform-result');
    if (transResult) transResult.style.display = 'none';
    switchTab('overview');
    showToast('Reset complete.', 'info');
  });

  // Tab switching
  document.querySelectorAll('.tab-btn-arch').forEach(btn => {
    btn.addEventListener('click', () => switchTab(btn.dataset.tab));
  });

  // Parse string
  document.getElementById('btn-parse').addEventListener('click', handleParse);
  document.getElementById('parse-string-input').addEventListener('keydown', e => {
    if (e.key === 'Enter') handleParse();
  });

  // Trace navigation
  document.getElementById('btn-trace-prev').addEventListener('click', () => {
    if (traceIndex > 0) { traceIndex--; updateTraceUI(); }
  });
  document.getElementById('btn-trace-next').addEventListener('click', () => {
    if (traceIndex < traceSteps.length - 1) { traceIndex++; updateTraceUI(); }
  });

  // Trace play/pause
  document.getElementById('btn-trace-play').addEventListener('click', () => {
    if (traceTimer) {
      clearInterval(traceTimer); traceTimer = null;
      document.getElementById('play-label').textContent = 'AUTO PLAY';
    } else {
      document.getElementById('play-label').textContent = 'PAUSE ⏸';
      traceTimer = setInterval(() => {
        if (traceIndex < traceSteps.length - 1) {
          traceIndex++;
          updateTraceUI();
        } else {
          clearInterval(traceTimer); traceTimer = null;
          document.getElementById('play-label').textContent = 'AUTO PLAY';
        }
      }, 700);
    }
  });

  // Left Recursion Elimination
  document.getElementById('btn-elim-lr').addEventListener('click', () => {
    if (!G) return;
    try {
      const result = eliminateLeftRecursion(G);
      const el = document.getElementById('transform-result');
      el.textContent = result;
      el.style.display = 'block';
      showToast('Left recursion eliminated. Loading into editor...', 'info');
      document.getElementById('grammar-input').value = result;
      updateLineNumbers();
      analyzeGrammar();
      handleParse();
      switchTab('tree');
    } catch(e) { showToast('Error: ' + e.message, 'error'); }
  });

  // Left Factoring
  document.getElementById('btn-left-factor').addEventListener('click', () => {
    if (!G) return;
    try {
      const result = leftFactor(G);
      const el = document.getElementById('transform-result');
      el.textContent = result;
      el.style.display = 'block';
      showToast('Left factoring applied. Loading into editor...', 'info');
      document.getElementById('grammar-input').value = result;
      updateLineNumbers();
      analyzeGrammar();
      handleParse();
      switchTab('tree');
    } catch(e) { showToast('Error: ' + e.message, 'error'); }
  });

  // Sample Grammars
  const modal    = document.getElementById('sample-modal');
  const sampleList = document.getElementById('sample-list');
  SAMPLES.forEach((s, i) => {
    const item = document.createElement('div');
    item.className = 'sample-item';
    item.innerHTML = `<h4>${escHtml(s.name)}</h4><p>${escHtml(s.desc)}</p><pre>${escHtml(s.grammar)}</pre>`;
    item.addEventListener('click', () => {
      document.getElementById('grammar-input').value = s.grammar;
      if (s.sampleInput) {
        document.getElementById('parse-string-input').value = s.sampleInput;
      }
      updateLineNumbers();
      modal.style.display = 'none';
      analyzeGrammar();
      handleParse();
      switchTab('overview');
    });
    sampleList.appendChild(item);
  });

  document.getElementById('btn-load-sample').addEventListener('click', () => {
    modal.style.display = 'grid';
  });
  document.getElementById('modal-close').addEventListener('click', () => {
    modal.style.display = 'none';
  });
  modal.addEventListener('click', e => { if (e.target === modal) modal.style.display = 'none'; });

  // File Upload
  document.getElementById('btn-upload').addEventListener('click', () => {
    document.getElementById('file-input').click();
  });
  document.getElementById('file-input').addEventListener('change', e => {
    const file = e.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = ev => {
      document.getElementById('grammar-input').value = ev.target.result;
      updateLineNumbers();
      showToast(`Loaded: ${file.name}`, 'success');
      analyzeGrammar();
    };
    reader.readAsText(file);
    e.target.value = '';
  });

  // Export buttons
  document.querySelectorAll('.export-btn[data-export]').forEach(btn => {
    btn.addEventListener('click', () => exportCSV(btn.dataset.export));
  });
  document.getElementById('btn-export-tree-svg').addEventListener('click', exportTreeSVG);

  // Theme toggle
  const themeToggle = document.getElementById('theme-toggle');
  if (themeToggle) {
    themeToggle.addEventListener('click', () => {
      const isLight = document.documentElement.getAttribute('data-theme') === 'light';
      document.documentElement.setAttribute('data-theme', isLight ? '' : 'light');
      const sun = document.getElementById('sun-icon');
      const moon = document.getElementById('moon-icon');
      if (sun) sun.style.display = isLight ? '' : 'none';
      if (moon) moon.style.display = isLight ? 'none' : '';
    });
  }

  // Auto-analyze default grammar and auto-parse on load
  const defaultGrammar = `E -> T E'\nE' -> + T E' | eps\nT -> F T'\nT' -> * F T' | eps\nF -> ( E ) | id`;
  document.getElementById('grammar-input').value = defaultGrammar;
  document.getElementById('parse-string-input').value = 'id + id * id';
  updateLineNumbers();
  analyzeGrammar();
  handleParse();
  switchTab('overview');
});
