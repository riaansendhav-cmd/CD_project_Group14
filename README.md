# L'Atelier LL(1) — Grammar Analyzer & Predictive Parser

An interactive compiler design studio for Context-Free Grammars (CFG), FIRST & FOLLOW derivations, predictive LL(1) parsing tables, derivation step traces, and visual syntax trees.

## Features
- **Grammar Specification**: Input productions with alternative rules (`|`) and empty strings (`eps` / `ε`).
- **FIRST & FOLLOW Sets**: Iterative computation with full ε-derivation handling.
- **LL(1) Predictive Parse Table**: Color-coded deterministic transition matrix with automatic conflict detection (FIRST/FIRST and FIRST/FOLLOW).
- **Interactive Step Trace**: Stack simulation showing stack pointer, input buffer, and actions.
- **Visual Parse Tree**: Clean vector-rendered SVG syntax derivation tree.
- **Automated Refactoring**: 1-click Direct Left Recursion elimination and Left Factoring.
- **Zero Dependencies**: Pure HTML5, CSS3, and modern Vanilla JavaScript.

## Getting Started
Simply open `index.html` in any modern web browser or serve via any static file server:

```bash
# Python
python -m http.server 8000

# Node.js
npx serve
```
Then visit `http://localhost:8000`.
