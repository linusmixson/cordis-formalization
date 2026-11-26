# Cordis Formalization

Lean 4 formalization and corrigendum for *A Programming Paradigm for Spatiotemporal Composability* ([arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1)).

## Contents

- [`lean/`](lean/) — Standalone Lean 4 (`v4.24.0`) Lake package with zero external dependencies, formalizing the calculus, paper-indexed results and counterexamples (`lean/Cordis/Results/`), and scoped repairs (`lean/Cordis/Repairs/`).
- [`docs/corrigendum-20261123.pdf`](docs/corrigendum-20261123.pdf) ([LaTeX source](docs/corrigendum-20261123.tex)) — Self-contained writeup of the counterexamples and repaired theorems.

## Verification

With [`elan`](https://github.com/leanprover/elan) installed:

```sh
cd lean
lake build
```

The package builds with `autoImplicit = false` and `warningAsError = true`. Its root module (`Cordis.lean`) runs `Cordis.AxiomAudit.check` across all 267 modules, verifying that every declaration depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## License

Eclipse Public License 2.0. See [`LICENSE`](LICENSE).
