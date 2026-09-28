<div align="center">

# Square-root growth of operator entanglement — the lower bound in Lean

**A complete, dependency-closed Lean proof that operator entanglement in an integrable brickwork circuit grows at least like the square root of time.**

[![Lean proof check](https://github.com/dicipler-pixel/sqrt-lower-bound-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/sqrt-lower-bound-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.28.0-blue)
![Theorems](https://img.shields.io/badge/theorems-661-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

</div>

---

## The result in one line

For the rectangular finite-field brickwork circuit over a finite field `F` of odd characteristic,
with a nontrivial additive character `ψ`, the von Neumann entanglement of the selected operator
after `n + 1` layers satisfies

```text
log q · √((n + 1)/π) − (3/2) log q  ≤  S(n + 1),      q = |F|
```

(`SqrtOpEnt.standalone_rectangular_lower_sqrt_bound` in
[`RequestProject/Main.lean`](RequestProject/Main.lean)). Integrable circuits are generally
expected to entangle operators at most logarithmically; this is the proved lower half of the
counterexample.

## Whose mathematics

The theorem is from Balázs Pozsgay and István Vona, *Square-root growth of operator entanglement
in an integrable brickwork circuit* (4 September 2026). This repository is Jeromie Beasley's
formalization of their lower bound: 30 files and 661 theorems, from the circuit and its gate up
through the fibre reduction, the flat spectrum, the central-binomial estimate
`√(t/π) − 1 ≤ t·C(2t, t)/4ᵗ ≤ √(t/π)` and the entropy assembly.

## What is in the library

| Stage | Files |
| :--- | :--- |
| The circuit, gate and phases | `Gate`, `CircuitPhase`, `GridPhase`, `PhasedFourier`, `ResidualCircuit`, `NegativeCircuit`, `RectangularCore`, `BlockTranspose` |
| Counting and sectors | `ColourCounting`, `CountSectors`, `SourceSectorWeights`, `WordStabilizer`, `WordMeasurement`, `LocalEquivalence` |
| Spectrum and response | `FlatSpectrum`, `FlatSpectrumEntropy`, `ResponseCones`, `MixedHessian`, `ExtremePositive`, `ExtremeNegative` |
| Entropy | `QuantumEntropy`, `EntropyLaw`, `EntropyMeasurement`, `FibreReduction`, `FibreEntropy`, `ResidualEntropy`, `ConcreteEntropyAssembly` |
| Estimates and the headline | `CentralBinomial`, `MeanAbsDeviation`, `Main` |

The module names keep the original project name `RequestProject` so the files stay byte-identical
to the checked source.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.28.0 and Mathlib `v4.28.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False control**: the claim that one layer's central-binomial weight `1·C(2,1)/4` equals `1` (it is `1/2`) must fail to compile, for a mathematical reason.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## What is not here

The upper-bound saturation and the `+ log t` correction are intentionally absent; see
[`LIMITATIONS.md`](LIMITATIONS.md).

## Licence, citation and AI use

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
