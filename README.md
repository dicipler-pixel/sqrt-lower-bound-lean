<div align="center">

# Square-root growth of operator entanglement — the lower bound in Lean

**A complete, dependency-closed Lean proof of the square-root lower bound on operator entanglement for the finite rectangular core to which the paper's Lemma 4.1 reduces an integrable brickwork circuit.**

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

For the finite rectangular core `Xₜ = Wₜᴴ Sₜ Wₜ` with `t = n + 1`, over a finite field `F` of odd
characteristic and with a nontrivial additive character `ψ`, the von Neumann operator
entanglement of `Xₜ` across the cut between its two length-`t` packets satisfies

```text
log q · √((n + 1)/π) − (3/2) log q  ≤  S(n + 1),      q = |F|
```

(`SqrtOpEnt.standalone_rectangular_lower_sqrt_bound` in
[`RequestProject/Main.lean`](RequestProject/Main.lean)). The only hypotheses are `ψ ≠ 1` and odd
characteristic. Integrable circuits are generally expected to entangle operators at most
logarithmically; this is the proved lower half of the counterexample. The step from the brickwork
circuit to `Xₜ` is the paper's Lemma 4.1 and is not formalized: no brickwork circuit is defined in
Lean.

## Whose mathematics

The theorem is from Balázs Pozsgay and István Vona, *Square-root growth of operator entanglement
in an integrable brickwork circuit* (4 September 2026). This repository is Jeromie Beasley's
formalization of their lower bound: 30 files and 661 theorems, from the gate and the finite core up
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

The reduction from the brickwork circuit to the finite core (Lemma 4.1) is not formalized. The
matching upper bound and the `+ log t` correction appear only in conditional form: Theorem 7.1
and its concrete version take the entropy sandwich (Propositions 5.3 and 5.4) and the branch
identity of Theorem 6.5 as hypotheses. See [`LIMITATIONS.md`](LIMITATIONS.md).

## Licence, citation and AI use

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
