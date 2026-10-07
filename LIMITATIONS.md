# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* **No brickwork circuit is defined in Lean.** The formalization starts at the finite rectangular
  core `Xₜ = Wₜᴴ Sₜ Wₜ`. The paper's Lemma 4.1, which reduces the evolved operator `O_q(t)` of the
  integrable brickwork circuit to `Xₜ`, is the paper's and is not formalized.
* Only the **lower** square-root bound is proved unconditionally
  (`SqrtOpEnt.standalone_rectangular_lower_sqrt_bound`; hypotheses: `ψ ≠ 1`, odd characteristic).
  The matching upper bound, the saturation statement and the `+ log t` correction appear only as
  conditional theorems (`vonNeumann_sqrt_law`, `vonNeumann_sqrt_law_isBigO`,
  `rectangularVonNeumann_sqrt_law`, `rectangularVonNeumann_sqrt_law_of_pulledSource`): the
  entropy sandwich of Propositions 5.3 and 5.4 and the branch identity of Theorem 6.5 enter them
  as hypotheses, and the pinching upper bound and the branch identity are not proved here.
* The gate properties of Lemma 3.1 (unitary, Hermitian, involutive, braid relation: `gate_braid`)
  and Proposition 3.2 are proved in `Gate.lean`. Integrability of the circuit as a consequence of
  the braid relation is not formalized.
* The Rényi-entropy results (linear growth for `0 ≤ α < 1`, logarithmic for `α > 1`) are the
  paper's and are not formalized. `flat_renyi` is only the identity for a uniform spectrum; Rényi
  entropies of the blocks of `Xₜ` are not defined.
* Some module docstrings (`ConcreteEntropyAssembly`, `MixedHessian`, `ResidualEntropy`)
  record the order of development and speak of "pending" inputs or a "next
  bridge". Those inputs were later discharged in `FibreReduction` and `FibreEntropy`; the files
  are kept byte-identical to the checked source, so the wording is left as it was.
* No physical interpretation is formalized.

Formalization is evidence for the mathematics, not for the physical interpretation.
