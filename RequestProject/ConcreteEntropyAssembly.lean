import RequestProject.EntropyMeasurement

/-!
# Assembly specialized to the concrete rectangular core

This file replaces the abstract entropy function in `EntropyLaw.lean` by the
eigenvalue-defined von Neumann entropy of the literal object `X_t`.  The exact
sector-weight theorem already proved for `X_t` identifies its weighted average
of branch entropies with the manuscript's binomial expectation as soon as the
remaining fixed-branch spectral identity is supplied.

The final estimate below therefore exposes only two kinds of pending input:
the fixed-branch entropy formula (the local-isometry/phase bridge) and the
standard local-measurement/pinching entropy inequalities.
-/

namespace SqrtOpEnt

open Finset

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Weighted average of the actual normalized count-block entropies of
`X_(n+1)`. -/
noncomputable def rectangularAverageBranchEntropy
    (psi : AddChar F ℂ) (n : ℕ) : ℝ :=
  ∑ j ∈ range (n + 1), ∑ l ∈ range (n + 2),
    rectangularCountWeight F psi (succPNat n) (j + 1) l *
      vonNeumannEntropy
        (rectangularCountBlock F psi (succPNat n) (j + 1) l)

/-- The local folded count measurement proves the lower-bound entropy
interface for the literal rectangular core. -/
theorem rectangularAverageBranchEntropy_le
    (psi : AddChar F ℂ) (n : ℕ) :
    rectangularAverageBranchEntropy F psi n ≤
      rectangularVonNeumannEntropy F psi (succPNat n) := by
  let e (k l : ℕ) : ℝ :=
    rectangularCountWeight F psi (succPNat n) k l *
      vonNeumannEntropy
        (rectangularCountBlock F psi (succPNat n) k l)
  have he_nonneg (k l : ℕ) : 0 ≤ e k l := by
    exact mul_nonneg (rectangularCountWeight_nonneg F psi _ _ _)
      (vonNeumannEntropy_nonneg_all _)
  have hfull :
      ∑ k ∈ range (n + 2), ∑ l ∈ range (n + 2), e k l ≤
        rectangularVonNeumannEntropy F psi (succPNat n) := by
    simpa only [e, ← Fin.sum_univ_eq_sum_range] using
      allRectangularCountBranchesEntropy_le F psi n
  unfold rectangularAverageBranchEntropy
  change (∑ j ∈ range (n + 1), ∑ l ∈ range (n + 2), e (j + 1) l) ≤ _
  calc
    (∑ j ∈ range (n + 1), ∑ l ∈ range (n + 2), e (j + 1) l) ≤
        (∑ l ∈ range (n + 2), e 0 l) +
          ∑ j ∈ range (n + 1), ∑ l ∈ range (n + 2), e (j + 1) l :=
      le_add_of_nonneg_left
        (Finset.sum_nonneg fun l hl => he_nonneg 0 l)
    _ = ∑ k ∈ range (n + 2), ∑ l ∈ range (n + 2), e k l := by
      rw [add_comm]
      have hs := (Finset.sum_range_succ'
        (fun k => ∑ l ∈ range (n + 2), e k l) (n + 1)).symm
      convert hs using 1
    _ ≤ rectangularVonNeumannEntropy F psi (succPNat n) := hfull

/-- With the fixed-branch entropy formula, the average of the literal `X_t`
blocks is exactly the binomial expectation used in Section 7. -/
theorem rectangularAverageBranchEntropy_eq_expImbEntropy
    (psi : AddChar F ℂ) (n : ℕ)
    (hbranch : ∀ j l : ℕ,
      j < n + 1 → l < n + 2 →
      vonNeumannEntropy
          (rectangularCountBlock F psi (succPNat n) (j + 1) l) =
        imbEntropy (Fintype.card F)
          ((j : ℤ) + l + 1 - (n + 1))) :
    rectangularAverageBranchEntropy F psi n =
      expImbEntropy (Fintype.card F) (n + 1) := by
  unfold rectangularAverageBranchEntropy expImbEntropy
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rw [rectangularCountWeight_eq_sectorWeight,
    hbranch j l (Finset.mem_range.mp hj) (by simpa using Finset.mem_range.mp hl)]
  norm_num

/-- Source-coordinate version of the branch assembly.  The folding map is
now discharged internally, so the remaining spectral hypothesis may be
proved directly from the pulled-back phase formula in `CircuitPhase.lean`. -/
theorem rectangularAverageBranchEntropy_eq_expImbEntropy_of_pulledSource
    (psi : AddChar F ℂ) (n : ℕ)
    (hbranch : ∀ j l : ℕ,
      j < n + 1 → l < n + 2 →
      vonNeumannEntropy (pulledSourceSectorBlock F psi n j l) =
        imbEntropy (Fintype.card F)
          ((j : ℤ) + l + 1 - (n + 1))) :
    rectangularAverageBranchEntropy F psi n =
      expImbEntropy (Fintype.card F) (n + 1) := by
  apply rectangularAverageBranchEntropy_eq_expImbEntropy F psi n
  intro j l hj hl
  rw [← vonNeumannEntropy_pulledSourceSectorBlock_eq_countBlock]
  exact hbranch j l hj hl

/-- A lower bound on every fixed count branch is enough for the averaged
lower bound.  This weaker interface is useful because one may further
measure the visible colour word inside a count branch; no coherent orbit
isometry is then needed. -/
theorem expImbEntropy_le_rectangularAverageBranchEntropy
    (psi : AddChar F ℂ) (n : ℕ)
    (hbranch : ∀ j l : ℕ,
      j < n + 1 → l < n + 2 →
      imbEntropy (Fintype.card F)
          ((j : ℤ) + l + 1 - (n + 1)) ≤
        vonNeumannEntropy
          (rectangularCountBlock F psi (succPNat n) (j + 1) l)) :
    expImbEntropy (Fintype.card F) (n + 1) ≤
      rectangularAverageBranchEntropy F psi n := by
  unfold rectangularAverageBranchEntropy expImbEntropy
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro l hl
  rw [rectangularCountWeight_eq_sectorWeight]
  have hb := hbranch j l (Finset.mem_range.mp hj) (Finset.mem_range.mp hl)
  norm_num at hb ⊢
  exact mul_le_mul_of_nonneg_left hb (by
    unfold sectorWeight
    positivity)

/-- Pulled-source version of the branchwise lower-bound interface. -/
theorem expImbEntropy_le_rectangularAverageBranchEntropy_of_pulledSource
    (psi : AddChar F ℂ) (n : ℕ)
    (hbranch : ∀ j l : ℕ,
      j < n + 1 → l < n + 2 →
      imbEntropy (Fintype.card F)
          ((j : ℤ) + l + 1 - (n + 1)) ≤
        vonNeumannEntropy (pulledSourceSectorBlock F psi n j l)) :
    expImbEntropy (Fintype.card F) (n + 1) ≤
      rectangularAverageBranchEntropy F psi n := by
  apply expImbEntropy_le_rectangularAverageBranchEntropy F psi n
  intro j l hj hl
  rw [← vonNeumannEntropy_pulledSourceSectorBlock_eq_countBlock]
  exact hbranch j l hj hl

/-- Extend the concrete positive-time entropy to natural time by assigning
zero at `t=0`; this is only an adapter for the existing asymptotic theorem. -/
noncomputable def rectangularEntropyNat (psi : AddChar F ℂ) (t : ℕ) : ℝ :=
  if ht : 0 < t then rectangularVonNeumannEntropy F psi ⟨t, ht⟩ else 0

@[simp]
theorem rectangularEntropyNat_succ (psi : AddChar F ℂ) (n : ℕ) :
    rectangularEntropyNat F psi (n + 1) =
      rectangularVonNeumannEntropy F psi (succPNat n) := by
  simp [rectangularEntropyNat, succPNat]

/-- Concrete `X_t` form of the finite square-root estimate.  Once the three
displayed manuscript interfaces are established for the literal blocks, the
conclusion is no longer about an arbitrary entropy function: it is exactly
the eigenvalue-defined operator entropy of `rectangularCore`.

`hbranch` is the signed-imbalance spectral reduction plus the residual flat
spectrum. `hmeasure` and `hpinch` are the standard entropy inequalities of
Propositions 5.3 and 5.4. -/
theorem rectangularVonNeumann_sqrt_law
    (psi : AddChar F ℂ)
    (hbranch : ∀ n j l : ℕ,
      j < n + 1 → l < n + 2 →
      vonNeumannEntropy
          (rectangularCountBlock F psi (succPNat n) (j + 1) l) =
        imbEntropy (Fintype.card F)
          ((j : ℤ) + l + 1 - (n + 1)))
    (hmeasure : ∀ n : ℕ,
      rectangularAverageBranchEntropy F psi n ≤
        rectangularVonNeumannEntropy F psi (succPNat n))
    (hpinch : ∀ n : ℕ,
      rectangularVonNeumannEntropy F psi (succPNat n) ≤
        binEntropy n + binEntropy (n + 1) +
          rectangularAverageBranchEntropy F psi n)
    (n : ℕ) :
    |rectangularVonNeumannEntropy F psi (succPNat n) -
        Real.log (Fintype.card F) *
          Real.sqrt (((n + 1 : ℕ) : ℝ) / Real.pi)| ≤
      2 * Real.log (Fintype.card F) +
        2 * Real.log ((n + 1 : ℕ) + 1) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hlow : ∀ t : ℕ, 1 ≤ t →
      expImbEntropy (Fintype.card F) t ≤ rectangularEntropyNat F psi t := by
    intro t ht
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    rw [← rectangularAverageBranchEntropy_eq_expImbEntropy F psi m
      (hbranch m)]
    simpa using hmeasure m
  have hupp : ∀ t : ℕ, 1 ≤ t →
      rectangularEntropyNat F psi t ≤
        binEntropy (t - 1) + binEntropy t +
          expImbEntropy (Fintype.card F) t := by
    intro t ht
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    rw [← rectangularAverageBranchEntropy_eq_expImbEntropy F psi m
      (hbranch m)]
    simpa using hpinch m
  simpa using vonNeumann_sqrt_law (Fintype.card F) hq
    (rectangularEntropyNat F psi) hlow hupp (n + 1) (by omega)

/-- Concrete square-root law with its remaining branch input stated in the
pulled source coordinates where the exact finite-field phase is available.
All folding and local basis reindexing is handled by
`vonNeumannEntropy_pulledSourceSectorBlock_eq_countBlock`. -/
theorem rectangularVonNeumann_sqrt_law_of_pulledSource
    (psi : AddChar F ℂ)
    (hbranch : ∀ n j l : ℕ,
      j < n + 1 → l < n + 2 →
      vonNeumannEntropy (pulledSourceSectorBlock F psi n j l) =
        imbEntropy (Fintype.card F)
          ((j : ℤ) + l + 1 - (n + 1)))
    (hmeasure : ∀ n : ℕ,
      rectangularAverageBranchEntropy F psi n ≤
        rectangularVonNeumannEntropy F psi (succPNat n))
    (hpinch : ∀ n : ℕ,
      rectangularVonNeumannEntropy F psi (succPNat n) ≤
        binEntropy n + binEntropy (n + 1) +
          rectangularAverageBranchEntropy F psi n)
    (n : ℕ) :
    |rectangularVonNeumannEntropy F psi (succPNat n) -
        Real.log (Fintype.card F) *
          Real.sqrt (((n + 1 : ℕ) : ℝ) / Real.pi)| ≤
      2 * Real.log (Fintype.card F) +
        2 * Real.log ((n + 1 : ℕ) + 1) := by
  apply rectangularVonNeumann_sqrt_law F psi _ hmeasure hpinch n
  intro m j l hj hl
  rw [← vonNeumannEntropy_pulledSourceSectorBlock_eq_countBlock]
  exact hbranch m j l hj hl

/-- **Concrete lower half of Theorem 7.1.**  Only fixed-sector flatness and
the local count-measurement inequality are needed; the pinching upper bound
plays no role. -/
theorem rectangularVonNeumann_sqrt_lower_bound
    (psi : AddChar F ℂ)
    (hbranch : ∀ n j l : ℕ,
      j < n + 1 → l < n + 2 →
      imbEntropy (Fintype.card F)
          ((j : ℤ) + l + 1 - (n + 1)) ≤
        vonNeumannEntropy
          (rectangularCountBlock F psi (succPNat n) (j + 1) l))
    (n : ℕ) :
    Real.log (Fintype.card F) *
          Real.sqrt (((n + 1 : ℕ) : ℝ) / Real.pi) -
        (3 / 2) * Real.log (Fintype.card F) ≤
      rectangularVonNeumannEntropy F psi (succPNat n) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hlow : ∀ t : ℕ, 1 ≤ t →
      expImbEntropy (Fintype.card F) t ≤ rectangularEntropyNat F psi t := by
    intro t ht
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    exact (expImbEntropy_le_rectangularAverageBranchEntropy F psi m
      (hbranch m)).trans (rectangularAverageBranchEntropy_le F psi m)
  simpa using vonNeumann_sqrt_lower_bound (Fintype.card F) hq
    (rectangularEntropyNat F psi) hlow (n + 1) (by omega)

/-- Source-coordinate form of the concrete lower bound.  This is the final
assembly target for the phase/support reduction of each pulled sector. -/
theorem rectangularVonNeumann_sqrt_lower_bound_of_pulledSource
    (psi : AddChar F ℂ)
    (hbranch : ∀ n j l : ℕ,
      j < n + 1 → l < n + 2 →
      imbEntropy (Fintype.card F)
          ((j : ℤ) + l + 1 - (n + 1)) ≤
        vonNeumannEntropy (pulledSourceSectorBlock F psi n j l))
    (n : ℕ) :
    Real.log (Fintype.card F) *
          Real.sqrt (((n + 1 : ℕ) : ℝ) / Real.pi) -
        (3 / 2) * Real.log (Fintype.card F) ≤
      rectangularVonNeumannEntropy F psi (succPNat n) := by
  apply rectangularVonNeumann_sqrt_lower_bound F psi _ n
  intro m j l hj hl
  rw [← vonNeumannEntropy_pulledSourceSectorBlock_eq_countBlock]
  exact hbranch m j l hj hl

end SqrtOpEnt
