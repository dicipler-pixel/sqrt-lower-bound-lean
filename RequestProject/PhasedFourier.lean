import RequestProject.LocalEquivalence
import RequestProject.ResidualEntropy

/-!
# Removing one-sided phases from finite-field Fourier matrices

The mixed-Hessian calculation determines only the left--right part of the
quadratic phase.  This file proves the exact spectral statement that makes
that sufficient: arbitrary left-only and right-only character phases are
diagonal local unitaries and therefore do not affect operator entanglement.
-/

namespace SqrtOpEnt

open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Diagonal matrix of additive-character phases. -/
noncomputable def characterDiagonal {X : Type*} [Fintype X] [DecidableEq X]
    (psi : AddChar F ℂ) (a : X → F) : Matrix X X ℂ :=
  Matrix.diagonal fun x => psi (a x)

/-- Additive-character phases have unit modulus, so their diagonal matrix is
unitary. -/
theorem characterDiagonal_mem_unitary
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : AddChar F ℂ) (a : X → F) :
    characterDiagonal psi a ∈ unitary (Matrix X X ℂ) := by
  have hphase (x : X) : star (psi (a x)) * psi (a x) = 1 := by
    rw [← starRingEnd_apply, ← AddChar.inv_apply_eq_conj]
    exact inv_mul_cancel₀ (AddChar.val_isUnit psi (a x)).ne_zero
  constructor <;> ext i j
  · by_cases hij : i = j
    · subst j
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · simpa [characterDiagonal] using hphase i
      · intro x hx hxi
        simp [characterDiagonal, hxi, Ne.symm hxi]
      · simp
    · rw [Matrix.mul_apply]
      rw [Matrix.one_apply, if_neg hij]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hxi : x = i
      · subst x
        simp [characterDiagonal, hij]
      · simp [characterDiagonal, hxi, Ne.symm hxi]
  · by_cases hij : i = j
    · subst j
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · simpa [characterDiagonal, mul_comm] using hphase i
      · intro x hx hxi
        simp [characterDiagonal, hxi, Ne.symm hxi]
      · simp
    · rw [Matrix.mul_apply]
      rw [Matrix.one_apply, if_neg hij]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hix : i = x
      · subst x
        simp [characterDiagonal, Ne.symm hij]
      · simp [characterDiagonal, hix, Ne.symm hix]

/-- A coefficient matrix obtained by applying the character to an arbitrary
finite-field phase. -/
noncomputable def phaseCoeff {X Y : Type*}
    (psi : AddChar F ℂ) (Q : X → Y → F) : Matrix X Y ℂ :=
  fun x y => psi (Q x y)

/-- If a phase is a bilinear Fourier phase plus one-sided terms, its
coefficient matrix is obtained from the Fourier core by diagonal unitaries. -/
theorem phaseCoeff_eq_characterDiagonal_mul_fourierCoeff_mul
    {nL nR : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (psi : AddChar F ℂ)
    (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F))
    (leftPhase : (Fin nL → F) → F) (rightPhase : S → F)
    (Q : (Fin nL → F) → S → F)
    (hQ : ∀ x s, Q x s =
      leftPhase x + x ⬝ᵥ K.mulVec (y s) + rightPhase s) :
    phaseCoeff psi Q =
      characterDiagonal psi leftPhase * fourierCoeff psi K y *
        characterDiagonal psi rightPhase := by
  classical
  ext x s
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · simp [phaseCoeff, characterDiagonal, fourierCoeff, hQ,
        psi.map_add_eq_mul, mul_assoc]
    · intro z hz hzx
      simp [characterDiagonal, hzx, Ne.symm hzx]
    · simp
  · intro z hz hzs
    simp [characterDiagonal, hzs]
  · simp

/-- One-sided phase terms do not change the entropy of a finite-field
Fourier coefficient matrix. -/
theorem phaseCoeff_vonNeumannEntropy_eq_fourierCoeff
    {nL nR : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (psi : AddChar F ℂ)
    (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F))
    (leftPhase : (Fin nL → F) → F) (rightPhase : S → F)
    (Q : (Fin nL → F) → S → F)
    (hQ : ∀ x s, Q x s =
      leftPhase x + x ⬝ᵥ K.mulVec (y s) + rightPhase s) :
    vonNeumannEntropy (phaseCoeff psi Q) =
      vonNeumannEntropy (fourierCoeff psi K y) := by
  rw [phaseCoeff_eq_characterDiagonal_mul_fourierCoeff_mul
    psi K y leftPhase rightPhase Q hQ]
  rw [vonNeumannEntropy_mul_unitary _ _
      (characterDiagonal_mem_unitary psi rightPhase),
    vonNeumannEntropy_unitary_mul _ _
      (characterDiagonal_mem_unitary psi leftPhase)]

end SqrtOpEnt
