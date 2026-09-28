import RequestProject.FlatSpectrum
import RequestProject.QuantumEntropy

/-!
# Flat Fourier cores as genuine density matrices

`FlatSpectrum.lean` proves the character-orthogonality identity `Mᴴ M = q^n I`.
This file connects that identity to the concrete spectral definitions in
`QuantumEntropy.lean`: the Hilbert--Schmidt normalization is computed, the
normalized Gram matrix is maximally mixed, and its von Neumann entropy is
therefore exactly `log |S|`.
-/

namespace SqrtOpEnt

open Matrix
open scoped BigOperators ComplexOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Squared norm of the finite-field Fourier coefficient matrix. -/
theorem fourierCoeff_schmidtNormSq {nL nR : ℕ} {S : Type*}
    [Fintype S] [DecidableEq S]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F))
    (hinj : ∀ s s' : S, K.mulVec (y s) = K.mulVec (y s') → s = s') :
    schmidtNormSq (fourierCoeff ψ K y) =
      (Fintype.card S : ℝ) * (Fintype.card F : ℝ) ^ nL := by
  have hgram := fourierCoeff_conjTranspose_mul ψ hψ K y hinj
  have htrace := congrArg Matrix.trace hgram
  rw [← schmidtGram, trace_schmidtGram] at htrace
  simp only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at htrace
  have hr : schmidtNormSq (fourierCoeff ψ K y) =
      (Fintype.card F : ℝ) ^ nL * (Fintype.card S : ℝ) := by
    exact_mod_cast htrace
  simpa [mul_comm] using hr

/-- The actual normalized Gram matrix of a Fourier core is maximally mixed. -/
theorem fourierCoeff_normalizedSchmidtGram {nL nR : ℕ} {S : Type*}
    [Fintype S] [DecidableEq S] [Nonempty S]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F))
    (hinj : ∀ s s' : S, K.mulVec (y s) = K.mulVec (y s') → s = s') :
    normalizedSchmidtGram (fourierCoeff ψ K y) =
      ((Fintype.card S : ℝ)⁻¹) • (1 : Matrix S S ℂ) := by
  rw [normalizedSchmidtGram, fourierCoeff_schmidtNormSq ψ hψ K y hinj, schmidtGram,
    fourierCoeff_conjTranspose_mul ψ hψ K y hinj]
  have hF : (Fintype.card F : ℝ) ^ nL ≠ 0 := by positivity
  have hS : (Fintype.card S : ℝ) ≠ 0 := by positivity
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [Complex.real_smul]
    push_cast
    norm_cast
    field_simp
    norm_cast
    simp [mul_comm]
  · simp [hij]

/-- Character orthogonality now yields the literal von Neumann entropy of the
normalized Schmidt spectrum, with no abstract entropy hypothesis. -/
theorem fourierCoeff_vonNeumannEntropy {nL nR : ℕ} {S : Type*}
    [Fintype S] [DecidableEq S] [Nonempty S]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F))
    (hinj : ∀ s s' : S, K.mulVec (y s) = K.mulVec (y s') → s = s') :
    vonNeumannEntropy (fourierCoeff ψ K y) = Real.log (Fintype.card S) := by
  apply vonNeumannEntropy_of_normalizedGram_eq_uniform
  exact fourierCoeff_normalizedSchmidtGram ψ hψ K y hinj

/-- The same flatness calculation gives the literal Schmidt rank `|S|`. -/
theorem fourierCoeff_operatorSchmidtRank {nL nR : ℕ} {S : Type*}
    [Fintype S] [DecidableEq S]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F))
    (hinj : ∀ s s' : S, K.mulVec (y s) = K.mulVec (y s') → s = s') :
    operatorSchmidtRank (fourierCoeff ψ K y) = Fintype.card S := by
  unfold operatorSchmidtRank
  rw [← Matrix.rank_conjTranspose_mul_self,
    fourierCoeff_conjTranspose_mul ψ hψ K y hinj]
  have hc : ((Fintype.card F : ℂ) ^ nL) ≠ 0 := by positivity
  rw [show ((Fintype.card F : ℂ) ^ nL) • (1 : Matrix S S ℂ) =
      Matrix.diagonal (fun _ : S => (Fintype.card F : ℂ) ^ nL) by
        ext i j
        simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]]
  simp [Matrix.rank_diagonal, hc]

end SqrtOpEnt
