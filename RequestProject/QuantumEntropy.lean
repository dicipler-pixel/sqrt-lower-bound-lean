import RequestProject.RectangularCore
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Finite-dimensional operator entanglement

This file defines the density matrix and von Neumann entropy attached to a
finite coefficient matrix.  Applied to `rectCoeff Xₜ`, these are the literal
normalized operator-Schmidt probabilities of the rectangular core.

The definitions use eigenvalues of `Mᴴ M`; no choice of singular vectors is
needed.  The basic certification proved here is that a nonzero coefficient
matrix produces a positive-semidefinite density matrix of trace one.
-/

namespace SqrtOpEnt

open Matrix
open scoped BigOperators
open scoped ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Regrouping the four operator indices preserves the Hilbert--Schmidt norm. -/
theorem schmidtNormSq_rectCoeff
    {F : Type*} [Fintype F] {t : ℕ}
    (X : Matrix (RectBasis F t) (RectBasis F t) ℂ) :
    schmidtNormSq (rectCoeff F X) = schmidtNormSq X := by
  classical
  simp only [schmidtNormSq, rectCoeff]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro leftOut hleftOut
  rw [Finset.sum_comm]

/-- Unitary monomial conjugation by the rectangle preserves the squared
Hilbert--Schmidt norm of the source. -/
theorem schmidtNormSq_rectangularCore
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (t : ℕ+) :
    schmidtNormSq (rectangularCore F ψ t) = schmidtNormSq (rectangularSource F t) := by
  classical
  let σ := rectangularCircuitPerm F (t : ℕ)
  simp only [schmidtNormSq, norm_rectangularCore_apply]
  calc
    (∑ u, ∑ v,
        ‖rectangularSource F t (σ u) (σ v)‖ ^ 2) =
      ∑ u, ∑ v, ‖rectangularSource F t (σ u) v‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact Equiv.sum_comp σ (fun v => ‖rectangularSource F t (σ u) v‖ ^ 2)
    _ = ∑ u, ∑ v, ‖rectangularSource F t u v‖ ^ 2 :=
      Equiv.sum_comp σ (fun u => ∑ v, ‖rectangularSource F t u v‖ ^ 2)

/-- The operator-Schmidt reshaping of `Xₜ` has the same squared norm as `Sₜ`. -/
theorem schmidtNormSq_rectCoeff_rectangularCore
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (t : ℕ+) :
    schmidtNormSq (rectCoeff F (rectangularCore F ψ t)) =
      schmidtNormSq (rectangularSource F t) := by
  rw [schmidtNormSq_rectCoeff, schmidtNormSq_rectangularCore]

/-- The trace of the Gram matrix is the squared Hilbert--Schmidt norm. -/
theorem trace_schmidtGram (M : Matrix m n ℂ) :
    (schmidtGram M).trace = (schmidtNormSq M : ℂ) := by
  classical
  simp only [schmidtGram, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, schmidtNormSq, Complex.sq_norm]
  rw [Finset.sum_comm]
  have hterm (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
    simpa only [starRingEnd_apply] using Complex.normSq_eq_conj_mul_self.symm
  simp_rw [hterm]
  push_cast
  rfl

/-- The squared Hilbert--Schmidt norm is positive exactly when the matrix is nonzero. -/
theorem schmidtNormSq_pos (M : Matrix m n ℂ) (hM : M ≠ 0) :
    0 < schmidtNormSq M := by
  apply (schmidtNormSq_nonneg M).lt_of_ne
  intro hzero
  have htrace : (schmidtGram M).trace = 0 := by
    rw [trace_schmidtGram, ← hzero]
    simp
  exact hM ((Matrix.trace_conjTranspose_mul_self_eq_zero_iff).mp htrace)

/-- The normalized Schmidt Gram matrix is positive semidefinite. -/
theorem normalizedSchmidtGram_posSemidef (M : Matrix m n ℂ) :
    (normalizedSchmidtGram M).PosSemidef := by
  unfold normalizedSchmidtGram schmidtGram
  exact (Matrix.posSemidef_conjTranspose_mul_self M).smul
    (inv_nonneg.mpr (schmidtNormSq_nonneg M))

/-- In particular, the normalized Schmidt Gram matrix is Hermitian. -/
theorem normalizedSchmidtGram_isHermitian (M : Matrix m n ℂ) :
    (normalizedSchmidtGram M).IsHermitian :=
  (normalizedSchmidtGram_posSemidef M).1

/-- A nonzero coefficient matrix gives a normalized density matrix. -/
theorem trace_normalizedSchmidtGram (M : Matrix m n ℂ) (hM : M ≠ 0) :
    (normalizedSchmidtGram M).trace = 1 := by
  rw [normalizedSchmidtGram, Matrix.trace_smul, trace_schmidtGram]
  have hnorm := (schmidtNormSq_pos M hM).ne'
  simp [hnorm]

/-- The normalized operator-Schmidt probabilities, indexed with multiplicity. -/
noncomputable def schmidtProbabilities (M : Matrix m n ℂ) : n → ℝ :=
  by
    classical
    exact (normalizedSchmidtGram_isHermitian M).eigenvalues

/-- Every normalized operator-Schmidt probability is nonnegative. -/
theorem schmidtProbabilities_nonneg (M : Matrix m n ℂ) (i : n) :
    0 ≤ schmidtProbabilities M i := by
  classical
  exact (normalizedSchmidtGram_posSemidef M).eigenvalues_nonneg i

/-- For a nonzero coefficient matrix, its Schmidt probabilities sum to one. -/
theorem sum_schmidtProbabilities (M : Matrix m n ℂ) (hM : M ≠ 0) :
    ∑ i, schmidtProbabilities M i = 1 := by
  classical
  have htrace :=
    (normalizedSchmidtGram_isHermitian M).trace_eq_sum_eigenvalues
  rw [trace_normalizedSchmidtGram M hM] at htrace
  have hre := congrArg Complex.re htrace
  simpa [schmidtProbabilities] using hre.symm

/-- Every Schmidt probability of a nonzero coefficient matrix is at most one. -/
theorem schmidtProbabilities_le_one (M : Matrix m n ℂ) (hM : M ≠ 0) (i : n) :
    schmidtProbabilities M i ≤ 1 := by
  classical
  rw [← sum_schmidtProbabilities M hM]
  exact Finset.single_le_sum (fun j _ => schmidtProbabilities_nonneg M j)
    (Finset.mem_univ i)

/-- Von Neumann entropy of the normalized Schmidt spectrum of `M`. -/
noncomputable def vonNeumannEntropy (M : Matrix m n ℂ) : ℝ :=
  ∑ i, Real.negMulLog (schmidtProbabilities M i)

/-- Exact Schmidt rank of a coefficient matrix. -/
noncomputable def operatorSchmidtRank (M : Matrix m n ℂ) : ℕ := M.rank

/-- Von Neumann entropy of a nonzero coefficient matrix is nonnegative. -/
theorem vonNeumannEntropy_nonneg (M : Matrix m n ℂ) (hM : M ≠ 0) :
    0 ≤ vonNeumannEntropy M := by
  classical
  exact Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (schmidtProbabilities_nonneg M i)
      (schmidtProbabilities_le_one M hM i)

/-- If the normalized Gram matrix is scalar, every Schmidt probability is that scalar. -/
theorem schmidtProbabilities_eq_of_normalizedGram_eq_smul_one
    [DecidableEq n] (M : Matrix m n ℂ) (c : ℝ)
    (hflat : normalizedSchmidtGram M = c • (1 : Matrix n n ℂ)) (i : n) :
    schmidtProbabilities M i = c := by
  classical
  let hA := normalizedSchmidtGram_isHermitian M
  let hscalar : (c • (1 : Matrix n n ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian]
    simp
  have heig : hA.eigenvalues = hscalar.eigenvalues :=
    (hA.eigenvalues_eq_eigenvalues_iff hscalar).2 (congrArg Matrix.charpoly hflat)
  change hA.eigenvalues i = c
  rw [heig, hscalar.eigenvalues_eq]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct_comm,
    ← EuclideanSpace.inner_eq_star_dotProduct]
  simp [hscalar.eigenvectorBasis.orthonormal.1 i]

/-- A maximally mixed normalized Gram matrix has entropy `log` of its dimension. -/
theorem vonNeumannEntropy_of_normalizedGram_eq_uniform [Nonempty n] [DecidableEq n]
    (M : Matrix m n ℂ)
    (hflat : normalizedSchmidtGram M =
      ((Fintype.card n : ℝ)⁻¹) • (1 : Matrix n n ℂ)) :
    vonNeumannEntropy M = Real.log (Fintype.card n) := by
  classical
  have hcard : 0 < Fintype.card n := Fintype.card_pos
  have hprob : ∀ i, schmidtProbabilities M i = (Fintype.card n : ℝ)⁻¹ :=
    schmidtProbabilities_eq_of_normalizedGram_eq_smul_one M _ hflat
  simp only [vonNeumannEntropy, hprob, Real.negMulLog]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_inv]
  have hcardR : (Fintype.card n : ℝ) ≠ 0 := by positivity
  field_simp

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Von Neumann operator entanglement of the concrete rectangular core `Xₜ`. -/
noncomputable def rectangularVonNeumannEntropy (ψ : AddChar F ℂ) (t : ℕ+) : ℝ :=
  vonNeumannEntropy (rectCoeff F (rectangularCore F ψ t))

/-- Exact operator-Schmidt rank of the object `Xₜ` in Eq. (4.1). -/
noncomputable def rectangularOperatorSchmidtRank (ψ : AddChar F ℂ) (t : ℕ+) : ℕ :=
  operatorSchmidtRank (rectCoeff F (rectangularCore F ψ t))

/-- The concrete density matrix of the rectangular core has trace one. -/
theorem trace_rectangularDensity (ψ : AddChar F ℂ) (t : ℕ+) :
    (rectangularDensity F ψ t).trace = 1 :=
  trace_normalizedSchmidtGram _ (rectCoeff_rectangularCore_ne_zero F ψ t)

/-- The concrete operator-Schmidt probabilities of `Xₜ` form a probability distribution. -/
theorem sum_rectangularSchmidtProbabilities (ψ : AddChar F ℂ) (t : ℕ+) :
    ∑ i, schmidtProbabilities (rectCoeff F (rectangularCore F ψ t)) i = 1 :=
  sum_schmidtProbabilities _ (rectCoeff_rectangularCore_ne_zero F ψ t)

/-- The concrete rectangular-core von Neumann entropy is nonnegative. -/
theorem rectangularVonNeumannEntropy_nonneg (ψ : AddChar F ℂ) (t : ℕ+) :
    0 ≤ rectangularVonNeumannEntropy F ψ t :=
  vonNeumannEntropy_nonneg _ (rectCoeff_rectangularCore_ne_zero F ψ t)

end SqrtOpEnt
