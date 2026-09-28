import RequestProject.LocalEquivalence
import Mathlib.Analysis.Convex.Jensen

/-!
# Entropy under finite local measurements

This file develops the finite-dimensional entropy inequality needed for the
lower bound.  The route is elementary: squared entry norms of a unitary form
a doubly stochastic matrix, and scalar concavity of `-x log x` shows that
unitary mixing can only increase the entropy of a diagonal probability
vector.  This is then lifted to positive semidefinite matrices and to local
projective measurements of a bipartite coefficient matrix.
-/

namespace SqrtOpEnt

open Matrix Finset
open scoped BigOperators ComplexOrder ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise squared norms of a complex matrix. -/
noncomputable def entryNormSq (U : Matrix n n ℂ) : Matrix n n ℝ :=
  fun i j => Complex.normSq (U i j)

/-- Squared entry norms of a unitary matrix form a doubly stochastic matrix. -/
theorem entryNormSq_mem_doublyStochastic (U : Matrix n n ℂ)
    (hU : U ∈ unitary (Matrix n n ℂ)) :
    entryNormSq U ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, ?_, ?_⟩
  · intro i
    have hUright : U * Uᴴ = 1 := by simpa using hU.2
    have hrow := congrArg (fun A : Matrix n n ℂ => A i i) hUright
    have hcast : ((∑ j, Complex.normSq (U i j) : ℝ) : ℂ) = 1 := by
      push_cast
      simpa [Matrix.mul_apply, Complex.normSq_eq_conj_mul_self,
        mul_comm] using hrow
    exact_mod_cast hcast
  · intro j
    have hUleft : Uᴴ * U = 1 := by simpa using hU.1
    have hcol := congrArg (fun A : Matrix n n ℂ => A j j) hUleft
    have hcast : ((∑ i, Complex.normSq (U i j) : ℝ) : ℂ) = 1 := by
      push_cast
      simpa [Matrix.mul_apply, Complex.normSq_eq_conj_mul_self] using hcol
    exact_mod_cast hcast

/-- A doubly stochastic mixing of a nonnegative vector cannot decrease its
`-x log x` entropy. -/
theorem sum_negMulLog_le_sum_negMulLog_mulVec
    (W : Matrix n n ℝ) (hW : W ∈ doublyStochastic ℝ n)
    (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ j, Real.negMulLog (x j) ≤
      ∑ i, Real.negMulLog ((W *ᵥ x) i) := by
  have hrow (i : n) :
      ∑ j, W i j * Real.negMulLog (x j) ≤
        Real.negMulLog ((W *ᵥ x) i) := by
    have h := Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset n))
      (w := fun j => W i j) (p := x)
      (fun j _ => nonneg_of_mem_doublyStochastic hW)
      (sum_row_of_mem_doublyStochastic hW i)
      (fun j _ => hx j)
    simpa [Matrix.mulVec, dotProduct, smul_eq_mul] using h
  calc
    (∑ j, Real.negMulLog (x j)) =
        ∑ i, ∑ j, W i j * Real.negMulLog (x j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hW]
      simp
    _ ≤ ∑ i, Real.negMulLog ((W *ᵥ x) i) :=
      Finset.sum_le_sum fun i _ => hrow i

/-- The diagonal of `U diag(x) Uᴴ`, after taking real parts, is the
doubly-stochastic mixing of `x` by the squared entry norms of `U`. -/
theorem re_diag_unitary_diagonal_conj
    (U : Matrix n n ℂ) (x : n → ℝ) (i : n) :
    Complex.re
        ((U * Matrix.diagonal (fun j => (x j : ℂ)) * Uᴴ) i i) =
      (entryNormSq U *ᵥ x) i := by
  have hterm (j : n) :
      Complex.re (U i j * (x j : ℂ) * star (U i j)) =
        Complex.normSq (U i j) * x j := by
    calc
      Complex.re (U i j * (x j : ℂ) * star (U i j)) =
          Complex.re ((x j : ℂ) * (star (U i j) * U i j)) := by
        congr 1
        ring
      _ = Complex.normSq (U i j) * x j := by
        change Complex.re
          ((x j : ℂ) * (conj (U i j) * U i j)) = _
        rw [← Complex.normSq_eq_conj_mul_self]
        simp [mul_comm]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  simp_rw [hterm]
  rfl

/-- Peierls' entropy inequality: the entropy of the diagonal of a positive
semidefinite matrix is at least the entropy of its eigenvalue vector. -/
theorem sum_negMulLog_eigenvalues_le_diagonal
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    ∑ j, Real.negMulLog (hA.1.eigenvalues j) ≤
      ∑ i, Real.negMulLog (Complex.re (A i i)) := by
  let U : Matrix n n ℂ := hA.1.eigenvectorUnitary
  have hU : U ∈ unitary (Matrix n n ℂ) := hA.1.eigenvectorUnitary.property
  have hdiag (i : n) :
      Complex.re (A i i) =
        (entryNormSq U *ᵥ hA.1.eigenvalues) i := by
    calc
      Complex.re (A i i) = Complex.re
          ((U * Matrix.diagonal (fun j => (hA.1.eigenvalues j : ℂ)) * Uᴴ) i i) := by
        have hs := congrArg (fun B : Matrix n n ℂ => Complex.re (B i i))
          hA.1.spectral_theorem
        simpa [Unitary.conjStarAlgAut_apply, U] using hs
      _ = (entryNormSq U *ᵥ hA.1.eigenvalues) i :=
        re_diag_unitary_diagonal_conj U hA.1.eigenvalues i
  simp_rw [hdiag]
  exact sum_negMulLog_le_sum_negMulLog_mulVec
    (entryNormSq U) (entryNormSq_mem_doublyStochastic U hU)
    hA.1.eigenvalues hA.eigenvalues_nonneg

/-- Peierls' inequality in an arbitrary orthonormal basis. -/
theorem sum_negMulLog_eigenvalues_le_unitary_diagonal
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (V : Matrix n n ℂ) (hV : V ∈ unitary (Matrix n n ℂ)) :
    ∑ j, Real.negMulLog (hA.1.eigenvalues j) ≤
      ∑ i, Real.negMulLog (Complex.re ((Vᴴ * A * V) i i)) := by
  let B : Matrix n n ℂ := Vᴴ * A * V
  have hB : B.PosSemidef := hA.conjTranspose_mul_mul_same V
  have hVright : V * Vᴴ = 1 := by simpa using hV.2
  have hchar : B.charpoly = A.charpoly := by
    calc
      B.charpoly = (Vᴴ * (A * V)).charpoly := by
        simp only [B, Matrix.mul_assoc]
      _ = ((A * V) * Vᴴ).charpoly := Matrix.charpoly_mul_comm _ _
      _ = A.charpoly := by rw [Matrix.mul_assoc, hVright, Matrix.mul_one]
  have heig : hB.1.eigenvalues = hA.1.eigenvalues :=
    (hB.1.eigenvalues_eq_eigenvalues_iff hA.1).2 hchar
  have h := sum_negMulLog_eigenvalues_le_diagonal B hB
  simpa only [B, heig] using h

/-- Spectral entropy of a positive semidefinite finite matrix. -/
noncomputable def posSemidefEntropy (A : Matrix n n ℂ)
    (hA : A.PosSemidef) : ℝ :=
  ∑ i, Real.negMulLog (hA.1.eigenvalues i)

/-- A nonnegative finite linear combination of positive semidefinite matrices
is positive semidefinite. -/
theorem posSemidef_sum_smul
    {I : Type*} [Fintype I]
    (p : I → ℝ) (hp : ∀ s, 0 ≤ p s)
    (rho : I → Matrix n n ℂ) (hrho : ∀ s, (rho s).PosSemidef) :
    (∑ s, p s • rho s).PosSemidef := by
  classical
  simpa using Matrix.posSemidef_sum (n := n) (R := ℂ)
    (Finset.univ : Finset I)
    (fun s _ => (hrho s).smul (hp s))

/-- Finite-dimensional concavity of spectral entropy on positive
semidefinite matrices. -/
theorem posSemidefEntropy_sum_smul_ge
    {I : Type*} [Fintype I]
    (p : I → ℝ) (hp : ∀ s, 0 ≤ p s) (hp_sum : ∑ s, p s = 1)
    (rho : I → Matrix n n ℂ) (hrho : ∀ s, (rho s).PosSemidef) :
    let R := ∑ s, p s • rho s
    let hR : R.PosSemidef := posSemidef_sum_smul p hp rho hrho
    ∑ s, p s * posSemidefEntropy (rho s) (hrho s) ≤
      posSemidefEntropy R hR := by
  classical
  dsimp only
  let R : Matrix n n ℂ := ∑ s, p s • rho s
  have hR : R.PosSemidef := posSemidef_sum_smul p hp rho hrho
  let V : Matrix n n ℂ := hR.1.eigenvectorUnitary
  have hV : V ∈ unitary (Matrix n n ℂ) := hR.1.eigenvectorUnitary.property
  let d (s : I) (i : n) : ℝ := Complex.re ((Vᴴ * rho s * V) i i)
  have hd_nonneg (s : I) (i : n) : 0 ≤ d s i := by
    have hB := (hrho s).conjTranspose_mul_mul_same V
    exact (Complex.nonneg_iff.mp hB.diag_nonneg).1
  have hdiag_matrix :
      ∑ s, p s • (Vᴴ * rho s * V) =
        Matrix.diagonal (fun i => (hR.1.eigenvalues i : ℂ)) := by
    calc
      (∑ s, p s • (Vᴴ * rho s * V)) = Vᴴ * R * V := by
        simp [R, Matrix.mul_sum, Matrix.sum_mul]
      _ = Matrix.diagonal (fun i => (hR.1.eigenvalues i : ℂ)) := by
        simpa [V, Unitary.conjStarAlgAut_apply] using
          hR.1.conjStarAlgAut_star_eigenvectorUnitary
  have heig (i : n) :
      ∑ s, p s * d s i = hR.1.eigenvalues i := by
    have hentry := congrArg
      (fun A : Matrix n n ℂ => Complex.re (A i i)) hdiag_matrix
    dsimp only at hentry
    rw [Matrix.sum_apply, Complex.re_sum] at hentry
    simpa [d] using hentry
  have hjensen (i : n) :
      ∑ s, p s * Real.negMulLog (d s i) ≤
        Real.negMulLog (hR.1.eigenvalues i) := by
    have h := Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset I))
      (w := p) (p := fun s => d s i)
      (fun s _ => hp s) hp_sum (fun s _ => hd_nonneg s i)
    simpa [smul_eq_mul, heig i] using h
  calc
    (∑ s, p s * posSemidefEntropy (rho s) (hrho s)) ≤
        ∑ s, p s * ∑ i, Real.negMulLog (d s i) := by
      apply Finset.sum_le_sum
      intro s hs
      have hspectral :
          posSemidefEntropy (rho s) (hrho s) ≤
            ∑ i, Real.negMulLog (d s i) := by
        simpa [posSemidefEntropy, d] using
          (sum_negMulLog_eigenvalues_le_unitary_diagonal
            (n := n) (rho s) (hrho s) V hV)
      exact mul_le_mul_of_nonneg_left
        hspectral (hp s)
    _ = ∑ i, ∑ s, p s * Real.negMulLog (d s i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ i, Real.negMulLog (hR.1.eigenvalues i) :=
      Finset.sum_le_sum fun i _ => hjensen i
    _ = posSemidefEntropy R hR := rfl

/-! ## Entropy of measurement branches -/

/-- The auxiliary spectral entropy agrees with the coefficient-matrix
entropy when it is applied to the normalized Schmidt Gram matrix. -/
theorem posSemidefEntropy_normalizedSchmidtGram
    (M : Matrix n n ℂ) :
    posSemidefEntropy (normalizedSchmidtGram M)
        (normalizedSchmidtGram_posSemidef M) =
      vonNeumannEntropy M := by
  rfl

/-- The entropy convention used here assigns entropy zero to the zero
coefficient matrix. -/
@[simp] theorem vonNeumannEntropy_zero :
    vonNeumannEntropy (0 : Matrix n n ℂ) = 0 := by
  classical
  have hflat :
      normalizedSchmidtGram (0 : Matrix n n ℂ) =
        (0 : ℝ) • (1 : Matrix n n ℂ) := by
    simp [normalizedSchmidtGram, schmidtNormSq, schmidtGram]
  unfold vonNeumannEntropy
  apply Finset.sum_eq_zero
  intro i hi
  rw [schmidtProbabilities_eq_of_normalizedGram_eq_smul_one
    (0 : Matrix n n ℂ) 0 hflat i]
  exact Real.negMulLog_zero

/-- Conjugate transposition preserves the Hilbert--Schmidt norm. -/
theorem schmidtNormSq_conjTranspose (M : Matrix n n ℂ) :
    schmidtNormSq Mᴴ = schmidtNormSq M := by
  classical
  simp only [schmidtNormSq, Matrix.conjTranspose_apply, norm_star]
  rw [Finset.sum_comm]

/-- For a square coefficient matrix, its two normalized reduced Gram
matrices have the same characteristic polynomial. -/
theorem normalizedSchmidtGram_conjTranspose_charpoly
    (M : Matrix n n ℂ) :
    (normalizedSchmidtGram Mᴴ).charpoly =
      (normalizedSchmidtGram M).charpoly := by
  classical
  unfold normalizedSchmidtGram schmidtGram
  rw [schmidtNormSq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  let c : ℝ := (schmidtNormSq M)⁻¹
  change (c • (M * Mᴴ)).charpoly = (c • (Mᴴ * M)).charpoly
  calc
    (c • (M * Mᴴ)).charpoly = ((c • M) * Mᴴ).charpoly := by
      rw [Matrix.smul_mul]
    _ = (Mᴴ * (c • M)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = (c • (Mᴴ * M)).charpoly := by rw [Matrix.mul_smul]

/-- Swapping the two Schmidt sides preserves entropy (for the square form
needed by the concrete count decomposition). -/
theorem vonNeumannEntropy_conjTranspose (M : Matrix n n ℂ) :
    vonNeumannEntropy Mᴴ = vonNeumannEntropy M := by
  rw [vonNeumannEntropy_eq_sum_negMulLog_roots,
    vonNeumannEntropy_eq_sum_negMulLog_roots,
    normalizedSchmidtGram_conjTranspose_charpoly]

/-- Keep precisely the rows carrying a prescribed finite measurement
label. -/
def rowMeasurementBlock {I : Type*} [DecidableEq I]
    (label : n → I) (M : Matrix n n ℂ) (s : I) : Matrix n n ℂ :=
  fun i j => if label i = s then M i j else 0

/-- The row-measurement branches add at the Gram-matrix level. -/
theorem sum_schmidtGram_rowMeasurementBlock
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : n → I) (M : Matrix n n ℂ) :
    ∑ s, schmidtGram (rowMeasurementBlock label M s) =
      schmidtGram M := by
  classical
  ext i j
  simp only [schmidtGram, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, rowMeasurementBlock]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single (label k)]
  · simp
  · intro s hs hne
    simp [hne.symm]
  · simp

/-- Squared norms of the row-measurement branches add to the squared norm
of the original coefficient matrix. -/
theorem sum_schmidtNormSq_rowMeasurementBlock
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : n → I) (M : Matrix n n ℂ) :
    ∑ s, schmidtNormSq (rowMeasurementBlock label M s) =
      schmidtNormSq M := by
  classical
  simp only [schmidtNormSq, rowMeasurementBlock]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (label i)]
  · simp
  · intro s hs hne
    simp [hne.symm]
  · simp

/-- Norm fraction carried by one member of a finite family of coefficient
matrices. -/
noncomputable def branchWeight {I : Type*}
    (M : Matrix n n ℂ) (A : I → Matrix n n ℂ) (s : I) : ℝ :=
  schmidtNormSq (A s) / schmidtNormSq M

theorem branchWeight_nonneg {I : Type*}
    (M : Matrix n n ℂ) (A : I → Matrix n n ℂ) (s : I) :
    0 ≤ branchWeight M A s := by
  exact div_nonneg (schmidtNormSq_nonneg _) (schmidtNormSq_nonneg _)

/-- If branch norms partition the norm of a nonzero matrix, their norm
fractions form a probability distribution. -/
theorem sum_branchWeight_eq_one
    {I : Type*} [Fintype I]
    (M : Matrix n n ℂ) (A : I → Matrix n n ℂ) (hM : M ≠ 0)
    (hnorm : ∑ s, schmidtNormSq (A s) = schmidtNormSq M) :
    ∑ s, branchWeight M A s = 1 := by
  simp only [branchWeight]
  rw [← Finset.sum_div, hnorm]
  exact div_self (schmidtNormSq_pos M hM).ne'

/-- After weighting by its squared norm, a branch's normalized Gram matrix
is its unnormalized Gram matrix divided by the total norm. -/
theorem branchWeight_smul_normalizedSchmidtGram
    {I : Type*} (M : Matrix n n ℂ) (A : I → Matrix n n ℂ)
    (s : I) (hM : M ≠ 0) :
    branchWeight M A s • normalizedSchmidtGram (A s) =
      (schmidtNormSq M)⁻¹ • schmidtGram (A s) := by
  by_cases hA : A s = 0
  · simp [hA, branchWeight, normalizedSchmidtGram, schmidtGram]
  · have hAnorm : schmidtNormSq (A s) ≠ 0 :=
      (schmidtNormSq_pos (A s) hA).ne'
    have hMnorm : schmidtNormSq M ≠ 0 :=
      (schmidtNormSq_pos M hM).ne'
    unfold branchWeight normalizedSchmidtGram
    rw [smul_smul]
    have hcoeff :
        schmidtNormSq (A s) / schmidtNormSq M *
            (schmidtNormSq (A s))⁻¹ =
          (schmidtNormSq M)⁻¹ := by
      field_simp
    rw [hcoeff]

/-- A Gram decomposition becomes a convex decomposition of normalized Gram
matrices after weighting each branch by its squared norm. -/
theorem sum_branchWeight_smul_normalizedSchmidtGram
    {I : Type*} [Fintype I]
    (M : Matrix n n ℂ) (A : I → Matrix n n ℂ) (hM : M ≠ 0)
    (hgram : ∑ s, schmidtGram (A s) = schmidtGram M) :
    ∑ s, branchWeight M A s • normalizedSchmidtGram (A s) =
      normalizedSchmidtGram M := by
  classical
  calc
    (∑ s, branchWeight M A s • normalizedSchmidtGram (A s)) =
        ∑ s, (schmidtNormSq M)⁻¹ • schmidtGram (A s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact branchWeight_smul_normalizedSchmidtGram M A s hM
    _ = (schmidtNormSq M)⁻¹ • ∑ s, schmidtGram (A s) := by
      rw [Finset.smul_sum]
    _ = normalizedSchmidtGram M := by
      rw [hgram]
      rfl

/-- Concavity of spectral entropy turns a norm and Gram partition into the
average-branch entropy inequality. -/
theorem weightedBranchEntropy_le
    {I : Type*} [Fintype I]
    (M : Matrix n n ℂ) (A : I → Matrix n n ℂ) (hM : M ≠ 0)
    (hnorm : ∑ s, schmidtNormSq (A s) = schmidtNormSq M)
    (hgram : ∑ s, schmidtGram (A s) = schmidtGram M) :
    ∑ s, branchWeight M A s * vonNeumannEntropy (A s) ≤
      vonNeumannEntropy M := by
  classical
  let p : I → ℝ := branchWeight M A
  let rho : I → Matrix n n ℂ := fun s => normalizedSchmidtGram (A s)
  have hp : ∀ s, 0 ≤ p s := fun s => branchWeight_nonneg M A s
  have hpsum : ∑ s, p s = 1 := sum_branchWeight_eq_one M A hM hnorm
  have hrho : ∀ s, (rho s).PosSemidef :=
    fun s => normalizedSchmidtGram_posSemidef (A s)
  have hmix : ∑ s, p s • rho s = normalizedSchmidtGram M := by
    exact sum_branchWeight_smul_normalizedSchmidtGram M A hM hgram
  have hconc := posSemidefEntropy_sum_smul_ge p hp hpsum rho hrho
  dsimp only at hconc
  simpa only [hmix, p, rho,
    posSemidefEntropy_normalizedSchmidtGram] using hconc

/-- Resolving a complete finite row label cannot increase the average
operator entanglement.  Zero input matrices are covered by convention. -/
theorem rowMeasurementEntropy_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : n → I) (M : Matrix n n ℂ) :
    ∑ s,
        (schmidtNormSq (rowMeasurementBlock label M s) / schmidtNormSq M) *
          vonNeumannEntropy (rowMeasurementBlock label M s) ≤
      vonNeumannEntropy M := by
  classical
  by_cases hM : M = 0
  · subst M
    have hblock (s : I) :
        rowMeasurementBlock label (0 : Matrix n n ℂ) s = 0 := by
      ext i j
      simp [rowMeasurementBlock]
    simp_rw [hblock]
    simp
  · exact weightedBranchEntropy_le M (rowMeasurementBlock label M) hM
      (sum_schmidtNormSq_rowMeasurementBlock label M)
      (sum_schmidtGram_rowMeasurementBlock label M)

/-- Keep precisely the columns carrying a prescribed finite measurement
label. -/
def columnMeasurementBlock {I : Type*} [DecidableEq I]
    (label : n → I) (M : Matrix n n ℂ) (s : I) : Matrix n n ℂ :=
  fun i j => if label j = s then M i j else 0

/-- A column branch becomes the corresponding row branch after conjugate
transposition. -/
theorem rowMeasurementBlock_conjTranspose
    {I : Type*} [DecidableEq I]
    (label : n → I) (M : Matrix n n ℂ) (s : I) :
    rowMeasurementBlock label Mᴴ s =
      (columnMeasurementBlock label M s)ᴴ := by
  ext i j
  by_cases h : label i = s <;>
    simp [rowMeasurementBlock, columnMeasurementBlock,
      Matrix.conjTranspose_apply, h]

/-- Resolving a complete finite column label cannot increase the average
operator entanglement. -/
theorem columnMeasurementEntropy_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : n → I) (M : Matrix n n ℂ) :
    ∑ s,
        (schmidtNormSq (columnMeasurementBlock label M s) / schmidtNormSq M) *
          vonNeumannEntropy (columnMeasurementBlock label M s) ≤
      vonNeumannEntropy M := by
  have h := rowMeasurementEntropy_le label Mᴴ
  simpa only [rowMeasurementBlock_conjTranspose,
    schmidtNormSq_conjTranspose, vonNeumannEntropy_conjTranspose] using h

/-- Simultaneous row/column measurement branch. -/
def twoSidedMeasurementBlock
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rowLabel : n → I) (colLabel : n → J)
    (M : Matrix n n ℂ) (a : I) (b : J) : Matrix n n ℂ :=
  rowMeasurementBlock rowLabel (columnMeasurementBlock colLabel M b) a

theorem column_rowMeasurementBlock_comm
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rowLabel : n → I) (colLabel : n → J)
    (M : Matrix n n ℂ) (a : I) (b : J) :
    columnMeasurementBlock colLabel (rowMeasurementBlock rowLabel M a) b =
      twoSidedMeasurementBlock rowLabel colLabel M a b := by
  ext i j
  by_cases hi : rowLabel i = a <;> by_cases hj : colLabel j = b <;>
    simp [twoSidedMeasurementBlock, rowMeasurementBlock,
      columnMeasurementBlock, hi, hj]

/-- Zero squared Hilbert--Schmidt norm characterizes the zero coefficient
matrix. -/
theorem schmidtNormSq_eq_zero_iff (M : Matrix n n ℂ) :
    schmidtNormSq M = 0 ↔ M = 0 := by
  constructor
  · intro hnorm
    by_contra hM
    have hpos := schmidtNormSq_pos M hM
    linarith
  · rintro rfl
    simp [schmidtNormSq]

/-- The branch weights telescope when a row measurement is followed by a
column measurement. -/
theorem twoSided_branchWeight_telescope
    {I J : Type*} [DecidableEq I] [Fintype J] [DecidableEq J]
    (rowLabel : n → I) (colLabel : n → J)
    (M : Matrix n n ℂ) (a : I) :
    (schmidtNormSq (rowMeasurementBlock rowLabel M a) / schmidtNormSq M) *
        (∑ b,
          (schmidtNormSq
              (twoSidedMeasurementBlock rowLabel colLabel M a b) /
            schmidtNormSq (rowMeasurementBlock rowLabel M a)) *
          vonNeumannEntropy
            (twoSidedMeasurementBlock rowLabel colLabel M a b)) =
      ∑ b,
        (schmidtNormSq
            (twoSidedMeasurementBlock rowLabel colLabel M a b) /
          schmidtNormSq M) *
        vonNeumannEntropy
          (twoSidedMeasurementBlock rowLabel colLabel M a b) := by
  classical
  let R := rowMeasurementBlock rowLabel M a
  by_cases hRnorm : schmidtNormSq R = 0
  · have hR : R = 0 := (schmidtNormSq_eq_zero_iff R).mp hRnorm
    have hbranch (b : J) :
        twoSidedMeasurementBlock rowLabel colLabel M a b = 0 := by
      rw [← column_rowMeasurementBlock_comm]
      change columnMeasurementBlock colLabel R b = 0
      rw [hR]
      ext i j
      simp [columnMeasurementBlock]
    simp [R, hRnorm, hbranch]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hcoeff :
        (schmidtNormSq R / schmidtNormSq M) *
            (schmidtNormSq
                (twoSidedMeasurementBlock rowLabel colLabel M a b) /
              schmidtNormSq R) =
          schmidtNormSq
              (twoSidedMeasurementBlock rowLabel colLabel M a b) /
            schmidtNormSq M := by
      field_simp
    rw [← mul_assoc, hcoeff]

/-- A complete local projective measurement on both Schmidt sides cannot
increase the average branch entropy. -/
theorem twoSidedMeasurementEntropy_le
    {I J : Type*} [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J]
    (rowLabel : n → I) (colLabel : n → J) (M : Matrix n n ℂ) :
    ∑ a, ∑ b,
        (schmidtNormSq
            (twoSidedMeasurementBlock rowLabel colLabel M a b) /
          schmidtNormSq M) *
        vonNeumannEntropy
          (twoSidedMeasurementBlock rowLabel colLabel M a b) ≤
      vonNeumannEntropy M := by
  classical
  calc
    (∑ a, ∑ b,
        (schmidtNormSq
            (twoSidedMeasurementBlock rowLabel colLabel M a b) /
          schmidtNormSq M) *
        vonNeumannEntropy
          (twoSidedMeasurementBlock rowLabel colLabel M a b)) =
        ∑ a,
          (schmidtNormSq (rowMeasurementBlock rowLabel M a) /
            schmidtNormSq M) *
          (∑ b,
            (schmidtNormSq
                (twoSidedMeasurementBlock rowLabel colLabel M a b) /
              schmidtNormSq (rowMeasurementBlock rowLabel M a)) *
            vonNeumannEntropy
              (twoSidedMeasurementBlock rowLabel colLabel M a b)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (twoSided_branchWeight_telescope
        rowLabel colLabel M a).symm
    _ ≤ ∑ a,
        (schmidtNormSq (rowMeasurementBlock rowLabel M a) /
          schmidtNormSq M) *
        vonNeumannEntropy (rowMeasurementBlock rowLabel M a) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left
      · simpa only [← column_rowMeasurementBlock_comm] using
          columnMeasurementEntropy_le colLabel
            (rowMeasurementBlock rowLabel M a)
      · exact div_nonneg (schmidtNormSq_nonneg _) (schmidtNormSq_nonneg _)
    _ ≤ vonNeumannEntropy M := rowMeasurementEntropy_le rowLabel M

/-- Squared norms of a complete two-sided projective measurement partition
the squared norm of the original coefficient matrix. -/
theorem sum_schmidtNormSq_twoSidedMeasurementBlock
    {I J : Type*} [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J]
    (rowLabel : n → I) (colLabel : n → J) (M : Matrix n n ℂ) :
    ∑ a, ∑ b,
      schmidtNormSq (twoSidedMeasurementBlock rowLabel colLabel M a b) =
        schmidtNormSq M := by
  have hcol (N : Matrix n n ℂ) :
      ∑ b, schmidtNormSq (columnMeasurementBlock colLabel N b) =
        schmidtNormSq N := by
    have h := sum_schmidtNormSq_rowMeasurementBlock colLabel Nᴴ
    simpa only [rowMeasurementBlock_conjTranspose,
      schmidtNormSq_conjTranspose] using h
  calc
    (∑ a, ∑ b,
        schmidtNormSq (twoSidedMeasurementBlock rowLabel colLabel M a b)) =
      ∑ a, ∑ b, schmidtNormSq
        (columnMeasurementBlock colLabel
          (rowMeasurementBlock rowLabel M a) b) := by
        simp_rw [column_rowMeasurementBlock_comm]
    _ = ∑ a, schmidtNormSq (rowMeasurementBlock rowLabel M a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hcol _
    _ = schmidtNormSq M :=
      sum_schmidtNormSq_rowMeasurementBlock rowLabel M

/-- If every nonzero word-resolved branch has entropy at least `c`, then
the unmeasured coefficient matrix also has entropy at least `c`. -/
theorem le_vonNeumannEntropy_of_twoSidedMeasurement
    {I J : Type*} [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J]
    (rowLabel : n → I) (colLabel : n → J)
    (M : Matrix n n ℂ) (hM : M ≠ 0) (c : ℝ)
    (hbranch : ∀ a b,
      twoSidedMeasurementBlock rowLabel colLabel M a b ≠ 0 →
        c ≤ vonNeumannEntropy
          (twoSidedMeasurementBlock rowLabel colLabel M a b)) :
    c ≤ vonNeumannEntropy M := by
  classical
  let A := twoSidedMeasurementBlock rowLabel colLabel M
  have hnorm : ∑ a, ∑ b, schmidtNormSq (A a b) = schmidtNormSq M :=
    sum_schmidtNormSq_twoSidedMeasurementBlock rowLabel colLabel M
  have hnormM : schmidtNormSq M ≠ 0 := (schmidtNormSq_pos M hM).ne'
  have hweights :
      ∑ a, ∑ b, schmidtNormSq (A a b) / schmidtNormSq M = 1 := by
    simp_rw [← Finset.sum_div]
    rw [hnorm, div_self hnormM]
  calc
    c = 1 * c := by simp
    _ = (∑ a, ∑ b,
        schmidtNormSq (A a b) / schmidtNormSq M) * c := by rw [hweights]
    _ = ∑ a, ∑ b,
        (schmidtNormSq (A a b) / schmidtNormSq M) * c := by
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ a, ∑ b,
        (schmidtNormSq (A a b) / schmidtNormSq M) *
          vonNeumannEntropy (A a b) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases hA : A a b = 0
      · simp [hA, schmidtNormSq]
      · exact mul_le_mul_of_nonneg_left (hbranch a b hA)
          (div_nonneg (schmidtNormSq_nonneg _) (schmidtNormSq_nonneg _))
    _ ≤ vonNeumannEntropy M :=
      twoSidedMeasurementEntropy_le rowLabel colLabel M

/-! ## Concrete folded count measurement -/

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Regard the folded `B` count as a label in its exact finite range. -/
def foldedBCountFin {t : ℕ} (z : FoldedPacket F t) : Fin (t + 1) :=
  ⟨foldedBCount F z, Nat.lt_succ_of_le (foldedBCount_le F z)⟩

/-- Regard the folded `A` count as a label in its exact finite range. -/
def foldedACountFin {t : ℕ} (z : FoldedPacket F t) : Fin (t + 1) :=
  ⟨foldedACount F z, Nat.lt_succ_of_le (foldedACount_le F z)⟩

omit [Field F] in
/-- The abstract two-sided projective branch is literally the count block
already used in the concrete construction. -/
theorem twoSidedMeasurementBlock_foldedCounts {t : ℕ}
    (M : Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ)
    (k l : Fin (t + 1)) :
    twoSidedMeasurementBlock (foldedBCountFin F) (foldedACountFin F)
        M k l =
      countBlock F M k l := by
  ext x y
  by_cases hk : foldedBCount F x = k.val <;>
    by_cases hl : foldedACount F y = l.val
  · have hk' : foldedBCountFin F x = k := Fin.ext hk
    have hl' : foldedACountFin F y = l := Fin.ext hl
    simp [twoSidedMeasurementBlock, rowMeasurementBlock,
      columnMeasurementBlock, countBlock, hk, hl, hk', hl']
  · have hl' : foldedACountFin F y ≠ l :=
      fun h => hl (congrArg Fin.val h)
    simp [twoSidedMeasurementBlock, rowMeasurementBlock,
      columnMeasurementBlock, countBlock, hl, hl']
  · have hk' : foldedBCountFin F x ≠ k :=
      fun h => hk (congrArg Fin.val h)
    simp [twoSidedMeasurementBlock, rowMeasurementBlock,
      columnMeasurementBlock, countBlock, hk, hk']
  · have hk' : foldedBCountFin F x ≠ k :=
      fun h => hk (congrArg Fin.val h)
    simp [twoSidedMeasurementBlock, rowMeasurementBlock,
      columnMeasurementBlock, countBlock, hk, hk']

/-- Entropy is nonnegative also for a zero coefficient matrix, under the
zero-entropy convention. -/
theorem vonNeumannEntropy_nonneg_all (M : Matrix n n ℂ) :
    0 ≤ vonNeumannEntropy M := by
  by_cases hM : M = 0
  · subst M
    simp
  · exact vonNeumannEntropy_nonneg M hM

/-- Measuring all folded count sectors of the concrete coefficient matrix
cannot increase its operator entanglement. -/
theorem allRectangularCountBranchesEntropy_le
    (psi : AddChar F ℂ) (n : ℕ) :
    ∑ k : Fin (n + 2), ∑ l : Fin (n + 2),
        rectangularCountWeight F psi (succPNat n) k l *
          vonNeumannEntropy
            (rectangularCountBlock F psi (succPNat n) k l) ≤
      rectangularVonNeumannEntropy F psi (succPNat n) := by
  let M := foldedRectCoeff F (rectangularCore F psi (succPNat n))
  have hmeasure := twoSidedMeasurementEntropy_le
    (foldedBCountFin F) (foldedACountFin F) M
  have hfold : vonNeumannEntropy M =
      rectangularVonNeumannEntropy F psi (succPNat n) := by
    unfold M foldedRectCoeff rectangularVonNeumannEntropy
    exact vonNeumannEntropy_reindex_equiv
      (foldPacketEquiv F (n + 1)) (foldPacketEquiv F (n + 1)) _
  simpa only [M, twoSidedMeasurementBlock_foldedCounts,
    rectangularCountWeight, hfold] using hmeasure

end SqrtOpEnt
