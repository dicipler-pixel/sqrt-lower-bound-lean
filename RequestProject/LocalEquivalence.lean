import RequestProject.CircuitPhase

/-!
# Spectral invariance under local basis reindexing

The concrete source-sector blocks are first described in packet coordinates
and then folded into the onsite operator basis.  This file proves that this
change of basis preserves the complete normalized Schmidt spectrum, not only
the Hilbert--Schmidt norm and rank.  It therefore removes the basis-reindexing
part of the remaining block-to-residual-core bridge.
-/

namespace SqrtOpEnt

open Matrix
open scoped BigOperators ComplexOrder

variable {m n m' n' : Type*}
  [Fintype m] [Fintype n] [Fintype m'] [Fintype n']

omit [Fintype n] [Fintype n'] in
/-- Reindexing the two axes of a coefficient matrix only reindexes its Gram
matrix along the column equivalence. -/
theorem schmidtGram_reindex_equiv
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) :
    schmidtGram (Matrix.reindex e f M) =
      Matrix.reindex f f (schmidtGram M) := by
  classical
  unfold schmidtGram
  rw [Matrix.conjTranspose_reindex]
  exact Matrix.reindexLinearEquiv_mul ℂ ℂ f e f Mᴴ M

/-- The normalized Schmidt Gram matrix transforms by the corresponding
column-basis reindexing. -/
theorem normalizedSchmidtGram_reindex_equiv
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) :
    normalizedSchmidtGram (Matrix.reindex e f M) =
      Matrix.reindex f f (normalizedSchmidtGram M) := by
  classical
  unfold normalizedSchmidtGram
  rw [schmidtNormSq_reindex_equiv, schmidtGram_reindex_equiv]
  ext i j
  rfl

/-- Von Neumann entropy can be read directly from the roots of the
characteristic polynomial of the normalized Gram matrix.  This
index-independent form is convenient when two matrices use equivalent, but
not definitionally equal, column index types. -/
theorem vonNeumannEntropy_eq_sum_negMulLog_roots [DecidableEq n]
    (M : Matrix m n ℂ) :
    vonNeumannEntropy M =
      (((normalizedSchmidtGram M).charpoly.roots.map Complex.re).map
        Real.negMulLog).sum := by
  classical
  let hA := normalizedSchmidtGram_isHermitian M
  rw [vonNeumannEntropy]
  change (∑ i, Real.negMulLog (hA.eigenvalues i)) = _
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp

/-- Arbitrary row and column reindexings preserve von Neumann operator
entropy. -/
theorem vonNeumannEntropy_reindex_equiv
    [DecidableEq n] [DecidableEq n']
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) :
    vonNeumannEntropy (Matrix.reindex e f M) = vonNeumannEntropy M := by
  rw [vonNeumannEntropy_eq_sum_negMulLog_roots,
    vonNeumannEntropy_eq_sum_negMulLog_roots,
    normalizedSchmidtGram_reindex_equiv,
    Matrix.charpoly_reindex]

omit [Fintype m] [Fintype m'] in
/-- The same local basis reindexing preserves exact operator Schmidt rank. -/
theorem operatorSchmidtRank_reindex_equiv
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) :
    operatorSchmidtRank (Matrix.reindex e f M) = operatorSchmidtRank M := by
  exact Matrix.rank_reindex e f M

/-! ## Removal of zero padding -/

variable {mPad nPad : Type*} [Fintype mPad] [Fintype nPad]

/-- Enlarge a coefficient matrix by adding identically zero rows and
columns.  The original matrix occupies the upper-left block. -/
def zeroPad (M : Matrix m n ℂ) : Matrix (m ⊕ mPad) (n ⊕ nPad) ℂ :=
  Matrix.fromBlocks M 0 0 0

/-- Zero padding does not change the squared Hilbert--Schmidt norm. -/
theorem schmidtNormSq_zeroPad (M : Matrix m n ℂ) :
    schmidtNormSq (zeroPad (mPad := mPad) (nPad := nPad) M) =
      schmidtNormSq M := by
  classical
  simp [schmidtNormSq, zeroPad, Fintype.sum_sum_type]

omit [Fintype n] [Fintype nPad] in
/-- The Gram matrix of a zero-padded coefficient matrix is the original
Gram matrix with a zero block appended. -/
theorem schmidtGram_zeroPad (M : Matrix m n ℂ) :
    schmidtGram (zeroPad (mPad := mPad) (nPad := nPad) M) =
      Matrix.fromBlocks (schmidtGram M) 0 0 0 := by
  classical
  unfold schmidtGram zeroPad
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp

/-- Normalization commutes with adjoining zero rows and columns. -/
theorem normalizedSchmidtGram_zeroPad (M : Matrix m n ℂ) :
    normalizedSchmidtGram (zeroPad (mPad := mPad) (nPad := nPad) M) =
      Matrix.fromBlocks (normalizedSchmidtGram M) 0 0 0 := by
  classical
  unfold normalizedSchmidtGram
  rw [schmidtNormSq_zeroPad, schmidtGram_zeroPad,
    Matrix.fromBlocks_smul]
  simp

/-- Adding zero rows and columns only adds zero Schmidt eigenvalues, hence
does not change von Neumann operator entropy. -/
theorem vonNeumannEntropy_zeroPad [DecidableEq n] [DecidableEq nPad]
    (M : Matrix m n ℂ) :
    vonNeumannEntropy (zeroPad (mPad := mPad) (nPad := nPad) M) =
      vonNeumannEntropy M := by
  rw [vonNeumannEntropy_eq_sum_negMulLog_roots,
    vonNeumannEntropy_eq_sum_negMulLog_roots,
    normalizedSchmidtGram_zeroPad,
    Matrix.charpoly_fromBlocks_zero₂₁]
  have hprod :
      (normalizedSchmidtGram M).charpoly *
          (0 : Matrix nPad nPad ℂ).charpoly ≠ 0 :=
    mul_ne_zero (Matrix.charpoly_monic _).ne_zero
      (Matrix.charpoly_monic _).ne_zero
  rw [Polynomial.roots_mul hprod, Matrix.charpoly_zero,
    Polynomial.roots_X_pow]
  simp [Multiset.nsmul_singleton, Multiset.map_replicate,
    Multiset.sum_replicate]

/-! ## Repetition of an independent spectator row -/

variable {z : Type*} [Fintype z]

/-- Repeat every row of a coefficient matrix once for each value of an
independent spectator. -/
def replicateRows (M : Matrix m n ℂ) : Matrix (z × m) n ℂ :=
  fun i j => M i.2 j

omit [Fintype n] in
theorem schmidtGram_replicateRows (M : Matrix m n ℂ) :
    schmidtGram (replicateRows (z := z) M) =
      (Fintype.card z : ℂ) • schmidtGram M := by
  classical
  ext i j
  simp [schmidtGram, replicateRows, Matrix.mul_apply,
    Fintype.sum_prod_type, mul_comm]

theorem schmidtNormSq_replicateRows (M : Matrix m n ℂ) :
    schmidtNormSq (replicateRows (z := z) M) =
      (Fintype.card z : ℝ) * schmidtNormSq M := by
  classical
  unfold schmidtNormSq replicateRows
  rw [Fintype.sum_prod_type]
  simp [Finset.mul_sum]

/-- Repeating all rows by a nonempty spectator multiplies both the Gram
matrix and its trace by the same factor, so normalization removes it. -/
theorem normalizedSchmidtGram_replicateRows [Nonempty z]
    (M : Matrix m n ℂ) :
    normalizedSchmidtGram (replicateRows (z := z) M) =
      normalizedSchmidtGram M := by
  classical
  unfold normalizedSchmidtGram
  rw [schmidtNormSq_replicateRows, schmidtGram_replicateRows]
  have hzR : (Fintype.card z : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card z ≠ 0)
  have hzC : (Fintype.card z : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card z ≠ 0)
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  rw [_root_.mul_inv_rev]
  calc
    (schmidtNormSq M : ℂ)⁻¹ * (Fintype.card z : ℂ)⁻¹ *
          ((Fintype.card z : ℂ) * schmidtGram M i j) =
        (schmidtNormSq M : ℂ)⁻¹ *
          ((Fintype.card z : ℂ)⁻¹ * (Fintype.card z : ℂ)) *
            schmidtGram M i j := by ring
    _ = _ := by rw [inv_mul_cancel₀ hzC]; simp

/-- An independent repeated row spectator does not change operator
entanglement entropy. -/
theorem vonNeumannEntropy_replicateRows [Nonempty z] [DecidableEq n]
    (M : Matrix m n ℂ) :
    vonNeumannEntropy (replicateRows (z := z) M) =
      vonNeumannEntropy M := by
  rw [vonNeumannEntropy_eq_sum_negMulLog_roots,
    vonNeumannEntropy_eq_sum_negMulLog_roots,
    normalizedSchmidtGram_replicateRows]

/-- Coordinate inclusion of the first summand, written as a rectangular
matrix. -/
def sumInlMatrix (a b : Type*) [DecidableEq a] : Matrix (a ⊕ b) a ℂ :=
  fun i j => match i with
    | .inl k => if k = j then 1 else 0
    | .inr _ => 0

omit [Fintype mPad] [Fintype nPad] in
/-- Zero padding is multiplication by the coordinate inclusions on its two
sides. -/
theorem zeroPad_eq_sumInlMatrix [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) :
    zeroPad (mPad := mPad) (nPad := nPad) M =
      sumInlMatrix m mPad * M * (sumInlMatrix n nPad)ᴴ := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [zeroPad, sumInlMatrix, Matrix.mul_apply]

/-- Projecting a zero-padded matrix back onto the first row and column
summands recovers the original matrix. -/
theorem sumInlMatrix_conjTranspose_mul_zeroPad_mul_sumInlMatrix
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) :
    (sumInlMatrix m mPad)ᴴ *
        zeroPad (mPad := mPad) (nPad := nPad) M *
      sumInlMatrix n nPad = M := by
  classical
  ext i j
  simp [zeroPad, sumInlMatrix, Matrix.mul_apply]

/-- Adding identically zero rows and columns preserves exact matrix rank. -/
theorem rank_zeroPad [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) :
    (zeroPad (mPad := mPad) (nPad := nPad) M).rank = M.rank := by
  apply le_antisymm
  · rw [zeroPad_eq_sumInlMatrix]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · calc
      M.rank = ((sumInlMatrix m mPad)ᴴ *
          zeroPad (mPad := mPad) (nPad := nPad) M *
          sumInlMatrix n nPad).rank := by
        rw [sumInlMatrix_conjTranspose_mul_zeroPad_mul_sumInlMatrix]
      _ ≤ (zeroPad (mPad := mPad) (nPad := nPad) M).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- In operator language, zero padding preserves exact Schmidt rank. -/
theorem operatorSchmidtRank_zeroPad [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) :
    operatorSchmidtRank (zeroPad (mPad := mPad) (nPad := nPad) M) =
      operatorSchmidtRank M := by
  exact rank_zeroPad M

/-! ## Unitary local changes of basis -/

variable [DecidableEq m] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A unitary change of row coordinates leaves the Schmidt Gram matrix
unchanged. -/
theorem schmidtGram_unitary_mul (U : Matrix m m ℂ) (M : Matrix m n ℂ)
    (hU : U ∈ unitary (Matrix m m ℂ)) :
    schmidtGram (U * M) = schmidtGram M := by
  have hUleft : Uᴴ * U = 1 := by simpa using hU.1
  unfold schmidtGram
  calc
    (U * M)ᴴ * (U * M) = Mᴴ * (Uᴴ * U) * M := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = Mᴴ * M := by rw [hUleft, Matrix.mul_one]

omit [DecidableEq n] in
/-- A unitary row transformation preserves the Hilbert--Schmidt norm. -/
theorem schmidtNormSq_unitary_mul (U : Matrix m m ℂ) (M : Matrix m n ℂ)
    (hU : U ∈ unitary (Matrix m m ℂ)) :
    schmidtNormSq (U * M) = schmidtNormSq M := by
  have h := congrArg Matrix.trace (schmidtGram_unitary_mul U M hU)
  exact Complex.ofReal_injective (by simpa only [trace_schmidtGram] using h)

omit [DecidableEq n] in
/-- A unitary row transformation preserves the normalized Schmidt density
matrix exactly. -/
theorem normalizedSchmidtGram_unitary_mul
    (U : Matrix m m ℂ) (M : Matrix m n ℂ)
    (hU : U ∈ unitary (Matrix m m ℂ)) :
    normalizedSchmidtGram (U * M) = normalizedSchmidtGram M := by
  unfold normalizedSchmidtGram
  rw [schmidtNormSq_unitary_mul U M hU, schmidtGram_unitary_mul U M hU]

omit [DecidableEq m] [DecidableEq n] in
/-- A unitary change of column coordinates conjugates the Schmidt Gram
matrix. -/
theorem schmidtGram_mul_unitary (M : Matrix m n ℂ) (V : Matrix n n ℂ) :
    schmidtGram (M * V) = Vᴴ * schmidtGram M * V := by
  unfold schmidtGram
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

omit [DecidableEq m] in
/-- A unitary column transformation preserves the Hilbert--Schmidt norm. -/
theorem schmidtNormSq_mul_unitary (M : Matrix m n ℂ) (V : Matrix n n ℂ)
    (hV : V ∈ unitary (Matrix n n ℂ)) :
    schmidtNormSq (M * V) = schmidtNormSq M := by
  have hVright : V * Vᴴ = 1 := by simpa using hV.2
  have htrace : ((schmidtNormSq (M * V) : ℝ) : ℂ) =
      ((schmidtNormSq M : ℝ) : ℂ) := by
    rw [← trace_schmidtGram, ← trace_schmidtGram,
      schmidtGram_mul_unitary]
    calc
      Matrix.trace (Vᴴ * schmidtGram M * V) =
          Matrix.trace (V * Vᴴ * schmidtGram M) :=
        Matrix.trace_mul_cycle Vᴴ (schmidtGram M) V
      _ = Matrix.trace (schmidtGram M) := by
        rw [hVright, Matrix.one_mul]
  exact Complex.ofReal_injective htrace

omit [DecidableEq m] in
/-- A unitary column transformation conjugates the normalized Schmidt
density matrix. -/
theorem normalizedSchmidtGram_mul_unitary
    (M : Matrix m n ℂ) (V : Matrix n n ℂ)
    (hV : V ∈ unitary (Matrix n n ℂ)) :
    normalizedSchmidtGram (M * V) =
      Vᴴ * normalizedSchmidtGram M * V := by
  unfold normalizedSchmidtGram
  rw [schmidtNormSq_mul_unitary M V hV, schmidtGram_mul_unitary]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- Unitary transformations on the row side preserve von Neumann operator
entropy. -/
theorem vonNeumannEntropy_unitary_mul (U : Matrix m m ℂ) (M : Matrix m n ℂ)
    (hU : U ∈ unitary (Matrix m m ℂ)) :
    vonNeumannEntropy (U * M) = vonNeumannEntropy M := by
  rw [vonNeumannEntropy_eq_sum_negMulLog_roots,
    vonNeumannEntropy_eq_sum_negMulLog_roots,
    normalizedSchmidtGram_unitary_mul U M hU]

omit [DecidableEq m] in
/-- Unitary transformations on the column side preserve von Neumann
operator entropy. -/
theorem vonNeumannEntropy_mul_unitary (M : Matrix m n ℂ) (V : Matrix n n ℂ)
    (hV : V ∈ unitary (Matrix n n ℂ)) :
    vonNeumannEntropy (M * V) = vonNeumannEntropy M := by
  have hVright : V * Vᴴ = 1 := by simpa using hV.2
  rw [vonNeumannEntropy_eq_sum_negMulLog_roots,
    vonNeumannEntropy_eq_sum_negMulLog_roots,
    normalizedSchmidtGram_mul_unitary M V hV]
  have hchar :
      (Vᴴ * normalizedSchmidtGram M * V).charpoly =
        (normalizedSchmidtGram M).charpoly := by
    calc
      (Vᴴ * normalizedSchmidtGram M * V).charpoly =
          (Vᴴ * (normalizedSchmidtGram M * V)).charpoly := by
            rw [Matrix.mul_assoc]
      _ = ((normalizedSchmidtGram M * V) * Vᴴ).charpoly :=
        Matrix.charpoly_mul_comm _ _
      _ = (normalizedSchmidtGram M).charpoly := by
        rw [Matrix.mul_assoc, hVright, Matrix.mul_one]
  rw [hchar]

omit [DecidableEq n] in
/-- Unitary transformations on either side preserve exact operator Schmidt
rank. -/
theorem operatorSchmidtRank_unitary_mul
    (U : Matrix m m ℂ) (M : Matrix m n ℂ)
    (hU : U ∈ unitary (Matrix m m ℂ)) :
    operatorSchmidtRank (U * M) = operatorSchmidtRank M := by
  have hUleft : Uᴴ * U = 1 := by simpa using hU.1
  unfold operatorSchmidtRank
  apply le_antisymm
  · exact Matrix.rank_mul_le_right U M
  · have h := Matrix.rank_mul_le_right Uᴴ (U * M)
    simpa only [← Matrix.mul_assoc, hUleft, Matrix.one_mul] using h

omit [Fintype m] [DecidableEq m] in
theorem operatorSchmidtRank_mul_unitary
    (M : Matrix m n ℂ) (V : Matrix n n ℂ)
    (hV : V ∈ unitary (Matrix n n ℂ)) :
    operatorSchmidtRank (M * V) = operatorSchmidtRank M := by
  have hVright : V * Vᴴ = 1 := by simpa using hV.2
  unfold operatorSchmidtRank
  apply le_antisymm
  · exact Matrix.rank_mul_le_left M V
  · have h := Matrix.rank_mul_le_left (M * V) Vᴴ
    simpa only [Matrix.mul_assoc, hVright, Matrix.mul_one] using h

/-! ## Combined local-equivalence interface -/

omit [DecidableEq m] in
/-- The complete generic padding/local-equivalence move used in the
fixed-sector reduction: append zero rows and columns, reindex both finite
bases, and apply unitaries on the two Schmidt sides.  None of these operations
changes von Neumann operator entropy. -/
theorem vonNeumannEntropy_unitary_reindex_zeroPad
    [DecidableEq mPad] [DecidableEq nPad]
    [DecidableEq m'] [DecidableEq n']
    (M : Matrix m n ℂ)
    (e : (m ⊕ mPad) ≃ m') (f : (n ⊕ nPad) ≃ n')
    (U : Matrix m' m' ℂ) (V : Matrix n' n' ℂ)
    (hU : U ∈ unitary (Matrix m' m' ℂ))
    (hV : V ∈ unitary (Matrix n' n' ℂ)) :
    vonNeumannEntropy
        (U * Matrix.reindex e f
          (zeroPad (mPad := mPad) (nPad := nPad) M) * V) =
      vonNeumannEntropy M := by
  rw [vonNeumannEntropy_mul_unitary _ V hV,
    vonNeumannEntropy_unitary_mul U _ hU,
    vonNeumannEntropy_reindex_equiv,
    vonNeumannEntropy_zeroPad]

/-- The same padding/local-equivalence move preserves exact operator
Schmidt rank. -/
theorem operatorSchmidtRank_unitary_reindex_zeroPad
    [DecidableEq mPad] [DecidableEq nPad]
    [DecidableEq m'] [DecidableEq n']
    (M : Matrix m n ℂ)
    (e : (m ⊕ mPad) ≃ m') (f : (n ⊕ nPad) ≃ n')
    (U : Matrix m' m' ℂ) (V : Matrix n' n' ℂ)
    (hU : U ∈ unitary (Matrix m' m' ℂ))
    (hV : V ∈ unitary (Matrix n' n' ℂ)) :
    operatorSchmidtRank
        (U * Matrix.reindex e f
          (zeroPad (mPad := mPad) (nPad := nPad) M) * V) =
      operatorSchmidtRank M := by
  rw [operatorSchmidtRank_mul_unitary _ V hV,
    operatorSchmidtRank_unitary_mul U _ hU,
    operatorSchmidtRank_reindex_equiv,
    operatorSchmidtRank_zeroPad]

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Folding a pulled-back source sector into the literal onsite count block
preserves its normalized Schmidt spectrum and hence its entropy. -/
theorem vonNeumannEntropy_pulledSourceSectorBlock_eq_countBlock
    (psi : AddChar F ℂ) (n j l : ℕ) :
    vonNeumannEntropy (pulledSourceSectorBlock F psi n j l) =
      vonNeumannEntropy
        (rectangularCountBlock F psi (succPNat n) (j + 1) l) := by
  rw [← foldedPulledSourceSectorBlock_eq_countBlock]
  exact (vonNeumannEntropy_reindex_equiv
    (foldPacketEquiv F (n + 1)) (foldPacketEquiv F (n + 1)) _).symm

end SqrtOpEnt
