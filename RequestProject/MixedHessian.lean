import RequestProject.ResponseCones

/-!
# Mixed Hessians from the cubic phase difference

This file begins the missing bridge between the response functions in
`ResponseCones.lean` and the Fourier matrices in `FlatSpectrum.lean`.

For the positive grid, Eq. (6.21) gives at each cell

`epsilon_ij * a_(i,j+1)^2 + 2 * epsilon_(i,j+1) * a_ij * a_(i,j+1)`.

For the negative grid we similarly expand Eq. (6.22). Differentiating once in
a left boundary coordinate and once in a right boundary coordinate gives the
two explicit mixed Hessians below. Their triangular support and diagonals are
proved from the response formulas, and for the negative branch the extra zero
column and exact one-dimensional kernel are proved as well. Only the forward
source response `epsilon` remains as an input to these formulas; its
construction from `X_t` is a later bridge.
-/

namespace SqrtOpEnt

open Finset Matrix

variable {F : Type*} [Field F]

/-- Mixed unit finite difference of a function of one left and one right
coordinate.  For a quadratic polynomial this extracts its `L*R`
coefficient. -/
def mixedUnitDifference (Q : F → F → F) : F :=
  Q 1 1 - Q 1 0 - Q 0 1 + Q 0 0

/-- Positive-grid top response, interpreted in the finite field. -/
def UposF (m i j : ℕ) : F := (Upos m i j : ℤ)

/-- Positive-grid right response, interpreted in the finite field. -/
def VposF (r n i j : ℕ) : F := (Vpos r n i j : ℤ)

/-- If the right label lies strictly above the left label, the response cones
prevent the two responses from meeting in any pair of variables in one row. -/
theorem UposF_mul_VposF_eq_zero_of_lt
    (r m n i jU jV : ℕ) (hmn : m < n) :
    UposF (F := F) m i jU * VposF (F := F) r n i jV = 0 := by
  by_cases hU : Upos m i jU = 0
  · simp [UposF, hU]
  by_cases hV : Vpos r n i jV = 0
  · simp [VposF, hV]
  have hUi : i + jU ≤ m := Upos_cone hU
  have hVi : n ≤ i := Vpos_cone hV
  omega

/-- Cell contribution to the positive mixed Hessian, obtained directly by
expanding Eq. (6.21) with the boundary responses `Upos`,`Vpos`. -/
def positiveCellMixed (ε : ℕ → ℕ → F) (r m n i j : ℕ) : F :=
  ε i j * 2 *
      (UposF (F := F) m i (j + 1) * VposF (F := F) r n i (j + 1)) +
    2 * ε i (j + 1) *
      (UposF (F := F) m i j * VposF (F := F) r n i (j + 1) +
        VposF (F := F) r n i j * UposF (F := F) m i (j + 1))

/-- `positiveCellMixed` is literally the mixed finite difference of the
quadratic cell contribution in Eq. (6.21). -/
theorem positiveCellMixed_eq_mixedUnitDifference
    (ε : ℕ → ℕ → F) (r m n i j : ℕ) (a b : F) :
    positiveCellMixed ε r m n i j =
      mixedUnitDifference (fun L R =>
        ε i j *
            (b + UposF (F := F) m i (j + 1) * L +
              VposF (F := F) r n i (j + 1) * R) ^ 2 +
          2 * ε i (j + 1) *
            (a + UposF (F := F) m i j * L +
              VposF (F := F) r n i j * R) *
            (b + UposF (F := F) m i (j + 1) * L +
              VposF (F := F) r n i (j + 1) * R)) := by
  unfold positiveCellMixed mixedUnitDifference
  ring

/-- The explicit positive mixed Hessian from the sum of all `r^2` cell
contributions in the cubic phase difference. -/
def positiveMixedHessian (ε : ℕ → ℕ → F) (r : ℕ) :
    Matrix (Fin r) (Fin r) F :=
  fun m n => ∑ i : Fin r, ∑ j : Fin r,
    positiveCellMixed ε r m n i j

/-- **Lemma 6.4, positive triangularity.**  The response-derived positive mixed
Hessian is lower triangular for every forward displacement `epsilon`. -/
theorem positiveMixedHessian_upper_zero (ε : ℕ → ℕ → F) (r : ℕ)
    (m n : Fin r) (hmn : m < n) :
    positiveMixedHessian ε r m n = 0 := by
  classical
  unfold positiveMixedHessian
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hsq := UposF_mul_VposF_eq_zero_of_lt
    (F := F) r m n i (j + 1) (j + 1) hmn
  have hforward := UposF_mul_VposF_eq_zero_of_lt
    (F := F) r m n i j (j + 1) hmn
  have hbackward := UposF_mul_VposF_eq_zero_of_lt
    (F := F) r m n i (j + 1) j hmn
  unfold positiveCellMixed
  rw [hsq, hforward]
  have hbackward' :
      VposF (F := F) r n i j * UposF (F := F) m i (j + 1) = 0 := by
    rw [mul_comm, hbackward]
  rw [hbackward']
  ring

/-- On a diagonal label, a top response evaluated one column to the right can
never meet a right response. -/
theorem UposF_succ_mul_VposF_diag_zero
    (r m i j jV : ℕ) :
    UposF (F := F) m i (j + 1) * VposF (F := F) r m i jV = 0 := by
  by_cases hU : Upos m i (j + 1) = 0
  · simp [UposF, hU]
  by_cases hV : Vpos r m i jV = 0
  · simp [VposF, hV]
  have hUi : i + (j + 1) ≤ m := Upos_cone hU
  have hVi : m ≤ i := Vpos_cone hV
  omega

/-- On the diagonal, the unshifted-left/shifted-right orientation can meet
only at the extremal cell `(i,j)=(m,0)`. -/
theorem UposF_mul_VposF_diag_zero_of_ne
    (r m i j : ℕ) (hne : (i, j) ≠ (m, 0)) :
    UposF (F := F) m i j * VposF (F := F) r m i (j + 1) = 0 := by
  by_cases hU : Upos m i j = 0
  · simp [UposF, hU]
  by_cases hV : Vpos r m i (j + 1) = 0
  · simp [VposF, hV]
  have hUi : i + j ≤ m := Upos_cone hU
  have hVi : m ≤ i := Vpos_cone hV
  exfalso
  apply hne
  apply Prod.ext
  · omega
  · omega

/-- Every diagonal cell contribution except the unique extremal cell vanishes. -/
theorem positiveCellMixed_diag_zero_of_ne (ε : ℕ → ℕ → F)
    (r m i j : ℕ) (hne : (i, j) ≠ (m, 0)) :
    positiveCellMixed ε r m m i j = 0 := by
  have hsq := UposF_succ_mul_VposF_diag_zero
    (F := F) r m i j (j + 1)
  have hforward := UposF_mul_VposF_diag_zero_of_ne
    (F := F) r m i j hne
  have hbackward := UposF_succ_mul_VposF_diag_zero
    (F := F) r m i j j
  unfold positiveCellMixed
  rw [hsq, hforward]
  have hbackward' :
      VposF (F := F) r m i j * UposF (F := F) m i (j + 1) = 0 := by
    rw [mul_comm, hbackward]
  rw [hbackward']
  ring

/-- **Eq. (6.23), diagonal part.**  If the forward source displacement is one
along the first interior column, the positive mixed Hessian has diagonal
`2*(-1)^(r-1)`, equivalently `2*(-1)^(r+1)`. -/
theorem positiveMixedHessian_diag (ε : ℕ → ℕ → F) (r : ℕ)
    (hε : ∀ m < r, ε m 1 = 1) (m : Fin r) :
    positiveMixedHessian ε r m m = 2 * (-1 : F) ^ (r - 1) := by
  classical
  let j0 : Fin r := ⟨0, Nat.zero_lt_of_lt m.isLt⟩
  unfold positiveMixedHessian
  rw [Finset.sum_eq_single m]
  · rw [Finset.sum_eq_single j0]
    · have hm : (m : ℕ) < r := m.isLt
      have hr : 1 ≤ r := by omega
      simp [positiveCellMixed, UposF, VposF, Upos, Vpos, j0, hε m m.isLt, hr]
    · intro j hj hjne
      apply positiveCellMixed_diag_zero_of_ne
      intro hp
      apply hjne
      apply Fin.ext
      simpa [j0] using congrArg Prod.snd hp
    · simp
  · intro i hi hine
    apply Finset.sum_eq_zero
    intro j hj
    apply positiveCellMixed_diag_zero_of_ne
    intro hp
    apply hine
    apply Fin.ext
    simpa using congrArg Prod.fst hp
  · simp

/-- In odd characteristic every positive-branch diagonal entry is nonzero. -/
theorem positiveMixedHessian_diag_ne_zero (ε : ℕ → ℕ → F) (r : ℕ)
    (hodd : ringChar F ≠ 2) (hε : ∀ m < r, ε m 1 = 1) (m : Fin r) :
    positiveMixedHessian ε r m m ≠ 0 := by
  rw [positiveMixedHessian_diag ε r hε m]
  exact mul_ne_zero (two_ne_zero_of_odd_char hodd) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- The response-derived positive mixed map is injective in odd characteristic. -/
theorem positiveMixedHessian_mulVec_injective (ε : ℕ → ℕ → F) (r : ℕ)
    (hodd : ringChar F ≠ 2) (hε : ∀ m < r, ε m 1 = 1) :
    ∀ y y' : Fin r → F,
      (positiveMixedHessian ε r).mulVec y = (positiveMixedHessian ε r).mulVec y' → y = y' :=
  mulVec_injective_of_triangular _
    (positiveMixedHessian_upper_zero ε r)
    (positiveMixedHessian_diag_ne_zero ε r hodd hε)

/-! ## The negative imbalance grid -/

/-- Negative-grid left response, interpreted in the finite field. -/
def UnegF (m i j : ℕ) : F := (Uneg m i j : ℤ)

/-- Negative-grid right response, interpreted in the finite field. -/
def VnegF (s n i j : ℕ) : F := (Vneg s n i j : ℤ)

/-- Above the triangular part, no negative-grid left and right responses can meet. -/
theorem UnegF_mul_VnegF_eq_zero_of_lt
    (s m n i jU jV : ℕ) (hmn : m < n) :
    UnegF (F := F) m i jU * VnegF (F := F) s n i jV = 0 := by
  by_cases hU : Uneg m i jU = 0
  · simp [UnegF, hU]
  by_cases hV : Vneg s n i jV = 0
  · simp [VnegF, hV]
  have hUi : i + jU ≤ m := Uneg_cone hU
  have hVi : n ≤ i := Vneg_cone hV
  omega

/-- The mixed part of the negative cell finite difference, Eq. (6.22).
The constant term `3 * ε_(i,j+1)^2` has zero mixed Hessian and is omitted. -/
def negativeCellMixed (ε : ℕ → ℕ → F) (s m n i j : ℕ) : F :=
  2 * (3 * ε i (j + 1) - ε i j) *
      (UnegF (F := F) m i (j + 1) * VnegF (F := F) s n i (j + 1)) -
    2 * ε i (j + 1) *
      (UnegF (F := F) m i j * VnegF (F := F) s n i (j + 1) +
        VnegF (F := F) s n i j * UnegF (F := F) m i (j + 1))

/-- `negativeCellMixed` is literally the mixed finite difference of the
quadratic cell contribution in Eq. (6.22). -/
theorem negativeCellMixed_eq_mixedUnitDifference
    (ε : ℕ → ℕ → F) (s m n i j : ℕ) (c d : F) :
    negativeCellMixed ε s m n i j =
      mixedUnitDifference (fun L R =>
        (3 * ε i (j + 1) - ε i j) *
            (d + UnegF (F := F) m i (j + 1) * L +
              VnegF (F := F) s n i (j + 1) * R) ^ 2 -
          2 * ε i (j + 1) *
            (c + UnegF (F := F) m i j * L +
              VnegF (F := F) s n i j * R) *
            (d + UnegF (F := F) m i (j + 1) * L +
              VnegF (F := F) s n i (j + 1) * R)) := by
  unfold negativeCellMixed mixedUnitDifference
  ring

/-- The explicit `s × (s+1)` negative mixed Hessian. -/
def negativeMixedHessian (ε : ℕ → ℕ → F) (s : ℕ) :
    Matrix (Fin s) (Fin (s + 1)) F :=
  fun m n => ∑ i : Fin s, ∑ j : Fin s,
    negativeCellMixed ε s m n i j

/-- **Eq. (6.24).** The negative mixed Hessian vanishes above its first
`s × s` lower-triangular block. -/
theorem negativeMixedHessian_upper_zero (ε : ℕ → ℕ → F) (s : ℕ)
    (m : Fin s) (n : Fin (s + 1)) (hmn : (m : ℕ) < (n : ℕ)) :
    negativeMixedHessian ε s m n = 0 := by
  classical
  unfold negativeMixedHessian
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have h01 := UnegF_mul_VnegF_eq_zero_of_lt
    (F := F) s m n i j (j + 1) hmn
  have h10 := UnegF_mul_VnegF_eq_zero_of_lt
    (F := F) s m n i (j + 1) j hmn
  have h11 := UnegF_mul_VnegF_eq_zero_of_lt
    (F := F) s m n i (j + 1) (j + 1) hmn
  have h10' :
      VnegF (F := F) s n i j * UnegF (F := F) m i (j + 1) = 0 := by
    rw [mul_comm, h10]
  unfold negativeCellMixed
  rw [h11, h01, h10']
  ring

/-- A shifted left response cannot meet a right response on the diagonal. -/
theorem UnegF_succ_mul_VnegF_diag_zero
    (s m i j jV : ℕ) :
    UnegF (F := F) m i (j + 1) * VnegF (F := F) s m i jV = 0 := by
  by_cases hU : Uneg m i (j + 1) = 0
  · simp [UnegF, hU]
  by_cases hV : Vneg s m i jV = 0
  · simp [VnegF, hV]
  have hUi : i + (j + 1) ≤ m := Uneg_cone hU
  have hVi : m ≤ i := Vneg_cone hV
  omega

/-- An unshifted left response can meet a diagonal right response only at
the extremal cell `(m,0)`. -/
theorem UnegF_mul_VnegF_diag_zero_of_ne
    (s m i j jV : ℕ) (hne : (i, j) ≠ (m, 0)) :
    UnegF (F := F) m i j * VnegF (F := F) s m i jV = 0 := by
  by_cases hU : Uneg m i j = 0
  · simp [UnegF, hU]
  by_cases hV : Vneg s m i jV = 0
  · simp [VnegF, hV]
  have hUi : i + j ≤ m := Uneg_cone hU
  have hVi : m ≤ i := Vneg_cone hV
  exfalso
  apply hne
  apply Prod.ext <;> omega

/-- Away from `(m,0)`, every diagonal negative-cell contribution vanishes. -/
theorem negativeCellMixed_diag_zero_of_ne (ε : ℕ → ℕ → F)
    (s m i j : ℕ) (hne : (i, j) ≠ (m, 0)) :
    negativeCellMixed ε s m m i j = 0 := by
  have h01 := UnegF_mul_VnegF_diag_zero_of_ne
    (F := F) s m i j (j + 1) hne
  have h10 := UnegF_succ_mul_VnegF_diag_zero
    (F := F) s m i j j
  have h11 := UnegF_succ_mul_VnegF_diag_zero
    (F := F) s m i j (j + 1)
  have h10' :
      VnegF (F := F) s m i j * UnegF (F := F) m i (j + 1) = 0 := by
    rw [mul_comm, h10]
  unfold negativeCellMixed
  rw [h11, h01, h10']
  ring

/-- **Eq. (6.25).** With the marked-source displacement from Eq. (6.17),
the diagonal is `-2*(-1)^(s-1-m)`. -/
theorem negativeMixedHessian_diag (ε : ℕ → ℕ → F) (s : ℕ)
    (hε : ∀ m < s, ε m 1 = (-1 : F) ^ (s - 1 - m)) (m : Fin s) :
    negativeMixedHessian ε s m (Fin.castSucc m) =
      -2 * (-1 : F) ^ (s - 1 - (m : ℕ)) := by
  classical
  let j0 : Fin s := ⟨0, Nat.zero_lt_of_lt m.isLt⟩
  unfold negativeMixedHessian
  rw [Finset.sum_eq_single m]
  · rw [Finset.sum_eq_single j0]
    · have hm : (m : ℕ) < s := m.isLt
      have hs : 1 ≤ s := by omega
      simp [negativeCellMixed, UnegF, VnegF, Uneg, Vneg, j0,
        hε m m.isLt, hs]
    · intro j hj hjne
      apply negativeCellMixed_diag_zero_of_ne
      intro hp
      apply hjne
      apply Fin.ext
      simpa [j0] using congrArg Prod.snd hp
    · simp
  · intro i hi hine
    apply Finset.sum_eq_zero
    intro j hj
    apply negativeCellMixed_diag_zero_of_ne
    intro hp
    apply hine
    apply Fin.ext
    simpa using congrArg Prod.fst hp
  · simp

/-- **Eq. (6.26).** The extra right boundary direction is a zero column. -/
theorem negativeMixedHessian_lastColumn (ε : ℕ → ℕ → F) (s : ℕ)
    (m : Fin s) :
    negativeMixedHessian ε s m (Fin.last s) = 0 := by
  apply negativeMixedHessian_upper_zero
  simp

/-- The nonsquare Hessian restricted to its first `s` columns. -/
def negativeMixedHessianSquare (ε : ℕ → ℕ → F) (s : ℕ) :
    Matrix (Fin s) (Fin s) F :=
  fun m n => negativeMixedHessian ε s m (Fin.castSucc n)

/-- The first `s` columns form a lower-triangular matrix. -/
theorem negativeMixedHessianSquare_upper_zero (ε : ℕ → ℕ → F) (s : ℕ)
    (m n : Fin s) (hmn : m < n) :
    negativeMixedHessianSquare ε s m n = 0 :=
  negativeMixedHessian_upper_zero ε s m (Fin.castSucc n) hmn

/-- In odd characteristic, every diagonal entry of the square restriction is nonzero. -/
theorem negativeMixedHessianSquare_diag_ne_zero (ε : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hε : ∀ m < s, ε m 1 = (-1 : F) ^ (s - 1 - m)) (m : Fin s) :
    negativeMixedHessianSquare ε s m m ≠ 0 := by
  rw [negativeMixedHessianSquare, negativeMixedHessian_diag ε s hε m]
  exact mul_ne_zero (neg_ne_zero.mpr (two_ne_zero_of_odd_char hodd))
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- The first `s` columns of the negative mixed Hessian give an injective map. -/
theorem negativeMixedHessianSquare_mulVec_injective
    (ε : ℕ → ℕ → F) (s : ℕ) (hodd : ringChar F ≠ 2)
    (hε : ∀ m < s, ε m 1 = (-1 : F) ^ (s - 1 - m)) :
    ∀ y y' : Fin s → F,
      (negativeMixedHessianSquare ε s).mulVec y =
        (negativeMixedHessianSquare ε s).mulVec y' → y = y' :=
  mulVec_injective_of_triangular _
    (negativeMixedHessianSquare_upper_zero ε s)
    (negativeMixedHessianSquare_diag_ne_zero ε s hodd hε)

/-- Multiplication by the nonsquare Hessian depends only on its first `s`
coordinates; the last coordinate is killed by Eq. (6.26). -/
theorem negativeMixedHessian_mulVec_eq_square
    (ε : ℕ → ℕ → F) (s : ℕ) (y : Fin (s + 1) → F) :
    (negativeMixedHessian ε s).mulVec y =
      (negativeMixedHessianSquare ε s).mulVec (fun n => y (Fin.castSucc n)) := by
  funext m
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp [negativeMixedHessianSquare, negativeMixedHessian_lastColumn]

/-- A vector is killed by the negative mixed Hessian exactly when all of its
first `s` coordinates vanish. -/
theorem negativeMixedHessian_mulVec_eq_zero_iff
    (ε : ℕ → ℕ → F) (s : ℕ) (hodd : ringChar F ≠ 2)
    (hε : ∀ m < s, ε m 1 = (-1 : F) ^ (s - 1 - m))
    (y : Fin (s + 1) → F) :
    (negativeMixedHessian ε s).mulVec y = 0 ↔
      ∀ n : Fin s, y (Fin.castSucc n) = 0 := by
  rw [negativeMixedHessian_mulVec_eq_square]
  constructor
  · intro hy
    have hinj := negativeMixedHessianSquare_mulVec_injective ε s hodd hε
      (fun n => y (Fin.castSucc n)) 0
    have hz : (negativeMixedHessianSquare ε s).mulVec
        (fun n => y (Fin.castSucc n)) =
        (negativeMixedHessianSquare ε s).mulVec 0 := by simpa using hy
    have hv := hinj hz
    intro n
    exact congrFun hv n
  · intro hy
    apply funext
    intro m
    simp [Matrix.mulVec, dotProduct, hy]

/-- A vector supported on the final coordinate. -/
def lastCoordinateVector (s : ℕ) (a : F) : Fin (s + 1) → F :=
  fun n => if n = Fin.last s then a else 0

/-- **Eq. (6.27), kernel statement.** The kernel of the negative mixed
Hessian consists exactly of the multiples of its final coordinate vector. -/
theorem negativeMixedHessian_kernel_iff
    (ε : ℕ → ℕ → F) (s : ℕ) (hodd : ringChar F ≠ 2)
    (hε : ∀ m < s, ε m 1 = (-1 : F) ^ (s - 1 - m))
    (y : Fin (s + 1) → F) :
    (negativeMixedHessian ε s).mulVec y = 0 ↔
      y = lastCoordinateVector s (y (Fin.last s)) := by
  rw [negativeMixedHessian_mulVec_eq_zero_iff ε s hodd hε]
  constructor
  · intro hy
    funext n
    rcases Fin.eq_castSucc_or_eq_last n with ⟨k, rfl⟩ | rfl
    · simp [lastCoordinateVector, hy]
    · simp [lastCoordinateVector]
  · intro hy n
    rw [hy]
    simp [lastCoordinateVector]

end SqrtOpEnt
