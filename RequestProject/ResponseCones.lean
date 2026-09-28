import RequestProject.FlatSpectrum

/-!
# Boundary response functions and triangular mixed Hessians

This file formalizes the combinatorial content of Lemma 6.3 and the linear-algebra
content of Lemma 6.4 of the manuscript.

The backward shear recurrence of the positive imbalance grid, Eq. (6.6),
`a_{i,j} = a_{i-1,j+1} - a_{i,j+1}`, is solved by the explicit responses of Eq. (6.12)
and (6.13),

`U^{(m)}_{i,j} = (-1)^{m-j-i} C(m-j, i)`,  `V^{(n)}_{i,j} = (-1)^{r-j-i+n} C(r-j, i-n)`,

and the negative grid, Eq. (6.10), is solved by the same formulas without signs,
Eqs. (6.15), (6.16).  We verify the recurrences together with the boundary data, and
the **one-sided response cones** of Eq. (6.11),

`U^{(m)}_{i,j} ≠ 0 ⟹ i + j ≤ m`,   `V^{(n)}_{i,j} ≠ 0 ⟹ i ≥ n`,

which are the only inputs (besides the extremal coefficients and the invertibility of `2`
in odd characteristic) needed for the triangularity of the mixed Hessian in Lemma 6.4.
The final step of Lemma 6.4 — a triangular matrix with nonvanishing diagonal has full
rank, so the mixed map is injective and Theorem 6.5 applies — is `mulVec_injective_of_triangular`.
-/

namespace SqrtOpEnt

open Finset Matrix

/-! ### Positive grid -/

/-- Response of the positive grid to the top boundary variable `L_m`, Eq. (6.12). -/
def Upos (m i j : ℕ) : ℤ := if i + j ≤ m then (-1)^(m - j - i) * ((m-j).choose i) else 0

/-- Response of the positive grid to the right boundary variable `R_n`, Eq. (6.13). -/
def Vpos (r n i j : ℕ) : ℤ :=
  if n ≤ i ∧ j ≤ r then (-1)^((r - j + n) - i) * ((r-j).choose (i-n)) else 0

/-- **Eq. (6.11), first cone.**  A top response reaches only cells with `i + j ≤ m`. -/
theorem Upos_cone {m i j : ℕ} (h : Upos m i j ≠ 0) : i + j ≤ m := by
  by_contra hc
  exact h (by simp [Upos, hc])

/-- **Eq. (6.11), second cone.**  A right response lives only in rows `i ≥ n`. -/
theorem Vpos_cone {r n i j : ℕ} (h : Vpos r n i j ≠ 0) : n ≤ i := by
  by_contra hc
  exact h (by simp [Vpos, hc])

/-- The backward recurrence (6.18) for the top responses, interior rows. -/
theorem Upos_rec (m i j : ℕ) : Upos m (i+1) j = Upos m i (j+1) - Upos m (i+1) (j+1) := by
  unfold Upos
  by_cases h1 : i + 1 + j ≤ m
  · by_cases h3 : i + 1 + (j+1) ≤ m
    · rw [if_pos h1, if_pos (show i + (j+1) ≤ m by omega), if_pos h3]
      have hp : ((m-j).choose (i+1) : ℤ)
          = ((m-(j+1)).choose i : ℤ) + ((m-(j+1)).choose (i+1) : ℤ) := by
        have hmj : m - j = (m - (j+1)) + 1 := by omega
        rw [hmj, Nat.choose_succ_succ]
        push_cast
        ring
      have he1 : m - (j+1) - i = m - j - (i+1) := by omega
      have he2 : m - j - (i+1) = (m - (j+1) - (i+1)) + 1 := by omega
      rw [he1, he2, pow_succ, hp]
      ring
    · rw [if_pos h1, if_pos (show i + (j+1) ≤ m by omega), if_neg h3]
      have hA : m - j = i + 1 := by omega
      have hB : m - (j+1) = i := by omega
      rw [hA, hB]
      simp
  · rw [if_neg h1, if_neg (show ¬ (i + (j+1) ≤ m) by omega),
      if_neg (show ¬ (i + 1 + (j+1) ≤ m) by omega)]
    ring

/-- The recurrence at the top row, where the incoming value is the boundary datum `L_j`
(a Kronecker delta in the label `m`). -/
theorem Upos_rec_top (m j : ℕ) :
    Upos m 0 j = (if j = m then 1 else 0) - Upos m 0 (j+1) := by
  unfold Upos
  by_cases hj : j ≤ m
  · rcases eq_or_lt_of_le hj with rfl | hlt
    · rw [if_pos (show 0 + j ≤ j by omega), if_neg (show ¬ (0 + (j+1) ≤ j) by omega),
        if_pos rfl]
      simp
    · rw [if_pos (show 0 + j ≤ m by omega), if_pos (show 0 + (j+1) ≤ m by omega),
        if_neg (show ¬ (j = m) by omega)]
      have he : m - j - 0 = (m - (j+1) - 0) + 1 := by omega
      rw [he, pow_succ]
      simp
  · rw [if_neg (show ¬ (0 + j ≤ m) by omega), if_neg (show ¬ (0 + (j+1) ≤ m) by omega),
      if_neg (show ¬ (j = m) by omega)]
    ring

/-- The positive right-boundary responses satisfy the same backward
recurrence away from the final boundary column. -/
theorem Vpos_rec (r n i j : ℕ) (hj : j < r) :
    Vpos r n (i + 1) j =
      Vpos r n i (j + 1) - Vpos r n (i + 1) (j + 1) := by
  unfold Vpos
  by_cases hni : n ≤ i
  · rw [if_pos (by omega : n ≤ i + 1 ∧ j ≤ r),
      if_pos (by omega : n ≤ i ∧ j + 1 ≤ r),
      if_pos (by omega : n ≤ i + 1 ∧ j + 1 ≤ r)]
    have hrj : r - j = (r - (j + 1)) + 1 := by omega
    have hk : i + 1 - n = (i - n) + 1 := by omega
    by_cases hsupp : i + 1 - n ≤ r - (j + 1)
    · have hpow : r - j + n - (i + 1) =
          r - (j + 1) + n - i := by omega
      have hpow' : r - (j + 1) + n - i =
          (r - (j + 1) + n - (i + 1)) + 1 := by omega
      rw [hpow, hrj, hk, Nat.choose_succ_succ, hpow', pow_succ]
      push_cast
      ring

    · by_cases hedge : i + 1 - n = r - j
      · have hk0 : i - n = r - (j + 1) := by omega
        have hpow0 : r - j + n - (i + 1) = 0 := by omega
        have hpow1 : r - (j + 1) + n - i = 0 := by omega
        have hz2 : (r - (j + 1)).choose (i + 1 - n) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        rw [hz2, hedge, Nat.choose_self, hk0, Nat.choose_self, hpow0, hpow1]
        norm_num
      · have hz0 : (r - j).choose (i + 1 - n) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have hz1 : (r - (j + 1)).choose (i - n) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have hz2 : (r - (j + 1)).choose (i + 1 - n) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        rw [hz0, hz1, hz2]
        norm_num
  · by_cases hnext : n = i + 1
    · subst n
      rw [if_pos (by omega : i + 1 ≤ i + 1 ∧ j ≤ r),
        if_neg (by omega : ¬ (i + 1 ≤ i ∧ j + 1 ≤ r)),
        if_pos (by omega : i + 1 ≤ i + 1 ∧ j + 1 ≤ r)]
      have hpow : r - j + (i + 1) - (i + 1) = r - j := by omega
      have hpow' : r - (j + 1) + (i + 1) - (i + 1) = r - (j + 1) := by
        omega
      have hrj : r - j = (r - (j + 1)) + 1 := by omega
      simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
      rw [hpow, hpow', hrj, pow_succ]
      ring
    · rw [if_neg (by omega : ¬ (n ≤ i + 1 ∧ j ≤ r)),
        if_neg (by omega : ¬ (n ≤ i ∧ j + 1 ≤ r)),
        if_neg (by omega : ¬ (n ≤ i + 1 ∧ j + 1 ≤ r))]
      ring

/-- At the top row the positive right response has zero incoming boundary
datum, hence only the minus recurrence remains. -/
theorem Vpos_rec_top (r n j : ℕ) (hj : j < r) :
    Vpos r n 0 j = -Vpos r n 0 (j + 1) := by
  unfold Vpos
  by_cases hn : n = 0
  · subst n
    rw [if_pos (by omega : 0 ≤ 0 ∧ j ≤ r),
      if_pos (by omega : 0 ≤ 0 ∧ j + 1 ≤ r)]
    have hrj : r - j = (r - (j + 1)) + 1 := by omega
    simp only [Nat.add_zero, Nat.sub_zero, Nat.choose_zero_right]
    rw [hrj, pow_succ]
    ring
  · rw [if_neg (by omega : ¬ (n ≤ 0 ∧ j ≤ r)),
      if_neg (by omega : ¬ (n ≤ 0 ∧ j + 1 ≤ r))]
    simp

/-- The extremal right response used in Lemma 6.4: `V^{(0)}_{r-1,1} = 1`. -/
theorem Vpos_extremal (r : ℕ) (hr : 1 ≤ r) : Vpos r 0 (r-1) 1 = 1 := by
  unfold Vpos
  rw [if_pos (by omega)]
  have h1 : r - 1 + 0 - (r-1) = 0 := by omega
  rw [h1]
  simp

/-- No top response reaches the source cell of the positive grid: `U^{(m)}_{r-1,1} = 0`
for every `m < r`. -/
theorem Upos_source (r m : ℕ) (hm : m < r) : Upos m (r-1) 1 = 0 := by
  unfold Upos
  rw [if_neg (by omega)]

/-! ### Negative grid -/

/-- Response of the negative grid to the left boundary variable `L_m`, Eq. (6.15). -/
def Uneg (m i j : ℕ) : ℤ := if i + j ≤ m then ((m-j).choose i : ℤ) else 0

/-- Response of the negative grid to the right boundary variable `R_n`, Eq. (6.16). -/
def Vneg (s n i j : ℕ) : ℤ := if n ≤ i ∧ j ≤ s then ((s-j).choose (i-n) : ℤ) else 0

theorem Uneg_cone {m i j : ℕ} (h : Uneg m i j ≠ 0) : i + j ≤ m := by
  by_contra hc
  exact h (by simp [Uneg, hc])

theorem Vneg_cone {s n i j : ℕ} (h : Vneg s n i j ≠ 0) : n ≤ i := by
  by_contra hc
  exact h (by simp [Vneg, hc])

/-- The recurrence (6.10) for the negative grid: the same Pascal induction without signs. -/
theorem Uneg_rec (m i j : ℕ) : Uneg m (i+1) j = Uneg m i (j+1) + Uneg m (i+1) (j+1) := by
  unfold Uneg
  by_cases h1 : i + 1 + j ≤ m
  · by_cases h3 : i + 1 + (j+1) ≤ m
    · rw [if_pos h1, if_pos (show i + (j+1) ≤ m by omega), if_pos h3]
      have hmj : m - j = (m - (j+1)) + 1 := by omega
      rw [hmj, Nat.choose_succ_succ]
      push_cast
      ring
    · rw [if_pos h1, if_pos (show i + (j+1) ≤ m by omega), if_neg h3]
      have hA : m - j = i + 1 := by omega
      have hB : m - (j+1) = i := by omega
      rw [hA, hB]
      simp
  · rw [if_neg h1, if_neg (show ¬ (i + (j+1) ≤ m) by omega),
      if_neg (show ¬ (i + 1 + (j+1) ≤ m) by omega)]
    ring

/-- Top-row boundary recurrence for the negative left responses. -/
theorem Uneg_rec_top (m j : ℕ) :
    Uneg m 0 j = (if j = m then 1 else 0) + Uneg m 0 (j + 1) := by
  unfold Uneg
  by_cases hj : j ≤ m
  · rcases eq_or_lt_of_le hj with rfl | hlt
    · rw [if_pos (by omega : 0 + j ≤ j),
        if_neg (by omega : ¬ (0 + (j + 1) ≤ j)), if_pos rfl]
      simp
    · rw [if_pos (by omega : 0 + j ≤ m),
        if_pos (by omega : 0 + (j + 1) ≤ m),
        if_neg (by omega : ¬ (j = m))]
      simp
  · rw [if_neg (by omega : ¬ (0 + j ≤ m)),
      if_neg (by omega : ¬ (0 + (j + 1) ≤ m)),
      if_neg (by omega : ¬ (j = m))]
    simp

/-- The negative right-boundary responses obey the plus-sign backward
recurrence away from the final boundary column. -/
theorem Vneg_rec (s n i j : ℕ) (hj : j < s) :
    Vneg s n (i + 1) j =
      Vneg s n i (j + 1) + Vneg s n (i + 1) (j + 1) := by
  unfold Vneg
  by_cases hni : n ≤ i
  · rw [if_pos (by omega : n ≤ i + 1 ∧ j ≤ s),
      if_pos (by omega : n ≤ i ∧ j + 1 ≤ s),
      if_pos (by omega : n ≤ i + 1 ∧ j + 1 ≤ s)]
    have hsj : s - j = (s - (j + 1)) + 1 := by omega
    have hk : i + 1 - n = (i - n) + 1 := by omega
    by_cases hsupp : i + 1 - n ≤ s - j
    · rw [hsj, hk, Nat.choose_succ_succ]
      push_cast
      ring

    · have hz0 : (s - j).choose (i + 1 - n) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      have hz1 : (s - (j + 1)).choose (i - n) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      have hz2 : (s - (j + 1)).choose (i + 1 - n) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [hz0, hz1, hz2]
      norm_num
  · by_cases hnext : n = i + 1
    · subst n
      rw [if_pos (by omega : i + 1 ≤ i + 1 ∧ j ≤ s),
        if_neg (by omega : ¬ (i + 1 ≤ i ∧ j + 1 ≤ s)),
        if_pos (by omega : i + 1 ≤ i + 1 ∧ j + 1 ≤ s)]
      simp
    · rw [if_neg (by omega : ¬ (n ≤ i + 1 ∧ j ≤ s)),
        if_neg (by omega : ¬ (n ≤ i ∧ j + 1 ≤ s)),
        if_neg (by omega : ¬ (n ≤ i + 1 ∧ j + 1 ≤ s))]
      ring

/-- At the top row the negative right response propagates unchanged. -/
theorem Vneg_rec_top (s n j : ℕ) (hj : j < s) :
    Vneg s n 0 j = Vneg s n 0 (j + 1) := by
  unfold Vneg
  by_cases hn : n = 0
  · subst n
    rw [if_pos (by omega : 0 ≤ 0 ∧ j ≤ s),
      if_pos (by omega : 0 ≤ 0 ∧ j + 1 ≤ s)]
    simp
  · rw [if_neg (by omega : ¬ (n ≤ 0 ∧ j ≤ s)),
      if_neg (by omega : ¬ (n ≤ 0 ∧ j + 1 ≤ s))]

/-- The extremal right response of the negative grid: `V^{(s)}_{s,0} = 1`. -/
theorem Vneg_extremal (s : ℕ) : Vneg s s s 0 = 1 := by
  unfold Vneg
  rw [if_pos (by omega)]
  simp

/-- No left response reaches the source cell of the negative grid: `U^{(m)}_{s,0} = 0`
for `m < s`. -/
theorem Uneg_source (s m : ℕ) (hm : m < s) : Uneg m s 0 = 0 := by
  unfold Uneg
  rw [if_neg (by omega)]

/-! ### Lemma 6.4: triangularity gives full mixed rank -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- In odd characteristic the diagonal coefficient `±2` of the mixed Hessian is invertible;
this is exactly where Subsection 3.5 uses `q` odd. -/
theorem two_ne_zero_of_odd_char (h : ringChar F ≠ 2) : (2 : F) ≠ 0 := Ring.two_ne_zero h

omit [Fintype F] [DecidableEq F] in
/-- **Lemma 6.4 (conclusion).**  A lower-triangular mixed Hessian with nonvanishing
diagonal has full rank, hence is injective on every set of allowed right configurations —
the hypothesis of the flat-spectrum theorem `fourierCoeff_conjTranspose_mul`. -/
theorem mulVec_injective_of_triangular {n : ℕ} (K : Matrix (Fin n) (Fin n) F)
    (htri : ∀ i j, i < j → K i j = 0) (hdiag : ∀ i, K i i ≠ 0) :
    ∀ y y' : Fin n → F, K.mulVec y = K.mulVec y' → y = y' := by
  have hdet : K.det = ∏ i, K i i := Matrix.det_of_lowerTriangular K (fun i j hij => htri i j hij)
  have hne : K.det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)
  exact mulVec_injective_of_isUnit (isUnit_iff_ne_zero.mpr hne)

end SqrtOpEnt
