import RequestProject.FlatSpectrumEntropy
import RequestProject.MixedHessian

/-!
# Entropy of the explicit residual mixed-Hessian cores

The manuscript's source constraint removes one right coordinate in each
branch.  We first record a convenient coordinate hyperplane by padding a
vector with a final zero.  We then parameterize the literal right-only source
equations using the response coefficients from `ResponseCones.lean`.  The
triangular calculations in `MixedHessian.lean` supply exactly the injectivity
hypothesis needed by the finite-field Fourier calculation in
`FlatSpectrumEntropy.lean`.

This proves the flat rank and von Neumann entropy of the explicit residual
cores.  The separate identification of a concrete count block of `X_t` with
one of these Fourier matrices remains the next bridge.
-/

namespace SqrtOpEnt

open Matrix

variable {F : Type*} [Field F]

/-- Include an `n`-component vector in `n+1` components with final coordinate
zero.  This is the canonical representative of the constrained right space. -/
def padLastZero (n : ℕ) (x : Fin n → F) : Fin (n + 1) → F :=
  Fin.lastCases 0 x

@[simp]
theorem padLastZero_castSucc (n : ℕ) (x : Fin n → F) (i : Fin n) :
    padLastZero n x (Fin.castSucc i) = x i := by
  simp [padLastZero]

@[simp]
theorem padLastZero_last (n : ℕ) (x : Fin n → F) :
    padLastZero n x (Fin.last n) = 0 := by
  simp [padLastZero]

theorem padLastZero_injective (n : ℕ) :
    Function.Injective (padLastZero (F := F) n) := by
  intro x y h
  funext i
  simpa using congrFun h (Fin.castSucc i)

/-! ## Positive imbalance -/

/-- The positive mixed Hessian stays injective after imposing the single
source constraint represented by `padLastZero`. -/
theorem positiveMixedHessian_padLastZero_injective
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    ∀ x y : Fin n → F,
      (positiveMixedHessian epsilon (n + 1)).mulVec (padLastZero n x) =
        (positiveMixedHessian epsilon (n + 1)).mulVec (padLastZero n y) →
      x = y := by
  intro x y h
  apply padLastZero_injective n
  exact positiveMixedHessian_mulVec_injective epsilon (n + 1) hodd hepsilon
    (padLastZero n x) (padLastZero n y) h

/-! ## Negative imbalance -/

/-- On the final-zero representatives, the negative rectangular Hessian is
the injective square block underlying the rank statement in Eq. (6.27). -/
theorem negativeMixedHessian_padLastZero_injective
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s, epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    ∀ x y : Fin s → F,
      (negativeMixedHessian epsilon s).mulVec (padLastZero s x) =
        (negativeMixedHessian epsilon s).mulVec (padLastZero s y) →
      x = y := by
  intro x y h
  rw [negativeMixedHessian_mulVec_eq_square,
    negativeMixedHessian_mulVec_eq_square] at h
  have h' :
      (negativeMixedHessianSquare epsilon s).mulVec x =
        (negativeMixedHessianSquare epsilon s).mulVec y := by
    simpa using h
  exact negativeMixedHessianSquare_mulVec_injective epsilon s hodd hepsilon x y h'

/-! ## Exact flat spectra -/

variable [Fintype F] [DecidableEq F]

/-- Positive residual core: rank `q^n` and von Neumann entropy `log(q^n)`.
Here `n=r-1`, matching the manuscript's positive-imbalance branch. -/
theorem positiveResidual_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    vonNeumannEntropy
        (fourierCoeff psi (positiveMixedHessian epsilon (n + 1))
          (padLastZero (F := F) n)) =
      Real.log ((Fintype.card F) ^ n) := by
  rw [fourierCoeff_vonNeumannEntropy psi hpsi _ _
    (positiveMixedHessian_padLastZero_injective epsilon n hodd hepsilon)]
  simp

/-- Positive residual core: exact operator Schmidt rank `q^n`. -/
theorem positiveResidual_operatorSchmidtRank
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    operatorSchmidtRank
        (fourierCoeff psi (positiveMixedHessian epsilon (n + 1))
          (padLastZero (F := F) n)) =
      (Fintype.card F) ^ n := by
  rw [fourierCoeff_operatorSchmidtRank psi hpsi _ _
    (positiveMixedHessian_padLastZero_injective epsilon n hodd hepsilon)]
  simp

/-- Negative residual core: rank `q^s` and von Neumann entropy `log(q^s)`.
The final zero coordinate removes precisely the one-dimensional kernel. -/
theorem negativeResidual_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s, epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    vonNeumannEntropy
        (fourierCoeff psi (negativeMixedHessian epsilon s)
          (padLastZero (F := F) s)) =
      Real.log ((Fintype.card F) ^ s) := by
  rw [fourierCoeff_vonNeumannEntropy psi hpsi _ _
    (negativeMixedHessian_padLastZero_injective epsilon s hodd hepsilon)]
  simp

/-- Negative residual core: exact operator Schmidt rank `q^s`. -/
theorem negativeResidual_operatorSchmidtRank
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s, epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    operatorSchmidtRank
        (fourierCoeff psi (negativeMixedHessian epsilon s)
          (padLastZero (F := F) s)) =
      (Fintype.card F) ^ s := by
  rw [fourierCoeff_operatorSchmidtRank psi hpsi _ _
    (negativeMixedHessian_padLastZero_injective epsilon s hodd hepsilon)]
  simp

/-! ## The literal source hyperplanes from the boundary responses -/

/-- Boundary-response reconstruction of a positive-grid field value. -/
def positiveBoundaryValue (r : ℕ) (L R : Fin r → F) (i j : ℕ) : F :=
  (∑ m : Fin r, UposF (F := F) m i j * L m) +
    ∑ n : Fin r, VposF (F := F) r n i j * R n

omit [Fintype F] [DecidableEq F] in
/-- The closed response formula has the prescribed right-boundary value. -/
theorem positiveBoundaryValue_right (r : ℕ) (L R : Fin r → F) (i : Fin r) :
    positiveBoundaryValue r L R i r = R i := by
  classical
  have hU (m : Fin r) : UposF (F := F) m i r = 0 := by
    unfold UposF Upos
    rw [if_neg (by omega)]
    norm_num
  have hV (n : Fin r) :
      VposF (F := F) r n i r = if n = i then 1 else 0 := by
    unfold VposF Vpos
    by_cases hni : n = i
    · subst n
      rw [if_pos (by omega)]
      simp
    · by_cases hle : (n : ℕ) ≤ i
      · rw [if_pos (by omega)]
        have hz : (r - r).choose ((i : ℕ) - n) = 0 := by
          apply Nat.choose_eq_zero_of_lt
          simp only [Nat.sub_self]
          omega
        rw [hz, if_neg hni]
        norm_num
      · rw [if_neg (by omega), if_neg hni]
        norm_num
  unfold positiveBoundaryValue
  simp only [hU, zero_mul, Finset.sum_const_zero, zero_add, hV]
  rw [Finset.sum_eq_single i]
  · simp
  · intro n hn hne
    simp [hne]
  · simp

omit [Fintype F] [DecidableEq F] in
/-- Backward recurrence at the top row of the positive grid. -/
theorem positiveBoundaryValue_top (r : ℕ) (L R : Fin r → F)
    (j : ℕ) (hj : j < r) :
    positiveBoundaryValue r L R 0 j =
      L ⟨j, hj⟩ - positiveBoundaryValue r L R 0 (j + 1) := by
  classical
  have hU (m : Fin r) : UposF (F := F) m 0 j =
      (if j = (m : ℕ) then 1 else 0) - UposF (F := F) m 0 (j + 1) := by
    unfold UposF
    rw [Upos_rec_top]
    split_ifs <;> push_cast <;> ring
  have hV (n : Fin r) : VposF (F := F) r n 0 j =
      -VposF (F := F) r n 0 (j + 1) := by
    unfold VposF
    rw [Vpos_rec_top r n  j hj]
    push_cast
    ring
  have hdelta :
      (∑ m : Fin r, (if j = (m : ℕ) then (1 : F) else 0) * L m) =
        L ⟨j, hj⟩ := by
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro m hm hne
      have hv : j ≠ (m : ℕ) := by
        intro h
        apply hne
        exact Fin.ext h.symm
      simp [hv]
    · simp
  unfold positiveBoundaryValue
  simp_rw [hU, hV, sub_mul, neg_mul, Finset.sum_sub_distrib]
  rw [hdelta]
  rw [Finset.sum_neg_distrib]
  ring

omit [Fintype F] [DecidableEq F] in
/-- Backward recurrence at every interior row of the positive grid. -/
theorem positiveBoundaryValue_rec (r : ℕ) (L R : Fin r → F)
    (i j : ℕ) (_hi : i + 1 < r) (hj : j < r) :
    positiveBoundaryValue r L R (i + 1) j =
      positiveBoundaryValue r L R i (j + 1) -
        positiveBoundaryValue r L R (i + 1) (j + 1) := by
  classical
  have hU (m : Fin r) : UposF (F := F) m (i + 1) j =
      UposF (F := F) m i (j + 1) -
        UposF (F := F) m (i + 1) (j + 1) := by
    unfold UposF
    rw [Upos_rec]
    push_cast
    ring
  have hV (n : Fin r) : VposF (F := F) r n (i + 1) j =
      VposF (F := F) r n i (j + 1) -
        VposF (F := F) r n (i + 1) (j + 1) := by
    unfold VposF
    rw [Vpos_rec r n i j hj]
    push_cast
    ring
  unfold positiveBoundaryValue
  simp_rw [hU, hV, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Positive source equation `a_(r-1,1)=0`, expressed in right-boundary
coordinates.  The left-boundary contribution vanishes by `Upos_source`. -/
def positiveSourceFunctional (r : ℕ) (R : Fin r → F) : F :=
  ∑ i : Fin r, VposF (F := F) r i (r - 1) 1 * R i

omit [Fintype F] [DecidableEq F] in
/-- No left response reaches the marked positive source variable, so its
reconstructed value is exactly the right-only source functional. -/
theorem positiveBoundaryValue_at_source (n : ℕ)
    (L R : Fin (n + 1) → F) :
    positiveBoundaryValue (n + 1) L R n 1 =
      positiveSourceFunctional (F := F) (n + 1) R := by
  unfold positiveBoundaryValue positiveSourceFunctional
  have hzero : ∀ m : Fin (n + 1), UposF (F := F) m n 1 = 0 := by
    intro m
    change ((Upos m n 1 : ℤ) : F) = 0
    have hz : Upos m n 1 = 0 := by
      simpa using Upos_source (n + 1) m (by omega)
    rw [hz]
    norm_num
  simp [hzero]

/-- Parameterize the positive source hyperplane at size `r=n+1` by solving
for `R_0`; its coefficient is one by `Vpos_extremal`. -/
def positiveAllowedRight (n : ℕ) (x : Fin n → F) : Fin (n + 1) → F :=
  Fin.cases
    (-∑ i : Fin n, VposF (F := F) (n + 1) i.succ n 1 * x i)
    x

omit [Fintype F] [DecidableEq F] in
theorem VposF_source_zero (n : ℕ) :
    VposF (F := F) (n + 1) (0 : Fin (n + 1)) (n + 1 - 1) 1 = 1 := by
  change ((Vpos (n + 1) 0 n 1 : ℤ) : F) = 1
  have hz : Vpos (n + 1) 0 n 1 = 1 := by
    simpa using Vpos_extremal (n + 1) (by omega)
  rw [hz]
  norm_num

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem positiveAllowedRight_zero (n : ℕ) (x : Fin n → F) :
    positiveAllowedRight n x 0 =
      -∑ i : Fin n, VposF (F := F) (n + 1) i.succ n 1 * x i := by
  simp [positiveAllowedRight]

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem positiveAllowedRight_succ (n : ℕ) (x : Fin n → F) (i : Fin n) :
    positiveAllowedRight n x i.succ = x i := by
  simp [positiveAllowedRight]

omit [Fintype F] [DecidableEq F] in
/-- The displayed parameterization satisfies the actual positive source
constraint. -/
theorem positiveAllowedRight_mem_sourceHyperplane (n : ℕ) (x : Fin n → F) :
    positiveSourceFunctional (F := F) (n + 1) (positiveAllowedRight n x) = 0 := by
  rw [positiveSourceFunctional, Fin.sum_univ_succ]
  rw [VposF_source_zero]
  simp

omit [Fintype F] [DecidableEq F] in
theorem positiveAllowedRight_injective (n : ℕ) :
    Function.Injective (positiveAllowedRight (F := F) n) := by
  intro x y h
  funext i
  simpa using congrFun h i.succ

/-- The literal positive source hyperplane. -/
abbrev PositiveSourceHyperplane (n : ℕ) :=
  {R : Fin (n + 1) → F // positiveSourceFunctional (F := F) (n + 1) R = 0}

/-- Solving for `R_0` is a bijective parameterization of the positive source
hyperplane, so it contains exactly `q^n` boundary configurations. -/
def positiveAllowedRightEquiv (n : ℕ) :
    (Fin n → F) ≃ PositiveSourceHyperplane (F := F) n where
  toFun x := ⟨positiveAllowedRight n x,
    positiveAllowedRight_mem_sourceHyperplane n x⟩
  invFun R := fun i => R.1 i.succ
  left_inv x := by
    funext i
    simp
  right_inv R := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => by simp) i
    have h := R.2
    rw [positiveSourceFunctional, Fin.sum_univ_succ,
      VposF_source_zero] at h
    simp only [one_mul] at h
    change positiveAllowedRight n (fun i => R.1 i.succ) 0 = R.1 0
    rw [positiveAllowedRight_zero]
    exact (eq_neg_of_add_eq_zero_left h).symm

theorem card_positiveSourceHyperplane (n : ℕ) :
    Fintype.card (PositiveSourceHyperplane (F := F) n) =
      (Fintype.card F) ^ n := by
  rw [← Fintype.card_congr (positiveAllowedRightEquiv (F := F) n)]
  simp

/-- Negative source equation `c_(s,0)=0`, expressed in right-boundary
coordinates.  Its final coefficient is one by `Vneg_extremal`. -/
def negativeBoundaryValue (s : ℕ) (L : Fin s → F)
    (R : Fin (s + 1) → F) (i j : ℕ) : F :=
  (∑ m : Fin s, UnegF (F := F) m i j * L m) +
    ∑ n : Fin (s + 1), VnegF (F := F) s n i j * R n

omit [Fintype F] [DecidableEq F] in
/-- The negative closed response formula has the prescribed final-column
boundary value. -/
theorem negativeBoundaryValue_right (s : ℕ) (L : Fin s → F)
    (R : Fin (s + 1) → F) (i : Fin (s + 1)) :
    negativeBoundaryValue s L R i s = R i := by
  classical
  have hU (m : Fin s) : UnegF (F := F) m i s = 0 := by
    unfold UnegF Uneg
    rw [if_neg (by omega)]
    norm_num
  have hV (n : Fin (s + 1)) :
      VnegF (F := F) s n i s = if n = i then 1 else 0 := by
    unfold VnegF Vneg
    by_cases hni : n = i
    · subst n
      rw [if_pos (by omega)]
      simp
    · by_cases hle : (n : ℕ) ≤ i
      · rw [if_pos (by omega)]
        have hz : (s - s).choose ((i : ℕ) - n) = 0 := by
          apply Nat.choose_eq_zero_of_lt
          simp only [Nat.sub_self]
          omega
        rw [hz, if_neg hni]
        norm_num
      · rw [if_neg (by omega), if_neg hni]
        norm_num
  unfold negativeBoundaryValue
  simp only [hU, zero_mul, Finset.sum_const_zero, zero_add, hV]
  rw [Finset.sum_eq_single i]
  · simp
  · intro n hn hne
    simp [hne]
  · simp

omit [Fintype F] [DecidableEq F] in
/-- Backward recurrence at the upper row of the negative grid. -/
theorem negativeBoundaryValue_top (s : ℕ) (L : Fin s → F)
    (R : Fin (s + 1) → F) (j : ℕ) (hj : j < s) :
    negativeBoundaryValue s L R 0 j =
      L ⟨j, hj⟩ + negativeBoundaryValue s L R 0 (j + 1) := by
  classical
  have hU (m : Fin s) : UnegF (F := F) m 0 j =
      (if j = (m : ℕ) then 1 else 0) + UnegF (F := F) m 0 (j + 1) := by
    unfold UnegF
    rw [Uneg_rec_top]
    split_ifs <;> push_cast <;> ring
  have hV (n : Fin (s + 1)) : VnegF (F := F) s n 0 j =
      VnegF (F := F) s n 0 (j + 1) := by
    unfold VnegF
    rw [Vneg_rec_top s n j hj]
  have hdelta :
      (∑ m : Fin s, (if j = (m : ℕ) then (1 : F) else 0) * L m) =
        L ⟨j, hj⟩ := by
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro m hm hne
      have hv : j ≠ (m : ℕ) := by
        intro h
        apply hne
        exact Fin.ext h.symm
      simp [hv]
    · simp
  unfold negativeBoundaryValue
  simp_rw [hU, hV, add_mul, Finset.sum_add_distrib]
  rw [hdelta]
  ring

omit [Fintype F] [DecidableEq F] in
/-- Backward recurrence at every lower row of the negative grid. -/
theorem negativeBoundaryValue_rec (s : ℕ) (L : Fin s → F)
    (R : Fin (s + 1) → F) (i j : ℕ)
    (_hi : i + 1 < s + 1) (hj : j < s) :
    negativeBoundaryValue s L R (i + 1) j =
      negativeBoundaryValue s L R i (j + 1) +
        negativeBoundaryValue s L R (i + 1) (j + 1) := by
  classical
  have hU (m : Fin s) : UnegF (F := F) m (i + 1) j =
      UnegF (F := F) m i (j + 1) +
        UnegF (F := F) m (i + 1) (j + 1) := by
    unfold UnegF
    rw [Uneg_rec]
    push_cast
    ring
  have hV (n : Fin (s + 1)) : VnegF (F := F) s n (i + 1) j =
      VnegF (F := F) s n i (j + 1) +
        VnegF (F := F) s n (i + 1) (j + 1) := by
    unfold VnegF
    rw [Vneg_rec s n i j hj]
    push_cast
    ring
  unfold negativeBoundaryValue
  simp_rw [hU, hV, add_mul, Finset.sum_add_distrib]
  ring

def negativeSourceFunctional (s : ℕ) (R : Fin (s + 1) → F) : F :=
  ∑ i : Fin (s + 1), VnegF (F := F) s i s 0 * R i

omit [Fintype F] [DecidableEq F] in
/-- No left response reaches the marked negative source variable, so its
reconstructed value is exactly the right-only source functional. -/
theorem negativeBoundaryValue_at_source (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    negativeBoundaryValue s L R s 0 = negativeSourceFunctional (F := F) s R := by
  unfold negativeBoundaryValue negativeSourceFunctional
  have hzero : ∀ m : Fin s, UnegF (F := F) m s 0 = 0 := by
    intro m
    unfold UnegF
    rw [Uneg_source s m m.isLt]
    norm_num
  simp [hzero]

/-- Parameterize the negative source hyperplane by solving for its final
coordinate `R_s`. -/
def negativeAllowedRight (s : ℕ) (x : Fin s → F) : Fin (s + 1) → F :=
  Fin.lastCases
    (-∑ i : Fin s, VnegF (F := F) s (Fin.castSucc i) s 0 * x i)
    x

omit [Fintype F] [DecidableEq F] in
theorem VnegF_source_last (s : ℕ) :
    VnegF (F := F) s (Fin.last s) s 0 = 1 := by
  simp [VnegF, Vneg_extremal]

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem negativeAllowedRight_castSucc (s : ℕ) (x : Fin s → F) (i : Fin s) :
    negativeAllowedRight s x (Fin.castSucc i) = x i := by
  simp [negativeAllowedRight]

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem negativeAllowedRight_last (s : ℕ) (x : Fin s → F) :
    negativeAllowedRight s x (Fin.last s) =
      -∑ i : Fin s, VnegF (F := F) s (Fin.castSucc i) s 0 * x i := by
  simp [negativeAllowedRight]

omit [Fintype F] [DecidableEq F] in
/-- The displayed parameterization satisfies the actual negative source
constraint. -/
theorem negativeAllowedRight_mem_sourceHyperplane (s : ℕ) (x : Fin s → F) :
    negativeSourceFunctional (F := F) s (negativeAllowedRight s x) = 0 := by
  rw [negativeSourceFunctional, Fin.sum_univ_castSucc]
  rw [VnegF_source_last]
  simp

omit [Fintype F] [DecidableEq F] in
theorem negativeAllowedRight_injective (s : ℕ) :
    Function.Injective (negativeAllowedRight (F := F) s) := by
  intro x y h
  funext i
  simpa using congrFun h (Fin.castSucc i)

/-- The literal negative source hyperplane. -/
abbrev NegativeSourceHyperplane (s : ℕ) :=
  {R : Fin (s + 1) → F // negativeSourceFunctional (F := F) s R = 0}

/-- Solving for `R_s` is a bijective parameterization of the negative source
hyperplane, so it contains exactly `q^s` boundary configurations. -/
def negativeAllowedRightEquiv (s : ℕ) :
    (Fin s → F) ≃ NegativeSourceHyperplane (F := F) s where
  toFun x := ⟨negativeAllowedRight s x,
    negativeAllowedRight_mem_sourceHyperplane s x⟩
  invFun R := fun i => R.1 (Fin.castSucc i)
  left_inv x := by
    funext i
    simp
  right_inv R := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => by simp) i
    have h := R.2
    rw [negativeSourceFunctional, Fin.sum_univ_castSucc,
      VnegF_source_last] at h
    simp only [one_mul] at h
    change negativeAllowedRight s (fun i => R.1 (Fin.castSucc i)) (Fin.last s) =
      R.1 (Fin.last s)
    rw [negativeAllowedRight_last]
    exact (eq_neg_of_add_eq_zero_right h).symm

theorem card_negativeSourceHyperplane (s : ℕ) :
    Fintype.card (NegativeSourceHyperplane (F := F) s) =
      (Fintype.card F) ^ s := by
  rw [← Fintype.card_congr (negativeAllowedRightEquiv (F := F) s)]
  simp

omit [Fintype F] [DecidableEq F] in
/-- The positive Hessian is injective on the literal response-defined source
hyperplane. -/
theorem positiveMixedHessian_allowedRight_injective
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    ∀ x y : Fin n → F,
      (positiveMixedHessian epsilon (n + 1)).mulVec (positiveAllowedRight n x) =
        (positiveMixedHessian epsilon (n + 1)).mulVec (positiveAllowedRight n y) →
      x = y := by
  intro x y h
  apply positiveAllowedRight_injective n
  exact positiveMixedHessian_mulVec_injective epsilon (n + 1) hodd hepsilon
    (positiveAllowedRight n x) (positiveAllowedRight n y) h

omit [Fintype F] [DecidableEq F] in
/-- The negative Hessian is injective on the literal response-defined source
hyperplane, because equality of its first `s` coordinates already determines
the boundary parameter. -/
theorem negativeMixedHessian_allowedRight_injective
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s, epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    ∀ x y : Fin s → F,
      (negativeMixedHessian epsilon s).mulVec (negativeAllowedRight s x) =
        (negativeMixedHessian epsilon s).mulVec (negativeAllowedRight s y) →
      x = y := by
  intro x y h
  rw [negativeMixedHessian_mulVec_eq_square,
    negativeMixedHessian_mulVec_eq_square] at h
  have h' :
      (negativeMixedHessianSquare epsilon s).mulVec x =
        (negativeMixedHessianSquare epsilon s).mulVec y := by
    simpa using h
  exact negativeMixedHessianSquare_mulVec_injective epsilon s hodd hepsilon x y h'

/-- Positive response-defined residual core: exact von Neumann entropy
`log(q^n)`, where `n=r-1`. -/
theorem positiveSourceHyperplane_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    vonNeumannEntropy
        (fourierCoeff psi (positiveMixedHessian epsilon (n + 1))
          (positiveAllowedRight (F := F) n)) =
      Real.log ((Fintype.card F) ^ n) := by
  rw [fourierCoeff_vonNeumannEntropy psi hpsi _ _
    (positiveMixedHessian_allowedRight_injective epsilon n hodd hepsilon)]
  simp

/-- Manuscript form `(r-1) log q` of the positive residual entropy. -/
theorem positiveSourceHyperplane_vonNeumannEntropy_eq_mul
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    vonNeumannEntropy
        (fourierCoeff psi (positiveMixedHessian epsilon (n + 1))
          (positiveAllowedRight (F := F) n)) =
      (n : ℝ) * Real.log (Fintype.card F) := by
  rw [positiveSourceHyperplane_vonNeumannEntropy psi hpsi epsilon n hodd hepsilon,
    Real.log_pow]

/-- Positive response-defined residual core: exact Schmidt rank `q^n`. -/
theorem positiveSourceHyperplane_operatorSchmidtRank
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    operatorSchmidtRank
        (fourierCoeff psi (positiveMixedHessian epsilon (n + 1))
          (positiveAllowedRight (F := F) n)) =
      (Fintype.card F) ^ n := by
  rw [fourierCoeff_operatorSchmidtRank psi hpsi _ _
    (positiveMixedHessian_allowedRight_injective epsilon n hodd hepsilon)]
  simp

/-- Negative response-defined residual core: exact von Neumann entropy
`log(q^s)`. -/
theorem negativeSourceHyperplane_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s, epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    vonNeumannEntropy
        (fourierCoeff psi (negativeMixedHessian epsilon s)
          (negativeAllowedRight (F := F) s)) =
      Real.log ((Fintype.card F) ^ s) := by
  rw [fourierCoeff_vonNeumannEntropy psi hpsi _ _
    (negativeMixedHessian_allowedRight_injective epsilon s hodd hepsilon)]
  simp

/-- Manuscript form `s log q` of the negative residual entropy. -/
theorem negativeSourceHyperplane_vonNeumannEntropy_eq_mul
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s, epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    vonNeumannEntropy
        (fourierCoeff psi (negativeMixedHessian epsilon s)
          (negativeAllowedRight (F := F) s)) =
      (s : ℝ) * Real.log (Fintype.card F) := by
  rw [negativeSourceHyperplane_vonNeumannEntropy psi hpsi epsilon s hodd hepsilon,
    Real.log_pow]

/-- Negative response-defined residual core: exact Schmidt rank `q^s`. -/
theorem negativeSourceHyperplane_operatorSchmidtRank
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s, epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    operatorSchmidtRank
        (fourierCoeff psi (negativeMixedHessian epsilon s)
          (negativeAllowedRight (F := F) s)) =
      (Fintype.card F) ^ s := by
  rw [fourierCoeff_operatorSchmidtRank psi hpsi _ _
    (negativeMixedHessian_allowedRight_injective epsilon s hodd hepsilon)]
  simp

end SqrtOpEnt
