import RequestProject.GridPhase

/-!
# The literal rectangle as a residual shear grid

This file connects the response-grid recurrences to the adjacent-gate word
used in `rectangularCore`.  We first move the finite circuit to total
natural-number arrays.  This removes `Fin` coercions from the row-by-row
calculation while preserving both the support permutation and its accumulated
finite-field exponent.
-/

namespace SqrtOpEnt

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local instance : Inhabited F := ⟨0⟩
local instance : Inhabited (Vq F) := ⟨Sum.inl 0⟩

/-- The triangular support update on two adjacent positions of a total
natural-number array. -/
def natGateAt (i : ℕ) (v : ℕ → Vq F) : ℕ → Vq F :=
  fun p => if p = i then (gateFun F (v i, v (i + 1))).1
    else if p = i + 1 then (gateFun F (v i, v (i + 1))).2
    else v p

/-- Apply total-array triangular gates in list order. -/
def natGateCircuit : List ℕ → (ℕ → Vq F) → (ℕ → Vq F)
  | [], v => v
  | i :: tail, v => natGateCircuit tail (natGateAt i v)

/-- Finite and total support updates agree at every valid address. -/
theorem extendFin_gateAtFun (n i : ℕ) (h : i + 1 < n)
    (v : SpatialBasis F n) :
    extendFin n (gateAtFun F n i v) = natGateAt i (extendFin n v) := by
  classical
  funext p
  by_cases hp : p < n
  · by_cases hpi : p = i
    · subst p
      have hi : i < n := by omega
      simp [extendFin, gateAtFun, natGateAt, h, hi]
    · by_cases hpis : p = i + 1
      · subst p
        have hne : (⟨i, by omega⟩ : Fin n) ≠ ⟨i + 1, h⟩ := by
          intro he
          have := congrArg Fin.val he
          change i = i + 1 at this
          omega
        have hi : i < n := by omega
        simp [extendFin, gateAtFun, natGateAt, h, hi, hne]
      · have hp_i : (⟨p, hp⟩ : Fin n) ≠ ⟨i, by omega⟩ := by
          intro he
          exact hpi (congrArg Fin.val he)
        have hp_is : (⟨p, hp⟩ : Fin n) ≠ ⟨i + 1, h⟩ := by
          intro he
          exact hpis (congrArg Fin.val he)
        simp [extendFin, gateAtFun, natGateAt, h, hp, hpi, hpis, hp_i, hp_is]
  · have hpi : p ≠ i := by omega
    have hpis : p ≠ i + 1 := by omega
    simp [extendFin, natGateAt, hp, hpi, hpis]

/-- A finite support circuit agrees with the total-array circuit when every
gate address is valid. -/
theorem extendFin_spatialCircuitPerm (n : ℕ) (word : List ℕ)
    (v : SpatialBasis F n) (hvalid : ∀ i ∈ word, i + 1 < n) :
    extendFin n (spatialCircuitPerm F n word v) =
      natGateCircuit word (extendFin n v) := by
  induction word generalizing v with
  | nil => rfl
  | cons i tail ih =>
      change extendFin n
          (spatialCircuitPerm F n tail (gateAtFun F n i v)) =
        natGateCircuit tail (natGateAt i (extendFin n v))
      rw [ih (gateAtFun F n i v) (by
        intro j hj
        exact hvalid j (by simp [hj]))]
      rw [extendFin_gateAtFun n i (hvalid i (by simp))]

/-- Total-array form of one local finite-field exponent. -/
def natGateAtExponent (i : ℕ) (v : ℕ → Vq F) : F :=
  gateExponent F (v i, v (i + 1))

/-- Accumulated total-array exponent in the same head-first convention as
`spatialCircuitExponent`. -/
def natGateCircuitExponent : List ℕ → (ℕ → Vq F) → F
  | [], _ => 0
  | i :: tail, v =>
      natGateCircuitExponent tail (natGateAt i v) + natGateAtExponent i v

/-- The finite and total exponent calculations agree for a valid word. -/
theorem spatialCircuitExponent_eq_nat (n : ℕ) (word : List ℕ)
    (v : SpatialBasis F n) (hvalid : ∀ i ∈ word, i + 1 < n) :
    spatialCircuitExponent F n word v =
      natGateCircuitExponent word (extendFin n v) := by
  induction word generalizing v with
  | nil => rfl
  | cons i tail ih =>
      simp only [spatialCircuitExponent, natGateCircuitExponent]
      change spatialCircuitExponent F n tail (gateAtFun F n i v) +
          gateAtExponent F n i v =
        natGateCircuitExponent tail (natGateAt i (extendFin n v)) +
          natGateAtExponent i (extendFin n v)
      rw [ih (gateAtFun F n i v) (by
        intro j hj
        exact hvalid j (by simp [hj]))]
      have hi := hvalid i (by simp)
      rw [extendFin_gateAtFun n i hi]
      unfold gateAtExponent natGateAtExponent
      rw [dif_pos hi]
      have hil : i < n := by omega
      simp [extendFin, hil, hi]

/-- Total support evolution respects concatenation of gate words. -/
theorem natGateCircuit_append (u v : List ℕ) (z : ℕ → Vq F) :
    natGateCircuit (u ++ v) z = natGateCircuit v (natGateCircuit u z) := by
  induction u generalizing z with
  | nil => rfl
  | cons i tail ih =>
      simp only [List.cons_append, natGateCircuit]
      rw [ih]

/-- The total accumulated exponent splits over concatenated gate words. -/
theorem natGateCircuitExponent_append (u v : List ℕ)
    (z : ℕ → Vq F) :
    natGateCircuitExponent (u ++ v) z =
      natGateCircuitExponent v (natGateCircuit u z) +
        natGateCircuitExponent u z := by
  induction u generalizing z with
  | nil => simp [natGateCircuit, natGateCircuitExponent]
  | cons i tail ih =>
      simp only [List.cons_append, natGateCircuit, natGateCircuitExponent]
      rw [ih]
      ring

/-! ## One inverse-shear row -/

/-- A row before an `A` strand is moved left across `r` consecutive `B`
strands.  The relation `B_j = a_j + a_(j+1)` is exactly the positive-grid
backward recurrence. -/
def positiveRowInput (b r : ℕ) (a : ℕ → F) (z : ℕ → Vq F) :
    ℕ → Vq F :=
  fun p => if b ≤ p ∧ p < b + r then
      Sum.inr (a (p - b) + a (p - b + 1))
    else if p = b + r then Sum.inl (a r)
    else z p

/-- The same row after the descending adjacent word: the moving `A` value
is `a_0`, and the displaced `B` values are `a_1,…,a_r`. -/
def positiveRowOutput (b r : ℕ) (a : ℕ → F) (z : ℕ → Vq F) :
    ℕ → Vq F :=
  fun p => if p = b then Sum.inl (a 0)
    else if b < p ∧ p ≤ b + r then Sum.inr (a (p - b))
    else z p

/-- The first gate of a row exposes the shorter row input and stores the
rightmost displaced `B` value in the ambient configuration. -/
theorem natGateAt_positiveRowInput_succ (b r : ℕ)
    (a : ℕ → F) (z : ℕ → Vq F) :
    natGateAt (b + r) (positiveRowInput b (r + 1) a z) =
      positiveRowInput b r a
        (fun p => if p = b + r + 1 then
          (Sum.inr (a (r + 1)) : Vq F) else z p) := by
  funext p
  unfold natGateAt
  by_cases hp0 : p = b + r
  · subst p
    rw [if_pos rfl]
    have hleft : positiveRowInput b (r + 1) a z (b + r) =
        Sum.inr (a r + a (r + 1)) := by
      simp [positiveRowInput]
    have hright : positiveRowInput b (r + 1) a z (b + r + 1) =
        Sum.inl (a (r + 1)) := by
      unfold positiveRowInput
      rw [if_neg (by omega), if_pos (by omega)]
    have hout : positiveRowInput b r a
        (fun p => if p = b + r + 1 then
          (Sum.inr (a (r + 1)) : Vq F) else z p)
        (b + r) = Sum.inl (a r) := by
      simp [positiveRowInput]
    rw [hleft, hright, hout]
    simp [gateFun]
  · by_cases hp1 : p = b + r + 1
    · subst p
      rw [if_neg (by omega : ¬ (b + r + 1 = b + r)), if_pos rfl]
      have hleft : positiveRowInput b (r + 1) a z (b + r) =
          Sum.inr (a r + a (r + 1)) := by
        simp [positiveRowInput]
      have hright : positiveRowInput b (r + 1) a z (b + r + 1) =
          Sum.inl (a (r + 1)) := by
        unfold positiveRowInput
        rw [if_neg (by omega), if_pos (by omega)]
      have hout : positiveRowInput b r a
          (fun p => if p = b + r + 1 then
            (Sum.inr (a (r + 1)) : Vq F) else z p)
          (b + r + 1) = Sum.inr (a (r + 1)) := by
        simp [positiveRowInput]
      rw [hleft, hright, hout]
      simp [gateFun]
    · rw [if_neg hp0, if_neg hp1]
      unfold positiveRowInput
      by_cases hp : b ≤ p ∧ p < b + r
      · rw [if_pos (by omega : b ≤ p ∧ p < b + (r + 1)), if_pos hp]
      · rw [if_neg (by omega : ¬ (b ≤ p ∧ p < b + (r + 1))),
          if_neg (by omega : ¬ (p = b + (r + 1))), if_neg hp,
          if_neg (by omega : ¬ (p = b + r))]
        simp [hp1]

/-- One descending gate word performs exactly one row of the positive
backward shear. -/
theorem natGateCircuit_descending_positiveRow (b r : ℕ)
    (a : ℕ → F) (z : ℕ → Vq F) :
    natGateCircuit (descendingSwaps b r) (positiveRowInput b r a z) =
      positiveRowOutput b r a z := by
  induction r generalizing z with
  | zero =>
      funext p
      by_cases hp : p = b
      · subst p
        simp [descendingSwaps, natGateCircuit, positiveRowInput,
          positiveRowOutput]
      · simp [descendingSwaps, natGateCircuit, positiveRowInput,
          positiveRowOutput, hp, show ¬ (b ≤ p ∧ p < b) by omega,
          show ¬ (b < p ∧ p ≤ b) by omega]
  | succ r ih =>
      rw [descendingSwaps_succ]
      simp only [natGateCircuit]
      let z' : ℕ → Vq F := fun p =>
        if p = b + r + 1 then Sum.inr (a (r + 1)) else z p
      have hstep :
          natGateAt (b + r) (positiveRowInput b (r + 1) a z) =
            positiveRowInput b r a z' := by
        funext p
        unfold natGateAt
        by_cases hp0 : p = b + r
        · subst p
          rw [if_pos rfl]
          change (gateFun F
              (positiveRowInput b (r + 1) a z (b + r),
              positiveRowInput b (r + 1) a z (b + r + 1))).1 =
            positiveRowInput b r a z' (b + r)
          have hleft : positiveRowInput b (r + 1) a z (b + r) =
              Sum.inr (a r + a (r + 1)) := by
            simp [positiveRowInput]
          have hright : positiveRowInput b (r + 1) a z (b + r + 1) =
              Sum.inl (a (r + 1)) := by
            unfold positiveRowInput
            rw [if_neg (by omega), if_pos (by omega)]
          have hout : positiveRowInput b r a z' (b + r) =
              Sum.inl (a r) := by
            simp [positiveRowInput]
          rw [hleft, hright, hout]
          simp [gateFun]
        · by_cases hp1 : p = b + r + 1
          · subst p
            rw [if_neg (by omega : ¬ (b + r + 1 = b + r)), if_pos rfl]
            change (gateFun F
                (positiveRowInput b (r + 1) a z (b + r),
                positiveRowInput b (r + 1) a z (b + r + 1))).2 =
              positiveRowInput b r a z' (b + r + 1)
            have hleft : positiveRowInput b (r + 1) a z (b + r) =
                Sum.inr (a r + a (r + 1)) := by
              simp [positiveRowInput]
            have hright : positiveRowInput b (r + 1) a z (b + r + 1) =
                Sum.inl (a (r + 1)) := by
              unfold positiveRowInput
              rw [if_neg (by omega), if_pos (by omega)]
            have hout : positiveRowInput b r a z' (b + r + 1) =
                Sum.inr (a (r + 1)) := by
              simp [positiveRowInput, z']
            rw [hleft, hright, hout]
            simp [gateFun]
          · rw [if_neg hp0, if_neg hp1]
            unfold positiveRowInput z'
            by_cases hp : b ≤ p ∧ p < b + r
            · rw [if_pos (by omega : b ≤ p ∧ p < b + (r + 1)), if_pos hp]
            · rw [if_neg (by omega : ¬ (b ≤ p ∧ p < b + (r + 1))),
                if_neg (by omega : ¬ (p = b + (r + 1))), if_neg hp,
                if_neg (by omega : ¬ (p = b + r)), if_neg hp1]
      rw [hstep, ih]
      funext p
      unfold positiveRowOutput z'
      by_cases hp0 : p = b
      · subst p
        simp
      · by_cases hp : b < p ∧ p ≤ b + r
        · rw [if_neg hp0, if_pos hp, if_neg hp0,
            if_pos (by omega : b < p ∧ p ≤ b + (r + 1))]
        · by_cases hp1 : p = b + r + 1
          · subst p
            rw [if_neg (by omega : ¬ (b + r + 1 = b)),
              if_neg (by omega : ¬ (b < b + r + 1 ∧ b + r + 1 ≤ b + r)),
              if_pos rfl, if_neg (by omega : ¬ (b + r + 1 = b)),
              if_pos (by omega : b < b + r + 1 ∧ b + r + 1 ≤ b + (r + 1))]
            rw [show b + r + 1 - b = r + 1 by omega]
          · rw [if_neg hp0, if_neg hp, if_neg hp1, if_neg hp0,
              if_neg (by omega : ¬ (b < p ∧ p ≤ b + (r + 1)))]

/-- The rightmost inverse crossing in a positive row contributes
`-a_r a_(r+1)^2`. -/
theorem natGateAtExponent_positiveRowInput_last (b r : ℕ)
    (a : ℕ → F) (z : ℕ → Vq F) :
    natGateAtExponent (b + r) (positiveRowInput b (r + 1) a z) =
      -(a r * (a (r + 1)) ^ 2) := by
  unfold natGateAtExponent
  have hleft : positiveRowInput b (r + 1) a z (b + r) =
      Sum.inr (a r + a (r + 1)) := by
    simp [positiveRowInput]
  have hright : positiveRowInput b (r + 1) a z (b + r + 1) =
      Sum.inl (a (r + 1)) := by
    unfold positiveRowInput
    rw [if_neg (by omega), if_pos (by omega)]
  rw [hleft, hright]
  simp [gateExponent]

/-- The exponent accumulated along one inverse-shear row is the negative
cubic row phase. -/
theorem natGateCircuitExponent_descending_positiveRow (b r : ℕ)
    (a : ℕ → F) (z : ℕ → Vq F) :
    natGateCircuitExponent (descendingSwaps b r) (positiveRowInput b r a z) =
      -∑ j ∈ Finset.range r, a j * (a (j + 1)) ^ 2 := by
  induction r generalizing z with
  | zero => simp [descendingSwaps, natGateCircuitExponent]
  | succ r ih =>
      rw [descendingSwaps_succ]
      simp only [natGateCircuitExponent]
      rw [natGateAt_positiveRowInput_succ]
      rw [ih]
      rw [natGateAtExponent_positiveRowInput_last]
      rw [Finset.sum_range_succ]
      ring

/-! ## The complete positive rectangle -/

/-- Response-formula value with total natural-number boundary arrays. -/
def positiveGridValue (r : ℕ) (L R : ℕ → F) (i j : ℕ) : F :=
  positiveBoundaryValue r (fun m => L m) (fun n => R n) i j

/-- Exact total-array configuration after the first `b` rows of the
positive `r × r` inverse-shear rectangle. -/
def positiveAfterRows (r b : ℕ) (L R : ℕ → F) : ℕ → Vq F :=
  fun p => if p < b then Sum.inl (positiveGridValue r L R p 0)
    else if p < b + r then
      Sum.inr (if b = 0 then L (p - b)
        else positiveGridValue r L R (b - 1) (p - b + 1))
    else if p < r + r then Sum.inl (R (p - r))
    else default

/-- Before row `b`, the explicit intermediate configuration is precisely a
`positiveRowInput` for the `b`th response-grid row. -/
theorem positiveAfterRows_eq_rowInput (r b : ℕ) (hb : b < r)
    (L R : ℕ → F) :
    positiveAfterRows r b L R =
      positiveRowInput b r (fun j => positiveGridValue r L R b j)
        (positiveAfterRows r b L R) := by
  funext p
  unfold positiveRowInput
  by_cases hp : b ≤ p ∧ p < b + r
  · rw [if_pos hp]
    unfold positiveAfterRows
    rw [if_neg (by omega : ¬ (p < b)), if_pos hp.2]
    by_cases hb0 : b = 0
    · subst b
      rw [if_pos rfl]
      have htop := positiveBoundaryValue_top r
        (fun m : Fin r => L m) (fun n : Fin r => R n)
        p (by omega)
      change positiveGridValue r L R 0 p =
        L p - positiveGridValue r L R 0 (p + 1) at htop
      change Sum.inr (L p) = Sum.inr
        (positiveGridValue r L R 0 p + positiveGridValue r L R 0 (p + 1))
      apply congrArg (fun x : F => (Sum.inr x : Vq F))
      rw [htop]
      ring
    · rw [if_neg hb0]
      obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
      have hrec := positiveBoundaryValue_rec r
        (fun m : Fin r => L m) (fun n : Fin r => R n)
        c (p - (c + 1)) (by omega) (by omega)
      change positiveGridValue r L R (c + 1) (p - (c + 1)) =
          positiveGridValue r L R c (p - (c + 1) + 1) -
            positiveGridValue r L R (c + 1) (p - (c + 1) + 1) at hrec
      apply congrArg (fun x : F => (Sum.inr x : Vq F))
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right]
      rw [hrec]
      ring
  · rw [if_neg hp]
    by_cases hpr : p = b + r
    · subst p
      unfold positiveAfterRows
      rw [if_neg (by omega : ¬ (b + r < b)),
        if_neg (by omega : ¬ (b + r < b + r)),
        if_pos (by omega : b + r < r + r)]
      have hright := positiveBoundaryValue_right r
        (fun m : Fin r => L m) (fun n : Fin r => R n) ⟨b, hb⟩
      change positiveGridValue r L R b r = R b at hright
      rw [if_pos rfl]
      congr 1
      simpa [show b + r - r = b by omega] using hright.symm
    · rw [if_neg hpr]

/-- Completing row `b` advances the explicit intermediate configuration by
one row. -/
theorem positiveRowOutput_eq_afterRows_succ (r b : ℕ) (hb : b < r)
    (L R : ℕ → F) :
    positiveRowOutput b r (fun j => positiveGridValue r L R b j)
        (positiveAfterRows r b L R) =
      positiveAfterRows r (b + 1) L R := by
  funext p
  unfold positiveRowOutput positiveAfterRows
  by_cases hp0 : p = b
  · subst p
    rw [if_pos rfl, if_pos (by omega : b < b + 1)]
  · by_cases hp : b < p ∧ p ≤ b + r
    · rw [if_neg hp0, if_pos hp]
      rw [if_neg (by omega : ¬ (p < b + 1)),
        if_pos (by omega : p < b + 1 + r), if_neg (by omega : ¬ (b + 1 = 0))]
      congr 2
      omega
    · rw [if_neg hp0, if_neg hp]
      by_cases hleft : p < b
      · rw [if_pos hleft, if_pos (by omega : p < b + 1)]
      · by_cases hright : b + r < p
        · rw [if_neg (by omega : ¬ (p < b)),
            if_neg (by omega : ¬ (p < b + r)),
            if_neg (by omega : ¬ (p < b + 1)),
            if_neg (by omega : ¬ (p < b + 1 + r))]
        · exfalso
          omega

/-- The first `b` schedule rows evolve the positive boundary configuration
to the explicit `positiveAfterRows` state. -/
theorem natGateCircuit_crossingPrefix_positive (r b : ℕ) (hb : b ≤ r)
    (L R : ℕ → F) :
    natGateCircuit (crossingPrefix r b) (positiveAfterRows r 0 L R) =
      positiveAfterRows r b L R := by
  induction b with
  | zero => simp [crossingPrefix, natGateCircuit]
  | succ b ih =>
      rw [crossingPrefix_succ, natGateCircuit_append, ih (by omega)]
      rw [positiveAfterRows_eq_rowInput r b (by omega)]
      rw [natGateCircuit_descending_positiveRow]
      exact positiveRowOutput_eq_afterRows_succ r b (by omega) L R

/-- The exponent of the first `b` positive rows is the negative cubic grid
phase over those rows. -/
theorem natGateCircuitExponent_crossingPrefix_positive
    (r b : ℕ) (hb : b ≤ r) (L R : ℕ → F) :
    natGateCircuitExponent (crossingPrefix r b) (positiveAfterRows r 0 L R) =
      -∑ i ∈ Finset.range b, ∑ j ∈ Finset.range r,
        positiveGridValue r L R i j *
          (positiveGridValue r L R i (j + 1)) ^ 2 := by
  induction b with
  | zero => simp [crossingPrefix, natGateCircuitExponent]
  | succ b ih =>
      rw [crossingPrefix_succ, natGateCircuitExponent_append,
        natGateCircuit_crossingPrefix_positive r b (by omega),
        positiveAfterRows_eq_rowInput r b (by omega),
        natGateCircuitExponent_descending_positiveRow,
        ih (by omega), Finset.sum_range_succ]
      ring

/-- Full positive rectangle support calculation. -/
theorem natGateCircuit_crossingSchedule_positive (r : ℕ) (L R : ℕ → F) :
    natGateCircuit (crossingSchedule r) (positiveAfterRows r 0 L R) =
      positiveAfterRows r r L R := by
  rw [crossingSchedule_eq_prefix]
  exact natGateCircuit_crossingPrefix_positive r r (le_refl r) L R

/-- Full positive rectangle exponent calculation. -/
theorem natGateCircuitExponent_crossingSchedule_positive
    (r : ℕ) (L R : ℕ → F) :
    natGateCircuitExponent (crossingSchedule r) (positiveAfterRows r 0 L R) =
      -∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
        positiveGridValue r L R i j *
          (positiveGridValue r L R i (j + 1)) ^ 2 := by
  rw [crossingSchedule_eq_prefix]
  exact natGateCircuitExponent_crossingPrefix_positive r r (le_refl r) L R

/-! ## Transfer to the literal finite rectangle -/

/-- Positive residual boundary data in the spatial basis: `B^r | A^r`. -/
def positiveBoundarySpatial (r : ℕ) (L R : Fin r → F) :
    SpatialBasis F (r + r) :=
  fun p => if h : (p : ℕ) < r then Sum.inr (L ⟨p, h⟩)
    else Sum.inl (R ⟨(p : ℕ) - r, by omega⟩)

/-- The same boundary data grouped into the two packets used by
`rectangularCircuit`. -/
def positiveBoundaryRect (r : ℕ) (L R : Fin r → F) : RectBasis F r :=
  (packetsToSpatial F).symm (positiveBoundarySpatial r L R)

@[simp]
theorem packetsToSpatial_positiveBoundaryRect (r : ℕ) (L R : Fin r → F) :
    packetsToSpatial F (positiveBoundaryRect r L R) =
      positiveBoundarySpatial r L R := by
  simp [positiveBoundaryRect]

/-- In packet coordinates the positive boundary is literally a `B` packet
followed by an `A` packet. -/
theorem positiveBoundaryRect_eq (r : ℕ) (L R : Fin r → F) :
    positiveBoundaryRect r L R =
      ((fun i => Sum.inr (L i)), fun i => Sum.inl (R i)) := by
  apply (packetsToSpatial F).injective
  rw [packetsToSpatial_positiveBoundaryRect]
  funext p
  by_cases hp : (p : ℕ) < r
  · have hcast : p = Fin.castAdd r ⟨p, hp⟩ := by
      apply Fin.ext
      rfl
    change positiveBoundarySpatial r L R p =
      Fin.append (fun i => Sum.inr (L i)) (fun i => Sum.inl (R i)) p
    rw [show Fin.append (fun i => Sum.inr (L i)) (fun i => Sum.inl (R i)) p =
        Sum.inr (L ⟨p, hp⟩) by
      calc
        _ = Fin.append (fun i => Sum.inr (L i)) (fun i => Sum.inl (R i))
            (Fin.castAdd r ⟨p, hp⟩) := congrArg _ hcast
        _ = _ := Fin.append_left _ _ _]
    simp [positiveBoundarySpatial, hp]
  · have hsub : (p : ℕ) - r < r := by omega
    have hnat : p = Fin.natAdd r ⟨(p : ℕ) - r, hsub⟩ := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    change positiveBoundarySpatial r L R p =
      Fin.append (fun i => Sum.inr (L i)) (fun i => Sum.inl (R i)) p
    rw [show Fin.append (fun i => Sum.inr (L i)) (fun i => Sum.inl (R i)) p =
        Sum.inl (R ⟨(p : ℕ) - r, hsub⟩) by
      calc
        _ = Fin.append (fun i => Sum.inr (L i)) (fun i => Sum.inl (R i))
            (Fin.natAdd r ⟨(p : ℕ) - r, hsub⟩) := congrArg _ hnat
        _ = _ := Fin.append_right _ _ _]
    simp [positiveBoundarySpatial, hp]

/-- The finite positive boundary configuration extends to the initial total
grid configuration. -/
theorem extendFin_positiveBoundarySpatial (r : ℕ) (L R : Fin r → F) :
    extendFin (r + r) (positiveBoundarySpatial r L R) =
      positiveAfterRows r 0 (extendFin r L) (extendFin r R) := by
  funext p
  by_cases hp : p < r
  · have htot : p < r + r := by omega
    simp [extendFin, positiveBoundarySpatial, positiveAfterRows, hp, htot]
  · by_cases htot : p < r + r
    · have hsub : p - r < r := by omega
      simp [extendFin, positiveBoundarySpatial, positiveAfterRows, hp, htot, hsub]
    · simp [extendFin, positiveAfterRows, htot, hp]

/-- On positive residual boundary data, the literal finite support circuit
is the response-grid evolution. -/
theorem spatialCircuitPerm_positiveBoundary (r : ℕ) (L R : Fin r → F) :
    spatialCircuitPerm F (r + r) (crossingSchedule r)
        (positiveBoundarySpatial r L R) =
      fun p : Fin (r + r) =>
        positiveAfterRows r r (extendFin r L) (extendFin r R) p := by
  funext p
  have htransfer := extendFin_spatialCircuitPerm (F := F) (r + r)
    (crossingSchedule r) (positiveBoundarySpatial r L R)
    (fun i hi => mem_crossingSchedule_lt hi)
  rw [extendFin_positiveBoundarySpatial,
    natGateCircuit_crossingSchedule_positive] at htransfer
  have hp := congrFun htransfer (p : ℕ)
  simpa using hp

/-- The source-side packet configuration produced by a positive residual
rectangle.  The left output packet is the left edge of the response grid;
the right output packet is its bottom edge with the corner omitted. -/
def positiveSourceRect (r : ℕ) (L R : Fin r → F) : RectBasis F r :=
  (fun i => Sum.inl (positiveBoundaryValue r L R i 0),
    fun j => Sum.inr (positiveBoundaryValue r L R (r - 1) (j + 1)))

/-- The literal support permutation sends positive boundary coordinates to
the two source-side edges of the response grid. -/
theorem rectangularCircuitPerm_positiveBoundary
    (r : ℕ) (L R : Fin r → F) :
    rectangularCircuitPerm F r (positiveBoundaryRect r L R) =
      positiveSourceRect r L R := by
  apply (packetsToSpatial F).injective
  simp only [rectangularCircuitPerm, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [packetsToSpatial_positiveBoundaryRect,
    spatialCircuitPerm_positiveBoundary]
  funext p
  by_cases hp : (p : ℕ) < r
  · have hcast : p = Fin.castAdd r ⟨p, hp⟩ := by
      apply Fin.ext
      rfl
    have hout : packetsToSpatial F (positiveSourceRect r L R) p =
        Sum.inl (positiveBoundaryValue r L R (p : ℕ) 0) := by
      change Fin.append (positiveSourceRect r L R).1
          (positiveSourceRect r L R).2 p = _
      rw [hcast, Fin.append_left]
      simp [positiveSourceRect]
    rw [hout]
    simp [positiveAfterRows, hp, positiveGridValue, extendFin]
  · have hsub : (p : ℕ) - r < r := by omega
    have hr : r ≠ 0 := by omega
    have hnat : p = Fin.natAdd r ⟨(p : ℕ) - r, hsub⟩ := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    have hout : packetsToSpatial F (positiveSourceRect r L R) p =
        Sum.inr (positiveBoundaryValue r L R (r - 1) ((p : ℕ) - r + 1)) := by
      change Fin.append (positiveSourceRect r L R).1
          (positiveSourceRect r L R).2 p = _
      rw [hnat, Fin.append_right]
      simp only [positiveSourceRect]
      congr 3
      omega
    rw [hout]
    simp [positiveAfterRows, hp, hsub, hr, positiveGridValue, extendFin]

/-! ## The marked positive source displacement -/

/-- The source-side pair whose right packet differs at exactly its marked
site.  Here we retain only the ket-minus-bra displacement: all unmarked
labels are zero and the marked `B` label is one. -/
def positiveUnitSource (n : ℕ) : RectBasis F (n + 1) :=
  (fun _ => Sum.inl 0,
    fun i => Sum.inr (if i = 0 then 1 else 0))

/-- Pull the marked source displacement backwards through the support
permutation. -/
def positiveUnitBoundary (n : ℕ) : RectBasis F (n + 1) :=
  (rectangularCircuitPerm F (n + 1)).symm (positiveUnitSource n)

/-- Left boundary labels of the pulled-back marked source displacement. -/
def positiveUnitDeltaL (n : ℕ) : Fin (n + 1) → F :=
  fun i => siteLabel F ((positiveUnitBoundary (F := F) n).1 i)

/-- Right boundary labels of the pulled-back marked source displacement. -/
def positiveUnitDeltaR (n : ℕ) : Fin (n + 1) → F :=
  fun i => siteLabel F ((positiveUnitBoundary (F := F) n).2 i)

theorem siteColour_positiveUnitBoundary_fst (n : ℕ) (i : Fin (n + 1)) :
    siteColour F ((positiveUnitBoundary (F := F) n).1 i) = .B := by
  have h := (siteColour_rectangularCircuitPerm_snd F (n + 1)
    (positiveUnitBoundary (F := F) n) i).symm
  simpa [positiveUnitBoundary, positiveUnitSource] using h

theorem siteColour_positiveUnitBoundary_snd (n : ℕ) (i : Fin (n + 1)) :
    siteColour F ((positiveUnitBoundary (F := F) n).2 i) = .A := by
  have h := (siteColour_rectangularCircuitPerm_fst F (n + 1)
    (positiveUnitBoundary (F := F) n) i).symm
  simpa [positiveUnitBoundary, positiveUnitSource] using h

theorem positiveUnitBoundary_fst_eq (n : ℕ) (i : Fin (n + 1)) :
    (positiveUnitBoundary (F := F) n).1 i =
      Sum.inr (positiveUnitDeltaL (F := F) n i) := by
  cases hval : (positiveUnitBoundary (F := F) n).1 i with
  | inl a =>
      have hcolour := siteColour_positiveUnitBoundary_fst (F := F) n i
      rw [hval] at hcolour
      contradiction
  | inr b =>
      simp [positiveUnitDeltaL, siteLabel, hval]

theorem positiveUnitBoundary_snd_eq (n : ℕ) (i : Fin (n + 1)) :
    (positiveUnitBoundary (F := F) n).2 i =
      Sum.inl (positiveUnitDeltaR (F := F) n i) := by
  cases hval : (positiveUnitBoundary (F := F) n).2 i with
  | inl a =>
      simp [positiveUnitDeltaR, siteLabel, hval]
  | inr b =>
      have hcolour := siteColour_positiveUnitBoundary_snd (F := F) n i
      rw [hval] at hcolour
      contradiction

/-- The field labels extracted from the inverse image really give the
positive `B^(n+1) | A^(n+1)` boundary configuration. -/
theorem positiveBoundaryRect_unitDelta (n : ℕ) :
    positiveBoundaryRect (n + 1) (positiveUnitDeltaL (F := F) n)
        (positiveUnitDeltaR (F := F) n) =
      positiveUnitBoundary (F := F) n := by
  apply (packetsToSpatial F).injective
  rw [packetsToSpatial_positiveBoundaryRect]
  funext p
  by_cases hp : (p : ℕ) < n + 1
  · have hcast : p = Fin.castAdd (n + 1) ⟨p, hp⟩ := by
      apply Fin.ext
      rfl
    have hout : packetsToSpatial F (positiveUnitBoundary (F := F) n) p =
        (positiveUnitBoundary (F := F) n).1 ⟨p, hp⟩ := by
      change Fin.append (positiveUnitBoundary (F := F) n).1
          (positiveUnitBoundary (F := F) n).2 p = _
      calc
        _ = Fin.append (positiveUnitBoundary (F := F) n).1
            (positiveUnitBoundary (F := F) n).2
            (Fin.castAdd (n + 1) ⟨p, hp⟩) := congrArg _ hcast
        _ = _ := Fin.append_left _ _ _
    rw [hout, positiveUnitBoundary_fst_eq]
    simp [positiveBoundarySpatial, hp]
  · have hsub : (p : ℕ) - (n + 1) < n + 1 := by omega
    have hnat : p = Fin.natAdd (n + 1) ⟨(p : ℕ) - (n + 1), hsub⟩ := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    have hout : packetsToSpatial F (positiveUnitBoundary (F := F) n) p =
        (positiveUnitBoundary (F := F) n).2
          ⟨(p : ℕ) - (n + 1), hsub⟩ := by
      change Fin.append (positiveUnitBoundary (F := F) n).1
          (positiveUnitBoundary (F := F) n).2 p = _
      calc
        _ = Fin.append (positiveUnitBoundary (F := F) n).1
            (positiveUnitBoundary (F := F) n).2
            (Fin.natAdd (n + 1) ⟨(p : ℕ) - (n + 1), hsub⟩) :=
              congrArg _ hnat
        _ = _ := Fin.append_right _ _ _
    rw [hout, positiveUnitBoundary_snd_eq]
    simp [positiveBoundarySpatial, hp]

/-- The response grid of the marked displacement has exactly the desired
source-side output. -/
theorem positiveSourceRect_unitDelta (n : ℕ) :
    positiveSourceRect (n + 1) (positiveUnitDeltaL (F := F) n)
        (positiveUnitDeltaR (F := F) n) =
      positiveUnitSource n := by
  rw [← rectangularCircuitPerm_positiveBoundary,
    positiveBoundaryRect_unitDelta]
  exact (rectangularCircuitPerm F (n + 1)).apply_symm_apply _

theorem positiveUnitEpsilon_col_zero (n : ℕ) (i : Fin (n + 1)) :
    positiveBoundaryValue (n + 1) (positiveUnitDeltaL (F := F) n)
        (positiveUnitDeltaR (F := F) n) i 0 = 0 := by
  have h := congrArg (fun z => z.1 i) (positiveSourceRect_unitDelta (F := F) n)
  exact Sum.inl.inj h

theorem positiveUnitEpsilon_bottom (n : ℕ) (j : Fin (n + 1)) :
    positiveBoundaryValue (n + 1) (positiveUnitDeltaL (F := F) n)
        (positiveUnitDeltaR (F := F) n) n (j + 1) =
      if j = 0 then 1 else 0 := by
  have h := congrArg (fun z => z.2 j) (positiveSourceRect_unitDelta (F := F) n)
  exact Sum.inr.inj h

/-- Every entry in the first nontrivial response-grid column of the marked
positive source displacement is one.  This is the hypothesis used by the
triangular mixed-Hessian calculation. -/
theorem positiveUnitEpsilon_col_one (n m : ℕ) (hm : m < n + 1) :
    positiveBoundaryValue (n + 1) (positiveUnitDeltaL (F := F) n)
        (positiveUnitDeltaR (F := F) n) m 1 = 1 := by
  let eps : ℕ → ℕ → F := positiveBoundaryValue (n + 1)
    (positiveUnitDeltaL (F := F) n) (positiveUnitDeltaR (F := F) n)
  have hout := positiveSourceRect_unitDelta (F := F) n
  have hleft (i : Fin (n + 1)) : eps i 0 = 0 := by
    exact positiveUnitEpsilon_col_zero (F := F) n i
  have hbase : eps n 1 = 1 := by
    have h := congrArg (fun z => z.2 (0 : Fin (n + 1))) hout
    change Sum.inr (eps n 1) = Sum.inr (if (0 : Fin (n + 1)) = 0 then 1 else 0) at h
    simpa using Sum.inr.inj h
  change eps m 1 = 1
  apply Nat.decreasingInduction (n := n)
      (motive := fun k _ => eps k 1 = 1) _ hbase (by omega)
  intro k hk hsucc
  have hrec := positiveBoundaryValue_rec (n + 1)
    (positiveUnitDeltaL (F := F) n) (positiveUnitDeltaR (F := F) n)
    k 0 (by omega) (by omega)
  change eps (k + 1) 0 = eps k 1 - eps (k + 1) 1 at hrec
  rw [hleft ⟨k + 1, by omega⟩, hsucc] at hrec
  linear_combination -hrec

/-- The response field generated by the marked positive source
displacement. -/
def positiveUnitEpsilon (n : ℕ) : ℕ → ℕ → F :=
  positiveBoundaryValue (n + 1) (positiveUnitDeltaL (F := F) n)
    (positiveUnitDeltaR (F := F) n)

theorem positiveUnitEpsilon_col_one' (n m : ℕ) (hm : m < n + 1) :
    positiveUnitEpsilon (F := F) n m 1 = 1 :=
  positiveUnitEpsilon_col_one (F := F) n m hm

/-- The concrete positive rectangle exponent is the negative accumulated
cubic grid phase. -/
theorem rectangularCircuitExponent_positiveBoundary
    (r : ℕ) (L R : Fin r → F) :
    rectangularCircuitExponent F r (positiveBoundaryRect r L R) =
      -∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
        positiveBoundaryValue r L R i j *
          (positiveBoundaryValue r L R i (j + 1)) ^ 2 := by
  unfold rectangularCircuitExponent
  rw [packetsToSpatial_positiveBoundaryRect]
  rw [spatialCircuitExponent_eq_nat (F := F) (r + r)
    (crossingSchedule r) (positiveBoundarySpatial r L R)
    (fun i hi => mem_crossingSchedule_lt hi)]
  rw [extendFin_positiveBoundarySpatial,
    natGateCircuitExponent_crossingSchedule_positive]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [positiveGridValue]

/-- Fin-indexed version of the concrete positive exponent formula. -/
theorem rectangularCircuitExponent_positiveBoundary_fin
    (r : ℕ) (L R : Fin r → F) :
    rectangularCircuitExponent F r (positiveBoundaryRect r L R) =
      -∑ i : Fin r, ∑ j : Fin r,
        positiveBoundaryValue r L R i j *
          (positiveBoundaryValue r L R i (j + 1)) ^ 2 := by
  rw [rectangularCircuitExponent_positiveBoundary]
  simp only [← Fin.sum_univ_eq_sum_range]

/-- The ket-minus-bra marked displacement turns the literal circuit phase
difference into the full response-grid cubic finite difference. -/
theorem rectangularCircuitExponent_positive_difference
    (n : ℕ) (L R : Fin (n + 1) → F) :
    rectangularCircuitExponent F (n + 1) (positiveBoundaryRect (n + 1) L R) -
        rectangularCircuitExponent F (n + 1)
          (positiveBoundaryRect (n + 1)
            (L + positiveUnitDeltaL (F := F) n)
            (R + positiveUnitDeltaR (F := F) n)) =
      positiveFullGridPhase (positiveUnitEpsilon (F := F) n) (n + 1) L R := by
  rw [rectangularCircuitExponent_positiveBoundary_fin,
    rectangularCircuitExponent_positiveBoundary_fin]
  unfold positiveFullGridPhase positiveFullCellPhase positiveUnitEpsilon
  have hadd (i j : ℕ) :
      positiveBoundaryValue (n + 1)
          (L + positiveUnitDeltaL (F := F) n)
          (R + positiveUnitDeltaR (F := F) n) i j =
        positiveBoundaryValue (n + 1) L R i j +
          positiveBoundaryValue (n + 1)
            (positiveUnitDeltaL (F := F) n)
            (positiveUnitDeltaR (F := F) n) i j :=
    positiveBoundaryValue_add (n + 1) L _ R _ i j
  simp_rw [hadd]
  rw [show -(∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        positiveBoundaryValue (n + 1) L R i j *
          positiveBoundaryValue (n + 1) L R i (j + 1) ^ 2) -
      -(∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        (positiveBoundaryValue (n + 1) L R i j +
          positiveBoundaryValue (n + 1) (positiveUnitDeltaL n)
            (positiveUnitDeltaR n) i j) *
          (positiveBoundaryValue (n + 1) L R i (j + 1) +
            positiveBoundaryValue (n + 1) (positiveUnitDeltaL n)
              (positiveUnitDeltaR n) i (j + 1)) ^ 2) =
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        (positiveBoundaryValue (n + 1) L R i j +
          positiveBoundaryValue (n + 1) (positiveUnitDeltaL n)
            (positiveUnitDeltaR n) i j) *
          (positiveBoundaryValue (n + 1) L R i (j + 1) +
            positiveBoundaryValue (n + 1) (positiveUnitDeltaL n)
              (positiveUnitDeltaR n) i (j + 1)) ^ 2) -
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          positiveBoundaryValue (n + 1) L R i j *
            positiveBoundaryValue (n + 1) L R i (j + 1) ^ 2 by ring]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]

end SqrtOpEnt
