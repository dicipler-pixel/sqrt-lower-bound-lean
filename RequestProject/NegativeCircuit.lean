import RequestProject.ResidualCircuit

/-!
# The literal negative residual shear grid

For imbalance `-s`, the active boundary word is `B A^s | B^(s+1)`.
Each schedule row moves one right-hand `B` left across the `s` copies of
`A`; its final crossing with the accumulated `B` prefix is an identity.
Removing that spectator gives the `(s+1) × s` negative response grid.
-/

namespace SqrtOpEnt

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local instance : Inhabited F := ⟨0⟩
local instance : Inhabited (Vq F) := ⟨Sum.inl 0⟩

/-! ## One forward-shear row -/

/-- Before a descending active row, the `A` inputs are consecutive
differences `c_j-c_(j+1)` and the moving rightmost `B` has value `c_s`. -/
def negativeActiveRowInput (b s : ℕ) (c : ℕ → F) (z : ℕ → Vq F) :
    ℕ → Vq F :=
  fun p => if b < p ∧ p < b + s + 1 then
      Sum.inl (c (p - b - 1) - c (p - b))
    else if p = b + s + 1 then Sum.inr (c s)
    else z p

/-- After the active crossings, the moving strand is `B(c_0)` and the
displaced `A` values are `c_1,…,c_s`. -/
def negativeActiveRowOutput (b s : ℕ) (c : ℕ → F) (z : ℕ → Vq F) :
    ℕ → Vq F :=
  fun p => if p = b + 1 then Sum.inr (c 0)
    else if b + 1 < p ∧ p ≤ b + s + 1 then
      Sum.inl (c (p - b - 1))
    else z p

/-- Exposing the rightmost active crossing reduces a row by one cell. -/
theorem natGateAt_negativeActiveRowInput_succ (b s : ℕ)
    (c : ℕ → F) (z : ℕ → Vq F) :
    natGateAt (b + s + 1) (negativeActiveRowInput b (s + 1) c z) =
      negativeActiveRowInput b s c
        (fun p => if p = b + s + 2 then
          (Sum.inl (c (s + 1)) : Vq F) else z p) := by
  funext p
  unfold natGateAt
  by_cases hp0 : p = b + s + 1
  · subst p
    rw [if_pos rfl]
    have hl : negativeActiveRowInput b (s + 1) c z (b + s + 1) =
        Sum.inl (c s - c (s + 1)) := by
      simp only [negativeActiveRowInput, if_pos (by omega :
        b < b + s + 1 ∧ b + s + 1 < b + (s + 1) + 1)]
      rw [show b + s + 1 - b - 1 = s by omega,
        show b + s + 1 - b = s + 1 by omega]
    have hr : negativeActiveRowInput b (s + 1) c z (b + s + 2) =
        Sum.inr (c (s + 1)) := by
      unfold negativeActiveRowInput
      rw [if_neg (by omega), if_pos (by omega)]
    have ho : negativeActiveRowInput b s c
        (fun p => if p = b + s + 2 then
          (Sum.inl (c (s + 1)) : Vq F) else z p) (b + s + 1) =
        Sum.inr (c s) := by
      simp [negativeActiveRowInput]
    rw [hl, hr, ho]
    simp [gateFun]
  · by_cases hp1 : p = b + s + 2
    · subst p
      rw [if_neg (by omega : ¬ (b + s + 2 = b + s + 1)), if_pos rfl]
      have hl : negativeActiveRowInput b (s + 1) c z (b + s + 1) =
          Sum.inl (c s - c (s + 1)) := by
        simp only [negativeActiveRowInput, if_pos (by omega :
          b < b + s + 1 ∧ b + s + 1 < b + (s + 1) + 1)]
        rw [show b + s + 1 - b - 1 = s by omega,
          show b + s + 1 - b = s + 1 by omega]
      have hr : negativeActiveRowInput b (s + 1) c z (b + s + 2) =
          Sum.inr (c (s + 1)) := by
        unfold negativeActiveRowInput
        rw [if_neg (by omega), if_pos (by omega)]
      have ho : negativeActiveRowInput b s c
          (fun p => if p = b + s + 2 then
            (Sum.inl (c (s + 1)) : Vq F) else z p) (b + s + 2) =
          Sum.inl (c (s + 1)) := by
        simp [negativeActiveRowInput]
      rw [hl, hr, ho]
      simp [gateFun]
    · rw [if_neg hp0, if_neg hp1]
      unfold negativeActiveRowInput
      by_cases hp : b < p ∧ p < b + s + 1
      · rw [if_pos (by omega : b < p ∧ p < b + (s + 1) + 1), if_pos hp]
      · rw [if_neg (by omega : ¬ (b < p ∧ p < b + (s + 1) + 1)),
          if_neg (by omega : ¬ (p = b + (s + 1) + 1)), if_neg hp,
          if_neg (by omega : ¬ (p = b + s + 1))]
        simp [hp1]

/-- The descending active word performs one complete forward-shear row. -/
theorem natGateCircuit_descending_negativeActiveRow (b s : ℕ)
    (c : ℕ → F) (z : ℕ → Vq F) :
    natGateCircuit (descendingSwaps (b + 1) s)
        (negativeActiveRowInput b s c z) =
      negativeActiveRowOutput b s c z := by
  induction s generalizing z with
  | zero =>
      funext p
      by_cases hp : p = b + 1
      · subst p
        simp [descendingSwaps, natGateCircuit, negativeActiveRowInput,
          negativeActiveRowOutput]
      · simp [descendingSwaps, natGateCircuit, negativeActiveRowInput,
          negativeActiveRowOutput, hp,
          show ¬ (b < p ∧ p < b + 0 + 1) by omega,
          show ¬ (b + 1 < p ∧ p ≤ b + 0 + 1) by omega]
  | succ s ih =>
      rw [descendingSwaps_succ]
      simp only [natGateCircuit]
      rw [show b + 1 + s = b + s + 1 by omega]
      rw [natGateAt_negativeActiveRowInput_succ]
      rw [ih]
      funext p
      unfold negativeActiveRowOutput
      by_cases hp0 : p = b + 1
      · subst p
        simp
      · by_cases hp : b + 1 < p ∧ p ≤ b + s + 1
        · rw [if_neg hp0, if_pos hp, if_neg hp0,
            if_pos (by omega : b + 1 < p ∧ p ≤ b + (s + 1) + 1)]
        · by_cases hp1 : p = b + s + 2
          · subst p
            simp [show ¬ (b + s + 2 = b + 1) by omega,
              show ¬ (b + 1 < b + s + 2 ∧ b + s + 2 ≤ b + s + 1) by omega,
              show b + 1 < b + s + 2 ∧
                b + s + 2 ≤ b + (s + 1) + 1 by omega,
              show b + s + 2 - b - 1 = s + 1 by omega]
          · simp [hp0, hp, hp1, show ¬ (b + 1 < p ∧
                p ≤ b + (s + 1) + 1) by omega]

/-- One active negative cell contributes `(c_j-c_(j+1))c_(j+1)^2`. -/
theorem natGateAtExponent_negativeActiveRowInput_last (b s : ℕ)
    (c : ℕ → F) (z : ℕ → Vq F) :
    natGateAtExponent (b + s + 1)
        (negativeActiveRowInput b (s + 1) c z) =
      (c s - c (s + 1)) * (c (s + 1)) ^ 2 := by
  unfold natGateAtExponent
  have hl : negativeActiveRowInput b (s + 1) c z (b + s + 1) =
      Sum.inl (c s - c (s + 1)) := by
    simp only [negativeActiveRowInput, if_pos (by omega :
      b < b + s + 1 ∧ b + s + 1 < b + (s + 1) + 1)]
    rw [show b + s + 1 - b - 1 = s by omega,
      show b + s + 1 - b = s + 1 by omega]
  have hr : negativeActiveRowInput b (s + 1) c z (b + s + 2) =
      Sum.inr (c (s + 1)) := by
    unfold negativeActiveRowInput
    rw [if_neg (by omega), if_pos (by omega)]
  rw [hl, hr]
  simp [gateExponent]

/-- Exponent accumulated along the active part of one negative row. -/
theorem natGateCircuitExponent_descending_negativeActiveRow (b s : ℕ)
    (c : ℕ → F) (z : ℕ → Vq F) :
    natGateCircuitExponent (descendingSwaps (b + 1) s)
        (negativeActiveRowInput b s c z) =
      ∑ j ∈ Finset.range s, (c j - c (j + 1)) * (c (j + 1)) ^ 2 := by
  induction s generalizing z with
  | zero => simp [descendingSwaps, natGateCircuitExponent]
  | succ s ih =>
      rw [descendingSwaps_succ]
      simp only [natGateCircuitExponent]
      rw [show b + 1 + s = b + s + 1 by omega]
      rw [natGateAt_negativeActiveRowInput_succ, ih,
        natGateAtExponent_negativeActiveRowInput_last,
        Finset.sum_range_succ]

/-- A complete schedule row is its active suffix followed by the final
same-colour crossing. -/
theorem descendingSwaps_eq_negativeActive_append (b s : ℕ) :
    descendingSwaps b (s + 1) = descendingSwaps (b + 1) s ++ [b] := by
  induction s with
  | zero => simp [descendingSwaps]
  | succ s ih =>
      rw [descendingSwaps_succ b (s + 1), ih,
        descendingSwaps_succ (b + 1) s]
      simp only [List.cons_append]
      congr 1 <;> omega

/-- Include the fixed `B` immediately to the left of an active row. -/
def negativeRowInput (b s : ℕ) (q : F) (c : ℕ → F)
    (z : ℕ → Vq F) : ℕ → Vq F :=
  negativeActiveRowInput b s c
    (fun p => if p = b then Sum.inr q else z p)

/-- Output of the complete negative row, including its final identity
crossing. -/
def negativeRowOutput (b s : ℕ) (q : F) (c : ℕ → F)
    (z : ℕ → Vq F) : ℕ → Vq F :=
  negativeActiveRowOutput b s c
    (fun p => if p = b then Sum.inr q else z p)

theorem natGateCircuit_descending_negativeRow (b s : ℕ) (q : F)
    (c : ℕ → F) (z : ℕ → Vq F) :
    natGateCircuit (descendingSwaps b (s + 1))
        (negativeRowInput b s q c z) =
      negativeRowOutput b s q c z := by
  rw [descendingSwaps_eq_negativeActive_append, natGateCircuit_append]
  unfold negativeRowInput negativeRowOutput
  rw [natGateCircuit_descending_negativeActiveRow]
  simp only [natGateCircuit]
  funext p
  unfold natGateAt negativeActiveRowOutput
  by_cases hp0 : p = b
  · subst p
    simp [gateFun]
  · by_cases hp1 : p = b + 1
    · subst p
      simp [gateFun]
    · simp [hp0, hp1]

theorem natGateCircuitExponent_descending_negativeRow
    (b s : ℕ) (q : F) (c : ℕ → F) (z : ℕ → Vq F) :
    natGateCircuitExponent (descendingSwaps b (s + 1))
        (negativeRowInput b s q c z) =
      ∑ j ∈ Finset.range s, (c j - c (j + 1)) * (c (j + 1)) ^ 2 := by
  rw [descendingSwaps_eq_negativeActive_append,
    natGateCircuitExponent_append]
  unfold negativeRowInput
  rw [natGateCircuitExponent_descending_negativeActiveRow,
    natGateCircuit_descending_negativeActiveRow]
  simp [natGateCircuitExponent, natGateAtExponent,
    negativeActiveRowOutput, gateExponent]

/-! ## The complete negative rectangle -/

def negativeGridValue (s : ℕ) (L R : ℕ → F) (i j : ℕ) : F :=
  negativeBoundaryValue s (fun m => L m) (fun n => R n) i j

@[simp]
theorem negativeGridValue_extend (s : ℕ) (L : Fin s → F)
    (R : Fin (s + 1) → F) (i j : ℕ) :
    negativeGridValue s (extendFin s L) (extendFin (s + 1) R) i j =
      negativeBoundaryValue s L R i j := by
  unfold negativeGridValue
  congr 1
  · funext m
    simp [extendFin, m.isLt]
  · funext k
    simp [extendFin, k.isLt]

/-- Configuration after the first `b` rows of the negative schedule. -/
def negativeAfterRows (s b : ℕ) (q : F) (L R : ℕ → F) : ℕ → Vq F :=
  fun p => if p = 0 then Sum.inr q
    else if p ≤ b then Sum.inr (negativeGridValue s L R (p - 1) 0)
    else if p < b + s + 1 then
      Sum.inl (if b = 0 then L (p - 1)
        else negativeGridValue s L R (b - 1) (p - b))
    else if p < (s + 1) + (s + 1) then Sum.inr (R (p - (s + 1)))
    else default

def negativeRowLeftValue (s b : ℕ) (q : F) (L R : ℕ → F) : F :=
  if b = 0 then q else negativeGridValue s L R (b - 1) 0

/-- The explicit intermediate configuration is the row-input normal form. -/
theorem negativeAfterRows_eq_rowInput (s b : ℕ) (hb : b < s + 1)
    (q : F) (L R : ℕ → F) :
    negativeAfterRows s b q L R =
      negativeRowInput b s (negativeRowLeftValue s b q L R)
        (fun j => negativeGridValue s L R b j)
        (negativeAfterRows s b q L R) := by
  funext p
  unfold negativeRowInput negativeActiveRowInput
  by_cases hp : b < p ∧ p < b + s + 1
  · rw [if_pos hp]
    unfold negativeAfterRows
    rw [if_neg (by omega : ¬ (p = 0)), if_neg (by omega : ¬ (p ≤ b)),
      if_pos hp.2]
    by_cases hb0 : b = 0
    · subst b
      rw [if_pos rfl]
      have htop := negativeBoundaryValue_top s
        (fun m : Fin s => L m) (fun n : Fin (s + 1) => R n)
        (p - 1) (by omega)
      change negativeGridValue s L R 0 (p - 1) =
          L (p - 1) + negativeGridValue s L R 0 (p - 1 + 1) at htop
      have hfield : L (p - 1) =
          negativeGridValue s L R 0 (p - 1) -
            negativeGridValue s L R 0 p := by
        rw [show p - 1 + 1 = p by omega] at htop
        rw [htop]
        ring
      rw [show p - 0 - 1 = p - 1 by omega,
        show p - 0 = p by omega]
      exact congrArg (fun x : F => (Sum.inl x : Vq F)) hfield
    · rw [if_neg hb0]
      obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
      have hrec := negativeBoundaryValue_rec s
        (fun m : Fin s => L m) (fun n : Fin (s + 1) => R n)
        c (p - (c + 1) - 1) (by omega) (by omega)
      change negativeGridValue s L R (c + 1) (p - (c + 1) - 1) =
          negativeGridValue s L R c (p - (c + 1) - 1 + 1) +
            negativeGridValue s L R (c + 1) (p - (c + 1) - 1 + 1) at hrec
      apply congrArg (fun x : F => (Sum.inl x : Vq F))
      simp only [Nat.succ_eq_add_one]
      rw [show c + 1 - 1 = c by omega]
      rw [show p - (c + 1) - 1 + 1 = p - (c + 1) by omega] at hrec
      rw [hrec]
      ring
  · rw [if_neg hp]
    by_cases hpr : p = b + s + 1
    · subst p
      rw [if_pos rfl]
      unfold negativeAfterRows
      rw [if_neg (by omega : ¬ (b + s + 1 = 0)),
        if_neg (by omega : ¬ (b + s + 1 ≤ b)),
        if_neg (by omega : ¬ (b + s + 1 < b + s + 1)),
        if_pos (by omega : b + s + 1 < (s + 1) + (s + 1))]
      have hright := negativeBoundaryValue_right s
        (fun m : Fin s => L m) (fun n : Fin (s + 1) => R n) ⟨b, hb⟩
      change negativeGridValue s L R b s = R b at hright
      apply congrArg (fun x : F => (Sum.inr x : Vq F))
      rw [show b + s + 1 - (s + 1) = b by omega]
      exact hright.symm
    · rw [if_neg hpr]
      by_cases hpb : p = b
      · subst p
        unfold negativeRowLeftValue negativeAfterRows
        by_cases hb0 : b = 0
        · subst b
          simp
        · simp [hb0]
      · simp [hpb]

/-- Completing row `b` advances the explicit negative configuration. -/
theorem negativeRowOutput_eq_afterRows_succ (s b : ℕ) (hb : b < s + 1)
    (q : F) (L R : ℕ → F) :
    negativeRowOutput b s (negativeRowLeftValue s b q L R)
        (fun j => negativeGridValue s L R b j)
        (negativeAfterRows s b q L R) =
      negativeAfterRows s (b + 1) q L R := by
  funext p
  unfold negativeRowOutput negativeActiveRowOutput negativeAfterRows
  by_cases hpzero : p = 0
  · subst p
    by_cases hb0 : b = 0
    · subst b
      simp [negativeRowLeftValue]
    · simp [negativeRowLeftValue, hb0, Ne.symm hb0]
  · by_cases hp0 : p = b + 1
    · subst p
      simp
    · by_cases hp : b + 1 < p ∧ p ≤ b + s + 1
      · rw [if_neg hp0, if_pos hp, if_neg hpzero,
          if_neg (by omega : ¬ (p ≤ b + 1)),
          if_pos (by omega : p < b + 1 + s + 1),
          if_neg (by omega : ¬ (b + 1 = 0))]
        congr 2 <;> omega
      · rw [if_neg hp0, if_neg hp]
        by_cases hple : p ≤ b
        · by_cases hpb : p = b
          · subst p
            have hb0 : b ≠ 0 := by omega
            simp [negativeRowLeftValue, hb0]
          · simp [hpzero, hp0, hp, hple, hpb,
              show ¬ (b + 1 < p) by omega]
        · by_cases hright : b + s + 1 < p
          · simp [hpzero, hp0, hp, hple, hright,
              show p ≠ b by omega,
              show ¬ p ≤ b + 1 by omega,
              show ¬ p < b + s + 1 by omega,
              show ¬ p < b + 1 + s + 1 by omega]
          · exfalso
            omega

theorem natGateCircuit_crossingPrefix_negative
    (s b : ℕ) (hb : b ≤ s + 1) (q : F) (L R : ℕ → F) :
    natGateCircuit (crossingPrefix (s + 1) b)
        (negativeAfterRows s 0 q L R) =
      negativeAfterRows s b q L R := by
  induction b with
  | zero => simp [crossingPrefix, natGateCircuit]
  | succ b ih =>
      rw [crossingPrefix_succ, natGateCircuit_append, ih (by omega),
        negativeAfterRows_eq_rowInput s b (by omega),
        natGateCircuit_descending_negativeRow]
      exact negativeRowOutput_eq_afterRows_succ s b (by omega) q L R

theorem natGateCircuitExponent_crossingPrefix_negative
    (s b : ℕ) (hb : b ≤ s + 1) (q : F) (L R : ℕ → F) :
    natGateCircuitExponent (crossingPrefix (s + 1) b)
        (negativeAfterRows s 0 q L R) =
      ∑ i ∈ Finset.range b, ∑ j ∈ Finset.range s,
        (negativeGridValue s L R i j - negativeGridValue s L R i (j + 1)) *
          (negativeGridValue s L R i (j + 1)) ^ 2 := by
  induction b with
  | zero => simp [crossingPrefix, natGateCircuitExponent]
  | succ b ih =>
      rw [crossingPrefix_succ, natGateCircuitExponent_append,
        natGateCircuit_crossingPrefix_negative s b (by omega),
        negativeAfterRows_eq_rowInput s b (by omega),
        natGateCircuitExponent_descending_negativeRow,
        ih (by omega), Finset.sum_range_succ]
      ring

theorem natGateCircuit_crossingSchedule_negative
    (s : ℕ) (q : F) (L R : ℕ → F) :
    natGateCircuit (crossingSchedule (s + 1))
        (negativeAfterRows s 0 q L R) =
      negativeAfterRows s (s + 1) q L R := by
  rw [crossingSchedule_eq_prefix]
  exact natGateCircuit_crossingPrefix_negative s (s + 1) (le_refl _) q L R

theorem natGateCircuitExponent_crossingSchedule_negative
    (s : ℕ) (q : F) (L R : ℕ → F) :
    natGateCircuitExponent (crossingSchedule (s + 1))
        (negativeAfterRows s 0 q L R) =
      ∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range s,
        (negativeGridValue s L R i j - negativeGridValue s L R i (j + 1)) *
          (negativeGridValue s L R i (j + 1)) ^ 2 := by
  rw [crossingSchedule_eq_prefix]
  exact natGateCircuitExponent_crossingPrefix_negative s (s + 1)
    (le_refl _) q L R

/-! ## Transfer to the finite rectangle -/

def negativeBoundarySpatial (s : ℕ) (q : F)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    SpatialBasis F ((s + 1) + (s + 1)) :=
  fun p => if hp0 : (p : ℕ) = 0 then Sum.inr q
    else if hp : (p : ℕ) < s + 1 then Sum.inl (L ⟨(p : ℕ) - 1, by omega⟩)
    else Sum.inr (R ⟨(p : ℕ) - (s + 1), by omega⟩)

def negativeBoundaryRect (s : ℕ) (q : F)
    (L : Fin s → F) (R : Fin (s + 1) → F) : RectBasis F (s + 1) :=
  (packetsToSpatial F).symm (negativeBoundarySpatial s q L R)

/-- Explicit packet form of the negative boundary configuration. -/
theorem negativeBoundaryRect_eq (s : ℕ) (q : F)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    negativeBoundaryRect s q L R =
      (Fin.cases (Sum.inr q) (fun i => Sum.inl (L i)),
        fun i => Sum.inr (R i)) := by
  apply (packetsToSpatial F).injective
  rw [negativeBoundaryRect, Equiv.apply_symm_apply]
  funext p
  change negativeBoundarySpatial s q L R p =
    Fin.append (Fin.cases (Sum.inr q) (fun i => Sum.inl (L i)))
      (fun i => Sum.inr (R i)) p
  by_cases hp : (p : ℕ) < s + 1
  · have hcast : p = Fin.castAdd (s + 1) ⟨p, hp⟩ := by
      apply Fin.ext
      rfl
    rw [hcast, Fin.append_left]
    refine Fin.cases ?_ (fun i => ?_) ⟨p, hp⟩
    · simp [negativeBoundarySpatial]
    · simp [negativeBoundarySpatial]
  · have hsub : (p : ℕ) - (s + 1) < s + 1 := by omega
    have hnat : p = Fin.natAdd (s + 1) ⟨(p : ℕ) - (s + 1), hsub⟩ := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [hnat, Fin.append_right]
    simp [negativeBoundarySpatial,
      show ¬ ((p : ℕ) - (s + 1) + (s + 1) ≤ s) by omega]

@[simp]
theorem packetsToSpatial_negativeBoundaryRect (s : ℕ) (q : F)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    packetsToSpatial F (negativeBoundaryRect s q L R) =
      negativeBoundarySpatial s q L R := by
  simp [negativeBoundaryRect]

theorem extendFin_negativeBoundarySpatial (s : ℕ) (q : F)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    extendFin ((s + 1) + (s + 1)) (negativeBoundarySpatial s q L R) =
      negativeAfterRows s 0 q (extendFin s L) (extendFin (s + 1) R) := by
  funext p
  by_cases hp0 : p = 0
  · subst p
    simp [extendFin, negativeBoundarySpatial, negativeAfterRows]
  · by_cases hp : p < s + 1
    · have htot : p < (s + 1) + (s + 1) := by omega
      have hsub : p - 1 < s := by omega
      simp [extendFin, negativeBoundarySpatial, negativeAfterRows,
        hp0, hp, htot, hsub]
    · by_cases htot : p < (s + 1) + (s + 1)
      · have hsub : p - (s + 1) < s + 1 := by omega
        simp [extendFin, negativeBoundarySpatial, negativeAfterRows,
          hp0, hp, htot, hsub]
      · simp [extendFin, negativeAfterRows, hp0, hp, htot]

def negativeSourceRect (s : ℕ) (q : F)
    (L : Fin s → F) (R : Fin (s + 1) → F) : RectBasis F (s + 1) :=
  (Fin.cases (Sum.inr q)
      (fun i => Sum.inr (negativeBoundaryValue s L R i 0)),
    Fin.cases (Sum.inr (negativeBoundaryValue s L R s 0))
      (fun j => Sum.inl (negativeBoundaryValue s L R s (j + 1))))

theorem spatialCircuitPerm_negativeBoundary (s : ℕ) (q : F)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    spatialCircuitPerm F ((s + 1) + (s + 1)) (crossingSchedule (s + 1))
        (negativeBoundarySpatial s q L R) =
      fun p : Fin ((s + 1) + (s + 1)) =>
        negativeAfterRows s (s + 1) q (extendFin s L)
          (extendFin (s + 1) R) p := by
  funext p
  have htransfer := extendFin_spatialCircuitPerm (F := F)
    ((s + 1) + (s + 1)) (crossingSchedule (s + 1))
    (negativeBoundarySpatial s q L R)
    (fun i hi => mem_crossingSchedule_lt hi)
  rw [extendFin_negativeBoundarySpatial,
    natGateCircuit_crossingSchedule_negative] at htransfer
  have hp := congrFun htransfer (p : ℕ)
  simpa using hp

theorem rectangularCircuitPerm_negativeBoundary (s : ℕ) (q : F)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    rectangularCircuitPerm F (s + 1) (negativeBoundaryRect s q L R) =
      negativeSourceRect s q L R := by
  apply (packetsToSpatial F).injective
  simp only [rectangularCircuitPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [packetsToSpatial_negativeBoundaryRect, spatialCircuitPerm_negativeBoundary]
  funext p
  by_cases hp : (p : ℕ) < s + 1
  · have hcast : p = Fin.castAdd (s + 1) ⟨p, hp⟩ := by
      apply Fin.ext
      rfl
    have hout : packetsToSpatial F (negativeSourceRect s q L R) p =
        (negativeSourceRect s q L R).1 ⟨p, hp⟩ := by
      change Fin.append (negativeSourceRect s q L R).1
          (negativeSourceRect s q L R).2 p = _
      calc
        _ = Fin.append (negativeSourceRect s q L R).1
            (negativeSourceRect s q L R).2
            (Fin.castAdd (s + 1) ⟨p, hp⟩) := congrArg _ hcast
        _ = _ := Fin.append_left _ _ _
    rw [hout]
    by_cases hp0 : (p : ℕ) = 0
    · have hpFin : p = 0 := by
        apply Fin.ext
        exact hp0
      subst p
      simp [negativeAfterRows, negativeSourceRect]
    · have hsub : (p : ℕ) - 1 < s := by omega
      have hsucc : (⟨p, hp⟩ : Fin (s + 1)) =
          (⟨(p : ℕ) - 1, hsub⟩ : Fin s).succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [hsucc]
      simp [negativeAfterRows, negativeSourceRect, hp0,
        negativeGridValue_extend, show ¬ (s + 1 < (p : ℕ)) by omega]
  · have hsub : (p : ℕ) - (s + 1) < s + 1 := by omega
    have hnat : p = Fin.natAdd (s + 1) ⟨(p : ℕ) - (s + 1), hsub⟩ := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    have hout : packetsToSpatial F (negativeSourceRect s q L R) p =
        (negativeSourceRect s q L R).2
          ⟨(p : ℕ) - (s + 1), hsub⟩ := by
      change Fin.append (negativeSourceRect s q L R).1
          (negativeSourceRect s q L R).2 p = _
      calc
        _ = Fin.append (negativeSourceRect s q L R).1
            (negativeSourceRect s q L R).2
            (Fin.natAdd (s + 1) ⟨(p : ℕ) - (s + 1), hsub⟩) :=
              congrArg _ hnat
        _ = _ := Fin.append_right _ _ _
    rw [hout]
    let j : Fin (s + 1) := ⟨(p : ℕ) - (s + 1), hsub⟩
    have hnat' : p = Fin.natAdd (s + 1) j := hnat
    calc
      negativeAfterRows s (s + 1) q (extendFin s L)
          (extendFin (s + 1) R) p =
        negativeAfterRows s (s + 1) q (extendFin s L)
          (extendFin (s + 1) R) (Fin.natAdd (s + 1) j) :=
            congrArg _ (congrArg Fin.val hnat')
      _ = (negativeSourceRect s q L R).2 j := by
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [negativeAfterRows, negativeSourceRect,
            negativeGridValue_extend]
        · simp [negativeAfterRows, negativeSourceRect,
            negativeGridValue_extend, show (k : ℕ) + 1 ≤ s by omega] <;>
            omega
      _ = _ := rfl

theorem rectangularCircuitExponent_negativeBoundary
    (s : ℕ) (q : F) (L : Fin s → F) (R : Fin (s + 1) → F) :
    rectangularCircuitExponent F (s + 1) (negativeBoundaryRect s q L R) =
      ∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range s,
        (negativeBoundaryValue s L R i j -
          negativeBoundaryValue s L R i (j + 1)) *
            (negativeBoundaryValue s L R i (j + 1)) ^ 2 := by
  unfold rectangularCircuitExponent
  rw [packetsToSpatial_negativeBoundaryRect]
  rw [spatialCircuitExponent_eq_nat (F := F)
    ((s + 1) + (s + 1)) (crossingSchedule (s + 1))
    (negativeBoundarySpatial s q L R) (fun i hi => mem_crossingSchedule_lt hi)]
  rw [extendFin_negativeBoundarySpatial,
    natGateCircuitExponent_crossingSchedule_negative]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [negativeGridValue]

/-! ## The marked negative source displacement -/

/-- The marked source displacement in the negative orientation.  The left
source packet is entirely `B`; on the right, the marked first site is `B`
and the remaining sites are `A`. -/
def negativeUnitSource (s : ℕ) : RectBasis F (s + 1) :=
  (fun _ => Sum.inr 0,
    Fin.cases (Sum.inr 1) (fun _ => Sum.inl 0))

/-- Pull the marked negative source displacement back through the literal
rectangular support permutation. -/
def negativeUnitBoundary (s : ℕ) : RectBasis F (s + 1) :=
  (rectangularCircuitPerm F (s + 1)).symm (negativeUnitSource s)

def negativeUnitDeltaQ (s : ℕ) : F :=
  siteLabel F ((negativeUnitBoundary (F := F) s).1 0)

def negativeUnitDeltaL (s : ℕ) : Fin s → F :=
  fun i => siteLabel F ((negativeUnitBoundary (F := F) s).1 i.succ)

def negativeUnitDeltaR (s : ℕ) : Fin (s + 1) → F :=
  fun i => siteLabel F ((negativeUnitBoundary (F := F) s).2 i)

theorem siteColour_negativeUnitBoundary_fst_zero (s : ℕ) :
    siteColour F ((negativeUnitBoundary (F := F) s).1 0) = .B := by
  have h := (siteColour_rectangularCircuitPerm_snd F (s + 1)
    (negativeUnitBoundary (F := F) s) 0).symm
  simpa [negativeUnitBoundary, negativeUnitSource] using h

theorem siteColour_negativeUnitBoundary_fst_succ (s : ℕ) (i : Fin s) :
    siteColour F ((negativeUnitBoundary (F := F) s).1 i.succ) = .A := by
  have h := (siteColour_rectangularCircuitPerm_snd F (s + 1)
    (negativeUnitBoundary (F := F) s) i.succ).symm
  simpa [negativeUnitBoundary, negativeUnitSource] using h

theorem siteColour_negativeUnitBoundary_snd (s : ℕ) (i : Fin (s + 1)) :
    siteColour F ((negativeUnitBoundary (F := F) s).2 i) = .B := by
  have h := (siteColour_rectangularCircuitPerm_fst F (s + 1)
    (negativeUnitBoundary (F := F) s) i).symm
  simpa [negativeUnitBoundary, negativeUnitSource] using h

theorem negativeUnitBoundary_fst_zero_eq (s : ℕ) :
    (negativeUnitBoundary (F := F) s).1 0 =
      Sum.inr (negativeUnitDeltaQ (F := F) s) := by
  cases hval : (negativeUnitBoundary (F := F) s).1 0 with
  | inl a =>
      have hcolour := siteColour_negativeUnitBoundary_fst_zero (F := F) s
      rw [hval] at hcolour
      contradiction
  | inr b => simp [negativeUnitDeltaQ, siteLabel, hval]

theorem negativeUnitBoundary_fst_succ_eq (s : ℕ) (i : Fin s) :
    (negativeUnitBoundary (F := F) s).1 i.succ =
      Sum.inl (negativeUnitDeltaL (F := F) s i) := by
  cases hval : (negativeUnitBoundary (F := F) s).1 i.succ with
  | inl a => simp [negativeUnitDeltaL, siteLabel, hval]
  | inr b =>
      have hcolour := siteColour_negativeUnitBoundary_fst_succ (F := F) s i
      rw [hval] at hcolour
      contradiction

theorem negativeUnitBoundary_snd_eq (s : ℕ) (i : Fin (s + 1)) :
    (negativeUnitBoundary (F := F) s).2 i =
      Sum.inr (negativeUnitDeltaR (F := F) s i) := by
  cases hval : (negativeUnitBoundary (F := F) s).2 i with
  | inl a =>
      have hcolour := siteColour_negativeUnitBoundary_snd (F := F) s i
      rw [hval] at hcolour
      contradiction
  | inr b => simp [negativeUnitDeltaR, siteLabel, hval]

/-- The labels extracted from the inverse image give exactly the negative
`B A^s | B^(s+1)` boundary configuration. -/
theorem negativeBoundaryRect_unitDelta (s : ℕ) :
    negativeBoundaryRect s (negativeUnitDeltaQ (F := F) s)
        (negativeUnitDeltaL (F := F) s)
        (negativeUnitDeltaR (F := F) s) =
      negativeUnitBoundary (F := F) s := by
  apply (packetsToSpatial F).injective
  rw [packetsToSpatial_negativeBoundaryRect]
  funext p
  by_cases hp0 : (p : ℕ) = 0
  · have hpFin : p = 0 := by
      apply Fin.ext
      exact hp0
    subst p
    have hout : packetsToSpatial F (negativeUnitBoundary (F := F) s) 0 =
        (negativeUnitBoundary (F := F) s).1 0 := by
      change Fin.append (negativeUnitBoundary (F := F) s).1
          (negativeUnitBoundary (F := F) s).2 0 = _
      exact Fin.append_left
        (negativeUnitBoundary (F := F) s).1
        (negativeUnitBoundary (F := F) s).2 (0 : Fin (s + 1))
    rw [hout, negativeUnitBoundary_fst_zero_eq]
    simp [negativeBoundarySpatial]
  · by_cases hp : (p : ℕ) < s + 1
    · have hsub : (p : ℕ) - 1 < s := by omega
      let i : Fin s := ⟨(p : ℕ) - 1, hsub⟩
      have hcast : p = Fin.castAdd (s + 1) i.succ := by
        apply Fin.ext
        change (p : ℕ) = (i : ℕ) + 1
        simp only [i]
        omega
      have hout : packetsToSpatial F (negativeUnitBoundary (F := F) s) p =
          (negativeUnitBoundary (F := F) s).1 i.succ := by
        change Fin.append (negativeUnitBoundary (F := F) s).1
            (negativeUnitBoundary (F := F) s).2 p = _
        calc
          _ = Fin.append (negativeUnitBoundary (F := F) s).1
              (negativeUnitBoundary (F := F) s).2
              (Fin.castAdd (s + 1) i.succ) := congrArg _ hcast
          _ = _ := Fin.append_left _ _ _
      rw [hout, negativeUnitBoundary_fst_succ_eq]
      simp [negativeBoundarySpatial, hp0, hp, i]
    · have hsub : (p : ℕ) - (s + 1) < s + 1 := by omega
      let i : Fin (s + 1) := ⟨(p : ℕ) - (s + 1), hsub⟩
      have hnat : p = Fin.natAdd (s + 1) i := by
        apply Fin.ext
        change (p : ℕ) = s + 1 + (i : ℕ)
        simp only [i]
        omega
      have hout : packetsToSpatial F (negativeUnitBoundary (F := F) s) p =
          (negativeUnitBoundary (F := F) s).2 i := by
        change Fin.append (negativeUnitBoundary (F := F) s).1
            (negativeUnitBoundary (F := F) s).2 p = _
        calc
          _ = Fin.append (negativeUnitBoundary (F := F) s).1
              (negativeUnitBoundary (F := F) s).2
              (Fin.natAdd (s + 1) i) := congrArg _ hnat
          _ = _ := Fin.append_right _ _ _
      rw [hout, negativeUnitBoundary_snd_eq]
      simp [negativeBoundarySpatial, hp0, hp, i]

/-- The marked response grid has exactly the prescribed source edges. -/
theorem negativeSourceRect_unitDelta (s : ℕ) :
    negativeSourceRect s (negativeUnitDeltaQ (F := F) s)
        (negativeUnitDeltaL (F := F) s)
        (negativeUnitDeltaR (F := F) s) =
      negativeUnitSource s := by
  rw [← rectangularCircuitPerm_negativeBoundary,
    negativeBoundaryRect_unitDelta]
  exact (rectangularCircuitPerm F (s + 1)).apply_symm_apply _

@[simp]
theorem negativeUnitDeltaQ_eq_zero (s : ℕ) :
    negativeUnitDeltaQ (F := F) s = 0 := by
  have h := congrArg (fun z => z.1 (0 : Fin (s + 1)))
    (negativeSourceRect_unitDelta (F := F) s)
  exact Sum.inr.inj h

/-- Response field of the marked negative source displacement. -/
def negativeUnitEpsilon (s : ℕ) : ℕ → ℕ → F :=
  negativeBoundaryValue s (negativeUnitDeltaL (F := F) s)
    (negativeUnitDeltaR (F := F) s)

theorem negativeUnitEpsilon_left (s : ℕ) (i : Fin s) :
    negativeUnitEpsilon (F := F) s i 0 = 0 := by
  have h := congrArg (fun z => z.1 i.succ)
    (negativeSourceRect_unitDelta (F := F) s)
  exact Sum.inr.inj h

theorem negativeUnitEpsilon_corner (s : ℕ) :
    negativeUnitEpsilon (F := F) s s 0 = 1 := by
  have h := congrArg (fun z => z.2 (0 : Fin (s + 1)))
    (negativeSourceRect_unitDelta (F := F) s)
  exact Sum.inr.inj h

theorem negativeUnitEpsilon_bottom (s : ℕ) (j : Fin s) :
    negativeUnitEpsilon (F := F) s s (j + 1) = 0 := by
  have h := congrArg (fun z => z.2 j.succ)
    (negativeSourceRect_unitDelta (F := F) s)
  exact Sum.inl.inj h

/-- The first nontrivial response column alternates in the negative
orientation, as required by the triangular mixed-Hessian calculation. -/
theorem negativeUnitEpsilon_col_one (s m : ℕ) (hm : m < s) :
    negativeUnitEpsilon (F := F) s m 1 =
      (-1 : F) ^ (s - 1 - m) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  let eps : ℕ → ℕ → F := negativeUnitEpsilon (F := F) (t + 1)
  have hcorner : eps (t + 1) 0 = 1 := by
    exact negativeUnitEpsilon_corner (F := F) (t + 1)
  have hbottom : eps (t + 1) 1 = 0 := by
    simpa using negativeUnitEpsilon_bottom (F := F) (t + 1) (0 : Fin (t + 1))
  have hrecBase := negativeBoundaryValue_rec (F := F) (t + 1)
    (negativeUnitDeltaL (F := F) (t + 1))
    (negativeUnitDeltaR (F := F) (t + 1)) t 0 (by omega) (by omega)
  change eps (t + 1) 0 = eps t 1 + eps (t + 1) 1 at hrecBase
  have hbase : eps t 1 = 1 := by
    rw [hcorner, hbottom] at hrecBase
    simpa using hrecBase.symm
  change eps m 1 = (-1 : F) ^ (t + 1 - 1 - m)
  apply Nat.decreasingInduction (n := t)
      (motive := fun k _ => eps k 1 = (-1 : F) ^ (t + 1 - 1 - k))
      _ (by simpa using hbase) (by omega)
  intro k hk hsucc
  have hrec := negativeBoundaryValue_rec (F := F) (t + 1)
    (negativeUnitDeltaL (F := F) (t + 1))
    (negativeUnitDeltaR (F := F) (t + 1)) k 0 (by omega) (by omega)
  change eps (k + 1) 0 = eps k 1 + eps (k + 1) 1 at hrec
  have hleft : eps (k + 1) 0 = 0 := by
    exact negativeUnitEpsilon_left (F := F) (t + 1) ⟨k + 1, by omega⟩
  rw [hleft, hsucc] at hrec
  rw [show t + 1 - 1 - k = (t + 1 - 1 - (k + 1)) + 1 by omega,
    pow_succ]
  linear_combination -hrec

/-- Fin-indexed form of the literal negative exponent. -/
theorem rectangularCircuitExponent_negativeBoundary_fin
    (s : ℕ) (q : F) (L : Fin s → F) (R : Fin (s + 1) → F) :
    rectangularCircuitExponent F (s + 1) (negativeBoundaryRect s q L R) =
      ∑ i : Fin (s + 1), ∑ j : Fin s,
        (negativeBoundaryValue s L R i j -
          negativeBoundaryValue s L R i (j + 1)) *
            (negativeBoundaryValue s L R i (j + 1)) ^ 2 := by
  rw [rectangularCircuitExponent_negativeBoundary]
  simp only [← Fin.sum_univ_eq_sum_range]

/-- The final response row contains no left-boundary variables. -/
theorem negativeBoundaryValue_last_row (s : ℕ) (L : Fin s → F)
    (R : Fin (s + 1) → F) (j : ℕ) :
    negativeBoundaryValue s L R s j = negativeBoundaryValue s 0 R s j := by
  classical
  unfold negativeBoundaryValue
  have hU (m : Fin s) : UnegF (F := F) m s j = 0 := by
    unfold UnegF Uneg
    rw [if_neg (by omega)]
    norm_num
  simp [hU]

/-- The extra bottom row of the literal negative circuit is a phase
depending only on the right boundary. -/
def negativeLastRowPhase (epsilon : ℕ → ℕ → F) (s : ℕ)
    (R : Fin (s + 1) → F) : F :=
  ∑ j : Fin s, negativeFullCellPhase epsilon s 0 R s j

theorem negativeFullCellPhase_last_row
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) (j : ℕ) :
    negativeFullCellPhase epsilon s L R s j =
      negativeFullCellPhase epsilon s 0 R s j := by
  unfold negativeFullCellPhase
  conv_lhs =>
    rw [negativeBoundaryValue_last_row s L R j,
      negativeBoundaryValue_last_row s L R (j + 1)]

/-- The marked displacement turns the literal negative circuit phase
difference into the full negative response-grid cubic difference, plus the
one-sided phase from the circuit's asymmetric final row. -/
theorem rectangularCircuitExponent_negative_difference
    (s : ℕ) (q : F) (L : Fin s → F) (R : Fin (s + 1) → F) :
    rectangularCircuitExponent F (s + 1) (negativeBoundaryRect s q L R) -
        rectangularCircuitExponent F (s + 1)
          (negativeBoundaryRect s (q + negativeUnitDeltaQ (F := F) s)
            (L + negativeUnitDeltaL (F := F) s)
            (R + negativeUnitDeltaR (F := F) s)) =
      negativeFullGridPhase (negativeUnitEpsilon (F := F) s) s L R +
        negativeLastRowPhase (negativeUnitEpsilon (F := F) s) s R := by
  rw [rectangularCircuitExponent_negativeBoundary_fin,
    rectangularCircuitExponent_negativeBoundary_fin]
  unfold negativeFullGridPhase negativeLastRowPhase
  have hadd (i j : ℕ) :
      negativeBoundaryValue s (L + negativeUnitDeltaL (F := F) s)
          (R + negativeUnitDeltaR (F := F) s) i j =
        negativeBoundaryValue s L R i j +
          negativeBoundaryValue s (negativeUnitDeltaL (F := F) s)
            (negativeUnitDeltaR (F := F) s) i j :=
    negativeBoundaryValue_add s L _ R _ i j
  have hrow (i : Fin (s + 1)) :
      (∑ j : Fin s,
          (negativeBoundaryValue s L R i j -
            negativeBoundaryValue s L R i (j + 1)) *
              (negativeBoundaryValue s L R i (j + 1)) ^ 2) -
        ∑ j : Fin s,
          (negativeBoundaryValue s (L + negativeUnitDeltaL (F := F) s)
              (R + negativeUnitDeltaR (F := F) s) i j -
            negativeBoundaryValue s (L + negativeUnitDeltaL (F := F) s)
              (R + negativeUnitDeltaR (F := F) s) i (j + 1)) *
                (negativeBoundaryValue s
                  (L + negativeUnitDeltaL (F := F) s)
                  (R + negativeUnitDeltaR (F := F) s) i (j + 1)) ^ 2 =
        ∑ j : Fin s, negativeFullCellPhase
          (negativeUnitEpsilon (F := F) s) s L R i j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hadd, hadd]
    rfl
  rw [← Finset.sum_sub_distrib]
  simp_rw [hrow]
  rw [Fin.sum_univ_castSucc]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact negativeFullCellPhase_last_row _ s L R j

end SqrtOpEnt
