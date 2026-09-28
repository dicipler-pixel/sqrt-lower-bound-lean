import RequestProject.RectangularCore

/-!
# Colour action of the crossing rectangle

The internal finite-field shear changes labels, but each active crossing swaps
the two visible colours.  Here we prove that the explicit `t^2` adjacent-swap
word `crossingSchedule t` transposes the two length-`t` colour packets.
-/

namespace SqrtOpEnt

/-! We first calculate a descending adjacent-swap word on a total `Nat`-indexed
sequence, avoiding boundary coercions during the combinatorial argument. -/

/-- Swap adjacent natural-number positions. -/
def natSwapAt {alpha : Type*} (i : ℕ) (c : ℕ → alpha) : ℕ → alpha :=
  fun p => if p = i then c (i + 1) else if p = i + 1 then c i else c p

/-- Apply adjacent swaps in list order. -/
def natSwapCircuit {alpha : Type*} : List ℕ → (ℕ → alpha) → (ℕ → alpha)
  | [], c => c
  | i :: tail, c => natSwapCircuit tail (natSwapAt i c)

/-- The word moving the entry at `i+n` leftward to `i`. -/
def descendingSwaps (i n : ℕ) : List ℕ :=
  (List.range n).reverse.map fun j => i + j

@[simp] theorem descendingSwaps_zero (i : ℕ) : descendingSwaps i 0 = [] := rfl

theorem descendingSwaps_succ (i n : ℕ) :
    descendingSwaps i (n + 1) = (i + n) :: descendingSwaps i n := by
  simp [descendingSwaps, List.range_succ]

/-- Closed form of one descending word: rotate the interval `[i,i+n]` once
to the right, moving its last entry to its first position. -/
def moveLastToFront {alpha : Type*} (i n : ℕ) (c : ℕ → alpha) : ℕ → alpha :=
  fun p => if p = i then c (i + n)
    else if i < p ∧ p ≤ i + n then c (p - 1)
    else c p

theorem natSwapCircuit_descending {alpha : Type*} (i n : ℕ) (c : ℕ → alpha) :
    natSwapCircuit (descendingSwaps i n) c = moveLastToFront i n c := by
  induction n generalizing c with
  | zero =>
      funext p
      simp only [descendingSwaps_zero, natSwapCircuit]
      by_cases hpi : p = i
      · subst p
        simp [moveLastToFront]
      · rw [moveLastToFront, if_neg hpi,
          if_neg (show ¬ (i < p ∧ p ≤ i + 0) by omega)]
  | succ n ih =>
      rw [descendingSwaps_succ]
      simp only [natSwapCircuit]
      rw [ih]
      funext p
      simp only [moveLastToFront, natSwapAt]
      split_ifs <;> try rfl
      all_goals (congr 1; omega)

/-! After `b` right strands have crossed, the layout is
`B[0:b] ++ A ++ B[b:t]`. -/

/-- Explicit state after the first `b` blocks of a block transposition. -/
def afterBlocks {alpha : Type*} (t b : ℕ) (c : ℕ → alpha) : ℕ → alpha :=
  fun p => if p < b then c (t + p)
    else if p < b + t then c (p - b)
    else c p

@[simp] theorem afterBlocks_zero {alpha : Type*} (t : ℕ) (c : ℕ → alpha) :
    afterBlocks t 0 c = c := by
  funext p
  simp [afterBlocks]

/-- One descending word advances the explicit layout by one block. -/
theorem moveLastToFront_afterBlocks {alpha : Type*}
    (t b : ℕ) (hb : b < t) (c : ℕ → alpha) :
    moveLastToFront b t (afterBlocks t b c) = afterBlocks t (b + 1) c := by
  funext p
  simp only [moveLastToFront, afterBlocks]
  split_ifs <;> try rfl
  all_goals (congr 1; omega)

/-- The prefix consisting of the first `b` crossing blocks. -/
def crossingPrefix (t b : ℕ) : List ℕ :=
  (List.range b).flatMap fun a => descendingSwaps a t

@[simp] theorem crossingPrefix_zero (t : ℕ) : crossingPrefix t 0 = [] := rfl

theorem crossingPrefix_succ (t b : ℕ) :
    crossingPrefix t (b + 1) = crossingPrefix t b ++ descendingSwaps b t := by
  simp [crossingPrefix, List.range_succ]

theorem natSwapCircuit_append {alpha : Type*} (u v : List ℕ) (c : ℕ → alpha) :
    natSwapCircuit (u ++ v) c = natSwapCircuit v (natSwapCircuit u c) := by
  induction u generalizing c with
  | nil => rfl
  | cons i tail ih =>
      simp only [List.cons_append, natSwapCircuit]
      rw [ih]

/-- Closed form after any valid number of crossing blocks. -/
theorem natSwapCircuit_crossingPrefix {alpha : Type*}
    (t b : ℕ) (hb : b ≤ t) (c : ℕ → alpha) :
    natSwapCircuit (crossingPrefix t b) c = afterBlocks t b c := by
  induction b with
  | zero => simp [natSwapCircuit]
  | succ b ih =>
      rw [crossingPrefix_succ, natSwapCircuit_append,
        ih (by omega), natSwapCircuit_descending,
        moveLastToFront_afterBlocks t b (by omega)]

/-- The manuscript schedule is the full crossing prefix. -/
theorem crossingSchedule_eq_prefix (t : ℕ) :
    crossingSchedule t = crossingPrefix t t := by
  rfl

/-- Total-array form of block transposition. -/
theorem natSwapCircuit_crossingSchedule {alpha : Type*} (t : ℕ) (c : ℕ → alpha) :
    natSwapCircuit (crossingSchedule t) c = afterBlocks t t c := by
  rw [crossingSchedule_eq_prefix, natSwapCircuit_crossingPrefix t t (le_refl t)]

/-! ## Transfer back to finite colour configurations -/

/-- Extend a finite tuple by a default value outside its range. -/
def extendFin {alpha : Type*} [Inhabited alpha]
    (n : ℕ) (c : Fin n → alpha) : ℕ → alpha :=
  fun p => if h : p < n then c ⟨p, h⟩ else default

@[simp] theorem extendFin_apply {alpha : Type*} [Inhabited alpha]
    {n : ℕ} (c : Fin n → alpha) (p : Fin n) :
    extendFin n c p = c p := by
  simp [extendFin]

/-- On an in-range adjacent pair, extending a finite swap agrees with the
corresponding total natural-number swap. -/
theorem extendFin_swapAtFun {alpha : Type*} [Inhabited alpha]
    (n i : ℕ) (h : i + 1 < n) (c : Fin n → alpha) :
    extendFin n (swapAtFun n i c) = natSwapAt i (extendFin n c) := by
  funext p
  by_cases hp : p < n
  · by_cases hpi : p = i
    · subst p
      (simp [extendFin, swapAtFun, natSwapAt, h]; omega)
    · by_cases hpis : p = i + 1
      · subst p
        (simp [extendFin, swapAtFun, natSwapAt, h]; omega)
      · have hp_i :
            (⟨p, hp⟩ : Fin n) ≠ ⟨i, by omega⟩ := by
          intro he
          exact hpi (congrArg Fin.val he)
        have hp_is :
            (⟨p, hp⟩ : Fin n) ≠ ⟨i + 1, by omega⟩ := by
          intro he
          exact hpis (congrArg Fin.val he)
        simp [extendFin, swapAtFun, natSwapAt, h, hp, hpi, hpis, hp_i, hp_is]
  · have hpi : p ≠ i := by omega
    have hpis : p ≠ i + 1 := by omega
    simp [extendFin, natSwapAt, hp, hpi, hpis]

instance : Inhabited VisibleColour := ⟨VisibleColour.A⟩

/-- A finite adjacent-swap circuit agrees with its total-array counterpart
provided every address in the word is valid. -/
theorem extendFin_colourCircuit
    (n : ℕ) (word : List ℕ) (c : Fin n → VisibleColour)
    (hvalid : ∀ i ∈ word, i + 1 < n) :
    extendFin n (colourCircuit n word c) =
      natSwapCircuit word (extendFin n c) := by
  induction word generalizing c with
  | nil => rfl
  | cons i tail ih =>
      simp only [colourCircuit, natSwapCircuit]
      rw [ih (swapAtFun n i c) (by
        intro j hj
        exact hvalid j (by simp [hj])),
        extendFin_swapAtFun n i (hvalid i (by simp))]

/-- The finite colour circuit of the complete rectangle is block
transposition, stated pointwise in spatial coordinates. -/
theorem colourCircuit_crossingSchedule (t : ℕ)
    (c : Fin (t + t) → VisibleColour) (p : Fin (t + t)) :
    colourCircuit (t + t) (crossingSchedule t) c p =
      if h : (p : ℕ) < t then
        c ⟨t + p, by omega⟩
      else c ⟨(p : ℕ) - t, by omega⟩ := by
  have hext := extendFin_colourCircuit (t + t) (crossingSchedule t) c
    (fun i hi => mem_crossingSchedule_lt hi)
  rw [natSwapCircuit_crossingSchedule] at hext
  have hp := congrFun hext (p : ℕ)
  rw [extendFin_apply] at hp
  by_cases hleft : (p : ℕ) < t
  · rw [dif_pos hleft]
    simpa [afterBlocks, extendFin, hleft] using hp
  · rw [dif_neg hleft]
    have htotal : (p : ℕ) < t + t := p.isLt
    have hsub : (p : ℕ) - t < t + t := by omega
    simpa [afterBlocks, extendFin, hleft, htotal, hsub] using hp

/-! ## Colour action of the actual triangular-gate permutation -/

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- The support permutation of the triangular-gate rectangle has the computed
block-transpose action after forgetting internal field labels. -/
theorem colour_spatialCircuitPerm_crossingSchedule
    (t : ℕ) (v : SpatialBasis F (t + t)) (p : Fin (t + t)) :
    siteColour F (spatialCircuitPerm F (t + t) (crossingSchedule t) v p) =
      if h : (p : ℕ) < t then
        siteColour F (v ⟨t + p, by omega⟩)
      else siteColour F (v ⟨(p : ℕ) - t, by omega⟩) := by
  calc
    _ = colourCircuit (t + t) (crossingSchedule t)
        (fun j => siteColour F (v j)) p :=
      congrFun (colour_spatialCircuitPerm F (t + t) (crossingSchedule t) v) p
    _ = _ := colourCircuit_crossingSchedule t _ p

omit [Fintype F] [DecidableEq F] in
/-- The output left packet receives exactly the input right packet's colour word. -/
theorem siteColour_rectangularCircuitPerm_fst
    (t : ℕ) (u : RectBasis F t) (i : Fin t) :
    siteColour F ((rectangularCircuitPerm F t u).1 i) = siteColour F (u.2 i) := by
  have h := colour_spatialCircuitPerm_crossingSchedule F t
    (packetsToSpatial F u) (Fin.castAdd t i)
  have hleft : ((Fin.castAdd t i : Fin (t + t)) : ℕ) < t := i.isLt
  rw [dif_pos hleft] at h
  have hind : (⟨t + (Fin.castAdd t i : ℕ), by omega⟩ : Fin (t + t)) =
      Fin.natAdd t i := by
    apply Fin.ext
    change t + (i : ℕ) = (Fin.natAdd t i : ℕ)
    simp only [Fin.val_natAdd]
  rw [hind] at h
  have happ : packetsToSpatial F u (Fin.natAdd t i) = u.2 i := by
    have hi := congrArg (fun z => z.2 i)
      ((packetsToSpatial F (t := t)).symm_apply_apply u)
    simpa [packetsToSpatial, Fin.appendEquiv] using hi
  rw [happ] at h
  change siteColour F
    (spatialCircuitPerm F (t + t) (crossingSchedule t) (packetsToSpatial F u)
      (Fin.castAdd t i)) = siteColour F (u.2 i)
  exact h

omit [Fintype F] [DecidableEq F] in
/-- The output right packet receives exactly the input left packet's colour word. -/
theorem siteColour_rectangularCircuitPerm_snd
    (t : ℕ) (u : RectBasis F t) (i : Fin t) :
    siteColour F ((rectangularCircuitPerm F t u).2 i) = siteColour F (u.1 i) := by
  have h := colour_spatialCircuitPerm_crossingSchedule F t
    (packetsToSpatial F u) (Fin.natAdd t i)
  rw [dif_neg (show ¬ ((Fin.natAdd t i : Fin (t + t)) : ℕ) < t by
    simp only [Fin.val_natAdd]
    omega)] at h
  have hind : (⟨(Fin.natAdd t i : ℕ) - t, by omega⟩ : Fin (t + t)) =
      Fin.castAdd t i := by
    apply Fin.ext
    change (Fin.natAdd t i : ℕ) - t = (i : ℕ)
    simp only [Fin.val_natAdd]
    omega
  rw [hind] at h
  have happ : packetsToSpatial F u (Fin.castAdd t i) = u.1 i := by
    have hi := congrArg (fun z => z.1 i)
      ((packetsToSpatial F (t := t)).symm_apply_apply u)
    simpa [packetsToSpatial, Fin.appendEquiv] using hi
  rw [happ] at h
  change siteColour F
    (spatialCircuitPerm F (t + t) (crossingSchedule t) (packetsToSpatial F u)
      (Fin.natAdd t i)) = siteColour F (u.1 i)
  exact h

end SqrtOpEnt
