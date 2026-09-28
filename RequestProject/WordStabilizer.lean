import RequestProject.WordMeasurement

/-!
# Triviality of visible-word stabilizers

This file proves the coherence statement behind Lemma 5.1 without developing
the full type-A Coxeter presentation.  Since there are only two visible
colours, orienting every mixed crossing as `B A -> A B` gives a terminating
sorting procedure.  Braided insertion sort supplies a canonical map from
each full internal colour fibre to its sorted fibre.  A single adjacent gate
does not change that canonical map.  Consequently any gate word which returns
to its initial visible word acts identically on the complete internal fibre.
-/

namespace SqrtOpEnt

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## A list model for adjacent gates -/

/-- Apply the triangular support map at two adjacent positions of a list.
Invalid addresses act as the identity. -/
def listGateAt : ℕ → List (Vq F) → List (Vq F)
  | 0, x :: y :: tail =>
      let p := gateFun F (x, y)
      p.1 :: p.2 :: tail
  | i + 1, x :: tail => x :: listGateAt i tail
  | _, v => v

/-- Finite-field exponent of one list crossing. -/
def listGateAtExponent : ℕ → List (Vq F) → F
  | 0, x :: y :: _ => gateExponent F (x, y)
  | i + 1, _ :: tail => listGateAtExponent i tail
  | _, _ => 0

@[simp] theorem listGateAt_length (i : ℕ) (v : List (Vq F)) :
    (listGateAt (F := F) i v).length = v.length := by
  induction i generalizing v with
  | zero =>
      cases v with
      | nil => rfl
      | cons x rest =>
          cases rest with
          | nil => rfl
          | cons y tail => simp [listGateAt]
  | succ i ih =>
      rcases v with _ | ⟨x, tail⟩
      · rfl
      · simp [listGateAt, ih]

/-- Apply a list word of adjacent triangular gates, head first. -/
def listGateCircuit : List ℕ → List (Vq F) → List (Vq F)
  | [], v => v
  | i :: tail, v => listGateCircuit tail (listGateAt i v)

/-- Accumulated exponent for the list circuit. -/
def listGateCircuitExponent : List ℕ → List (Vq F) → F
  | [], _ => 0
  | i :: tail, v =>
      listGateCircuitExponent tail (listGateAt i v) +
        listGateAtExponent i v

@[simp] theorem listGateCircuit_length (word : List ℕ) (v : List (Vq F)) :
    (listGateCircuit (F := F) word v).length = v.length := by
  induction word generalizing v with
  | nil => rfl
  | cons i word ih => simp [listGateCircuit, ih]

/-! ## Braided insertion sort -/

/-- Insert one site into an already colour-sorted list.  Only a leading `B`
crossing an `A` invokes the triangular gate. -/
def braidedInsert : Vq F → List (Vq F) → List (Vq F)
  | x, [] => [x]
  | Sum.inr c, Sum.inl d :: tail =>
      let p := gateFun F (Sum.inr c, Sum.inl d)
      p.1 :: braidedInsert p.2 tail
  | x, y :: tail => x :: y :: tail

/-- Exponent accumulated by `braidedInsert`. -/
def braidedInsertExponent : Vq F → List (Vq F) → F
  | _, [] => 0
  | Sum.inr c, Sum.inl d :: tail =>
      let p := gateFun F (Sum.inr c, Sum.inl d)
      braidedInsertExponent p.2 tail +
        gateExponent F (Sum.inr c, Sum.inl d)
  | _, _ :: _ => 0

/-- Canonically sort a fully labelled two-colour word. -/
def braidedSort : List (Vq F) → List (Vq F)
  | [] => []
  | x :: tail => braidedInsert x (braidedSort tail)

/-- Total finite-field phase accumulated by braided insertion sort. -/
def braidedSortExponent : List (Vq F) → F
  | [] => 0
  | x :: tail =>
      braidedInsertExponent x (braidedSort tail) +
        braidedSortExponent tail

@[simp] theorem braidedInsert_length (x : Vq F) (v : List (Vq F)) :
    (braidedInsert x v).length = v.length + 1 := by
  induction v generalizing x with
  | nil => cases x <;> rfl
  | cons y tail ih =>
      rcases x with a | a <;> rcases y with b | b <;>
        simp [braidedInsert, ih]

@[simp] theorem braidedSort_length (v : List (Vq F)) :
    (braidedSort v).length = v.length := by
  induction v with
  | nil => rfl
  | cons x tail ih => simp [braidedSort, ih]

/-! The concrete adjacent-gate words implementing the two recursive maps. -/

/-- Shift every adjacent-gate address by one, leaving a new head site
untouched. -/
def shiftGateWord (word : List ℕ) : List ℕ := word.map Nat.succ

/-- Shift every adjacent-gate address by an arbitrary prefix length. -/
def shiftGateWordBy (k : ℕ) (word : List ℕ) : List ℕ :=
  word.map (k + ·)

@[simp] theorem shiftGateWordBy_zero (word : List ℕ) :
    shiftGateWordBy 0 word = word := by
  simp [shiftGateWordBy]

theorem shiftGateWordBy_succ (k : ℕ) (word : List ℕ) :
    shiftGateWordBy (k + 1) word =
      shiftGateWord (shiftGateWordBy k word) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change (k + 1 + i) :: shiftGateWordBy (k + 1) word =
        (k + i + 1) :: shiftGateWord (shiftGateWordBy k word)
      rw [ih]
      congr 1 <;> omega

theorem shiftGateWordBy_shift (k : ℕ) (word : List ℕ) :
    shiftGateWordBy k (shiftGateWord word) =
      shiftGateWord (shiftGateWordBy k word) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change (k + (i + 1)) :: shiftGateWordBy k (shiftGateWord word) =
        (k + i + 1) :: shiftGateWord (shiftGateWordBy k word)
      rw [ih]
      congr 1 <;> omega

/-- Adjacent word implementing `braidedInsert`. -/
def braidedInsertSchedule : Vq F → List (Vq F) → List ℕ
  | Sum.inr _, Sum.inl d :: tail =>
      0 :: shiftGateWord (braidedInsertSchedule (Sum.inr d) tail)
  | _, _ => []

/-- Adjacent word implementing recursive braided insertion sort. -/
def braidedSortSchedule : List (Vq F) → List ℕ
  | [] => []
  | x :: tail =>
      shiftGateWord (braidedSortSchedule tail) ++
        braidedInsertSchedule x (braidedSort tail)

/-- Every address used by braided insertion is valid in the full input
list. -/
theorem mem_braidedInsertSchedule_lt (x : Vq F) (v : List (Vq F))
    {i : ℕ} (hi : i ∈ braidedInsertSchedule x v) :
    i + 1 < (x :: v).length := by
  induction v generalizing x i with
  | nil => cases x <;> simp [braidedInsertSchedule] at hi
  | cons y tail ih =>
      rcases x with a | a <;> rcases y with b | b
      · simp [braidedInsertSchedule] at hi
      · simp [braidedInsertSchedule] at hi
      · simp only [braidedInsertSchedule, List.mem_cons,
          shiftGateWord, List.mem_map] at hi
        rcases hi with rfl | ⟨j, hj, rfl⟩
        · simp
        · have := ih (Sum.inr b) hj
          simp only [List.length_cons] at this ⊢
          omega
      · simp [braidedInsertSchedule] at hi

/-- Every address used by braided sorting is valid in the sorted list. -/
theorem mem_braidedSortSchedule_lt (v : List (Vq F))
    {i : ℕ} (hi : i ∈ braidedSortSchedule v) :
    i + 1 < v.length := by
  induction v generalizing i with
  | nil => simp [braidedSortSchedule] at hi
  | cons x tail ih =>
      simp only [braidedSortSchedule, List.mem_append, shiftGateWord,
        List.mem_map] at hi
      rcases hi with ⟨j, hj, rfl⟩ | hi
      · have := ih hj
        simp only [List.length_cons]
        omega
      · simpa using mem_braidedInsertSchedule_lt x (braidedSort tail) hi

/-- Shifting a gate word leaves the head site fixed. -/
theorem listGateCircuit_shiftGateWord (word : List ℕ)
    (x : Vq F) (v : List (Vq F)) :
    listGateCircuit (F := F) (shiftGateWord word) (x :: v) =
      x :: listGateCircuit (F := F) word v := by
  induction word generalizing x v with
  | nil => rfl
  | cons i tail ih =>
      simp only [shiftGateWord, List.map_cons, listGateCircuit, listGateAt]
      exact ih x (listGateAt i v)

/-- The shifted word has the same exponent as the unshifted tail word. -/
theorem listGateCircuitExponent_shiftGateWord (word : List ℕ)
    (x : Vq F) (v : List (Vq F)) :
    listGateCircuitExponent (F := F) (shiftGateWord word) (x :: v) =
      listGateCircuitExponent (F := F) word v := by
  induction word generalizing x v with
  | nil => rfl
  | cons i tail ih =>
      simp only [shiftGateWord, List.map_cons, listGateCircuitExponent,
        listGateAt, listGateAtExponent]
      simpa [shiftGateWord] using congrArg
        (fun z => z + listGateAtExponent (F := F) i v)
        (ih x (listGateAt (F := F) i v))

/-- A shifted circuit acts only after a fixed prefix. -/
theorem listGateCircuit_shiftGateWordBy (pre : List (Vq F))
    (word : List ℕ) (v : List (Vq F)) :
    listGateCircuit (F := F) (shiftGateWordBy pre.length word)
        (pre ++ v) =
      pre ++ listGateCircuit (F := F) word v := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
      rw [List.length_cons, shiftGateWordBy_succ]
      change listGateCircuit (F := F)
          (shiftGateWord (shiftGateWordBy pre.length word))
          (x :: (pre ++ v)) = _
      rw [listGateCircuit_shiftGateWord, ih]
      simp

/-- The shifted circuit has exactly the exponent of the unshifted suffix
circuit. -/
theorem listGateCircuitExponent_shiftGateWordBy
    (pre : List (Vq F)) (word : List ℕ) (v : List (Vq F)) :
    listGateCircuitExponent (F := F)
        (shiftGateWordBy pre.length word) (pre ++ v) =
      listGateCircuitExponent (F := F) word v := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
      rw [List.length_cons, shiftGateWordBy_succ]
      change listGateCircuitExponent (F := F)
          (shiftGateWord (shiftGateWordBy pre.length word))
          (x :: (pre ++ v)) = _
      rw [listGateCircuitExponent_shiftGateWord, ih]

/-- A valid adjacent gate commutes with appending an untouched suffix. -/
theorem listGateAt_append_of_lt (i : ℕ) (v tail : List (Vq F))
    (hi : i + 1 < v.length) :
    listGateAt (F := F) i (v ++ tail) =
      listGateAt (F := F) i v ++ tail := by
  induction i generalizing v with
  | zero =>
      rcases v with _ | ⟨x, v⟩
      · simp at hi
      rcases v with _ | ⟨y, rest⟩
      · simp at hi
      simp [listGateAt]
  | succ i ih =>
      rcases v with _ | ⟨x, rest⟩
      · simp at hi
      simp only [List.length_cons] at hi
      simp only [List.cons_append, listGateAt]
      rw [ih rest (by omega)]

/-- Appending an untouched suffix does not change a valid gate exponent. -/
theorem listGateAtExponent_append_of_lt (i : ℕ)
    (v tail : List (Vq F)) (hi : i + 1 < v.length) :
    listGateAtExponent (F := F) i (v ++ tail) =
      listGateAtExponent (F := F) i v := by
  induction i generalizing v with
  | zero =>
      rcases v with _ | ⟨x, v⟩
      · simp at hi
      rcases v with _ | ⟨y, rest⟩
      · simp at hi
      simp [listGateAtExponent]
  | succ i ih =>
      rcases v with _ | ⟨x, rest⟩
      · simp at hi
      simp only [List.length_cons] at hi
      simp only [List.cons_append, listGateAtExponent]
      exact ih rest (by omega)

/-- A circuit whose every address is valid in `v` leaves an appended suffix
untouched. -/
theorem listGateCircuit_append_suffix_of_forall
    (word : List ℕ) (v tail : List (Vq F))
    (hvalid : ∀ i ∈ word, i + 1 < v.length) :
    listGateCircuit (F := F) word (v ++ tail) =
      listGateCircuit (F := F) word v ++ tail := by
  induction word generalizing v with
  | nil => rfl
  | cons i word ih =>
      simp only [listGateCircuit]
      rw [listGateAt_append_of_lt i v tail (hvalid i (by simp))]
      apply ih
      · intro j hj
        simpa using hvalid j (by simp [hj])

/-- Under the same validity condition, an appended suffix contributes no
phase. -/
theorem listGateCircuitExponent_append_suffix_of_forall
    (word : List ℕ) (v tail : List (Vq F))
    (hvalid : ∀ i ∈ word, i + 1 < v.length) :
    listGateCircuitExponent (F := F) word (v ++ tail) =
      listGateCircuitExponent (F := F) word v := by
  induction word generalizing v with
  | nil => rfl
  | cons i word ih =>
      simp only [listGateCircuitExponent]
      rw [listGateAt_append_of_lt i v tail (hvalid i (by simp)),
        listGateAtExponent_append_of_lt i v tail (hvalid i (by simp))]
      rw [ih]
      · intro j hj
        simpa using hvalid j (by simp [hj])

/-- A valid word embedded after `pre` acts only on the middle segment. -/
theorem listGateCircuit_segment (pre core post : List (Vq F))
    (word : List ℕ) (hvalid : ∀ i ∈ word, i + 1 < core.length) :
    listGateCircuit (F := F) (shiftGateWordBy pre.length word)
        (pre ++ core ++ post) =
      pre ++ listGateCircuit (F := F) word core ++ post := by
  rw [List.append_assoc, listGateCircuit_shiftGateWordBy]
  rw [listGateCircuit_append_suffix_of_forall word core post hvalid]
  simp [List.append_assoc]

/-- The exponent of an embedded valid word is the exponent of its middle
segment. -/
theorem listGateCircuitExponent_segment
    (pre core post : List (Vq F)) (word : List ℕ)
    (hvalid : ∀ i ∈ word, i + 1 < core.length) :
    listGateCircuitExponent (F := F)
        (shiftGateWordBy pre.length word) (pre ++ core ++ post) =
      listGateCircuitExponent (F := F) word core := by
  rw [List.append_assoc, listGateCircuitExponent_shiftGateWordBy]
  exact listGateCircuitExponent_append_suffix_of_forall word core post hvalid

/-- List circuits respect concatenation in head-first order. -/
theorem listGateCircuit_append (u w : List ℕ) (v : List (Vq F)) :
    listGateCircuit (F := F) (u ++ w) v =
      listGateCircuit (F := F) w (listGateCircuit (F := F) u v) := by
  induction u generalizing v with
  | nil => rfl
  | cons i tail ih =>
      simp only [List.cons_append, listGateCircuit]
      exact ih (listGateAt i v)

/-- Accumulated exponents split over concatenated list circuits. -/
theorem listGateCircuitExponent_append (u w : List ℕ)
    (v : List (Vq F)) :
    listGateCircuitExponent (F := F) (u ++ w) v =
      listGateCircuitExponent (F := F) w
          (listGateCircuit (F := F) u v) +
        listGateCircuitExponent (F := F) u v := by
  induction u generalizing v with
  | nil => simp [listGateCircuit, listGateCircuitExponent]
  | cons i tail ih =>
      simp only [List.cons_append, listGateCircuit,
        listGateCircuitExponent]
      rw [ih]
      ring

/-- The insertion schedule realizes `braidedInsert`. -/
theorem listGateCircuit_braidedInsertSchedule
    (x : Vq F) (v : List (Vq F)) :
    listGateCircuit (F := F) (braidedInsertSchedule x v) (x :: v) =
      braidedInsert x v := by
  induction v generalizing x with
  | nil => cases x <;> rfl
  | cons y tail ih =>
      rcases x with a | a <;> rcases y with b | b
      · rfl
      · rfl
      · simp only [braidedInsertSchedule, listGateCircuit, listGateAt,
          gateFun, braidedInsert]
        rw [listGateCircuit_shiftGateWord]
        congr 1
        exact ih (Sum.inr b)
      · rfl

/-- Its accumulated exponent is `braidedInsertExponent`. -/
theorem listGateCircuitExponent_braidedInsertSchedule
    (x : Vq F) (v : List (Vq F)) :
    listGateCircuitExponent (F := F) (braidedInsertSchedule x v) (x :: v) =
      braidedInsertExponent x v := by
  induction v generalizing x with
  | nil => cases x <;> rfl
  | cons y tail ih =>
      rcases x with a | a <;> rcases y with b | b
      · rfl
      · rfl
      · simp only [braidedInsertSchedule, listGateCircuitExponent,
          listGateAt, listGateAtExponent, gateFun, braidedInsertExponent]
        rw [listGateCircuitExponent_shiftGateWord, ih]
      · rfl

/-- The canonical sorting schedule realizes `braidedSort`. -/
theorem listGateCircuit_braidedSortSchedule (v : List (Vq F)) :
    listGateCircuit (F := F) (braidedSortSchedule v) v = braidedSort v := by
  induction v with
  | nil => rfl
  | cons x tail ih =>
      simp only [braidedSortSchedule, listGateCircuit_append,
        listGateCircuit_shiftGateWord, ih, braidedSort]
      exact listGateCircuit_braidedInsertSchedule x (braidedSort tail)

/-- The sorting schedule realizes `braidedSortExponent`. -/
theorem listGateCircuitExponent_braidedSortSchedule (v : List (Vq F)) :
    listGateCircuitExponent (F := F) (braidedSortSchedule v) v =
      braidedSortExponent v := by
  induction v with
  | nil => rfl
  | cons x tail ih =>
      rw [braidedSortSchedule, listGateCircuitExponent_append,
        listGateCircuit_shiftGateWord,
        listGateCircuitExponent_shiftGateWord, ih,
        listGateCircuit_braidedSortSchedule,
        listGateCircuitExponent_braidedInsertSchedule]
      rfl

@[simp] theorem braidedInsert_A (a : F) (v : List (Vq F)) :
    braidedInsert (Sum.inl a) v = Sum.inl a :: v := by
  cases v <;> simp [braidedInsert]

@[simp] theorem braidedInsertExponent_A (a : F) (v : List (Vq F)) :
    braidedInsertExponent (Sum.inl a) v = 0 := by
  cases v <;> simp [braidedInsertExponent]

@[simp] theorem braidedInsert_B_nil (b : F) :
    braidedInsert (Sum.inr b) [] = [Sum.inr b] := rfl

@[simp] theorem braidedInsertExponent_B_nil (b : F) :
    braidedInsertExponent (Sum.inr b) [] = 0 := rfl

/-- A single adjacent triangular gate does not change the canonically
sorted fully-labelled configuration. -/
theorem braidedSort_listGateAt (i : ℕ) (v : List (Vq F)) :
    braidedSort (listGateAt (F := F) i v) = braidedSort v := by
  induction i generalizing v with
  | zero =>
      rcases v with _ | ⟨x, v⟩
      · rfl
      rcases v with _ | ⟨y, tail⟩
      · simp [listGateAt]
      rcases x with a | a <;> rcases y with b | b <;>
        simp [listGateAt, braidedSort, braidedInsert, gateFun]
  | succ i ih =>
      rcases v with _ | ⟨x, v⟩
      · rfl
      rcases v with _ | ⟨y, tail⟩
      · simp [listGateAt]
      simp only [listGateAt, braidedSort]
      rw [ih]
      rfl

/-- The phase of a single crossing followed by canonical sorting is the
canonical sorting phase of the original word. -/
theorem braidedSortExponent_listGateAt (i : ℕ) (v : List (Vq F)) :
    braidedSortExponent (listGateAt (F := F) i v) +
        listGateAtExponent (F := F) i v =
      braidedSortExponent v := by
  induction i generalizing v with
  | zero =>
      rcases v with _ | ⟨x, v⟩
      · simp [listGateAt, listGateAtExponent, braidedSortExponent]
      rcases v with _ | ⟨y, tail⟩
      · simp [listGateAt, listGateAtExponent, braidedSortExponent]
      rcases x with a | a <;> rcases y with b | b <;>
        simp [listGateAt, listGateAtExponent, braidedSort,
          braidedSortExponent, braidedInsert, braidedInsertExponent,
          gateFun, gateExponent] <;> ring
  | succ i ih =>
      rcases v with _ | ⟨x, v⟩
      · simp [listGateAt, listGateAtExponent, braidedSortExponent]
      rcases v with _ | ⟨y, tail⟩
      · simp [listGateAt, listGateAtExponent, braidedSortExponent]
      simp only [listGateAt, listGateAtExponent, braidedSortExponent]
      rw [braidedSort_listGateAt, add_assoc, ih]
      rfl

/-- Visible word of a fully labelled list. -/
def visibleWordList (v : List (Vq F)) : List VisibleColour :=
  v.map (siteColour F)

/-- Ordinary insertion on two visible colours, in the order `A < B`. -/
def colourInsert : VisibleColour → List VisibleColour → List VisibleColour
  | c, [] => [c]
  | .B, .A :: tail => .A :: colourInsert .B tail
  | c, v => c :: v

@[simp] theorem colourInsert_A (v : List VisibleColour) :
    colourInsert .A v = .A :: v := by
  cases v with
  | nil => rfl
  | cons x tail => cases x <;> rfl

@[simp] theorem colourInsert_B_cons_B (v : List VisibleColour) :
    colourInsert .B (.B :: v) = .B :: .B :: v := rfl

/-- Ordinary insertion sort of a visible word. -/
def colourSort : List VisibleColour → List VisibleColour
  | [] => []
  | c :: tail => colourInsert c (colourSort tail)

/-- Forgetting labels turns braided insertion into ordinary colour
insertion. -/
theorem visibleWordList_braidedInsert (x : Vq F) (v : List (Vq F)) :
    visibleWordList (F := F) (braidedInsert x v) =
      colourInsert (siteColour F x) (visibleWordList (F := F) v) := by
  induction v generalizing x with
  | nil => cases x <;> rfl
  | cons y tail ih =>
      rcases x with a | a <;> rcases y with b | b
      · simp [visibleWordList, braidedInsert, siteColour]
      · simp [visibleWordList, braidedInsert, siteColour]
      · simp only [visibleWordList, braidedInsert, gateFun, List.map_cons,
          siteColour, colourInsert]
        congr 1
        exact ih (Sum.inr b)
      · simp [visibleWordList, braidedInsert, siteColour]

/-- Forgetting labels turns braided sorting into ordinary insertion sort. -/
theorem visibleWordList_braidedSort (v : List (Vq F)) :
    visibleWordList (F := F) (braidedSort v) =
      colourSort (visibleWordList (F := F) v) := by
  induction v with
  | nil => rfl
  | cons x tail ih =>
      rw [braidedSort, visibleWordList_braidedInsert, ih]
      rfl

@[simp] theorem colourInsert_B_normal (a b : ℕ) :
    colourInsert .B
        (List.replicate a .A ++ List.replicate b .B) =
      List.replicate a .A ++ List.replicate (b + 1) .B := by
  induction a with
  | zero =>
      cases b <;> simp [colourInsert, List.replicate_succ]
  | succ a ih =>
      simp [List.replicate_succ, colourInsert, ih]

/-- Closed form of binary insertion sort. -/
theorem colourSort_eq_normal (c : List VisibleColour) :
    colourSort c =
      List.replicate (c.count .A) .A ++
        List.replicate (c.count .B) .B := by
  induction c with
  | nil => rfl
  | cons x tail ih =>
      rcases x with _ | _
      · simp [colourSort, ih, colourInsert, List.replicate_succ]
      · simp [colourSort, ih, List.replicate_succ]

/-- A binary word is exhausted by its `A` and `B` counts. -/
theorem count_A_add_count_B (c : List VisibleColour) :
    c.count .A + c.count .B = c.length := by
  induction c with
  | nil => rfl
  | cons x tail ih =>
      have hAB : VisibleColour.A ≠ VisibleColour.B := by decide
      cases x with
      | A =>
          simp only [List.count_cons, List.length_cons]
          have hAA : (VisibleColour.A == VisibleColour.A) = true := by decide
          have hAB' : (VisibleColour.A == VisibleColour.B) = false := by decide
          rw [hAA, hAB']
          norm_num
          omega
      | B =>
          simp only [List.count_cons, List.length_cons]
          have hBA : (VisibleColour.B == VisibleColour.A) = false := by decide
          have hBB : (VisibleColour.B == VisibleColour.B) = true := by decide
          rw [hBA, hBB]
          norm_num
          omega

/-- Two words of the same length and with the same number of `A` letters
have the same canonical sorted visible word. -/
theorem colourSort_eq_of_length_countA_eq
    (c d : List VisibleColour) (hlen : c.length = d.length)
    (hA : c.count .A = d.count .A) :
    colourSort c = colourSort d := by
  have hc := count_A_add_count_B c
  have hd := count_A_add_count_B d
  have hB : c.count .B = d.count .B := by omega
  rw [colourSort_eq_normal, colourSort_eq_normal, hA, hB]

/-! ## Reversing paths and rearranging visible words -/

/-- One list gate is an involution. -/
theorem listGateAt_involutive (i : ℕ) :
    Function.Involutive (listGateAt (F := F) i) := by
  intro v
  induction i generalizing v with
  | zero =>
      rcases v with _ | ⟨x, v⟩
      · rfl
      rcases v with _ | ⟨y, tail⟩
      · rfl
      rcases x with a | a <;> rcases y with b | b <;>
        simp [listGateAt, gateFun]
  | succ i ih =>
      rcases v with _ | ⟨x, tail⟩
      · rfl
      simp only [listGateAt]
      rw [ih]

/-- Reversing a gate word gives its inverse support path. -/
theorem listGateCircuit_reverse_left (word : List ℕ)
    (v : List (Vq F)) :
    listGateCircuit (F := F) word.reverse
        (listGateCircuit (F := F) word v) = v := by
  induction word generalizing v with
  | nil => rfl
  | cons i tail ih =>
      rw [List.reverse_cons, listGateCircuit_append]
      simp only [listGateCircuit]
      rw [ih, listGateAt_involutive]

/-- The same reversed word is also a right inverse. -/
theorem listGateCircuit_reverse_right (word : List ℕ)
    (v : List (Vq F)) :
    listGateCircuit (F := F) word
        (listGateCircuit (F := F) word.reverse v) = v := by
  simpa using listGateCircuit_reverse_left (F := F) word.reverse v

/-- A list gate's visible output depends only on its visible input word. -/
theorem visibleWordList_listGateAt_congr (i : ℕ)
    (v w : List (Vq F))
    (hvw : visibleWordList (F := F) v = visibleWordList (F := F) w) :
    visibleWordList (F := F) (listGateAt (F := F) i v) =
      visibleWordList (F := F) (listGateAt (F := F) i w) := by
  induction i generalizing v w with
  | zero =>
      rcases v with _ | ⟨x, v⟩ <;> rcases w with _ | ⟨y, w⟩
      · rfl
      · simp [visibleWordList] at hvw
      · simp [visibleWordList] at hvw
      rcases v with _ | ⟨x', tail⟩ <;> rcases w with _ | ⟨y', rest⟩
      · exact hvw
      · simp [visibleWordList] at hvw
      · simp [visibleWordList] at hvw
      · simp only [listGateAt, visibleWordList, List.map_cons,
          siteColour_gateFun_fst, siteColour_gateFun_snd]
        have hhead := congrArg List.head? hvw
        have htail := congrArg List.tail hvw
        simp only [visibleWordList, List.map_cons, List.head?_cons,
          Option.some.injEq] at hhead
        simp only [visibleWordList, List.map_cons, List.tail_cons] at htail
        have hsecond := congrArg List.head? htail
        have hrest := congrArg List.tail htail
        simp only [List.head?_cons, Option.some.injEq] at hsecond
        simp only [List.tail_cons] at hrest
        rw [hhead, hsecond, hrest]
  | succ i ih =>
      rcases v with _ | ⟨x, tail⟩ <;> rcases w with _ | ⟨y, rest⟩
      · rfl
      · simp [visibleWordList] at hvw
      · simp [visibleWordList] at hvw
      · simp only [listGateAt, visibleWordList, List.map_cons,
          List.cons.injEq] at ⊢ hvw
        exact ⟨hvw.1, ih tail rest hvw.2⟩

/-- The same label-independence holds for a complete list circuit. -/
theorem visibleWordList_listGateCircuit_congr (word : List ℕ)
    (v w : List (Vq F))
    (hvw : visibleWordList (F := F) v = visibleWordList (F := F) w) :
    visibleWordList (F := F) (listGateCircuit (F := F) word v) =
      visibleWordList (F := F) (listGateCircuit (F := F) word w) := by
  induction word generalizing v w with
  | nil => exact hvw
  | cons i tail ih =>
      exact ih _ _ (visibleWordList_listGateAt_congr i v w hvw)

/-- A zero-labelled representative of one visible site. -/
def colourRepresentativeSite : VisibleColour → Vq F
  | .A => Sum.inl 0
  | .B => Sum.inr 0

/-- Zero-labelled representative of a visible list word. -/
def colourRepresentative (c : List VisibleColour) : List (Vq F) :=
  c.map (colourRepresentativeSite (F := F))

@[simp] theorem visibleWordList_colourRepresentative
    (c : List VisibleColour) :
    visibleWordList (F := F) (colourRepresentative (F := F) c) = c := by
  induction c with
  | nil => rfl
  | cons x tail ih =>
      change siteColour F (colourRepresentativeSite (F := F) x) ::
          visibleWordList (F := F) (colourRepresentative (F := F) tail) =
        x :: tail
      rw [ih]
      cases x <;> rfl

/-- Canonical adjacent-gate word taking visible word `c` to visible word
`d`, assuming the two words have the same length and colour content. -/
def colourRearrangementWord (c d : List VisibleColour) : List ℕ :=
  braidedSortSchedule (colourRepresentative (F := F) c) ++
    (braidedSortSchedule (colourRepresentative (F := F) d)).reverse

/-- Rearranging two equally long visible words never addresses a gate
outside their common packet. -/
theorem mem_colourRearrangementWord_lt (c d : List VisibleColour)
    (hlen : c.length = d.length) {i : ℕ}
    (hi : i ∈ colourRearrangementWord (F := F) c d) :
    i + 1 < c.length := by
  simp only [colourRearrangementWord, List.mem_append,
    List.mem_reverse] at hi
  rcases hi with hi | hi
  · simpa [colourRepresentative] using
      mem_braidedSortSchedule_lt
        (colourRepresentative (F := F) c) hi
  · have h := mem_braidedSortSchedule_lt
      (colourRepresentative (F := F) d) hi
    simpa [colourRepresentative, hlen] using h

/-- The canonical rearrangement word really carries every internal point
of the `c` fibre into the `d` fibre. -/
theorem visibleWordList_colourRearrangementWord
    (c d : List VisibleColour) (v : List (Vq F))
    (hv : visibleWordList (F := F) v = c)
    (hlen : c.length = d.length) (hA : c.count .A = d.count .A) :
    visibleWordList (F := F)
        (listGateCircuit (F := F) (colourRearrangementWord (F := F) c d) v) = d := by
  let vc := colourRepresentative (F := F) c
  let vd := colourRepresentative (F := F) d
  let wc := braidedSortSchedule vc
  let wd := braidedSortSchedule vd
  have hvc : visibleWordList (F := F) vc = c := by
    exact visibleWordList_colourRepresentative c
  have hvd : visibleWordList (F := F) vd = d := by
    exact visibleWordList_colourRepresentative d
  have hsortColour : visibleWordList (F := F) (braidedSort vc) =
      visibleWordList (F := F) (braidedSort vd) := by
    rw [visibleWordList_braidedSort, visibleWordList_braidedSort,
      hvc, hvd]
    exact colourSort_eq_of_length_countA_eq c d hlen hA
  rw [colourRearrangementWord, listGateCircuit_append]
  have hfirst : visibleWordList (F := F)
      (listGateCircuit (F := F) wc v) =
      visibleWordList (F := F) (braidedSort vc) := by
    calc
      _ = visibleWordList (F := F)
          (listGateCircuit (F := F) wc vc) :=
        visibleWordList_listGateCircuit_congr wc v vc (hv.trans hvc.symm)
      _ = _ := by rw [listGateCircuit_braidedSortSchedule]
  calc
    visibleWordList (F := F)
        (listGateCircuit (F := F) wd.reverse
          (listGateCircuit (F := F) wc v)) =
        visibleWordList (F := F)
          (listGateCircuit (F := F) wd.reverse (braidedSort vd)) := by
      apply visibleWordList_listGateCircuit_congr
      exact hfirst.trans hsortColour
    _ = visibleWordList (F := F) vd := by
      rw [← listGateCircuit_braidedSortSchedule vd,
        listGateCircuit_reverse_left]
    _ = d := hvd

/-- Reversing the canonical rearrangement carries the target fibre back to
the source fibre. -/
theorem visibleWordList_colourRearrangementWord_reverse
    (c d : List VisibleColour) (v : List (Vq F))
    (hv : visibleWordList (F := F) v = d)
    (hlen : c.length = d.length) (hA : c.count .A = d.count .A) :
    visibleWordList (F := F)
        (listGateCircuit (F := F)
          (colourRearrangementWord (F := F) c d).reverse v) = c := by
  let vc := colourRepresentative (F := F) c
  let word := colourRearrangementWord (F := F) c d
  have hforward : visibleWordList (F := F)
      (listGateCircuit (F := F) word vc) = d := by
    exact visibleWordList_colourRearrangementWord c d vc
      (visibleWordList_colourRepresentative c) hlen hA
  calc
    visibleWordList (F := F) (listGateCircuit (F := F) word.reverse v) =
        visibleWordList (F := F)
          (listGateCircuit (F := F) word.reverse
            (listGateCircuit (F := F) word vc)) := by
      apply visibleWordList_listGateCircuit_congr
      exact hv.trans hforward.symm
    _ = c := by
      rw [listGateCircuit_reverse_left,
        visibleWordList_colourRepresentative]

/-- Braided insertion has a colour word determined only by the input colour
word (not by any internal field labels). -/
theorem visibleWordList_braidedInsert_congr
    (x y : Vq F) (v w : List (Vq F))
    (hxy : siteColour F x = siteColour F y)
    (hvw : visibleWordList (F := F) v = visibleWordList (F := F) w) :
    visibleWordList (F := F) (braidedInsert x v) =
      visibleWordList (F := F) (braidedInsert y w) := by
  induction v generalizing w x y with
  | nil =>
      cases w with
      | nil => simpa [visibleWordList, braidedInsert] using hxy
      | cons z zs => simp [visibleWordList] at hvw
  | cons z zs ih =>
      cases w with
      | nil => simp [visibleWordList] at hvw
      | cons t ts =>
          have hzt : siteColour F z = siteColour F t := by
            simpa [visibleWordList] using congrArg List.head? hvw
          have hzsts : visibleWordList (F := F) zs =
              visibleWordList (F := F) ts := by
            simpa [visibleWordList] using congrArg List.tail hvw
          rcases x with a | a <;> rcases y with b | b <;>
            simp [siteColour] at hxy
          · simpa [visibleWordList, braidedInsert, siteColour] using
              And.intro hzt hzsts
          · rcases z with c | c <;> rcases t with d | d <;>
              simp [siteColour] at hzt
            · simp only [braidedInsert, gateFun, visibleWordList,
                List.map_cons, siteColour]
              congr 1
              exact ih (Sum.inr c) (Sum.inr d) ts (by simp [siteColour]) hzsts
            · simp only [visibleWordList, braidedInsert, List.map_cons, siteColour]
              exact congrArg
                (fun q => VisibleColour.B :: VisibleColour.B :: q) hzsts

/-- Hence the visible word of the sorted output depends only on the visible
word of the input. -/
theorem visibleWordList_braidedSort_congr (v w : List (Vq F))
    (hvw : visibleWordList (F := F) v = visibleWordList (F := F) w) :
    visibleWordList (F := F) (braidedSort v) =
      visibleWordList (F := F) (braidedSort w) := by
  induction v generalizing w with
  | nil =>
      cases w with
      | nil => rfl
      | cons y ys => simp [visibleWordList] at hvw
  | cons x xs ih =>
      cases w with
      | nil => simp [visibleWordList] at hvw
      | cons y ys =>
          have hxy : siteColour F x = siteColour F y := by
            simpa [visibleWordList] using congrArg List.head? hvw
          have hxsys : visibleWordList (F := F) xs =
              visibleWordList (F := F) ys := by
            simpa [visibleWordList] using congrArg List.tail hvw
          exact visibleWordList_braidedInsert_congr x y _ _ hxy (ih ys hxsys)

/-- On a fixed visible-word fibre, braided insertion is injective in all
internal labels. -/
theorem braidedInsert_injective_same_colours
    (x y : Vq F) (v w : List (Vq F))
    (hxy : siteColour F x = siteColour F y)
    (hvw : visibleWordList (F := F) v = visibleWordList (F := F) w)
    (hins : braidedInsert x v = braidedInsert y w) :
    x = y ∧ v = w := by
  induction v generalizing w x y with
  | nil =>
      cases w with
      | nil => simpa [braidedInsert] using hins
      | cons z zs => simp [visibleWordList] at hvw
  | cons z zs ih =>
      cases w with
      | nil => simp [visibleWordList] at hvw
      | cons t ts =>
          have hzt : siteColour F z = siteColour F t := by
            simpa [visibleWordList] using congrArg List.head? hvw
          have hzsts : visibleWordList (F := F) zs =
              visibleWordList (F := F) ts := by
            simpa [visibleWordList] using congrArg List.tail hvw
          rcases x with a | a <;> rcases y with b | b <;>
            simp [siteColour] at hxy
          · simpa [braidedInsert] using hins
          · rcases z with c | c <;> rcases t with d | d <;>
              simp [siteColour] at hzt
            · simp only [braidedInsert, gateFun, List.cons.injEq] at hins
              have hrec := ih (Sum.inr c) (Sum.inr d) ts
                (by simp [siteColour]) hzsts hins.2
              have hcd : c = d := by
                simpa using congrArg (siteLabel F) hrec.1
              subst d
              have hab : a = b := by
                have := congrArg (siteLabel F) hins.1
                simp [siteLabel] at this
                exact this
              subst b
              exact ⟨rfl, by simp [hrec.2]⟩
            · simpa [braidedInsert] using hins

/-- Canonical braided sorting is injective on each complete internal
visible-word fibre. -/
theorem braidedSort_injective_same_colours
    (v w : List (Vq F))
    (hvw : visibleWordList (F := F) v = visibleWordList (F := F) w)
    (hsort : braidedSort v = braidedSort w) : v = w := by
  induction v generalizing w with
  | nil =>
      cases w with
      | nil => rfl
      | cons y ys => simp [visibleWordList] at hvw
  | cons x xs ih =>
      cases w with
      | nil => simp [visibleWordList] at hvw
      | cons y ys =>
          have hxy : siteColour F x = siteColour F y := by
            simpa [visibleWordList] using congrArg List.head? hvw
          have hxsys : visibleWordList (F := F) xs =
              visibleWordList (F := F) ys := by
            simpa [visibleWordList] using congrArg List.tail hvw
          have hins := braidedInsert_injective_same_colours x y
            (braidedSort xs) (braidedSort ys) hxy
            (visibleWordList_braidedSort_congr xs ys hxsys) hsort
          exact congrArg₂ List.cons hins.1 (ih ys hxsys hins.2)

/-! ## Circuit paths and the finite tuple model -/

/-- Canonical sorting is constant along every adjacent-gate path. -/
theorem braidedSort_listGateCircuit (word : List ℕ) (v : List (Vq F)) :
    braidedSort (listGateCircuit (F := F) word v) = braidedSort v := by
  induction word generalizing v with
  | nil => rfl
  | cons i tail ih =>
      rw [listGateCircuit, ih, braidedSort_listGateAt]

/-- Canonical sorting also records the exact accumulated phase along a
gate path. -/
theorem braidedSortExponent_listGateCircuit (word : List ℕ)
    (v : List (Vq F)) :
    braidedSortExponent (listGateCircuit (F := F) word v) +
        listGateCircuitExponent (F := F) word v =
      braidedSortExponent v := by
  induction word generalizing v with
  | nil => simp [listGateCircuit, listGateCircuitExponent]
  | cons i tail ih =>
      simp only [listGateCircuit, listGateCircuitExponent]
      rw [← add_assoc, ih, braidedSortExponent_listGateAt]

/-- **Lemma 5.1, list form (support).**  A gate word returning to the same
visible word fixes every internal label. -/
theorem listGateCircuit_eq_self_of_visibleWord
    (word : List ℕ) (v : List (Vq F))
    (hcolour : visibleWordList (F := F)
        (listGateCircuit (F := F) word v) = visibleWordList (F := F) v) :
    listGateCircuit (F := F) word v = v := by
  apply braidedSort_injective_same_colours _ _ hcolour
  exact braidedSort_listGateCircuit word v

/-- **Lemma 5.1, list form (phase).**  Such a stabilizing path has no
residual finite-field exponent. -/
theorem listGateCircuitExponent_eq_zero_of_visibleWord
    (word : List ℕ) (v : List (Vq F))
    (hcolour : visibleWordList (F := F)
        (listGateCircuit (F := F) word v) = visibleWordList (F := F) v) :
    listGateCircuitExponent (F := F) word v = 0 := by
  have hfix := listGateCircuit_eq_self_of_visibleWord word v hcolour
  have hphase := braidedSortExponent_listGateCircuit word v
  rw [hfix] at hphase
  have heq : braidedSortExponent v + listGateCircuitExponent word v =
      braidedSortExponent v + 0 := by simpa using hphase
  exact add_left_cancel heq

/-- Converting a finite tuple to a list commutes with one adjacent gate. -/
theorem ofFn_gateAtFun (n i : ℕ) (v : SpatialBasis F n) :
    List.ofFn (gateAtFun F n i v) =
      listGateAt (F := F) i (List.ofFn v) := by
  classical
  induction i generalizing n with
  | zero =>
      cases n with
      | zero => simp [gateAtFun, listGateAt]
      | succ n =>
          cases n with
          | zero => simp [gateAtFun, listGateAt]
          | succ n =>
              simp [List.ofFn_succ, gateAtFun, listGateAt, Function.update]
              funext j
              by_cases h : j.succ.succ = (1 : Fin (n + 2))
              · have hv := congrArg Fin.val h
                norm_num at hv
              · rw [if_neg h]
  | succ i ih =>
      cases n with
      | zero => simp [gateAtFun, listGateAt]
      | succ n =>
          cases n with
          | zero => simp [gateAtFun, listGateAt]
          | succ n =>
              let tail : SpatialBasis F (n + 1) := fun j => v j.succ
              have hhead : gateAtFun F (n + 2) (i + 1) v 0 = v 0 := by
                unfold gateAtFun
                by_cases h : i < n
                · rw [dif_pos (by omega)]
                  simp [Function.update]
                · rw [dif_neg (by omega)]
              have htail :
                  (fun j : Fin (n + 1) =>
                    gateAtFun F (n + 2) (i + 1) v j.succ) =
                    gateAtFun F (n + 1) i tail := by
                funext j
                unfold gateAtFun
                by_cases h : i < n
                · rw [dif_pos (by omega), dif_pos (by omega)]
                  have hleft :
                      (j.succ = (⟨i + 1, by omega⟩ : Fin (n + 2))) ↔
                        j = (⟨i, by omega⟩ : Fin (n + 1)) := by
                    simp [Fin.ext_iff]
                  have hright :
                      (j.succ = (⟨i + 1 + 1, by omega⟩ : Fin (n + 2))) ↔
                        j = (⟨i + 1, by omega⟩ : Fin (n + 1)) := by
                    simp [Fin.ext_iff]
                  simp only [Function.update_apply, hleft, hright, tail]
                  have hil : (⟨i, by omega⟩ : Fin (n + 1)).succ =
                      (⟨i + 1, by omega⟩ : Fin (n + 2)) := by
                    apply Fin.ext
                    rfl
                  have hir : (⟨i + 1, by omega⟩ : Fin (n + 1)).succ =
                      (⟨i + 1 + 1, by omega⟩ : Fin (n + 2)) := by
                    apply Fin.ext
                    rfl
                  rw [hil, hir]
                · rw [dif_neg (by omega), dif_neg (by omega)]
              rw [List.ofFn_succ]
              change gateAtFun F (n + 2) (i + 1) v 0 ::
                  List.ofFn (fun j : Fin (n + 1) =>
                    gateAtFun F (n + 2) (i + 1) v j.succ) = _
              rw [hhead, htail, ih]
              have hvlist : List.ofFn v = v 0 :: List.ofFn tail := by
                simp [List.ofFn_succ, tail]
              rw [hvlist]
              rfl

/-- The one-gate finite and list exponents agree. -/
theorem gateAtExponent_eq_listGateAtExponent_ofFn
    (n i : ℕ) (v : SpatialBasis F n) :
    gateAtExponent F n i v =
      listGateAtExponent (F := F) i (List.ofFn v) := by
  induction i generalizing n with
  | zero =>
      cases n with
      | zero => simp [gateAtExponent, listGateAtExponent]
      | succ n =>
          cases n with
          | zero => simp [gateAtExponent, listGateAtExponent]
          | succ n =>
              simp [gateAtExponent, listGateAtExponent, List.ofFn_succ]
  | succ i ih =>
      cases n with
      | zero => simp [gateAtExponent, listGateAtExponent]
      | succ n =>
          simpa [gateAtExponent, listGateAtExponent, List.ofFn_succ] using
            ih n (fun j => v j.succ)

/-- Conversion to lists commutes with a complete finite gate circuit. -/
theorem ofFn_spatialCircuitPerm (n : ℕ) (word : List ℕ)
    (v : SpatialBasis F n) :
    List.ofFn (spatialCircuitPerm F n word v) =
      listGateCircuit (F := F) word (List.ofFn v) := by
  induction word generalizing v with
  | nil => rfl
  | cons i tail ih =>
      change List.ofFn
          (spatialCircuitPerm F n tail (gateAtFun F n i v)) = _
      rw [ih, ofFn_gateAtFun]
      rfl

/-- The accumulated finite-field circuit exponent is unchanged by conversion
to the list model. -/
theorem spatialCircuitExponent_eq_listGateCircuitExponent
    (n : ℕ) (word : List ℕ) (v : SpatialBasis F n) :
    spatialCircuitExponent F n word v =
      listGateCircuitExponent (F := F) word (List.ofFn v) := by
  induction word generalizing v with
  | nil => rfl
  | cons i tail ih =>
      simp only [spatialCircuitExponent, listGateCircuitExponent]
      rw [ih]
      change listGateCircuitExponent tail
          (List.ofFn (gateAtFun F n i v)) + gateAtExponent F n i v = _
      rw [ofFn_gateAtFun,
        gateAtExponent_eq_listGateAtExponent_ofFn]

/-- Finite circuit support splits over concatenated gate words. -/
theorem spatialCircuitPerm_append (n : ℕ) (u w : List ℕ)
    (v : SpatialBasis F n) :
    spatialCircuitPerm F n (u ++ w) v =
      spatialCircuitPerm F n w (spatialCircuitPerm F n u v) := by
  apply List.ofFn_injective
  rw [ofFn_spatialCircuitPerm, ofFn_spatialCircuitPerm,
    ofFn_spatialCircuitPerm, listGateCircuit_append]

/-- Finite circuit exponents split over concatenated gate words. -/
theorem spatialCircuitExponent_append (n : ℕ) (u w : List ℕ)
    (v : SpatialBasis F n) :
    spatialCircuitExponent F n (u ++ w) v =
      spatialCircuitExponent F n w (spatialCircuitPerm F n u v) +
        spatialCircuitExponent F n u v := by
  rw [spatialCircuitExponent_eq_listGateCircuitExponent,
    spatialCircuitExponent_eq_listGateCircuitExponent,
    spatialCircuitExponent_eq_listGateCircuitExponent,
    ofFn_spatialCircuitPerm, listGateCircuitExponent_append]

/-- The reversed finite word is the inverse support path. -/
theorem spatialCircuitPerm_reverse_left (n : ℕ) (word : List ℕ)
    (v : SpatialBasis F n) :
    spatialCircuitPerm F n word.reverse
        (spatialCircuitPerm F n word v) = v := by
  apply List.ofFn_injective
  rw [ofFn_spatialCircuitPerm, ofFn_spatialCircuitPerm,
    listGateCircuit_reverse_left]

theorem spatialCircuitPerm_reverse_right (n : ℕ) (word : List ℕ)
    (v : SpatialBasis F n) :
    spatialCircuitPerm F n word
        (spatialCircuitPerm F n word.reverse v) = v := by
  simpa using spatialCircuitPerm_reverse_left (F := F) n word.reverse v

/-- The list visible word of a finite tuple is its pointwise visible word
converted with `List.ofFn`. -/
theorem visibleWordList_ofFn (n : ℕ) (v : SpatialBasis F n) :
    visibleWordList (F := F) (List.ofFn v) =
      List.ofFn (fun i => siteColour F (v i)) := by
  unfold visibleWordList
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rfl

/-- **Lemma 5.1 (support).**  If an adjacent-gate circuit stabilizes a
visible word, it fixes every internal label in that fibre. -/
theorem spatialCircuitPerm_eq_self_of_colour
    (n : ℕ) (word : List ℕ) (v : SpatialBasis F n)
    (hcolour : (fun i =>
        siteColour F (spatialCircuitPerm F n word v i)) =
      fun i => siteColour F (v i)) :
    spatialCircuitPerm F n word v = v := by
  apply List.ofFn_injective
  rw [ofFn_spatialCircuitPerm]
  apply listGateCircuit_eq_self_of_visibleWord
  rw [← ofFn_spatialCircuitPerm, visibleWordList_ofFn,
    visibleWordList_ofFn, hcolour]

/-- **Lemma 5.1 (phase).**  A visible-word stabilizer has exactly zero
finite-field exponent, hence no residual phase. -/
theorem spatialCircuitExponent_eq_zero_of_colour
    (n : ℕ) (word : List ℕ) (v : SpatialBasis F n)
    (hcolour : (fun i =>
        siteColour F (spatialCircuitPerm F n word v i)) =
      fun i => siteColour F (v i)) :
    spatialCircuitExponent F n word v = 0 := by
  rw [spatialCircuitExponent_eq_listGateCircuitExponent]
  apply listGateCircuitExponent_eq_zero_of_visibleWord
  rw [← ofFn_spatialCircuitPerm, visibleWordList_ofFn,
    visibleWordList_ofFn, hcolour]

/-- Matrix-valued conclusion of Lemma 5.1 on one visible-word fibre. -/
theorem spatialCircuit_apply_stabilizer
    (psi : AddChar F ℂ) (n : ℕ) (word : List ℕ)
    (v : SpatialBasis F n)
    (hcolour : (fun i =>
        siteColour F (spatialCircuitPerm F n word v i)) =
      fun i => siteColour F (v i)) :
    spatialCircuitPerm F n word v = v ∧
      spatialCircuitPhase F psi n word v = 1 := by
  refine ⟨spatialCircuitPerm_eq_self_of_colour n word v hcolour, ?_⟩
  rw [spatialCircuitPhase_eq_character,
    spatialCircuitExponent_eq_zero_of_colour n word v hcolour]
  simp

/-- Two adjacent-gate paths with the same final visible word have the same
full internal support action.  This is the path-independence form of
Lemma 5.1 used in the padding reduction. -/
theorem spatialCircuitPerm_eq_of_colour_eq
    (n : ℕ) (word₁ word₂ : List ℕ) (v : SpatialBasis F n)
    (hcolour : (fun i =>
        siteColour F (spatialCircuitPerm F n word₁ v i)) =
      fun i => siteColour F (spatialCircuitPerm F n word₂ v i)) :
    spatialCircuitPerm F n word₁ v =
      spatialCircuitPerm F n word₂ v := by
  apply List.ofFn_injective
  rw [ofFn_spatialCircuitPerm, ofFn_spatialCircuitPerm]
  apply braidedSort_injective_same_colours
  · rw [← ofFn_spatialCircuitPerm, ← ofFn_spatialCircuitPerm,
      visibleWordList_ofFn, visibleWordList_ofFn, hcolour]
  · rw [braidedSort_listGateCircuit, braidedSort_listGateCircuit]

/-- The corresponding accumulated finite-field exponents are also equal. -/
theorem spatialCircuitExponent_eq_of_colour_eq
    (n : ℕ) (word₁ word₂ : List ℕ) (v : SpatialBasis F n)
    (hcolour : (fun i =>
        siteColour F (spatialCircuitPerm F n word₁ v i)) =
      fun i => siteColour F (spatialCircuitPerm F n word₂ v i)) :
    spatialCircuitExponent F n word₁ v =
      spatialCircuitExponent F n word₂ v := by
  have hsupp := spatialCircuitPerm_eq_of_colour_eq n word₁ word₂ v hcolour
  rw [spatialCircuitExponent_eq_listGateCircuitExponent,
    spatialCircuitExponent_eq_listGateCircuitExponent]
  have h₁ := braidedSortExponent_listGateCircuit (F := F) word₁ (List.ofFn v)
  have h₂ := braidedSortExponent_listGateCircuit (F := F) word₂ (List.ofFn v)
  rw [← ofFn_spatialCircuitPerm] at h₁ h₂
  rw [hsupp] at h₁
  exact add_left_cancel (h₁.trans h₂.symm)

/-- Character phases of two paths agreeing visibly are identical. -/
theorem spatialCircuitPhase_eq_of_colour_eq
    (psi : AddChar F ℂ) (n : ℕ) (word₁ word₂ : List ℕ)
    (v : SpatialBasis F n)
    (hcolour : (fun i =>
        siteColour F (spatialCircuitPerm F n word₁ v i)) =
      fun i => siteColour F (spatialCircuitPerm F n word₂ v i)) :
    spatialCircuitPhase F psi n word₁ v =
      spatialCircuitPhase F psi n word₂ v := by
  rw [spatialCircuitPhase_eq_character, spatialCircuitPhase_eq_character,
    spatialCircuitExponent_eq_of_colour_eq n word₁ word₂ v hcolour]

/-! ## Explicit rearrangements in the finite tuple model -/

/-- Canonical adjacent word rearranging one finite visible word into another. -/
def finiteColourRearrangementWord {n : ℕ}
    (c d : Fin n → VisibleColour) : List ℕ :=
  colourRearrangementWord (F := F) (List.ofFn c) (List.ofFn d)

/-- The finite rearrangement word carries the whole `c` fibre into the `d`
fibre whenever their colour content agrees. -/
theorem colour_finiteColourRearrangementWord {n : ℕ}
    (c d : Fin n → VisibleColour) (v : SpatialBasis F n)
    (hv : (fun i => siteColour F (v i)) = c)
    (hA : (List.ofFn c).count .A = (List.ofFn d).count .A) :
    (fun i => siteColour F
      (spatialCircuitPerm F n (finiteColourRearrangementWord (F := F) c d) v i)) =
      d := by
  apply List.ofFn_injective
  rw [← visibleWordList_ofFn]
  rw [ofFn_spatialCircuitPerm]
  apply visibleWordList_colourRearrangementWord
  · rw [visibleWordList_ofFn, hv]
  · simp
  · exact hA

/-- The corresponding support equivalence between two finite word fibres. -/
def finiteColourRearrangementPerm {n : ℕ}
    (c d : Fin n → VisibleColour) : Equiv.Perm (SpatialBasis F n) :=
  spatialCircuitPerm F n (finiteColourRearrangementWord (F := F) c d)

end SqrtOpEnt
