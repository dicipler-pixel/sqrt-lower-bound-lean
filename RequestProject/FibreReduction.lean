import RequestProject.WordStabilizer

/-!
# Reduction of visible-word fibres to residual cores

This file implements the padding step of Lemma 5.2.  A fixed visible-word
fibre is first reindexed by packet-local triangular circuits.  The rectangle
can then be replaced, using `spatialCircuitExponent_eq_of_colour_eq`, by a
path which acts only on the residual positive or negative core.  The sites
outside that core are subsequently resolved by a local measurement.
-/

namespace SqrtOpEnt

open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem ofFn_packetsToSpatial (t : ℕ) (v : RectBasis F t) :
    List.ofFn (packetsToSpatial F v) =
      List.ofFn v.1 ++ List.ofFn v.2 := by
  change List.ofFn (Fin.append v.1 v.2) = _
  exact List.ofFn_fin_append v.1 v.2

/-! ## Packet concatenation at ambient size `m + s + 1` -/

/-- Put an `m`-site spectator before an `(s+1)`-site residual packet. -/
def packetPreCore (m s : ℕ) (pre : PacketBasis F m)
    (core : PacketBasis F (s + 1)) : PacketBasis F (m + s + 1) :=
  fun i => Fin.append pre core (Fin.cast (by omega) i)

/-- Put an `(s+1)`-site residual packet before an `m`-site spectator. -/
def packetPostCore (m s : ℕ) (core : PacketBasis F (s + 1))
    (post : PacketBasis F m) : PacketBasis F (m + s + 1) :=
  fun i => Fin.append core post (Fin.cast (by omega) i)

theorem ofFn_packetPreCore (m s : ℕ) (pre : PacketBasis F m)
    (core : PacketBasis F (s + 1)) :
    List.ofFn (packetPreCore (F := F) m s pre core) =
      List.ofFn pre ++ List.ofFn core := by
  let h : m + (s + 1) = m + s + 1 := by omega
  change List.ofFn (fun i : Fin (m + s + 1) =>
      Fin.append pre core (Fin.cast h.symm i)) = _
  rw [← List.ofFn_congr h]
  exact List.ofFn_fin_append pre core

theorem ofFn_packetPostCore (m s : ℕ) (core : PacketBasis F (s + 1))
    (post : PacketBasis F m) :
    List.ofFn (packetPostCore (F := F) m s core post) =
      List.ofFn core ++ List.ofFn post := by
  let h : (s + 1) + m = m + s + 1 := by omega
  change List.ofFn (fun i : Fin (m + s + 1) =>
      Fin.append core post (Fin.cast h.symm i)) = _
  rw [← List.ofFn_congr h]
  exact List.ofFn_fin_append core post

/-- Extract the prefix spectator from a packet split as `m | (s+1)`. -/
def packetPrePart (m s : ℕ) (v : PacketBasis F (m + s + 1)) :
    PacketBasis F m :=
  fun i => v ⟨i, by omega⟩

/-- Extract the residual suffix from a packet split as `m | (s+1)`. -/
def packetPreCorePart (m s : ℕ) (v : PacketBasis F (m + s + 1)) :
    PacketBasis F (s + 1) :=
  fun i => v ⟨m + i, by omega⟩

/-- Extract the residual prefix from a packet split as `(s+1) | m`. -/
def packetPostCorePart (m s : ℕ) (v : PacketBasis F (m + s + 1)) :
    PacketBasis F (s + 1) :=
  fun i => v ⟨i, by omega⟩

/-- Extract the suffix spectator from a packet split as `(s+1) | m`. -/
def packetPostPart (m s : ℕ) (v : PacketBasis F (m + s + 1)) :
    PacketBasis F m :=
  fun i => v ⟨s + 1 + i, by omega⟩

@[simp] theorem packetPrePart_packetPreCore (m s : ℕ)
    (pre : PacketBasis F m) (core : PacketBasis F (s + 1)) :
    packetPrePart (F := F) m s (packetPreCore m s pre core) = pre := by
  funext i
  let h : m + s + 1 = m + (s + 1) := by omega
  change Fin.append pre core (Fin.cast h ⟨i, by omega⟩) = pre i
  have hi : Fin.cast h (⟨i, by omega⟩ : Fin (m + s + 1)) =
      Fin.castAdd (s + 1) i := by
    apply Fin.ext
    rfl
  rw [hi]
  exact Fin.addCases_left _

@[simp] theorem packetPreCorePart_packetPreCore (m s : ℕ)
    (pre : PacketBasis F m) (core : PacketBasis F (s + 1)) :
    packetPreCorePart (F := F) m s (packetPreCore m s pre core) = core := by
  funext i
  let h : m + s + 1 = m + (s + 1) := by omega
  change Fin.append pre core (Fin.cast h ⟨m + i, by omega⟩) = core i
  have hi : Fin.cast h (⟨m + i, by omega⟩ : Fin (m + s + 1)) =
      Fin.natAdd m i := by
    apply Fin.ext
    rfl
  rw [hi]
  exact Fin.addCases_right _

@[simp] theorem packetPostCorePart_packetPostCore (m s : ℕ)
    (core : PacketBasis F (s + 1)) (post : PacketBasis F m) :
    packetPostCorePart (F := F) m s (packetPostCore m s core post) = core := by
  funext i
  let h : m + s + 1 = (s + 1) + m := by omega
  change Fin.append core post (Fin.cast h ⟨i, by omega⟩) = core i
  have hi : Fin.cast h (⟨i, by omega⟩ : Fin (m + s + 1)) =
      Fin.castAdd m i := by
    apply Fin.ext
    rfl
  rw [hi]
  exact Fin.addCases_left _

@[simp] theorem packetPostPart_packetPostCore (m s : ℕ)
    (core : PacketBasis F (s + 1)) (post : PacketBasis F m) :
    packetPostPart (F := F) m s (packetPostCore m s core post) = post := by
  funext i
  let h : m + s + 1 = (s + 1) + m := by omega
  change Fin.append core post
      (Fin.cast h ⟨s + 1 + i, by omega⟩) = post i
  have hi : Fin.cast h
      (⟨s + 1 + i, by omega⟩ : Fin (m + s + 1)) =
      Fin.natAdd (s + 1) i := by
    apply Fin.ext
    rfl
  rw [hi]
  exact Fin.addCases_right _

/-- Splitting a packet as `m | (s+1)` and concatenating the two pieces is
the identity. -/
theorem packetPreCore_parts (m s : ℕ)
    (v : PacketBasis F (m + s + 1)) :
    packetPreCore (F := F) m s (packetPrePart m s v)
      (packetPreCorePart m s v) = v := by
  funext i
  let h : m + s + 1 = m + (s + 1) := by omega
  change Fin.append (packetPrePart m s v) (packetPreCorePart m s v)
      (Fin.cast h i) = v i
  have hi : i = Fin.cast h.symm (Fin.cast h i) := by simp
  conv_rhs => rw [hi]
  generalize Fin.cast h i = j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [packetPrePart]
    congr 1
  · intro k
    simp [packetPreCorePart]
    congr 1

/-- Splitting a packet as `(s+1) | m` and concatenating the pieces is the
identity. -/
theorem packetPostCore_parts (m s : ℕ)
    (v : PacketBasis F (m + s + 1)) :
    packetPostCore (F := F) m s (packetPostCorePart m s v)
      (packetPostPart m s v) = v := by
  funext i
  let h : m + s + 1 = (s + 1) + m := by omega
  change Fin.append (packetPostCorePart m s v) (packetPostPart m s v)
      (Fin.cast h i) = v i
  have hi : i = Fin.cast h.symm (Fin.cast h i) := by simp
  conv_rhs => rw [hi]
  generalize Fin.cast h i = j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [packetPostCorePart]
    congr 1
  · intro k
    simp [packetPostPart]
    congr 1
    apply Fin.ext
    simp [Nat.add_comm]

/-! ## Padded positive and negative coefficient indices -/

/-- A positive residual row, with an identical prefix spectator in its two
operator legs. -/
def positivePaddedRow (m s : ℕ) (pre : PacketBasis F m)
    (L : Fin (s + 1) → F) :
    PacketBasis F (m + s + 1) × PacketBasis F (m + s + 1) :=
  (packetPreCore m s pre (positiveExtremeRow (F := F) s L).1,
    packetPreCore m s pre (positiveExtremeRow (F := F) s L).2)

/-- A positive residual column, with an identical suffix spectator. -/
def positivePaddedColumn (m s : ℕ) (post : PacketBasis F m)
    (x : Fin s → F) :
    PacketBasis F (m + s + 1) × PacketBasis F (m + s + 1) :=
  (packetPostCore m s (positiveExtremeColumn (F := F) s x).1 post,
    packetPostCore m s (positiveExtremeColumn (F := F) s x).2 post)

/-- A negative residual row, with an identical prefix spectator. -/
def negativePaddedRow (m s : ℕ) (pre : PacketBasis F m)
    (p : F × (Fin s → F)) :
    PacketBasis F (m + s + 1) × PacketBasis F (m + s + 1) :=
  (packetPreCore m s pre (negativeExtremeRow (F := F) s p).1,
    packetPreCore m s pre (negativeExtremeRow (F := F) s p).2)

/-- A negative residual column, with an identical suffix spectator. -/
def negativePaddedColumn (m s : ℕ) (post : PacketBasis F m)
    (x : Fin s → F) :
    PacketBasis F (m + s + 1) × PacketBasis F (m + s + 1) :=
  (packetPostCore m s (negativeExtremeColumn (F := F) s x).1 post,
    packetPostCore m s (negativeExtremeColumn (F := F) s x).2 post)

theorem positivePaddedRow_injective (m s : ℕ) (pre : PacketBasis F m) :
    Function.Injective (positivePaddedRow (F := F) m s pre) := by
  intro L L' h
  apply positiveExtremeRow_injective (F := F) s
  apply Prod.ext
  · simpa [positivePaddedRow] using congrArg
      (fun z => packetPreCorePart (F := F) m s z.1) h
  · simpa [positivePaddedRow] using congrArg
      (fun z => packetPreCorePart (F := F) m s z.2) h

theorem positivePaddedColumn_injective (m s : ℕ) (post : PacketBasis F m) :
    Function.Injective (positivePaddedColumn (F := F) m s post) := by
  intro x y h
  apply positiveExtremeColumn_injective (F := F) s
  apply Prod.ext
  · simpa [positivePaddedColumn] using congrArg
      (fun z => packetPostCorePart (F := F) m s z.1) h
  · simpa [positivePaddedColumn] using congrArg
      (fun z => packetPostCorePart (F := F) m s z.2) h

theorem negativePaddedRow_injective (m s : ℕ) (pre : PacketBasis F m) :
    Function.Injective (negativePaddedRow (F := F) m s pre) := by
  intro p q h
  apply negativeExtremeRow_injective (F := F) s
  apply Prod.ext
  · simpa [negativePaddedRow] using congrArg
      (fun z => packetPreCorePart (F := F) m s z.1) h
  · simpa [negativePaddedRow] using congrArg
      (fun z => packetPreCorePart (F := F) m s z.2) h

theorem negativePaddedColumn_injective (m s : ℕ) (post : PacketBasis F m) :
    Function.Injective (negativePaddedColumn (F := F) m s post) := by
  intro x y h
  apply negativeExtremeColumn_injective (F := F) s
  apply Prod.ext
  · simpa [negativePaddedColumn] using congrArg
      (fun z => packetPostCorePart (F := F) m s z.1) h
  · simpa [negativePaddedColumn] using congrArg
      (fun z => packetPostCorePart (F := F) m s z.2) h

/-! ## A rectangle embedded between two spectator strings -/

/-- The `(s+1) × (s+1)` crossing rectangle embedded after `m` spectator
sites on the left and before `m` spectator sites on the right. -/
def embeddedRectangularCircuitPerm (m s : ℕ) :
    Equiv.Perm (RectBasis F (m + s + 1)) :=
  (packetsToSpatial F).trans
    ((spatialCircuitPerm F ((m + s + 1) + (m + s + 1))
      (shiftGateWordBy m (crossingSchedule (s + 1)))).trans
      (packetsToSpatial F).symm)

/-- Finite-field exponent of the embedded residual rectangle. -/
def embeddedRectangularCircuitExponent (m s : ℕ)
    (v : RectBasis F (m + s + 1)) : F :=
  spatialCircuitExponent F ((m + s + 1) + (m + s + 1))
    (shiftGateWordBy m (crossingSchedule (s + 1)))
    (packetsToSpatial F v)

/-- Spectators make no contribution to the embedded circuit exponent. -/
theorem embeddedRectangularCircuitExponent_apply (m s : ℕ)
    (pre post : PacketBasis F m)
    (left right : PacketBasis F (s + 1)) :
    embeddedRectangularCircuitExponent (F := F) m s
        (packetPreCore m s pre left, packetPostCore m s right post) =
      rectangularCircuitExponent F (s + 1) (left, right) := by
  unfold embeddedRectangularCircuitExponent rectangularCircuitExponent
  rw [spatialCircuitExponent_eq_listGateCircuitExponent]
  rw [ofFn_packetsToSpatial, ofFn_packetPreCore, ofFn_packetPostCore]
  rw [show List.ofFn pre ++ List.ofFn left ++
        (List.ofFn right ++ List.ofFn post) =
      List.ofFn pre ++ (List.ofFn left ++ List.ofFn right) ++
        List.ofFn post by simp [List.append_assoc]]
  have hvalid : ∀ i ∈ crossingSchedule (s + 1),
      i + 1 < (List.ofFn left ++ List.ofFn right).length := by
    intro i hi
    have h := mem_crossingSchedule_lt hi
    simp only [List.length_append, List.length_ofFn]
    omega
  rw [show shiftGateWordBy m (crossingSchedule (s + 1)) =
      shiftGateWordBy (List.ofFn pre).length
        (crossingSchedule (s + 1)) by simp]
  rw [listGateCircuitExponent_segment _ _ _ _ hvalid]
  rw [← ofFn_packetsToSpatial (F := F) (s + 1) (left, right)]
  rw [← spatialCircuitExponent_eq_listGateCircuitExponent]

/-- Padding a source-supported residual pair by identical spectators on the
two operator legs preserves the marked-source support condition. -/
theorem rectangularSource_ne_zero_pad (m s : ℕ)
    (pre post : PacketBasis F m)
    (u v : RectBasis F (s + 1))
    (huv : rectangularSource F (succPNat s) u v ≠ 0) :
    rectangularSource F (succPNat (m + s))
        (packetPreCore m s pre u.1, packetPostCore m s u.2 post)
        (packetPreCore m s pre v.1, packetPostCore m s v.2 post) ≠ 0 := by
  rw [rectangularSource_ne_zero_iff] at huv ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [huv.1]
  · intro k hk
    by_cases hcore : (k : ℕ) < s + 1
    · let i : Fin (s + 1) := ⟨k, hcore⟩
      have hi0 : i ≠ 0 := by
        intro hi
        apply hk
        apply Fin.ext
        simpa [i] using congrArg Fin.val hi
      have htail := huv.2.1 i hi0
      have hu := congrFun
        (packetPostCorePart_packetPostCore (F := F) m s u.2 post) i
      have hv := congrFun
        (packetPostCorePart_packetPostCore (F := F) m s v.2 post) i
      exact hu.trans (htail.trans hv.symm)
    · have hklt : (k : ℕ) < m + s + 1 := k.isLt
      let i : Fin m := ⟨(k : ℕ) - (s + 1), by omega⟩
      have hkform : (k : ℕ) = s + 1 + i := by
        dsimp [i]
        omega
      have hu := congrFun
        (packetPostPart_packetPostCore (F := F) m s u.2 post) i
      have hv := congrFun
        (packetPostPart_packetPostCore (F := F) m s v.2 post) i
      change packetPostCore m s u.2 post k =
        packetPostCore m s v.2 post k
      have kk : k = (⟨s + 1 + i, by omega⟩ : Fin (m + s + 1)) := by
        apply Fin.ext
        exact hkform
      rw [kk]
      change packetPostPart m s (packetPostCore m s u.2 post) i =
        packetPostPart m s (packetPostCore m s v.2 post) i
      exact hu.trans hv.symm
  · have hzero := huv.2.2.1
    have hpart := congrFun
      (packetPostCorePart_packetPostCore (F := F) m s u.2 post) 0
    exact hpart.trans hzero
  · have hzero := huv.2.2.2
    have hpart := congrFun
      (packetPostCorePart_packetPostCore (F := F) m s v.2 post) 0
    exact hpart.trans hzero

/-- Exact support criterion for a padded residual pair. -/
theorem rectangularSource_ne_zero_pad_iff (m s : ℕ)
    (preU preV postU postV : PacketBasis F m)
    (u v : RectBasis F (s + 1)) :
    rectangularSource F (succPNat (m + s))
        (packetPreCore m s preU u.1, packetPostCore m s u.2 postU)
        (packetPreCore m s preV v.1, packetPostCore m s v.2 postV) ≠ 0 ↔
      preU = preV ∧ postU = postV ∧
        rectangularSource F (succPNat s) u v ≠ 0 := by
  constructor
  · intro h
    rw [rectangularSource_ne_zero_iff] at h
    have hpre : preU = preV := by
      have hp := congrArg (packetPrePart (F := F) m s) h.1
      simpa using hp
    have hpost : postU = postV := by
      funext i
      let k : Fin (m + s + 1) := ⟨s + 1 + i, by omega⟩
      have hk : k ≠ 0 := by
        intro hk0
        have hz := congrArg Fin.val hk0
        simp [k] at hz
      have heq := h.2.1 k hk
      have hu := congrFun
        (packetPostPart_packetPostCore (F := F) m s u.2 postU) i
      have hv := congrFun
        (packetPostPart_packetPostCore (F := F) m s v.2 postV) i
      exact hu.symm.trans (heq.trans hv)
    refine ⟨hpre, hpost, ?_⟩
    rw [rectangularSource_ne_zero_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hc := congrArg (packetPreCorePart (F := F) m s) h.1
      simpa using hc
    · intro i hi
      have hiLt : (i : ℕ) < s + 1 := i.isLt
      change (i : ℕ) < s + 1 at hiLt
      let k : Fin (m + s + 1) :=
        ⟨i, by omega⟩
      have hk : k ≠ 0 := by
        intro hk0
        have hz : (i : ℕ) = 0 := by
          simpa [k] using congrArg Fin.val hk0
        apply hi
        apply Fin.ext
        exact hz
      have heq := h.2.1 k hk
      have hu := congrFun
        (packetPostCorePart_packetPostCore (F := F) m s u.2 postU) i
      have hv := congrFun
        (packetPostCorePart_packetPostCore (F := F) m s v.2 postV) i
      exact hu.symm.trans (heq.trans hv)
    · have hu := congrFun
        (packetPostCorePart_packetPostCore (F := F) m s u.2 postU) 0
      exact hu.symm.trans h.2.2.1
    · have hv := congrFun
        (packetPostCorePart_packetPostCore (F := F) m s v.2 postV) 0
      exact hv.symm.trans h.2.2.2
  · rintro ⟨rfl, rfl, h⟩
    exact rectangularSource_ne_zero_pad (F := F) m s preU postU u v h

/-- The embedded rectangle leaves both spectators untouched and applies the
ordinary residual rectangle to the two middle packets. -/
theorem embeddedRectangularCircuitPerm_apply (m s : ℕ)
    (pre post : PacketBasis F m)
    (left right : PacketBasis F (s + 1)) :
    embeddedRectangularCircuitPerm (F := F) m s
        (packetPreCore m s pre left, packetPostCore m s right post) =
      (packetPreCore m s pre
          (rectangularCircuitPerm F (s + 1) (left, right)).1,
        packetPostCore m s
          (rectangularCircuitPerm F (s + 1) (left, right)).2 post) := by
  apply (packetsToSpatial F).injective
  simp only [embeddedRectangularCircuitPerm, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  apply List.ofFn_injective
  rw [ofFn_spatialCircuitPerm]
  rw [ofFn_packetsToSpatial, ofFn_packetPreCore, ofFn_packetPostCore]
  rw [show List.ofFn pre ++ List.ofFn left ++
        (List.ofFn right ++ List.ofFn post) =
      List.ofFn pre ++ (List.ofFn left ++ List.ofFn right) ++
        List.ofFn post by simp [List.append_assoc]]
  have hvalid : ∀ i ∈ crossingSchedule (s + 1),
      i + 1 < (List.ofFn left ++ List.ofFn right).length := by
    intro i hi
    have h := mem_crossingSchedule_lt hi
    simp only [List.length_append, List.length_ofFn]
    omega
  rw [show shiftGateWordBy m (crossingSchedule (s + 1)) =
      shiftGateWordBy (List.ofFn pre).length
        (crossingSchedule (s + 1)) by simp]
  rw [listGateCircuit_segment _ _ _ _ hvalid]
  rw [← ofFn_packetsToSpatial (F := F) (s + 1) (left, right)]
  rw [← ofFn_spatialCircuitPerm]
  have hrect : spatialCircuitPerm F ((s + 1) + (s + 1))
      (crossingSchedule (s + 1)) (packetsToSpatial F (left, right)) =
      packetsToSpatial F
        (rectangularCircuitPerm F (s + 1) (left, right)) := by
    simp [rectangularCircuitPerm]
  rw [hrect]
  rw [ofFn_packetsToSpatial (F := F) (s + 1)]
  rw [ofFn_packetsToSpatial (F := F) (m + s + 1)
    (packetPreCore m s pre
        (rectangularCircuitPerm F (s + 1) (left, right)).1,
      packetPostCore m s
        (rectangularCircuitPerm F (s + 1) (left, right)).2 post)]
  rw [ofFn_packetPreCore, ofFn_packetPostCore]
  simp [List.append_assoc]

/-- Forgetting labels, the left output word of a rectangle is its input
right word. -/
theorem visibleWordList_rectangularCircuitPerm_fst (t : ℕ)
    (u : RectBasis F t) :
    visibleWordList (F := F)
        (List.ofFn (rectangularCircuitPerm F t u).1) =
      visibleWordList (F := F) (List.ofFn u.2) := by
  rw [visibleWordList_ofFn, visibleWordList_ofFn]
  congr 1
  funext i
  exact siteColour_rectangularCircuitPerm_fst F t u i

/-- Forgetting labels, the right output word of a rectangle is its input
left word. -/
theorem visibleWordList_rectangularCircuitPerm_snd (t : ℕ)
    (u : RectBasis F t) :
    visibleWordList (F := F)
        (List.ofFn (rectangularCircuitPerm F t u).2) =
      visibleWordList (F := F) (List.ofFn u.1) := by
  rw [visibleWordList_ofFn, visibleWordList_ofFn]
  congr 1
  funext i
  exact siteColour_rectangularCircuitPerm_snd F t u i

/-- The word obtained by dropping the first site of a finite packet is the
tail of its full visible word. -/
theorem visibleWordList_ofFn_succ (n : ℕ) (v : PacketBasis F (n + 1)) :
    visibleWordList (F := F) (List.ofFn (fun i : Fin n => v i.succ)) =
      (visibleWordList (F := F) (List.ofFn v)).tail := by
  rw [List.ofFn_succ]
  simp [visibleWordList]

/-- The two active positive core inputs emerge with all-`A` left words and
all-`B` right words. -/
theorem positiveExtreme_rectangular_visibleWords (s : ℕ)
    (L : Fin (s + 1) → F) (x : Fin s → F) :
    let ket := rectangularCircuitPerm F (s + 1)
      ((positiveExtremeRow (F := F) s L).1,
        (positiveExtremeColumn (F := F) s x).1)
    let bra := rectangularCircuitPerm F (s + 1)
      ((positiveExtremeRow (F := F) s L).2,
        (positiveExtremeColumn (F := F) s x).2)
    visibleWordList (F := F) (List.ofFn ket.1) =
        List.replicate (s + 1) .A ∧
      visibleWordList (F := F) (List.ofFn ket.2) =
        List.replicate (s + 1) .B ∧
      visibleWordList (F := F) (List.ofFn bra.1) =
        List.replicate (s + 1) .A ∧
      visibleWordList (F := F) (List.ofFn bra.2) =
        List.replicate (s + 1) .B := by
  dsimp only
  rw [visibleWordList_rectangularCircuitPerm_fst,
    visibleWordList_rectangularCircuitPerm_snd,
    visibleWordList_rectangularCircuitPerm_fst,
    visibleWordList_rectangularCircuitPerm_snd]
  simp [visibleWordList, positiveExtremeRow, positiveExtremeColumn,
    siteColour, Function.comp_def, List.ofFn_const, List.replicate_succ]

/-- The negative active core emits all `B` on the left and its marked `B`
followed by `A` on the right. -/
theorem negativeExtreme_rectangular_visibleWords (s : ℕ)
    (p : F × (Fin s → F)) (x : Fin s → F) :
    let ket := rectangularCircuitPerm F (s + 1)
      ((negativeExtremeRow (F := F) s p).1,
        (negativeExtremeColumn (F := F) s x).1)
    let bra := rectangularCircuitPerm F (s + 1)
      ((negativeExtremeRow (F := F) s p).2,
        (negativeExtremeColumn (F := F) s x).2)
    visibleWordList (F := F) (List.ofFn ket.1) =
        List.replicate (s + 1) .B ∧
      visibleWordList (F := F) (List.ofFn ket.2) =
        .B :: List.replicate s .A ∧
      visibleWordList (F := F) (List.ofFn bra.1) =
        List.replicate (s + 1) .B ∧
      visibleWordList (F := F) (List.ofFn bra.2) =
        .B :: List.replicate s .A := by
  dsimp only
  rw [visibleWordList_rectangularCircuitPerm_fst,
    visibleWordList_rectangularCircuitPerm_snd,
    visibleWordList_rectangularCircuitPerm_fst,
    visibleWordList_rectangularCircuitPerm_snd]
  simp [visibleWordList, negativeExtremeRow, negativeExtremeColumn,
    siteColour, Function.comp_def, List.ofFn_succ, List.ofFn_const,
    List.replicate_succ]

/-- The padded positive residual indices reach source support under the
embedded rectangle. -/
theorem positivePadded_embedded_source (m s : ℕ)
    (pre post : PacketBasis F m) (L : Fin (s + 1) → F)
    (x : Fin s → F) :
    rectangularSource F (succPNat (m + s))
        (embeddedRectangularCircuitPerm (F := F) m s
          ((positivePaddedRow (F := F) m s pre L).1,
            (positivePaddedColumn (F := F) m s post x).1))
        (embeddedRectangularCircuitPerm (F := F) m s
          ((positivePaddedRow (F := F) m s pre L).2,
            (positivePaddedColumn (F := F) m s post x).2)) ≠ 0 := by
  have hcore := (positiveExtreme_sourceSector (F := F) s L x).1
  change rectangularSource F (succPNat s)
      (rectangularCircuitPerm F (s + 1)
        ((positiveExtremeRow (F := F) s L).1,
          (positiveExtremeColumn (F := F) s x).1))
      (rectangularCircuitPerm F (s + 1)
        ((positiveExtremeRow (F := F) s L).2,
          (positiveExtremeColumn (F := F) s x).2)) ≠ 0 at hcore
  rw [positivePaddedRow, positivePaddedColumn,
    embeddedRectangularCircuitPerm_apply,
    embeddedRectangularCircuitPerm_apply]
  exact rectangularSource_ne_zero_pad m s pre post _ _ hcore

/-- The same embedded-support statement for the negative residual core. -/
theorem negativePadded_embedded_source (m s : ℕ)
    (pre post : PacketBasis F m) (p : F × (Fin s → F))
    (x : Fin s → F) :
    rectangularSource F (succPNat (m + s))
        (embeddedRectangularCircuitPerm (F := F) m s
          ((negativePaddedRow (F := F) m s pre p).1,
            (negativePaddedColumn (F := F) m s post x).1))
        (embeddedRectangularCircuitPerm (F := F) m s
          ((negativePaddedRow (F := F) m s pre p).2,
            (negativePaddedColumn (F := F) m s post x).2)) ≠ 0 := by
  have hcore := (negativeExtreme_sourceSector (F := F) s p x).1
  change rectangularSource F (succPNat s)
      (rectangularCircuitPerm F (s + 1)
        ((negativeExtremeRow (F := F) s p).1,
          (negativeExtremeColumn (F := F) s x).1))
      (rectangularCircuitPerm F (s + 1)
        ((negativeExtremeRow (F := F) s p).2,
          (negativeExtremeColumn (F := F) s x).2)) ≠ 0 at hcore
  rw [negativePaddedRow, negativePaddedColumn,
    embeddedRectangularCircuitPerm_apply,
    embeddedRectangularCircuitPerm_apply]
  exact rectangularSource_ne_zero_pad m s pre post _ _ hcore

/-! ## Source-local output rearrangements -/

/-- Apply a packet circuit to the source-left packet and a separate circuit
to the unmarked tail of the source-right packet.  The marked site itself is
untouched. -/
def sourceLocalFun (n : ℕ) (leftWord tailWord : List ℕ)
    (u : RectBasis F (n + 1)) : RectBasis F (n + 1) :=
  (spatialCircuitPerm F (n + 1) leftWord u.1,
    Fin.cons (u.2 0)
      (spatialCircuitPerm F n tailWord (fun i => u.2 i.succ)))

/-- Visible words under a source-local rearrangement: the left packet and
the unmarked right tail are rearranged independently, while the marked site
is unchanged. -/
theorem sourceLocalFun_visibleWords (n : ℕ)
    (leftSource leftTarget tailSource tailTarget : List VisibleColour)
    (u : RectBasis F (n + 1))
    (hleft : visibleWordList (F := F) (List.ofFn u.1) = leftSource)
    (htail : visibleWordList (F := F)
      (List.ofFn (fun i : Fin n => u.2 i.succ)) = tailSource)
    (hlenLeft : leftSource.length = leftTarget.length)
    (hcountLeft : leftSource.count .A = leftTarget.count .A)
    (hlenTail : tailSource.length = tailTarget.length)
    (hcountTail : tailSource.count .A = tailTarget.count .A) :
    let out := sourceLocalFun (F := F) n
      (colourRearrangementWord (F := F) leftSource leftTarget)
      (colourRearrangementWord (F := F) tailSource tailTarget) u
    visibleWordList (F := F) (List.ofFn out.1) = leftTarget ∧
      visibleWordList (F := F) (List.ofFn out.2) =
        siteColour F (u.2 0) :: tailTarget := by
  dsimp only
  constructor
  · rw [sourceLocalFun, ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord
      leftSource leftTarget _ hleft hlenLeft hcountLeft
  · rw [sourceLocalFun, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, visibleWordList, List.map_cons]
    congr 1
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord
      tailSource tailTarget _ htail hlenTail hcountTail

/-- Such source-local rearrangements preserve the marked matrix-unit
support. -/
theorem sourceLocalFun_preserves_source (n : ℕ)
    (leftWord tailWord : List ℕ) (u v : RectBasis F (n + 1))
    (huv : rectangularSource F (succPNat n) u v ≠ 0) :
    rectangularSource F (succPNat n)
      (sourceLocalFun (F := F) n leftWord tailWord u)
      (sourceLocalFun (F := F) n leftWord tailWord v) ≠ 0 := by
  rw [rectangularSource_ne_zero_iff] at huv ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [sourceLocalFun, huv.1]
  · intro k hk
    cases k using Fin.cases with
    | zero => exact (hk rfl).elim
    | succ i =>
        simp only [sourceLocalFun, Fin.cons_succ]
        have htail : (fun j : Fin n => u.2 j.succ) =
            fun j : Fin n => v.2 j.succ := by
          funext j
          exact huv.2.1 j.succ (by simp)
        rw [htail]
  · simpa [sourceLocalFun] using huv.2.2.1
  · simpa [sourceLocalFun] using huv.2.2.2

theorem sourceLocalFun_reverse_left (n : ℕ)
    (leftWord tailWord : List ℕ) (u : RectBasis F (n + 1)) :
    sourceLocalFun (F := F) n leftWord.reverse tailWord.reverse
        (sourceLocalFun (F := F) n leftWord tailWord u) = u := by
  apply Prod.ext
  · simp [sourceLocalFun, spatialCircuitPerm_reverse_left]
  · funext i
    cases i using Fin.cases with
    | zero => simp [sourceLocalFun]
    | succ k =>
        simp [sourceLocalFun, spatialCircuitPerm_reverse_left]

/-- Source-local rearrangements preserve and reflect marked-source support. -/
theorem sourceLocalFun_source_ne_zero_iff (n : ℕ)
    (leftWord tailWord : List ℕ) (u v : RectBasis F (n + 1)) :
    rectangularSource F (succPNat n)
        (sourceLocalFun (F := F) n leftWord tailWord u)
        (sourceLocalFun (F := F) n leftWord tailWord v) ≠ 0 ↔
      rectangularSource F (succPNat n) u v ≠ 0 := by
  constructor
  · intro h
    have h' := sourceLocalFun_preserves_source (F := F) n
      leftWord.reverse tailWord.reverse _ _ h
    simpa [sourceLocalFun_reverse_left] using h'
  · exact sourceLocalFun_preserves_source (F := F) n leftWord tailWord u v

/-- The output-rearrangement exponent is identical on the ket and bra of a
source-supported pair, so it cancels from the coefficient phase. -/
theorem sourceLocalExponent_eq (n : ℕ)
    (leftWord tailWord : List ℕ) (u v : RectBasis F (n + 1))
    (huv : rectangularSource F (succPNat n) u v ≠ 0) :
    spatialCircuitExponent F (n + 1) leftWord u.1 +
        spatialCircuitExponent F n tailWord (fun i => u.2 i.succ) =
      spatialCircuitExponent F (n + 1) leftWord v.1 +
        spatialCircuitExponent F n tailWord (fun i => v.2 i.succ) := by
  rw [rectangularSource_ne_zero_iff] at huv
  rw [huv.1]
  have htail : (fun i : Fin n => u.2 i.succ) =
      fun i : Fin n => v.2 i.succ := by
    funext i
    exact huv.2.1 i.succ (by simp)
  rw [htail]

/-! ## Spatial words for packet-local rearrangements -/

/-- Execute independent circuits on the two boundary packets. -/
def boundaryLocalWord (n : ℕ) (leftWord rightWord : List ℕ) : List ℕ :=
  leftWord ++ shiftGateWordBy (n + 1) rightWord

/-- Componentwise support action of the boundary-local word. -/
def boundaryLocalPerm (n : ℕ) (leftWord rightWord : List ℕ) :
    Equiv.Perm (RectBasis F (n + 1)) :=
  Equiv.prodCongr (spatialCircuitPerm F (n + 1) leftWord)
    (spatialCircuitPerm F (n + 1) rightWord)

theorem spatialCircuitPerm_boundaryLocalWord (n : ℕ)
    (leftWord rightWord : List ℕ) (u : RectBasis F (n + 1))
    (hleft : ∀ i ∈ leftWord, i + 1 < n + 1) :
    spatialCircuitPerm F ((n + 1) + (n + 1))
        (boundaryLocalWord n leftWord rightWord) (packetsToSpatial F u) =
      packetsToSpatial F (boundaryLocalPerm (F := F) n leftWord rightWord u) := by
  apply List.ofFn_injective
  rw [ofFn_spatialCircuitPerm, ofFn_packetsToSpatial]
  unfold boundaryLocalWord boundaryLocalPerm
  simp only [Equiv.prodCongr_apply]
  rw [listGateCircuit_append]
  rw [listGateCircuit_append_suffix_of_forall leftWord
    (List.ofFn u.1) (List.ofFn u.2) (by
      intro i hi
      simpa using hleft i hi)]
  rw [show shiftGateWordBy (n + 1) rightWord =
      shiftGateWordBy
        (listGateCircuit (F := F) leftWord (List.ofFn u.1)).length
        rightWord by simp]
  rw [listGateCircuit_shiftGateWordBy]
  rw [← ofFn_spatialCircuitPerm, ← ofFn_spatialCircuitPerm]
  change List.ofFn (spatialCircuitPerm F (n + 1) leftWord u.1) ++
      List.ofFn (spatialCircuitPerm F (n + 1) rightWord u.2) =
    List.ofFn (packetsToSpatial F
      (spatialCircuitPerm F (n + 1) leftWord u.1,
        spatialCircuitPerm F (n + 1) rightWord u.2))
  exact (ofFn_packetsToSpatial (F := F) (n + 1)
    (spatialCircuitPerm F (n + 1) leftWord u.1,
      spatialCircuitPerm F (n + 1) rightWord u.2)).symm

/-- Boundary-local exponents split into independent row- and column-packet
terms. -/
theorem spatialCircuitExponent_boundaryLocalWord (n : ℕ)
    (leftWord rightWord : List ℕ) (u : RectBasis F (n + 1))
    (hleft : ∀ i ∈ leftWord, i + 1 < n + 1) :
    spatialCircuitExponent F ((n + 1) + (n + 1))
        (boundaryLocalWord n leftWord rightWord) (packetsToSpatial F u) =
      spatialCircuitExponent F (n + 1) leftWord u.1 +
        spatialCircuitExponent F (n + 1) rightWord u.2 := by
  rw [spatialCircuitExponent_eq_listGateCircuitExponent,
    ofFn_packetsToSpatial]
  unfold boundaryLocalWord
  rw [listGateCircuitExponent_append]
  rw [listGateCircuit_append_suffix_of_forall leftWord
    (List.ofFn u.1) (List.ofFn u.2) (by
      intro i hi
      simpa using hleft i hi)]
  rw [show shiftGateWordBy (n + 1) rightWord =
      shiftGateWordBy
        (listGateCircuit (F := F) leftWord (List.ofFn u.1)).length
        rightWord by simp]
  rw [listGateCircuitExponent_shiftGateWordBy]
  rw [listGateCircuitExponent_append_suffix_of_forall leftWord
    (List.ofFn u.1) (List.ofFn u.2) (by
      intro i hi
      simpa using hleft i hi)]
  rw [← spatialCircuitExponent_eq_listGateCircuitExponent,
    ← spatialCircuitExponent_eq_listGateCircuitExponent]
  ring

/-- Spatial word executing a circuit on the source-left packet and another
on the unmarked right tail. -/
def sourceLocalWord (n : ℕ) (leftWord tailWord : List ℕ) : List ℕ :=
  leftWord ++ shiftGateWordBy (n + 2) tailWord

theorem spatialCircuitPerm_sourceLocalWord (n : ℕ)
    (leftWord tailWord : List ℕ) (u : RectBasis F (n + 1))
    (hleft : ∀ i ∈ leftWord, i + 1 < n + 1) :
    spatialCircuitPerm F ((n + 1) + (n + 1))
        (sourceLocalWord n leftWord tailWord) (packetsToSpatial F u) =
      packetsToSpatial F (sourceLocalFun (F := F) n leftWord tailWord u) := by
  apply List.ofFn_injective
  rw [ofFn_spatialCircuitPerm, ofFn_packetsToSpatial]
  unfold sourceLocalWord sourceLocalFun
  rw [listGateCircuit_append]
  rw [listGateCircuit_append_suffix_of_forall leftWord
    (List.ofFn u.1) (List.ofFn u.2) (by
      intro i hi
      simpa using hleft i hi)]
  have hright : List.ofFn u.2 =
      u.2 0 :: List.ofFn (fun i : Fin n => u.2 i.succ) := by
    exact List.ofFn_succ (f := u.2)
  rw [hright]
  rw [show shiftGateWordBy (n + 2) tailWord =
      shiftGateWordBy
        (listGateCircuit (F := F) leftWord (List.ofFn u.1)).length
        (shiftGateWord tailWord) by
      rw [show n + 2 = (n + 1) + 1 by omega,
        shiftGateWordBy_succ, ← shiftGateWordBy_shift]
      simp]
  rw [listGateCircuit_shiftGateWordBy,
    listGateCircuit_shiftGateWord]
  rw [← ofFn_spatialCircuitPerm, ← ofFn_spatialCircuitPerm]
  rw [ofFn_packetsToSpatial]
  simp [List.ofFn_succ]

theorem spatialCircuitExponent_sourceLocalWord (n : ℕ)
    (leftWord tailWord : List ℕ) (u : RectBasis F (n + 1))
    (hleft : ∀ i ∈ leftWord, i + 1 < n + 1) :
    spatialCircuitExponent F ((n + 1) + (n + 1))
        (sourceLocalWord n leftWord tailWord) (packetsToSpatial F u) =
      spatialCircuitExponent F (n + 1) leftWord u.1 +
        spatialCircuitExponent F n tailWord (fun i => u.2 i.succ) := by
  rw [spatialCircuitExponent_eq_listGateCircuitExponent,
    ofFn_packetsToSpatial]
  unfold sourceLocalWord
  rw [listGateCircuitExponent_append]
  rw [listGateCircuit_append_suffix_of_forall leftWord
    (List.ofFn u.1) (List.ofFn u.2) (by
      intro i hi
      simpa using hleft i hi)]
  have hright : List.ofFn u.2 =
      u.2 0 :: List.ofFn (fun i : Fin n => u.2 i.succ) := by
    exact List.ofFn_succ (f := u.2)
  rw [hright]
  rw [show shiftGateWordBy (n + 2) tailWord =
      shiftGateWordBy
        (listGateCircuit (F := F) leftWord (List.ofFn u.1)).length
        (shiftGateWord tailWord) by
      rw [show n + 2 = (n + 1) + 1 by omega,
        shiftGateWordBy_succ, ← shiftGateWordBy_shift]
      simp]
  rw [listGateCircuitExponent_shiftGateWordBy,
    listGateCircuitExponent_shiftGateWord]
  rw [← hright]
  rw [listGateCircuitExponent_append_suffix_of_forall leftWord
    (List.ofFn u.1) (List.ofFn u.2) (by
      intro i hi
      simpa using hleft i hi)]
  rw [← spatialCircuitExponent_eq_listGateCircuitExponent,
    ← spatialCircuitExponent_eq_listGateCircuitExponent]
  ring

/-! ## The complete residual replacement path -/

/-- Boundary rearrangement, embedded residual rectangle, and source-local
output rearrangement, in execution order. -/
def paddedReductionWord (m s : ℕ)
    (inputLeft inputRight outputLeft outputTail : List ℕ) : List ℕ :=
  (boundaryLocalWord (m + s) inputLeft inputRight ++
      shiftGateWordBy m (crossingSchedule (s + 1))) ++
    sourceLocalWord (m + s) outputLeft outputTail

/-- Packet-coordinate support output of the replacement path. -/
def paddedReductionOutput (m s : ℕ)
    (inputLeft inputRight outputLeft outputTail : List ℕ)
    (u : RectBasis F (m + s + 1)) : RectBasis F (m + s + 1) :=
  sourceLocalFun (F := F) (m + s) outputLeft outputTail
    (embeddedRectangularCircuitPerm (F := F) m s
      (boundaryLocalPerm (F := F) (m + s) inputLeft inputRight u))

/-- Apply the replacement support path to the ket and bra determined by a
coefficient row and column. -/
def paddedReductionOutputPair (m s : ℕ)
    (inputLeft inputRight outputLeft outputTail : List ℕ)
    (row col : PacketBasis F (m + s + 1) ×
      PacketBasis F (m + s + 1)) :
    RectBasis F (m + s + 1) × RectBasis F (m + s + 1) :=
  (paddedReductionOutput (F := F) m s inputLeft inputRight
      outputLeft outputTail (row.1, col.1),
    paddedReductionOutput (F := F) m s inputLeft inputRight
      outputLeft outputTail (row.2, col.2))

/-- Support action of the complete replacement path. -/
theorem spatialCircuitPerm_paddedReductionWord (m s : ℕ)
    (inputLeft inputRight outputLeft outputTail : List ℕ)
    (u : RectBasis F (m + s + 1))
    (hinputLeft : ∀ i ∈ inputLeft, i + 1 < m + s + 1)
    (houtputLeft : ∀ i ∈ outputLeft, i + 1 < m + s + 1) :
    spatialCircuitPerm F ((m + s + 1) + (m + s + 1))
        (paddedReductionWord m s inputLeft inputRight outputLeft outputTail)
        (packetsToSpatial F u) =
      packetsToSpatial F
        (paddedReductionOutput (F := F) m s inputLeft inputRight
          outputLeft outputTail u) := by
  rw [paddedReductionWord, spatialCircuitPerm_append,
    spatialCircuitPerm_append]
  rw [spatialCircuitPerm_boundaryLocalWord _ _ _ _ hinputLeft]
  have hmiddle (z : RectBasis F (m + s + 1)) :
      spatialCircuitPerm F ((m + s + 1) + (m + s + 1))
          (shiftGateWordBy m (crossingSchedule (s + 1)))
          (packetsToSpatial F z) =
        packetsToSpatial F
          (embeddedRectangularCircuitPerm (F := F) m s z) := by
    simp [embeddedRectangularCircuitPerm]
  rw [hmiddle]
  exact spatialCircuitPerm_sourceLocalWord
    (F := F) (m + s) outputLeft outputTail _ houtputLeft

/-- Exact exponent decomposition of the replacement path. -/
theorem spatialCircuitExponent_paddedReductionWord (m s : ℕ)
    (inputLeft inputRight outputLeft outputTail : List ℕ)
    (u : RectBasis F (m + s + 1))
    (hinputLeft : ∀ i ∈ inputLeft, i + 1 < m + s + 1)
    (houtputLeft : ∀ i ∈ outputLeft, i + 1 < m + s + 1) :
    spatialCircuitExponent F ((m + s + 1) + (m + s + 1))
        (paddedReductionWord m s inputLeft inputRight outputLeft outputTail)
        (packetsToSpatial F u) =
      (let mid := boundaryLocalPerm (F := F) (m + s)
          inputLeft inputRight u
       let source := embeddedRectangularCircuitPerm (F := F) m s mid
       spatialCircuitExponent F (m + s + 1) outputLeft source.1 +
         spatialCircuitExponent F (m + s) outputTail
           (fun i => source.2 i.succ) +
         embeddedRectangularCircuitExponent (F := F) m s mid +
         (spatialCircuitExponent F (m + s + 1) inputLeft u.1 +
           spatialCircuitExponent F (m + s + 1) inputRight u.2)) := by
  rw [paddedReductionWord, spatialCircuitExponent_append,
    spatialCircuitExponent_append]
  rw [spatialCircuitPerm_append]
  rw [spatialCircuitPerm_boundaryLocalWord _ _ _ _ hinputLeft]
  have hmiddle (z : RectBasis F (m + s + 1)) :
      spatialCircuitPerm F ((m + s + 1) + (m + s + 1))
          (shiftGateWordBy m (crossingSchedule (s + 1)))
          (packetsToSpatial F z) =
        packetsToSpatial F
          (embeddedRectangularCircuitPerm (F := F) m s z) := by
    simp [embeddedRectangularCircuitPerm]
  rw [hmiddle]
  rw [spatialCircuitExponent_sourceLocalWord _ _ _ _ houtputLeft]
  unfold embeddedRectangularCircuitExponent
  rw [spatialCircuitExponent_boundaryLocalWord _ _ _ _ hinputLeft]
  simp only [Nat.add_comm 1 s]
  ring

/-! ## Canonical colour words for the two signs -/

@[simp] theorem visibleWordList_append (v w : List (Vq F)) :
    visibleWordList (F := F) (v ++ w) =
      visibleWordList (F := F) v ++ visibleWordList (F := F) w := by
  simp [visibleWordList]

def normalColourWord (a b : ℕ) : List VisibleColour :=
  List.replicate a .A ++ List.replicate b .B

/-- A fixed internally-zero packet representing the canonical spectator
word. -/
def normalPacket (a b : ℕ) : PacketBasis F (a + b) :=
  Fin.append (fun _ : Fin a => Sum.inl 0)
    (fun _ : Fin b => Sum.inr 0)

@[simp] theorem normalPacket_visibleWord (a b : ℕ) :
    visibleWordList (F := F) (List.ofFn (normalPacket (F := F) a b)) =
      normalColourWord a b := by
  rw [show List.ofFn (normalPacket (F := F) a b) =
      List.ofFn (fun _ : Fin a => (Sum.inl 0 : Vq F)) ++
        List.ofFn (fun _ : Fin b => (Sum.inr 0 : Vq F)) by
    exact List.ofFn_fin_append _ _]
  simp [normalColourWord, visibleWordList, siteColour, List.ofFn_const]

def positiveMiddleLeftWord (a b s : ℕ) : List VisibleColour :=
  normalColourWord a b ++ List.replicate (s + 1) .B

def positiveMiddleRightWord (a b s : ℕ) : List VisibleColour :=
  List.replicate (s + 1) .A ++ normalColourWord a b

def positiveSourceLeftWord (a b s : ℕ) : List VisibleColour :=
  normalColourWord a b ++ List.replicate (s + 1) .A

def positiveSourceRightTailWord (a b s : ℕ) : List VisibleColour :=
  List.replicate s .B ++ normalColourWord a b

def negativeMiddleLeftWord (a b s : ℕ) : List VisibleColour :=
  normalColourWord a b ++ .B :: List.replicate s .A

def negativeMiddleRightWord (a b s : ℕ) : List VisibleColour :=
  List.replicate (s + 1) .B ++ normalColourWord a b

def negativeSourceLeftWord (a b s : ℕ) : List VisibleColour :=
  normalColourWord a b ++ List.replicate (s + 1) .B

def negativeSourceRightTailWord (a b s : ℕ) : List VisibleColour :=
  List.replicate s .A ++ normalColourWord a b

@[simp] theorem normalColourWord_length (a b : ℕ) :
    (normalColourWord a b).length = a + b := by
  simp [normalColourWord]

@[simp] theorem normalColourWord_count_A (a b : ℕ) :
    (normalColourWord a b).count .A = a := by
  simp [normalColourWord, List.count_replicate,
    show VisibleColour.A ≠ VisibleColour.B by decide]

@[simp] theorem normalColourWord_count_B (a b : ℕ) :
    (normalColourWord a b).count .B = b := by
  simp [normalColourWord, List.count_replicate,
    show VisibleColour.B ≠ VisibleColour.A by decide]

/-- Input and output rearrangement words for a positive residual. -/
def positiveReductionWord (a b s : ℕ)
    (rowWord colWord : List VisibleColour) : List ℕ :=
  paddedReductionWord (a + b) s
    (colourRearrangementWord (F := F) rowWord
      (positiveMiddleLeftWord a b s))
    (colourRearrangementWord (F := F) colWord
      (positiveMiddleRightWord a b s))
    (colourRearrangementWord (F := F)
      (positiveSourceLeftWord a b s) colWord)
    (colourRearrangementWord (F := F)
      (positiveSourceRightTailWord a b s) rowWord.tail)

/-- Input and output rearrangement words for a negative residual. -/
def negativeReductionWord (a b s : ℕ)
    (rowWord colWord : List VisibleColour) : List ℕ :=
  paddedReductionWord (a + b) s
    (colourRearrangementWord (F := F) rowWord
      (negativeMiddleLeftWord a b s))
    (colourRearrangementWord (F := F) colWord
      (negativeMiddleRightWord a b s))
    (colourRearrangementWord (F := F)
      (negativeSourceLeftWord a b s) colWord)
    (colourRearrangementWord (F := F)
      (negativeSourceRightTailWord a b s) rowWord.tail)

/-- Row reindexing which transports the prescribed word to the positive
middle word. -/
def positiveTransportedRow (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b))
    (L : Fin (s + 1) → F) :
    PacketBasis F (a + b + s + 1) × PacketBasis F (a + b + s + 1) :=
  let w := colourRearrangementWord (F := F) rowWord
    (positiveMiddleLeftWord a b s)
  (spatialCircuitPerm F (a + b + s + 1) w.reverse
      (positivePaddedRow (F := F) (a + b) s pre L).1,
    spatialCircuitPerm F (a + b + s + 1) w.reverse
      (positivePaddedRow (F := F) (a + b) s pre L).2)

def positiveTransportedColumn (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b))
    (x : Fin s → F) :
    PacketBasis F (a + b + s + 1) × PacketBasis F (a + b + s + 1) :=
  let w := colourRearrangementWord (F := F) colWord
    (positiveMiddleRightWord a b s)
  (spatialCircuitPerm F (a + b + s + 1) w.reverse
      (positivePaddedColumn (F := F) (a + b) s post x).1,
    spatialCircuitPerm F (a + b + s + 1) w.reverse
      (positivePaddedColumn (F := F) (a + b) s post x).2)

def negativeTransportedRow (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b))
    (p : F × (Fin s → F)) :
    PacketBasis F (a + b + s + 1) × PacketBasis F (a + b + s + 1) :=
  let w := colourRearrangementWord (F := F) rowWord
    (negativeMiddleLeftWord a b s)
  (spatialCircuitPerm F (a + b + s + 1) w.reverse
      (negativePaddedRow (F := F) (a + b) s pre p).1,
    spatialCircuitPerm F (a + b + s + 1) w.reverse
      (negativePaddedRow (F := F) (a + b) s pre p).2)

def negativeTransportedColumn (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b))
    (x : Fin s → F) :
    PacketBasis F (a + b + s + 1) × PacketBasis F (a + b + s + 1) :=
  let w := colourRearrangementWord (F := F) colWord
    (negativeMiddleRightWord a b s)
  (spatialCircuitPerm F (a + b + s + 1) w.reverse
      (negativePaddedColumn (F := F) (a + b) s post x).1,
    spatialCircuitPerm F (a + b + s + 1) w.reverse
      (negativePaddedColumn (F := F) (a + b) s post x).2)

theorem positivePaddedRow_visibleWord (a b s : ℕ)
    (pre : PacketBasis F (a + b)) (L : Fin (s + 1) → F)
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b) :
    visibleWordList (F := F)
        (List.ofFn (positivePaddedRow (F := F) (a + b) s pre L).1) =
        positiveMiddleLeftWord a b s ∧
      visibleWordList (F := F)
        (List.ofFn (positivePaddedRow (F := F) (a + b) s pre L).2) =
        positiveMiddleLeftWord a b s := by
  constructor
  · change visibleWordList (F := F)
        (List.ofFn (packetPreCore (a + b) s pre
          (positiveExtremeRow (F := F) s L).1)) = _
    rw [ofFn_packetPreCore]
    rw [visibleWordList_append, hpre]
    simp [visibleWordList, positiveExtremeRow,
      positiveMiddleLeftWord, siteColour, Function.comp_def,
      List.ofFn_const, List.replicate_succ]
  · change visibleWordList (F := F)
        (List.ofFn (packetPreCore (a + b) s pre
          (positiveExtremeRow (F := F) s L).2)) = _
    rw [ofFn_packetPreCore]
    rw [visibleWordList_append, hpre]
    simp [visibleWordList, positiveExtremeRow,
      positiveMiddleLeftWord, siteColour, Function.comp_def,
      List.ofFn_const, List.replicate_succ]

theorem positivePaddedColumn_visibleWord (a b s : ℕ)
    (post : PacketBasis F (a + b)) (x : Fin s → F)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b) :
    visibleWordList (F := F)
        (List.ofFn (positivePaddedColumn (F := F) (a + b) s post x).1) =
        positiveMiddleRightWord a b s ∧
      visibleWordList (F := F)
        (List.ofFn (positivePaddedColumn (F := F) (a + b) s post x).2) =
        positiveMiddleRightWord a b s := by
  constructor
  · change visibleWordList (F := F)
        (List.ofFn (packetPostCore (a + b) s
          (positiveExtremeColumn (F := F) s x).1 post)) = _
    rw [ofFn_packetPostCore]
    rw [visibleWordList_append, hpost]
    simp [visibleWordList, positiveExtremeColumn,
      positiveMiddleRightWord, siteColour, Function.comp_def,
      List.ofFn_const, List.replicate_succ]
  · change visibleWordList (F := F)
        (List.ofFn (packetPostCore (a + b) s
          (positiveExtremeColumn (F := F) s x).2 post)) = _
    rw [ofFn_packetPostCore]
    rw [visibleWordList_append, hpost]
    simp [visibleWordList, positiveExtremeColumn,
      positiveMiddleRightWord, siteColour, Function.comp_def,
      List.ofFn_const, List.replicate_succ]

theorem negativePaddedRow_visibleWord (a b s : ℕ)
    (pre : PacketBasis F (a + b)) (p : F × (Fin s → F))
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b) :
    visibleWordList (F := F)
        (List.ofFn (negativePaddedRow (F := F) (a + b) s pre p).1) =
        negativeMiddleLeftWord a b s ∧
      visibleWordList (F := F)
        (List.ofFn (negativePaddedRow (F := F) (a + b) s pre p).2) =
        negativeMiddleLeftWord a b s := by
  constructor
  · change visibleWordList (F := F)
        (List.ofFn (packetPreCore (a + b) s pre
          (negativeExtremeRow (F := F) s p).1)) = _
    rw [ofFn_packetPreCore]
    rw [visibleWordList_append, hpre]
    simp [visibleWordList, negativeExtremeRow,
      negativeMiddleLeftWord, siteColour, Function.comp_def,
      List.ofFn_succ, List.ofFn_const]
  · change visibleWordList (F := F)
        (List.ofFn (packetPreCore (a + b) s pre
          (negativeExtremeRow (F := F) s p).2)) = _
    rw [ofFn_packetPreCore]
    rw [visibleWordList_append, hpre]
    simp [visibleWordList, negativeExtremeRow,
      negativeMiddleLeftWord, siteColour, Function.comp_def,
      List.ofFn_succ, List.ofFn_const]

theorem negativePaddedColumn_visibleWord (a b s : ℕ)
    (post : PacketBasis F (a + b)) (x : Fin s → F)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b) :
    visibleWordList (F := F)
        (List.ofFn (negativePaddedColumn (F := F) (a + b) s post x).1) =
        negativeMiddleRightWord a b s ∧
      visibleWordList (F := F)
        (List.ofFn (negativePaddedColumn (F := F) (a + b) s post x).2) =
        negativeMiddleRightWord a b s := by
  constructor
  · change visibleWordList (F := F)
        (List.ofFn (packetPostCore (a + b) s
          (negativeExtremeColumn (F := F) s x).1 post)) = _
    rw [ofFn_packetPostCore]
    rw [visibleWordList_append, hpost]
    simp [visibleWordList, negativeExtremeColumn,
      negativeMiddleRightWord, siteColour, Function.comp_def,
      List.ofFn_const, List.replicate_succ]
  · change visibleWordList (F := F)
        (List.ofFn (packetPostCore (a + b) s
          (negativeExtremeColumn (F := F) s x).2 post)) = _
    rw [ofFn_packetPostCore]
    rw [visibleWordList_append, hpost]
    simp [visibleWordList, negativeExtremeColumn,
      negativeMiddleRightWord, siteColour, Function.comp_def,
      List.ofFn_const, List.replicate_succ]

/-! ## Visible source words after the embedded residual rectangle -/

theorem positivePadded_embedded_visibleWords (a b s : ℕ)
    (pre post : PacketBasis F (a + b))
    (L : Fin (s + 1) → F) (x : Fin s → F)
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b) :
    let ket := embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((positivePaddedRow (F := F) (a + b) s pre L).1,
        (positivePaddedColumn (F := F) (a + b) s post x).1)
    let bra := embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((positivePaddedRow (F := F) (a + b) s pre L).2,
        (positivePaddedColumn (F := F) (a + b) s post x).2)
    visibleWordList (F := F) (List.ofFn ket.1) =
        positiveSourceLeftWord a b s ∧
      visibleWordList (F := F) (List.ofFn ket.2) =
        .B :: positiveSourceRightTailWord a b s ∧
      visibleWordList (F := F) (List.ofFn bra.1) =
        positiveSourceLeftWord a b s ∧
      visibleWordList (F := F) (List.ofFn bra.2) =
        .B :: positiveSourceRightTailWord a b s := by
  dsimp only
  rw [positivePaddedRow, positivePaddedColumn,
    embeddedRectangularCircuitPerm_apply,
    embeddedRectangularCircuitPerm_apply]
  have hc := positiveExtreme_rectangular_visibleWords (F := F) s L x
  dsimp only at hc
  rcases hc with ⟨hkL, hkR, hbL, hbR⟩
  constructor
  · rw [ofFn_packetPreCore, visibleWordList_append, hpre, hkL]
    rfl
  constructor
  · rw [ofFn_packetPostCore, visibleWordList_append, hkR, hpost]
    simp [positiveSourceRightTailWord, List.replicate_succ,
      List.append_assoc]
  constructor
  · rw [ofFn_packetPreCore, visibleWordList_append, hpre, hbL]
    rfl
  · rw [ofFn_packetPostCore, visibleWordList_append, hbR, hpost]
    simp [positiveSourceRightTailWord, List.replicate_succ,
      List.append_assoc]

theorem negativePadded_embedded_visibleWords (a b s : ℕ)
    (pre post : PacketBasis F (a + b))
    (p : F × (Fin s → F)) (x : Fin s → F)
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b) :
    let ket := embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((negativePaddedRow (F := F) (a + b) s pre p).1,
        (negativePaddedColumn (F := F) (a + b) s post x).1)
    let bra := embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((negativePaddedRow (F := F) (a + b) s pre p).2,
        (negativePaddedColumn (F := F) (a + b) s post x).2)
    visibleWordList (F := F) (List.ofFn ket.1) =
        negativeSourceLeftWord a b s ∧
      visibleWordList (F := F) (List.ofFn ket.2) =
        .B :: negativeSourceRightTailWord a b s ∧
      visibleWordList (F := F) (List.ofFn bra.1) =
        negativeSourceLeftWord a b s ∧
      visibleWordList (F := F) (List.ofFn bra.2) =
        .B :: negativeSourceRightTailWord a b s := by
  dsimp only
  rw [negativePaddedRow, negativePaddedColumn,
    embeddedRectangularCircuitPerm_apply,
    embeddedRectangularCircuitPerm_apply]
  have hc := negativeExtreme_rectangular_visibleWords (F := F) s p x
  dsimp only at hc
  rcases hc with ⟨hkL, hkR, hbL, hbR⟩
  constructor
  · rw [ofFn_packetPreCore, visibleWordList_append, hpre, hkL]
    rfl
  constructor
  · rw [ofFn_packetPostCore, visibleWordList_append, hkR, hpost]
    rfl
  constructor
  · rw [ofFn_packetPreCore, visibleWordList_append, hpre, hbL]
    rfl
  · rw [ofFn_packetPostCore, visibleWordList_append, hbR, hpost]
    rfl

/-! ## Transport into prescribed visible-word fibres -/

/-- The positive padded rows, pulled back through the input rearrangement,
have the prescribed row word on both operator legs. -/
theorem positiveTransportedRow_visibleWord (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b))
    (L : Fin (s + 1) → F)
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hlen : rowWord.length = (positiveMiddleLeftWord a b s).length)
    (hA : rowWord.count .A = (positiveMiddleLeftWord a b s).count .A) :
    visibleWordList (F := F)
        (List.ofFn (positiveTransportedRow (F := F)
          a b s rowWord pre L).1) = rowWord ∧
      visibleWordList (F := F)
        (List.ofFn (positiveTransportedRow (F := F)
          a b s rowWord pre L).2) = rowWord := by
  have hp := positivePaddedRow_visibleWord (F := F) a b s pre L hpre
  constructor
  · unfold positiveTransportedRow
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord_reverse
      rowWord (positiveMiddleLeftWord a b s) _ hp.1 hlen hA
  · unfold positiveTransportedRow
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord_reverse
      rowWord (positiveMiddleLeftWord a b s) _ hp.2 hlen hA

/-- Positive columns are transported into their prescribed word fibre. -/
theorem positiveTransportedColumn_visibleWord (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b))
    (x : Fin s → F)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hlen : colWord.length = (positiveMiddleRightWord a b s).length)
    (hA : colWord.count .A = (positiveMiddleRightWord a b s).count .A) :
    visibleWordList (F := F)
        (List.ofFn (positiveTransportedColumn (F := F)
          a b s colWord post x).1) = colWord ∧
      visibleWordList (F := F)
        (List.ofFn (positiveTransportedColumn (F := F)
          a b s colWord post x).2) = colWord := by
  have hp := positivePaddedColumn_visibleWord (F := F) a b s post x hpost
  constructor
  · unfold positiveTransportedColumn
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord_reverse
      colWord (positiveMiddleRightWord a b s) _ hp.1 hlen hA
  · unfold positiveTransportedColumn
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord_reverse
      colWord (positiveMiddleRightWord a b s) _ hp.2 hlen hA

/-- Negative rows are transported into their prescribed word fibre. -/
theorem negativeTransportedRow_visibleWord (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b))
    (p : F × (Fin s → F))
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hlen : rowWord.length = (negativeMiddleLeftWord a b s).length)
    (hA : rowWord.count .A = (negativeMiddleLeftWord a b s).count .A) :
    visibleWordList (F := F)
        (List.ofFn (negativeTransportedRow (F := F)
          a b s rowWord pre p).1) = rowWord ∧
      visibleWordList (F := F)
        (List.ofFn (negativeTransportedRow (F := F)
          a b s rowWord pre p).2) = rowWord := by
  have hp := negativePaddedRow_visibleWord (F := F) a b s pre p hpre
  constructor
  · unfold negativeTransportedRow
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord_reverse
      rowWord (negativeMiddleLeftWord a b s) _ hp.1 hlen hA
  · unfold negativeTransportedRow
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord_reverse
      rowWord (negativeMiddleLeftWord a b s) _ hp.2 hlen hA

/-- Negative columns are transported into their prescribed word fibre. -/
theorem negativeTransportedColumn_visibleWord (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b))
    (x : Fin s → F)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hlen : colWord.length = (negativeMiddleRightWord a b s).length)
    (hA : colWord.count .A = (negativeMiddleRightWord a b s).count .A) :
    visibleWordList (F := F)
        (List.ofFn (negativeTransportedColumn (F := F)
          a b s colWord post x).1) = colWord ∧
      visibleWordList (F := F)
        (List.ofFn (negativeTransportedColumn (F := F)
          a b s colWord post x).2) = colWord := by
  have hp := negativePaddedColumn_visibleWord (F := F) a b s post x hpost
  constructor
  · unfold negativeTransportedColumn
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord_reverse
      colWord (negativeMiddleRightWord a b s) _ hp.1 hlen hA
  · unfold negativeTransportedColumn
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord_reverse
      colWord (negativeMiddleRightWord a b s) _ hp.2 hlen hA

/-! ## The input rearrangements recover the padded cores -/

theorem boundaryLocalPerm_positiveTransported (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (pre post : PacketBasis F (a + b))
    (L : Fin (s + 1) → F) (x : Fin s → F) :
    let leftWord := colourRearrangementWord (F := F) rowWord
      (positiveMiddleLeftWord a b s)
    let rightWord := colourRearrangementWord (F := F) colWord
      (positiveMiddleRightWord a b s)
    boundaryLocalPerm (F := F) (a + b + s) leftWord rightWord
        ((positiveTransportedRow (F := F) a b s rowWord pre L).1,
          (positiveTransportedColumn (F := F) a b s colWord post x).1) =
        ((positivePaddedRow (F := F) (a + b) s pre L).1,
          (positivePaddedColumn (F := F) (a + b) s post x).1) ∧
      boundaryLocalPerm (F := F) (a + b + s) leftWord rightWord
        ((positiveTransportedRow (F := F) a b s rowWord pre L).2,
          (positiveTransportedColumn (F := F) a b s colWord post x).2) =
        ((positivePaddedRow (F := F) (a + b) s pre L).2,
          (positivePaddedColumn (F := F) (a + b) s post x).2) := by
  dsimp only
  constructor <;>
    simp [boundaryLocalPerm,
      positiveTransportedRow, positiveTransportedColumn,
      spatialCircuitPerm_reverse_right]

theorem boundaryLocalPerm_negativeTransported (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (pre post : PacketBasis F (a + b))
    (p : F × (Fin s → F)) (x : Fin s → F) :
    let leftWord := colourRearrangementWord (F := F) rowWord
      (negativeMiddleLeftWord a b s)
    let rightWord := colourRearrangementWord (F := F) colWord
      (negativeMiddleRightWord a b s)
    boundaryLocalPerm (F := F) (a + b + s) leftWord rightWord
        ((negativeTransportedRow (F := F) a b s rowWord pre p).1,
          (negativeTransportedColumn (F := F) a b s colWord post x).1) =
        ((negativePaddedRow (F := F) (a + b) s pre p).1,
          (negativePaddedColumn (F := F) (a + b) s post x).1) ∧
      boundaryLocalPerm (F := F) (a + b + s) leftWord rightWord
        ((negativeTransportedRow (F := F) a b s rowWord pre p).2,
          (negativeTransportedColumn (F := F) a b s colWord post x).2) =
        ((negativePaddedRow (F := F) (a + b) s pre p).2,
          (negativePaddedColumn (F := F) (a + b) s post x).2) := by
  dsimp only
  constructor <;>
    simp [boundaryLocalPerm,
      negativeTransportedRow, negativeTransportedColumn,
      spatialCircuitPerm_reverse_right]

/-! ## Active support and final words of the replacement path -/

theorem positiveTransported_reduction_source (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (pre post : PacketBasis F (a + b))
    (L : Fin (s + 1) → F) (x : Fin s → F) :
    let row := positiveTransportedRow (F := F)
      a b s rowWord pre L
    let col := positiveTransportedColumn (F := F)
      a b s colWord post x
    let out := paddedReductionOutputPair (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (positiveMiddleLeftWord a b s))
      (colourRearrangementWord (F := F) colWord
        (positiveMiddleRightWord a b s))
      (colourRearrangementWord (F := F)
        (positiveSourceLeftWord a b s) colWord)
      (colourRearrangementWord (F := F)
        (positiveSourceRightTailWord a b s) rowWord.tail)
      row col
    rectangularSource F (succPNat (a + b + s)) out.1 out.2 ≠ 0 := by
  dsimp only
  unfold paddedReductionOutputPair paddedReductionOutput
  have hb := boundaryLocalPerm_positiveTransported (F := F)
    a b s rowWord colWord pre post L x
  dsimp only at hb
  rw [hb.1, hb.2]
  apply sourceLocalFun_preserves_source
  exact positivePadded_embedded_source (F := F) (a + b) s pre post L x

theorem negativeTransported_reduction_source (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (pre post : PacketBasis F (a + b))
    (p : F × (Fin s → F)) (x : Fin s → F) :
    let row := negativeTransportedRow (F := F)
      a b s rowWord pre p
    let col := negativeTransportedColumn (F := F)
      a b s colWord post x
    let out := paddedReductionOutputPair (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (negativeMiddleLeftWord a b s))
      (colourRearrangementWord (F := F) colWord
        (negativeMiddleRightWord a b s))
      (colourRearrangementWord (F := F)
        (negativeSourceLeftWord a b s) colWord)
      (colourRearrangementWord (F := F)
        (negativeSourceRightTailWord a b s) rowWord.tail)
      row col
    rectangularSource F (succPNat (a + b + s)) out.1 out.2 ≠ 0 := by
  dsimp only
  unfold paddedReductionOutputPair paddedReductionOutput
  have hb := boundaryLocalPerm_negativeTransported (F := F)
    a b s rowWord colWord pre post p x
  dsimp only at hb
  rw [hb.1, hb.2]
  apply sourceLocalFun_preserves_source
  exact negativePadded_embedded_source (F := F) (a + b) s pre post p x

theorem positiveTransported_reduction_visibleWords (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (pre post : PacketBasis F (a + b))
    (L : Fin (s + 1) → F) (x : Fin s → F)
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a + s + 1) :
    let row := positiveTransportedRow (F := F)
      a b s rowWord pre L
    let col := positiveTransportedColumn (F := F)
      a b s colWord post x
    let out := paddedReductionOutputPair (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (positiveMiddleLeftWord a b s))
      (colourRearrangementWord (F := F) colWord
        (positiveMiddleRightWord a b s))
      (colourRearrangementWord (F := F)
        (positiveSourceLeftWord a b s) colWord)
      (colourRearrangementWord (F := F)
        (positiveSourceRightTailWord a b s) rowWord.tail)
      row col
    visibleWordList (F := F) (List.ofFn out.1.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn out.1.2) = rowWord ∧
      visibleWordList (F := F) (List.ofFn out.2.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn out.2.2) = rowWord := by
  dsimp only
  unfold paddedReductionOutputPair paddedReductionOutput
  have hb := boundaryLocalPerm_positiveTransported (F := F)
    a b s rowWord colWord pre post L x
  dsimp only at hb
  rw [hb.1, hb.2]
  let ket := embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((positivePaddedRow (F := F) (a + b) s pre L).1,
        (positivePaddedColumn (F := F) (a + b) s post x).1)
  let bra := embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((positivePaddedRow (F := F) (a + b) s pre L).2,
        (positivePaddedColumn (F := F) (a + b) s post x).2)
  have hv := positivePadded_embedded_visibleWords (F := F)
    a b s pre post L x hpre hpost
  change visibleWordList (F := F) (List.ofFn ket.1) = _ ∧
      visibleWordList (F := F) (List.ofFn ket.2) = _ ∧
      visibleWordList (F := F) (List.ofFn bra.1) = _ ∧
      visibleWordList (F := F) (List.ofFn bra.2) = _ at hv
  have hrowEq : .B :: rowWord.tail = rowWord :=
    List.cons_head?_tail hrowHead
  have htailLen : (positiveSourceRightTailWord a b s).length =
      rowWord.tail.length := by
    simp [positiveSourceRightTailWord, List.length_tail, hrowLen]
    omega
  have htailA : (positiveSourceRightTailWord a b s).count .A =
      rowWord.tail.count .A := by
    have hc := congrArg (List.count .A) hrowEq
    simp at hc
    simp [positiveSourceRightTailWord, List.count_replicate, hrowA, hc]
  have hleftLen : (positiveSourceLeftWord a b s).length =
      colWord.length := by
    simp [positiveSourceLeftWord, hcolLen]
    omega
  have hleftA : (positiveSourceLeftWord a b s).count .A =
      colWord.count .A := by
    simp [positiveSourceLeftWord, List.count_replicate, hcolA]
    omega
  have hketTail : visibleWordList (F := F)
      (List.ofFn (fun i : Fin (a + b + s) => ket.2 i.succ)) =
        positiveSourceRightTailWord a b s := by
    rw [visibleWordList_ofFn_succ, hv.2.1]
    rfl
  have hbraTail : visibleWordList (F := F)
      (List.ofFn (fun i : Fin (a + b + s) => bra.2 i.succ)) =
        positiveSourceRightTailWord a b s := by
    rw [visibleWordList_ofFn_succ, hv.2.2.2]
    rfl
  have hketMark : siteColour F (ket.2 0) = .B := by
    have hh := congrArg List.head? hv.2.1
    simpa [visibleWordList, List.ofFn_succ] using hh
  have hbraMark : siteColour F (bra.2 0) = .B := by
    have hh := congrArg List.head? hv.2.2.2
    simpa [visibleWordList, List.ofFn_succ] using hh
  have hk := sourceLocalFun_visibleWords (F := F) (a + b + s)
    (positiveSourceLeftWord a b s) colWord
    (positiveSourceRightTailWord a b s) rowWord.tail ket
    hv.1 hketTail hleftLen hleftA htailLen htailA
  have hb' := sourceLocalFun_visibleWords (F := F) (a + b + s)
    (positiveSourceLeftWord a b s) colWord
    (positiveSourceRightTailWord a b s) rowWord.tail bra
    hv.2.2.1 hbraTail hleftLen hleftA htailLen htailA
  dsimp only at hk hb'
  rw [hketMark, hrowEq] at hk
  rw [hbraMark, hrowEq] at hb'
  exact ⟨hk.1, hk.2, hb'.1, hb'.2⟩

theorem negativeTransported_reduction_visibleWords (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (pre post : PacketBasis F (a + b))
    (p : F × (Fin s → F)) (x : Fin s → F)
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a + s)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a) :
    let row := negativeTransportedRow (F := F)
      a b s rowWord pre p
    let col := negativeTransportedColumn (F := F)
      a b s colWord post x
    let out := paddedReductionOutputPair (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (negativeMiddleLeftWord a b s))
      (colourRearrangementWord (F := F) colWord
        (negativeMiddleRightWord a b s))
      (colourRearrangementWord (F := F)
        (negativeSourceLeftWord a b s) colWord)
      (colourRearrangementWord (F := F)
        (negativeSourceRightTailWord a b s) rowWord.tail)
      row col
    visibleWordList (F := F) (List.ofFn out.1.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn out.1.2) = rowWord ∧
      visibleWordList (F := F) (List.ofFn out.2.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn out.2.2) = rowWord := by
  dsimp only
  unfold paddedReductionOutputPair paddedReductionOutput
  have hb := boundaryLocalPerm_negativeTransported (F := F)
    a b s rowWord colWord pre post p x
  dsimp only at hb
  rw [hb.1, hb.2]
  let ket := embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((negativePaddedRow (F := F) (a + b) s pre p).1,
        (negativePaddedColumn (F := F) (a + b) s post x).1)
  let bra := embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((negativePaddedRow (F := F) (a + b) s pre p).2,
        (negativePaddedColumn (F := F) (a + b) s post x).2)
  have hv := negativePadded_embedded_visibleWords (F := F)
    a b s pre post p x hpre hpost
  change visibleWordList (F := F) (List.ofFn ket.1) = _ ∧
      visibleWordList (F := F) (List.ofFn ket.2) = _ ∧
      visibleWordList (F := F) (List.ofFn bra.1) = _ ∧
      visibleWordList (F := F) (List.ofFn bra.2) = _ at hv
  have hrowEq : .B :: rowWord.tail = rowWord :=
    List.cons_head?_tail hrowHead
  have htailLen : (negativeSourceRightTailWord a b s).length =
      rowWord.tail.length := by
    simp [negativeSourceRightTailWord, List.length_tail, hrowLen]
    omega
  have htailA : (negativeSourceRightTailWord a b s).count .A =
      rowWord.tail.count .A := by
    have hc := congrArg (List.count .A) hrowEq
    simp at hc
    simp [negativeSourceRightTailWord, hrowA, hc]
    omega
  have hleftLen : (negativeSourceLeftWord a b s).length =
      colWord.length := by
    simp [negativeSourceLeftWord, hcolLen]
    omega
  have hleftA : (negativeSourceLeftWord a b s).count .A =
      colWord.count .A := by
    simp [negativeSourceLeftWord, List.count_replicate, hcolA]
  have hketTail : visibleWordList (F := F)
      (List.ofFn (fun i : Fin (a + b + s) => ket.2 i.succ)) =
        negativeSourceRightTailWord a b s := by
    rw [visibleWordList_ofFn_succ, hv.2.1]
    rfl
  have hbraTail : visibleWordList (F := F)
      (List.ofFn (fun i : Fin (a + b + s) => bra.2 i.succ)) =
        negativeSourceRightTailWord a b s := by
    rw [visibleWordList_ofFn_succ, hv.2.2.2]
    rfl
  have hketMark : siteColour F (ket.2 0) = .B := by
    have hh := congrArg List.head? hv.2.1
    simpa [visibleWordList, List.ofFn_succ] using hh
  have hbraMark : siteColour F (bra.2 0) = .B := by
    have hh := congrArg List.head? hv.2.2.2
    simpa [visibleWordList, List.ofFn_succ] using hh
  have hk := sourceLocalFun_visibleWords (F := F) (a + b + s)
    (negativeSourceLeftWord a b s) colWord
    (negativeSourceRightTailWord a b s) rowWord.tail ket
    hv.1 hketTail hleftLen hleftA htailLen htailA
  have hb' := sourceLocalFun_visibleWords (F := F) (a + b + s)
    (negativeSourceLeftWord a b s) colWord
    (negativeSourceRightTailWord a b s) rowWord.tail bra
    hv.2.2.1 hbraTail hleftLen hleftA htailLen htailA
  dsimp only at hk hb'
  rw [hketMark, hrowEq] at hk
  rw [hbraMark, hrowEq] at hb'
  exact ⟨hk.1, hk.2, hb'.1, hb'.2⟩

/-! ## Evaluation and path independence on a complete word fibre -/

theorem spatialCircuitPerm_positiveReductionWord (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (hrowLen : rowWord.length = a + b + s + 1)
    (hcolLen : colWord.length = a + b + s + 1) :
    spatialCircuitPerm F
        ((a + b + s + 1) + (a + b + s + 1))
        (positiveReductionWord (F := F) a b s rowWord colWord)
        (packetsToSpatial F u) =
      packetsToSpatial F
        (paddedReductionOutput (F := F) (a + b) s
          (colourRearrangementWord (F := F) rowWord
            (positiveMiddleLeftWord a b s))
          (colourRearrangementWord (F := F) colWord
            (positiveMiddleRightWord a b s))
          (colourRearrangementWord (F := F)
            (positiveSourceLeftWord a b s) colWord)
          (colourRearrangementWord (F := F)
            (positiveSourceRightTailWord a b s) rowWord.tail) u) := by
  unfold positiveReductionWord
  apply spatialCircuitPerm_paddedReductionWord
  · intro i hi
    have h := mem_colourRearrangementWord_lt
      rowWord (positiveMiddleLeftWord a b s) (by
        simp [positiveMiddleLeftWord, hrowLen]
        omega) hi
    simpa [hrowLen] using h
  · intro i hi
    have h := mem_colourRearrangementWord_lt
      (positiveSourceLeftWord a b s) colWord (by
        simp [positiveSourceLeftWord, hcolLen]
        omega) hi
    simp [positiveSourceLeftWord] at h
    omega

theorem spatialCircuitPerm_negativeReductionWord (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (hrowLen : rowWord.length = a + b + s + 1)
    (hcolLen : colWord.length = a + b + s + 1) :
    spatialCircuitPerm F
        ((a + b + s + 1) + (a + b + s + 1))
        (negativeReductionWord (F := F) a b s rowWord colWord)
        (packetsToSpatial F u) =
      packetsToSpatial F
        (paddedReductionOutput (F := F) (a + b) s
          (colourRearrangementWord (F := F) rowWord
            (negativeMiddleLeftWord a b s))
          (colourRearrangementWord (F := F) colWord
            (negativeMiddleRightWord a b s))
          (colourRearrangementWord (F := F)
            (negativeSourceLeftWord a b s) colWord)
          (colourRearrangementWord (F := F)
            (negativeSourceRightTailWord a b s) rowWord.tail) u) := by
  unfold negativeReductionWord
  apply spatialCircuitPerm_paddedReductionWord
  · intro i hi
    have h := mem_colourRearrangementWord_lt
      rowWord (negativeMiddleLeftWord a b s) (by
        simp [negativeMiddleLeftWord, hrowLen]
        omega) hi
    simpa [hrowLen] using h
  · intro i hi
    have h := mem_colourRearrangementWord_lt
      (negativeSourceLeftWord a b s) colWord (by
        simp [negativeSourceLeftWord, hcolLen]
        omega) hi
    simp [negativeSourceLeftWord] at h
    omega

/-- On every input carrying the prescribed positive-sector packet words,
the replacement path visibly transposes those packets. -/
theorem visibleWord_positiveReductionWord (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) = rowWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a + s + 1) :
    visibleWordList (F := F)
        (List.ofFn (spatialCircuitPerm F
          ((a + b + s + 1) + (a + b + s + 1))
          (positiveReductionWord (F := F) a b s rowWord colWord)
          (packetsToSpatial F u))) = colWord ++ rowWord := by
  let pre : PacketBasis F (a + b) := normalPacket (F := F) a b
  let post : PacketBasis F (a + b) := normalPacket (F := F) a b
  let L : Fin (s + 1) → F := 0
  let x : Fin s → F := 0
  let row := positiveTransportedRow (F := F) a b s rowWord pre L
  let col := positiveTransportedColumn (F := F) a b s colWord post x
  have hrowMidLen : rowWord.length =
      (positiveMiddleLeftWord a b s).length := by
    simp [positiveMiddleLeftWord, hrowLen]
    omega
  have hrowMidA : rowWord.count .A =
      (positiveMiddleLeftWord a b s).count .A := by
    simp [positiveMiddleLeftWord, List.count_replicate, hrowA]
  have hcolMidLen : colWord.length =
      (positiveMiddleRightWord a b s).length := by
    simp [positiveMiddleRightWord, hcolLen]
    omega
  have hcolMidA : colWord.count .A =
      (positiveMiddleRightWord a b s).count .A := by
    simp [positiveMiddleRightWord, List.count_replicate, hcolA]
    omega
  have hr := positiveTransportedRow_visibleWord (F := F)
    a b s rowWord pre L (normalPacket_visibleWord (F := F) a b)
      hrowMidLen hrowMidA
  have hc := positiveTransportedColumn_visibleWord (F := F)
    a b s colWord post x (normalPacket_visibleWord (F := F) a b)
      hcolMidLen hcolMidA
  change visibleWordList (F := F) (List.ofFn row.1) = rowWord ∧
      visibleWordList (F := F) (List.ofFn row.2) = rowWord at hr
  change visibleWordList (F := F) (List.ofFn col.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn col.2) = colWord at hc
  have hin : visibleWordList (F := F)
      (List.ofFn (packetsToSpatial F u)) =
      visibleWordList (F := F)
        (List.ofFn (packetsToSpatial F (row.1, col.1))) := by
    rw [ofFn_packetsToSpatial, ofFn_packetsToSpatial,
      visibleWordList_append, visibleWordList_append,
      huLeft, huRight, hr.1, hc.1]
  have hout := visibleWordList_listGateCircuit_congr
    (F := F) (positiveReductionWord (F := F) a b s rowWord colWord)
    (List.ofFn (packetsToSpatial F u))
    (List.ofFn (packetsToSpatial F (row.1, col.1))) hin
  rw [← ofFn_spatialCircuitPerm, ← ofFn_spatialCircuitPerm] at hout
  calc
    _ = visibleWordList (F := F)
        (List.ofFn (spatialCircuitPerm F
          ((a + b + s + 1) + (a + b + s + 1))
          (positiveReductionWord (F := F) a b s rowWord colWord)
          (packetsToSpatial F (row.1, col.1)))) := hout
    _ = _ := by
      rw [spatialCircuitPerm_positiveReductionWord
        (F := F) a b s rowWord colWord (row.1, col.1)
        hrowLen hcolLen]
      rw [ofFn_packetsToSpatial, visibleWordList_append]
      have hv := positiveTransported_reduction_visibleWords (F := F)
        a b s rowWord colWord pre post L x
        (normalPacket_visibleWord (F := F) a b)
        (normalPacket_visibleWord (F := F) a b)
        hrowLen hrowA hrowHead hcolLen hcolA
      change visibleWordList (F := F)
          (List.ofFn (paddedReductionOutput (F := F) (a + b) s
            _ _ _ _ (row.1, col.1)).1) = colWord ∧
        visibleWordList (F := F)
          (List.ofFn (paddedReductionOutput (F := F) (a + b) s
            _ _ _ _ (row.1, col.1)).2) = rowWord ∧ _ at hv
      rw [hv.1, hv.2.1]

/-- Negative-sector analogue of `visibleWord_positiveReductionWord`. -/
theorem visibleWord_negativeReductionWord (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) = rowWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a + s)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a) :
    visibleWordList (F := F)
        (List.ofFn (spatialCircuitPerm F
          ((a + b + s + 1) + (a + b + s + 1))
          (negativeReductionWord (F := F) a b s rowWord colWord)
          (packetsToSpatial F u))) = colWord ++ rowWord := by
  let pre : PacketBasis F (a + b) := normalPacket (F := F) a b
  let post : PacketBasis F (a + b) := normalPacket (F := F) a b
  let p : F × (Fin s → F) := (0, 0)
  let x : Fin s → F := 0
  let row := negativeTransportedRow (F := F) a b s rowWord pre p
  let col := negativeTransportedColumn (F := F) a b s colWord post x
  have hrowMidLen : rowWord.length =
      (negativeMiddleLeftWord a b s).length := by
    simp [negativeMiddleLeftWord, hrowLen]
    omega
  have hrowMidA : rowWord.count .A =
      (negativeMiddleLeftWord a b s).count .A := by
    simp [negativeMiddleLeftWord, List.count_replicate, hrowA]
  have hcolMidLen : colWord.length =
      (negativeMiddleRightWord a b s).length := by
    simp [negativeMiddleRightWord, hcolLen]
    omega
  have hcolMidA : colWord.count .A =
      (negativeMiddleRightWord a b s).count .A := by
    simp [negativeMiddleRightWord, List.count_replicate, hcolA]
  have hr := negativeTransportedRow_visibleWord (F := F)
    a b s rowWord pre p (normalPacket_visibleWord (F := F) a b)
      hrowMidLen hrowMidA
  have hc := negativeTransportedColumn_visibleWord (F := F)
    a b s colWord post x (normalPacket_visibleWord (F := F) a b)
      hcolMidLen hcolMidA
  change visibleWordList (F := F) (List.ofFn row.1) = rowWord ∧
      visibleWordList (F := F) (List.ofFn row.2) = rowWord at hr
  change visibleWordList (F := F) (List.ofFn col.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn col.2) = colWord at hc
  have hin : visibleWordList (F := F)
      (List.ofFn (packetsToSpatial F u)) =
      visibleWordList (F := F)
        (List.ofFn (packetsToSpatial F (row.1, col.1))) := by
    rw [ofFn_packetsToSpatial, ofFn_packetsToSpatial,
      visibleWordList_append, visibleWordList_append,
      huLeft, huRight, hr.1, hc.1]
  have hout := visibleWordList_listGateCircuit_congr
    (F := F) (negativeReductionWord (F := F) a b s rowWord colWord)
    (List.ofFn (packetsToSpatial F u))
    (List.ofFn (packetsToSpatial F (row.1, col.1))) hin
  rw [← ofFn_spatialCircuitPerm, ← ofFn_spatialCircuitPerm] at hout
  calc
    _ = visibleWordList (F := F)
        (List.ofFn (spatialCircuitPerm F
          ((a + b + s + 1) + (a + b + s + 1))
          (negativeReductionWord (F := F) a b s rowWord colWord)
          (packetsToSpatial F (row.1, col.1)))) := hout
    _ = _ := by
      rw [spatialCircuitPerm_negativeReductionWord
        (F := F) a b s rowWord colWord (row.1, col.1)
        hrowLen hcolLen]
      rw [ofFn_packetsToSpatial, visibleWordList_append]
      have hv := negativeTransported_reduction_visibleWords (F := F)
        a b s rowWord colWord pre post p x
        (normalPacket_visibleWord (F := F) a b)
        (normalPacket_visibleWord (F := F) a b)
        hrowLen hrowA hrowHead hcolLen hcolA
      change visibleWordList (F := F)
          (List.ofFn (paddedReductionOutput (F := F) (a + b) s
            _ _ _ _ (row.1, col.1)).1) = colWord ∧
        visibleWordList (F := F)
          (List.ofFn (paddedReductionOutput (F := F) (a + b) s
            _ _ _ _ (row.1, col.1)).2) = rowWord ∧ _ at hv
      rw [hv.1, hv.2.1]

/-- The complete crossing rectangle visibly swaps its two packet words. -/
theorem visibleWord_crossingSchedule (t : ℕ) (u : RectBasis F t) :
    visibleWordList (F := F)
        (List.ofFn (spatialCircuitPerm F (t + t) (crossingSchedule t)
          (packetsToSpatial F u))) =
      visibleWordList (F := F) (List.ofFn u.2) ++
        visibleWordList (F := F) (List.ofFn u.1) := by
  have hp : spatialCircuitPerm F (t + t) (crossingSchedule t)
      (packetsToSpatial F u) =
      packetsToSpatial F (rectangularCircuitPerm F t u) := by
    simp [rectangularCircuitPerm]
  rw [hp, ofFn_packetsToSpatial, visibleWordList_append,
    visibleWordList_rectangularCircuitPerm_fst,
    visibleWordList_rectangularCircuitPerm_snd]

theorem positiveReduction_colour_eq_crossing (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) = rowWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a + s + 1) :
    (fun i => siteColour F
      (spatialCircuitPerm F
        ((a + b + s + 1) + (a + b + s + 1))
        (crossingSchedule (a + b + s + 1))
        (packetsToSpatial F u) i)) =
    fun i => siteColour F
      (spatialCircuitPerm F
        ((a + b + s + 1) + (a + b + s + 1))
        (positiveReductionWord (F := F) a b s rowWord colWord)
        (packetsToSpatial F u) i) := by
  apply List.ofFn_injective
  rw [← visibleWordList_ofFn, ← visibleWordList_ofFn,
    visibleWord_crossingSchedule, huLeft, huRight,
    visibleWord_positiveReductionWord a b s rowWord colWord u
      huLeft huRight hrowLen hrowA hrowHead hcolLen hcolA]

theorem negativeReduction_colour_eq_crossing (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) = rowWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a + s)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a) :
    (fun i => siteColour F
      (spatialCircuitPerm F
        ((a + b + s + 1) + (a + b + s + 1))
        (crossingSchedule (a + b + s + 1))
        (packetsToSpatial F u) i)) =
    fun i => siteColour F
      (spatialCircuitPerm F
        ((a + b + s + 1) + (a + b + s + 1))
        (negativeReductionWord (F := F) a b s rowWord colWord)
        (packetsToSpatial F u) i) := by
  apply List.ofFn_injective
  rw [← visibleWordList_ofFn, ← visibleWordList_ofFn,
    visibleWord_crossingSchedule, huLeft, huRight,
    visibleWord_negativeReductionWord a b s rowWord colWord u
      huLeft huRight hrowLen hrowA hrowHead hcolLen hcolA]

/-- Exact path-independent exponent identity on a positive word fibre. -/
theorem rectangularCircuitExponent_eq_positiveReductionWord (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) = rowWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a + s + 1) :
    rectangularCircuitExponent F (a + b + s + 1) u =
      spatialCircuitExponent F
        ((a + b + s + 1) + (a + b + s + 1))
        (positiveReductionWord (F := F) a b s rowWord colWord)
        (packetsToSpatial F u) := by
  unfold rectangularCircuitExponent
  apply spatialCircuitExponent_eq_of_colour_eq
  exact positiveReduction_colour_eq_crossing (F := F)
    a b s rowWord colWord u huLeft huRight
    hrowLen hrowA hrowHead hcolLen hcolA

/-- Exact path-independent exponent identity on a negative word fibre. -/
theorem rectangularCircuitExponent_eq_negativeReductionWord (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) = rowWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a + s)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a) :
    rectangularCircuitExponent F (a + b + s + 1) u =
      spatialCircuitExponent F
        ((a + b + s + 1) + (a + b + s + 1))
        (negativeReductionWord (F := F) a b s rowWord colWord)
        (packetsToSpatial F u) := by
  unfold rectangularCircuitExponent
  apply spatialCircuitExponent_eq_of_colour_eq
  exact negativeReduction_colour_eq_crossing (F := F)
    a b s rowWord colWord u huLeft huRight
    hrowLen hrowA hrowHead hcolLen hcolA

/-- Support-action form of positive path independence in packet
coordinates. -/
theorem rectangularCircuitPerm_eq_positiveReductionOutput (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) = rowWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a + s + 1) :
    rectangularCircuitPerm F (a + b + s + 1) u =
      paddedReductionOutput (F := F) (a + b) s
        (colourRearrangementWord (F := F) rowWord
          (positiveMiddleLeftWord a b s))
        (colourRearrangementWord (F := F) colWord
          (positiveMiddleRightWord a b s))
        (colourRearrangementWord (F := F)
          (positiveSourceLeftWord a b s) colWord)
        (colourRearrangementWord (F := F)
          (positiveSourceRightTailWord a b s) rowWord.tail) u := by
  have h := spatialCircuitPerm_eq_of_colour_eq
    (F := F) ((a + b + s + 1) + (a + b + s + 1))
    (crossingSchedule (a + b + s + 1))
    (positiveReductionWord (F := F) a b s rowWord colWord)
    (packetsToSpatial F u)
    (positiveReduction_colour_eq_crossing (F := F)
      a b s rowWord colWord u huLeft huRight
      hrowLen hrowA hrowHead hcolLen hcolA)
  have hrect : spatialCircuitPerm F
      ((a + b + s + 1) + (a + b + s + 1))
      (crossingSchedule (a + b + s + 1)) (packetsToSpatial F u) =
      packetsToSpatial F
        (rectangularCircuitPerm F (a + b + s + 1) u) := by
    simp [rectangularCircuitPerm]
  rw [hrect, spatialCircuitPerm_positiveReductionWord
    (F := F) a b s rowWord colWord u hrowLen hcolLen] at h
  exact (packetsToSpatial F).injective h

/-- Support-action form of negative path independence. -/
theorem rectangularCircuitPerm_eq_negativeReductionOutput (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (u : RectBasis F (a + b + s + 1))
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) = rowWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a + s)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a) :
    rectangularCircuitPerm F (a + b + s + 1) u =
      paddedReductionOutput (F := F) (a + b) s
        (colourRearrangementWord (F := F) rowWord
          (negativeMiddleLeftWord a b s))
        (colourRearrangementWord (F := F) colWord
          (negativeMiddleRightWord a b s))
        (colourRearrangementWord (F := F)
          (negativeSourceLeftWord a b s) colWord)
        (colourRearrangementWord (F := F)
          (negativeSourceRightTailWord a b s) rowWord.tail) u := by
  have h := spatialCircuitPerm_eq_of_colour_eq
    (F := F) ((a + b + s + 1) + (a + b + s + 1))
    (crossingSchedule (a + b + s + 1))
    (negativeReductionWord (F := F) a b s rowWord colWord)
    (packetsToSpatial F u)
    (negativeReduction_colour_eq_crossing (F := F)
      a b s rowWord colWord u huLeft huRight
      hrowLen hrowA hrowHead hcolLen hcolA)
  have hrect : spatialCircuitPerm F
      ((a + b + s + 1) + (a + b + s + 1))
      (crossingSchedule (a + b + s + 1)) (packetsToSpatial F u) =
      packetsToSpatial F
        (rectangularCircuitPerm F (a + b + s + 1) u) := by
    simp [rectangularCircuitPerm]
  rw [hrect, spatialCircuitPerm_negativeReductionWord
    (F := F) a b s rowWord colWord u hrowLen hcolLen] at h
  exact (packetsToSpatial F).injective h

end SqrtOpEnt
