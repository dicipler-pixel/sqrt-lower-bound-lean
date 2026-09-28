import RequestProject.QuantumEntropy

/-!
# Folded colour-count sectors of the rectangular core

This file puts the coefficient matrix of `Xₜ` into the folded onsite basis and
defines the literal `(k,l)` blocks of Section 5.  The left label `k` counts
folded `B` colours and the right label `l` counts folded `A` colours.

The decomposition theorem below is purely finite-dimensional: every entry of
the concrete rectangular coefficient matrix belongs to exactly one count
block.  Subsequent files can therefore prove the source-specific support and
weight formula block by block.
-/

namespace SqrtOpEnt

open Matrix
open scoped BigOperators

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- One folded site carries its ket and bra basis labels. -/
abbrev FoldedSite := Vq F × Vq F

/-- Folded basis configurations of a packet. -/
abbrev FoldedPacket (t : ℕ) := Fin t → FoldedSite F

/-- Pair the ket and bra packets site by site. -/
def foldPacketEquiv (t : ℕ) :
    (PacketBasis F t × PacketBasis F t) ≃ FoldedPacket F t where
  toFun p i := (p.1 i, p.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv p := by rcases p with ⟨p, q⟩; rfl
  right_inv z := rfl

/-- The operator-Schmidt coefficient matrix in the onsite folded basis. -/
noncomputable def foldedRectCoeff {t : ℕ}
    (X : Matrix (RectBasis F t) (RectBasis F t) ℂ) :
    Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ :=
  Matrix.reindex (foldPacketEquiv F t) (foldPacketEquiv F t) (rectCoeff F X)

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Folding the paired packet indices is an invertible reindexing. -/
theorem foldedRectCoeff_ne_zero {t : ℕ}
    (X : Matrix (RectBasis F t) (RectBasis F t) ℂ) (hX : X ≠ 0) :
    foldedRectCoeff F X ≠ 0 := by
  intro hzero
  let e :
      Matrix (PacketBasis F t × PacketBasis F t) (PacketBasis F t × PacketBasis F t) ℂ ≃
        Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ :=
    Matrix.reindex (foldPacketEquiv F t) (foldPacketEquiv F t)
  have hz : e (rectCoeff F X) = e 0 := by
    simpa [e, foldedRectCoeff] using hzero
  have hcoeff : rectCoeff F X = 0 := e.injective hz
  exact hX (rectCoeff_injective F (by simpa using hcoeff))

/-- In particular, the folded coefficient matrix of `Xₜ` is nonzero. -/
theorem foldedRectCoeff_rectangularCore_ne_zero (ψ : AddChar F ℂ) (t : ℕ+) :
    foldedRectCoeff F (rectangularCore F ψ t) ≠ 0 :=
  foldedRectCoeff_ne_zero F _ (rectangularCore_ne_zero F ψ t)

/-- A folded basis label lies in the visible `A` colour space. -/
def IsFoldedA : FoldedSite F → Prop
  | (Sum.inl _, Sum.inl _) => True
  | _ => False

/-- A folded basis label lies in the visible `B` colour space. -/
def IsFoldedB : FoldedSite F → Prop
  | (Sum.inr _, Sum.inr _) => True
  | _ => False

instance instDecidableIsFoldedA (z : FoldedSite F) : Decidable (IsFoldedA F z) :=
  match z with
  | (Sum.inl _, Sum.inl _) => isTrue trivial
  | (Sum.inl _, Sum.inr _) => isFalse id
  | (Sum.inr _, Sum.inl _) => isFalse id
  | (Sum.inr _, Sum.inr _) => isFalse id

instance instDecidableIsFoldedB (z : FoldedSite F) : Decidable (IsFoldedB F z) :=
  match z with
  | (Sum.inl _, Sum.inl _) => isFalse id
  | (Sum.inl _, Sum.inr _) => isFalse id
  | (Sum.inr _, Sum.inl _) => isFalse id
  | (Sum.inr _, Sum.inr _) => isTrue trivial

/-- Number of visible `A` sites in a folded packet configuration. -/
def foldedACount {t : ℕ} (z : FoldedPacket F t) : ℕ :=
  (Finset.univ.filter fun i => IsFoldedA F (z i)).card

/-- Number of visible `B` sites in a folded packet configuration. -/
def foldedBCount {t : ℕ} (z : FoldedPacket F t) : ℕ :=
  (Finset.univ.filter fun i => IsFoldedB F (z i)).card

omit [Field F] [Fintype F] [DecidableEq F] in
theorem foldedACount_le {t : ℕ} (z : FoldedPacket F t) : foldedACount F z ≤ t := by
  simpa [foldedACount] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin t)))
      (p := fun i => IsFoldedA F (z i)))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem foldedBCount_le {t : ℕ} (z : FoldedPacket F t) : foldedBCount F z ≤ t := by
  simpa [foldedBCount] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin t)))
      (p := fun i => IsFoldedB F (z i)))

/-- The `(k,l)` count block of a folded coefficient matrix. -/
def countBlock {t : ℕ}
    (M : Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ) (k l : ℕ) :
    Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ :=
  fun x y => if foldedBCount F x = k ∧ foldedACount F y = l then M x y else 0

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Every folded coefficient matrix is the sum of its finitely many count blocks. -/
theorem sum_countBlocks {t : ℕ}
    (M : Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ) :
    ∑ k ∈ Finset.range (t + 1), ∑ l ∈ Finset.range (t + 1), countBlock F M k l = M := by
  classical
  ext x y
  simp only [Matrix.sum_apply]
  change (∑ k ∈ Finset.range (t + 1), ∑ l ∈ Finset.range (t + 1),
    if foldedBCount F x = k ∧ foldedACount F y = l then M x y else 0) = M x y
  rw [Finset.sum_eq_single (foldedBCount F x)]
  · rw [Finset.sum_eq_single (foldedACount F y)]
    · simp
    · intro l hl hne
      simp [hne.symm]
    · intro hout
      exact (hout (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (foldedACount_le F y)))).elim
  · intro k hk hne
    simp [hne.symm]
  · intro hout
    exact (hout (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (foldedBCount_le F x)))).elim

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Entrywise squared norms are partitioned by the count blocks. -/
theorem sum_countBlock_normSq_apply {t : ℕ}
    (M : Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ)
    (x y : FoldedPacket F t) :
    ∑ k ∈ Finset.range (t + 1), ∑ l ∈ Finset.range (t + 1),
      ‖countBlock F M k l x y‖ ^ 2 = ‖M x y‖ ^ 2 := by
  classical
  rw [Finset.sum_eq_single (foldedBCount F x)]
  · rw [Finset.sum_eq_single (foldedACount F y)]
    · simp [countBlock]
    · intro l hl hne
      simp [countBlock, hne.symm]
    · intro hout
      exact (hout (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (foldedACount_le F y)))).elim
  · intro k hk hne
    simp [countBlock, hne.symm]
  · intro hout
    exact (hout (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (foldedBCount_le F x)))).elim

omit [Field F] [DecidableEq F] in
/-- The squared Hilbert--Schmidt norm of the full folded matrix is the sum of
the squared norms of all count blocks. -/
theorem sum_countBlock_schmidtNormSq {t : ℕ}
    (M : Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ) :
    ∑ k ∈ Finset.range (t + 1), ∑ l ∈ Finset.range (t + 1),
      schmidtNormSq (countBlock F M k l) = schmidtNormSq M := by
  classical
  simp only [schmidtNormSq]
  calc
    (∑ k ∈ Finset.range (t + 1), ∑ l ∈ Finset.range (t + 1),
        ∑ x, ∑ y, ‖countBlock F M k l x y‖ ^ 2) =
      ∑ k ∈ Finset.range (t + 1), ∑ x, ∑ l ∈ Finset.range (t + 1),
        ∑ y, ‖countBlock F M k l x y‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ k ∈ Finset.range (t + 1), ∑ l ∈ Finset.range (t + 1),
        ∑ y, ‖countBlock F M k l x y‖ ^ 2 := by rw [Finset.sum_comm]
    _ = ∑ x, ∑ k ∈ Finset.range (t + 1), ∑ y,
        ∑ l ∈ Finset.range (t + 1), ‖countBlock F M k l x y‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ∑ k ∈ Finset.range (t + 1),
        ∑ l ∈ Finset.range (t + 1), ‖countBlock F M k l x y‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ‖M x y‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          exact sum_countBlock_normSq_apply F M x y

/-- The concrete `(k,l)` branch coefficient matrix of `Xₜ`. -/
noncomputable def rectangularCountBlock (ψ : AddChar F ℂ) (t : ℕ+) (k l : ℕ) :
    Matrix (FoldedPacket F t) (FoldedPacket F t) ℂ :=
  countBlock F (foldedRectCoeff F (rectangularCore F ψ t)) k l

/-- The rectangular core is exactly the coherent sum of its count blocks. -/
theorem rectangularCountBlock_sum (ψ : AddChar F ℂ) (t : ℕ+) :
    ∑ k ∈ Finset.range ((t : ℕ) + 1), ∑ l ∈ Finset.range ((t : ℕ) + 1),
      rectangularCountBlock F ψ t k l = foldedRectCoeff F (rectangularCore F ψ t) :=
  sum_countBlocks F _

/-- Squared-norm weight of a concrete count block, normalized by the full core. -/
noncomputable def rectangularCountWeight (ψ : AddChar F ℂ) (t : ℕ+) (k l : ℕ) : ℝ :=
  schmidtNormSq (rectangularCountBlock F ψ t k l) /
    schmidtNormSq (foldedRectCoeff F (rectangularCore F ψ t))

/-- Count-block weights are nonnegative. -/
theorem rectangularCountWeight_nonneg (ψ : AddChar F ℂ) (t : ℕ+) (k l : ℕ) :
    0 ≤ rectangularCountWeight F ψ t k l := by
  apply div_nonneg
  · exact schmidtNormSq_nonneg _
  · exact (schmidtNormSq_pos _ (foldedRectCoeff_rectangularCore_ne_zero F ψ t)).le

/-- The denominator used in every concrete count-block weight is strictly positive. -/
theorem rectangularCountWeight_denominator_pos (ψ : AddChar F ℂ) (t : ℕ+) :
    0 < schmidtNormSq (foldedRectCoeff F (rectangularCore F ψ t)) :=
  schmidtNormSq_pos _ (foldedRectCoeff_rectangularCore_ne_zero F ψ t)

/-- The concrete count-block weights form a probability distribution. -/
theorem rectangularCountWeight_sum (ψ : AddChar F ℂ) (t : ℕ+) :
    ∑ k ∈ Finset.range ((t : ℕ) + 1), ∑ l ∈ Finset.range ((t : ℕ) + 1),
      rectangularCountWeight F ψ t k l = 1 := by
  let M := foldedRectCoeff F (rectangularCore F ψ t)
  let D := schmidtNormSq M
  change (∑ k ∈ Finset.range ((t : ℕ) + 1), ∑ l ∈ Finset.range ((t : ℕ) + 1),
    schmidtNormSq (countBlock F M k l) / D) = 1
  calc
    _ = ∑ k ∈ Finset.range ((t : ℕ) + 1),
        (∑ l ∈ Finset.range ((t : ℕ) + 1), schmidtNormSq (countBlock F M k l)) / D := by
          apply Finset.sum_congr rfl
          intro k hk
          exact (Finset.sum_div _ _ _).symm
    _ = (∑ k ∈ Finset.range ((t : ℕ) + 1),
        ∑ l ∈ Finset.range ((t : ℕ) + 1), schmidtNormSq (countBlock F M k l)) / D :=
      (Finset.sum_div _ _ _).symm
    _ = D / D := by rw [sum_countBlock_schmidtNormSq]
    _ = 1 := div_self (by
      exact (rectangularCountWeight_denominator_pos F ψ t).ne')

end SqrtOpEnt
