import RequestProject.ExtremePositive
import RequestProject.ExtremeNegative
import RequestProject.EntropyMeasurement

/-!
# Resolving visible words inside a source-count sector

For the lower bound it is enough to measure the complete visible word on
both Schmidt sides after the count measurement.  This avoids coherently
choosing a different packet rearrangement in each word fibre.  The generic
measurement theorem then reduces a count-branch lower bound to the entropy
of every nonzero word-resolved fibre.
-/

namespace SqrtOpEnt

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The visible word of the first input packet, read from the bra row
coordinate.  On source support this is the marked `B` followed by the
unmarked right source word. -/
def coefficientRowWord (n : ℕ)
    (a : PacketBasis F (n + 1) × PacketBasis F (n + 1)) :
    Fin (n + 1) → VisibleColour :=
  fun i => siteColour F (a.2 i)

/-- The visible word of the second input packet, read from the bra column
coordinate.  On source support this is the left source word. -/
def coefficientColumnWord (n : ℕ)
    (b : PacketBasis F (n + 1) × PacketBasis F (n + 1)) :
    Fin (n + 1) → VisibleColour :=
  fun i => siteColour F (b.2 i)

/-- A complete visible-word fibre inside a pulled source-count block. -/
noncomputable def pulledSourceWordFibreBlock
    (psi : AddChar F ℂ) (n j l : ℕ)
    (u v : Fin (n + 1) → VisibleColour) :=
  twoSidedMeasurementBlock (coefficientRowWord (F := F) n)
    (coefficientColumnWord (F := F) n)
    (pulledSourceSectorBlock F psi n j l) u v

theorem pulledSourceSectorBlock_ne_zero_of_bounds
    (psi : AddChar F ℂ) (n j l : ℕ)
    (hj : j < n + 1) (hl : l < n + 2) :
    pulledSourceSectorBlock F psi n j l ≠ 0 := by
  intro hzero
  have hjpos : 0 < n.choose j := Nat.choose_pos (by omega)
  have hlpos : 0 < (n + 1).choose l := Nat.choose_pos (by omega)
  have hqpos : 0 < Fintype.card F := Fintype.card_pos
  have hpos : 0 < (((n + 1).choose l * (Fintype.card F) ^ (n + 1)) *
      (n.choose j * (Fintype.card F) ^ n) : ℕ) := by positivity
  have hnormpos : 0 < schmidtNormSq
      (pulledSourceSectorBlock F psi n j l) := by
    rw [schmidtNormSq_pulledSourceSectorBlock]
    exact_mod_cast hpos
  rw [hzero] at hnormpos
  simp [schmidtNormSq] at hnormpos

/-- If every nonzero visible-word fibre contains the signed-imbalance
entropy, then so does the unresolved count branch. -/
theorem imbEntropy_le_pulledSourceSectorBlock_of_wordFibres
    (psi : AddChar F ℂ) (n j l : ℕ)
    (hj : j < n + 1) (hl : l < n + 2)
    (hfibre : ∀ u v,
      pulledSourceWordFibreBlock (F := F) psi n j l u v ≠ 0 →
        imbEntropy (Fintype.card F)
            ((j : ℤ) + l + 1 - (n + 1)) ≤
          vonNeumannEntropy
            (pulledSourceWordFibreBlock (F := F) psi n j l u v)) :
    imbEntropy (Fintype.card F) ((j : ℤ) + l + 1 - (n + 1)) ≤
      vonNeumannEntropy (pulledSourceSectorBlock F psi n j l) := by
  exact le_vonNeumannEntropy_of_twoSidedMeasurement
    (coefficientRowWord (F := F) n)
    (coefficientColumnWord (F := F) n)
    (pulledSourceSectorBlock F psi n j l)
    (pulledSourceSectorBlock_ne_zero_of_bounds psi n j l hj hl)
    (imbEntropy (Fintype.card F) ((j : ℤ) + l + 1 - (n + 1)))
    hfibre

end SqrtOpEnt
