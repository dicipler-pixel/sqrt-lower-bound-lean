import RequestProject.SourceSectorWeights

/-!
# Finite-field phase carried by the concrete rectangle

The monomial circuit was originally recorded with its phase directly in
`Complex`.  Here we retain the finite-field exponent before applying the
additive character.  This gives an exact phase formula for every nonzero
entry of the concrete object `X_t`: it is the additive character of the
difference between the accumulated ket and bra exponents.
-/

namespace SqrtOpEnt

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Finite-field exponent contributed by one triangular crossing. -/
def gateExponent : Vq F × Vq F → F
  | (Sum.inl _, Sum.inl _) => 0
  | (Sum.inr _, Sum.inr _) => 0
  | (Sum.inl a, Sum.inr b) => a * b ^ 2
  | (Sum.inr c, Sum.inl d) => -((c - d) * d ^ 2)

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem gatePhase_eq_character (psi : AddChar F ℂ) (v : Vq F × Vq F) :
    gatePhase F psi v = psi (gateExponent F v) := by
  rcases v with ⟨x, y⟩
  rcases x with a | a <;> rcases y with b | b <;>
    simp [gatePhase, gateExponent]

/-- Exponent contributed by an adjacent gate at positions `i,i+1`. -/
def gateAtExponent (n i : ℕ) (v : SpatialBasis F n) : F := by
  by_cases h : i + 1 < n
  · exact gateExponent F (v ⟨i, Nat.lt_of_succ_lt h⟩, v ⟨i + 1, h⟩)
  · exact 0

omit [Fintype F] [DecidableEq F] in
theorem gateAtPhase_eq_character (psi : AddChar F ℂ) (n i : ℕ)
    (v : SpatialBasis F n) :
    gateAtPhase F psi n i v = psi (gateAtExponent F n i v) := by
  unfold gateAtPhase gateAtExponent
  split_ifs
  · exact gatePhase_eq_character F psi _
  · simp

/-- Sum of all local finite-field exponents along an adjacent-gate word. -/
def spatialCircuitExponent (n : ℕ) :
    List ℕ → SpatialBasis F n → F
  | [], _ => 0
  | i :: tail, v =>
      spatialCircuitExponent n tail (gateAtPerm F n i v) +
        gateAtExponent F n i v

omit [Fintype F] [DecidableEq F] in
/-- The complex circuit phase is exactly the additive character of the
accumulated finite-field exponent. -/
theorem spatialCircuitPhase_eq_character (psi : AddChar F ℂ) (n : ℕ)
    (word : List ℕ) (v : SpatialBasis F n) :
    spatialCircuitPhase F psi n word v =
      psi (spatialCircuitExponent F n word v) := by
  induction word generalizing v with
  | nil => simp [spatialCircuitPhase, spatialCircuitExponent]
  | cons i tail ih =>
      simp only [spatialCircuitPhase, spatialCircuitExponent, ih,
        gateAtPhase_eq_character]
      exact (psi.map_add_eq_mul _ _).symm

/-- The accumulated finite-field exponent of the concrete `t × t`
rectangle in packet coordinates. -/
def rectangularCircuitExponent (t : ℕ) (v : RectBasis F t) : F :=
  spatialCircuitExponent F (t + t) (crossingSchedule t) (packetsToSpatial F v)

omit [Fintype F] [DecidableEq F] in
theorem rectangularCircuitPhase_eq_character (psi : AddChar F ℂ) (t : ℕ)
    (v : RectBasis F t) :
    rectangularCircuitPhase F psi t v = psi (rectangularCircuitExponent F t v) :=
  spatialCircuitPhase_eq_character F psi _ _ _

/-- On source support, every concrete `X_t` entry is the character of a
finite-field phase difference. -/
theorem rectangularCore_apply_eq_phaseDifference
    (psi : AddChar F ℂ) (t : ℕ+) (u v : RectBasis F t)
    (hsource : rectangularSource F t (rectangularCircuitPerm F t u)
        (rectangularCircuitPerm F t v) = 1) :
    rectangularCore F psi t u v =
      psi (rectangularCircuitExponent F t v -
        rectangularCircuitExponent F t u) := by
  rw [rectangularCore_apply, rectangularCircuitPhase_eq_character,
    rectangularCircuitPhase_eq_character, hsource]
  have hstar : star (psi (rectangularCircuitExponent F t u)) =
      psi (-rectangularCircuitExponent F t u) := by
    calc
      star (psi (rectangularCircuitExponent F t u)) =
          (psi (rectangularCircuitExponent F t u))⁻¹ := by
        simpa only [starRingEnd_apply] using
          (AddChar.inv_apply_eq_conj psi (rectangularCircuitExponent F t u)).symm
      _ = psi (-rectangularCircuitExponent F t u) :=
        (AddChar.map_neg_eq_inv psi _).symm
  rw [hstar, mul_one, ← psi.map_add_eq_mul]
  congr 1
  ring

/-- Equivalent support-oriented form: nonzero entries of `X_(n+1)` have the
exact phase-difference formula above. -/
theorem rectangularCore_apply_eq_phaseDifference_of_ne_zero
    (psi : AddChar F ℂ) (n : ℕ) (u v : RectBasis F (n + 1))
    (hcore : rectangularCore F psi (succPNat n) u v ≠ 0) :
    rectangularCore F psi (succPNat n) u v =
      psi (rectangularCircuitExponent F (n + 1) v -
        rectangularCircuitExponent F (n + 1) u) := by
  have hs : rectangularSource F (succPNat n)
      (rectangularCircuitPerm F (n + 1) u)
      (rectangularCircuitPerm F (n + 1) v) ≠ 0 :=
    (rectangularCore_ne_zero_apply_iff F psi (succPNat n) u v).mp hcore
  have hone : rectangularSource F (succPNat n)
      (rectangularCircuitPerm F (n + 1) u)
      (rectangularCircuitPerm F (n + 1) v) = 1 :=
    rectangularSource_eq_one_of_ne_zero F n _ _ hs
  exact rectangularCore_apply_eq_phaseDifference F psi (succPNat n) u v hone

/-- The same phase formula at the level of a concrete source-count block of
the operator-Schmidt coefficient matrix.  Thus the blocks whose norms were
counted in `SourceSectorWeights.lean` are now explicitly character-valued
finite-difference matrices. -/
theorem pulledSourceSectorBlock_apply_eq_phaseDifference_of_ne_zero
    (psi : AddChar F ℂ) (n j l : ℕ)
    (x y : PacketBasis F (n + 1) × PacketBasis F (n + 1))
    (hblock : pulledSourceSectorBlock F psi n j l x y ≠ 0) :
    pulledSourceSectorBlock F psi n j l x y =
      let p := coeffOperatorPairEquiv F (n + 1) (x, y)
      psi (rectangularCircuitExponent F (n + 1) p.2 -
        rectangularCircuitExponent F (n + 1) p.1) := by
  unfold pulledSourceSectorBlock at hblock ⊢
  dsimp only
  by_cases hsector : packetBCount F
      (fun i => (coreSourcePairEquiv F n (x, y)).1.2 i.succ) = j ∧
      packetACount F (coreSourcePairEquiv F n (x, y)).1.1 = l
  · let p := coeffOperatorPairEquiv F (n + 1) (x, y)
    rw [if_pos hsector] at hblock ⊢
    have hcore : rectangularCore F psi (succPNat n) p.1 p.2 ≠ 0 := by
      simpa [p, coeffOperatorPairEquiv] using hblock
    simpa [p, coeffOperatorPairEquiv] using
      rectangularCore_apply_eq_phaseDifference_of_ne_zero F psi n p.1 p.2 hcore
  · rw [if_neg hsector] at hblock
    exact (hblock rfl).elim

end SqrtOpEnt
