import RequestProject.NegativeCircuit

/-!
# The concrete negative extreme sector

This file identifies the literal source-count block with no unmarked right
`B` sites and no left `A` sites.  Its residual imbalance is `-s`.  The one
spectator field label repeats rows, while the asymmetric last circuit row is
a column-only phase; neither changes the normalized Schmidt spectrum.
-/

namespace SqrtOpEnt

open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Active row parameters: the spectator `B` label and the `s` left-boundary
`A` labels. -/
def negativeExtremeRow (s : ℕ) (p : F × (Fin s → F)) :
    PacketBasis F (s + 1) × PacketBasis F (s + 1) :=
  (Fin.cases
      (Sum.inr (p.1 + negativeUnitDeltaQ (F := F) s))
      (fun i => Sum.inl (p.2 i + negativeUnitDeltaL (F := F) s i)),
    Fin.cases (Sum.inr p.1) (fun i => Sum.inl (p.2 i)))

/-- Active column parameters on the negative source hyperplane. -/
def negativeExtremeColumn (s : ℕ) (x : Fin s → F) :
    PacketBasis F (s + 1) × PacketBasis F (s + 1) :=
  let R := negativeAllowedRight s x
  ((fun i => Sum.inr (R i + negativeUnitDeltaR (F := F) s i)),
    fun i => Sum.inr (R i))

theorem negativeExtremeRow_injective (s : ℕ) :
    Function.Injective (negativeExtremeRow (F := F) s) := by
  intro p p' h
  apply Prod.ext
  · have hq := congrArg (fun z => siteLabel F (z.2 0)) h
    simpa [negativeExtremeRow, siteLabel] using hq
  · funext i
    have hi := congrArg (fun z => siteLabel F (z.2 i.succ)) h
    simpa [negativeExtremeRow, siteLabel] using hi

theorem negativeExtremeColumn_injective (s : ℕ) :
    Function.Injective (negativeExtremeColumn (F := F) s) := by
  intro x y h
  apply negativeAllowedRight_injective (F := F) s
  funext i
  have hi := congrArg (fun z => siteLabel F (z.2 i)) h
  simpa [negativeExtremeColumn, siteLabel] using hi

/-- Regrouping an active row and column gives the shifted ket boundary and
the unshifted bra boundary. -/
theorem coeffOperatorPair_negativeExtreme (s : ℕ)
    (p : F × (Fin s → F)) (x : Fin s → F) :
    coeffOperatorPairEquiv F (s + 1)
        (negativeExtremeRow (F := F) s p,
          negativeExtremeColumn (F := F) s x) =
      (negativeBoundaryRect s
          (p.1 + negativeUnitDeltaQ (F := F) s)
          (p.2 + negativeUnitDeltaL (F := F) s)
          (negativeAllowedRight s x + negativeUnitDeltaR (F := F) s),
        negativeBoundaryRect s p.1 p.2 (negativeAllowedRight s x)) := by
  rw [negativeBoundaryRect_eq, negativeBoundaryRect_eq]
  rfl

theorem coreSourcePair_negativeExtreme (s : ℕ)
    (p : F × (Fin s → F)) (x : Fin s → F) :
    coreSourcePairEquiv F s
        (negativeExtremeRow (F := F) s p,
          negativeExtremeColumn (F := F) s x) =
      (negativeSourceRect s
          (p.1 + negativeUnitDeltaQ (F := F) s)
          (p.2 + negativeUnitDeltaL (F := F) s)
          (negativeAllowedRight s x + negativeUnitDeltaR (F := F) s),
        negativeSourceRect s p.1 p.2 (negativeAllowedRight s x)) := by
  change (Equiv.prodCongr (rectangularCircuitPerm F (s + 1))
      (rectangularCircuitPerm F (s + 1)))
        (coeffOperatorPairEquiv F (s + 1)
          (negativeExtremeRow (F := F) s p,
            negativeExtremeColumn (F := F) s x)) = _
  rw [coeffOperatorPair_negativeExtreme]
  change (rectangularCircuitPerm F (s + 1) _,
      rectangularCircuitPerm F (s + 1) _) = _
  rw [rectangularCircuitPerm_negativeBoundary,
    rectangularCircuitPerm_negativeBoundary]

theorem negativeBase_source_zero (s : ℕ)
    (L : Fin s → F) (x : Fin s → F) :
    negativeBoundaryValue s L (negativeAllowedRight s x) s 0 = 0 := by
  rw [negativeBoundaryValue_at_source]
  exact negativeAllowedRight_mem_sourceHyperplane s x

/-- The source pair of an active negative row and column is exactly the
canonical marked-source support pair. -/
theorem coreSourcePair_negativeExtreme_eq_sourcePair (s : ℕ)
    (p : F × (Fin s → F)) (x : Fin s → F) :
    coreSourcePairEquiv F s
        (negativeExtremeRow (F := F) s p,
          negativeExtremeColumn (F := F) s x) =
      sourcePairOfParameters F s
        ((negativeSourceRect s p.1 p.2 (negativeAllowedRight s x)).1,
          fun i =>
            (negativeSourceRect s p.1 p.2
              (negativeAllowedRight s x)).2 i.succ) := by
  rw [coreSourcePair_negativeExtreme]
  let R := negativeAllowedRight s x
  let eps : ℕ → ℕ → F := negativeBoundaryValue s p.2 R
  have hshift (i j : ℕ) :
      negativeBoundaryValue s
          (p.2 + negativeUnitDeltaL (F := F) s)
          (R + negativeUnitDeltaR (F := F) s) i j =
        eps i j + negativeUnitEpsilon (F := F) s i j := by
    exact negativeBoundaryValue_add s p.2 _ R _ i j
  have hzero : eps s 0 = 0 := by
    exact negativeBase_source_zero (F := F) s p.2 x
  apply Prod.ext
  · apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [negativeSourceRect, sourcePairOfParameters,
          negativeUnitDeltaQ_eq_zero]
      · simp only [negativeSourceRect, sourcePairOfParameters,
          Fin.cons_zero, Fin.cases_succ]
        rw [hshift, negativeUnitEpsilon_left]
        simp [eps, R]
    · funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [negativeSourceRect, sourcePairOfParameters, Fin.cons_zero]
        rw [hshift, hzero, negativeUnitEpsilon_corner]
        simp
      · simp only [negativeSourceRect, sourcePairOfParameters,
          Fin.cons_succ, Fin.cases_succ]
        rw [hshift, negativeUnitEpsilon_bottom]
        simp [eps, R]
  · apply Prod.ext
    · rfl
    · funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [negativeSourceRect, sourcePairOfParameters, Fin.cons_zero]
        change Sum.inr (eps s 0) = Sum.inr 0
        rw [hzero]
      · rfl

theorem negativeExtreme_sourceSector (s : ℕ)
    (p : F × (Fin s → F)) (x : Fin s → F) :
    SourceSectorPredicate F s 0 0
      (coreSourcePairEquiv F s
        (negativeExtremeRow (F := F) s p,
          negativeExtremeColumn (F := F) s x)) := by
  rw [coreSourcePair_negativeExtreme_eq_sourcePair]
  refine ⟨sourcePairOfParameters_mem_support F s _, ?_, ?_⟩
  · simp [sourcePairOfParameters, negativeSourceRect,
      packetBCount, siteColour]
  · unfold packetACount
    apply Finset.card_eq_zero.mpr
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases i using Fin.cases with
    | zero => simp [sourcePairOfParameters, negativeSourceRect, siteColour]
    | succ k => simp [sourcePairOfParameters, negativeSourceRect, siteColour]

/-! ## Literal active coefficient matrix -/

/-- The negative response-grid coefficient including the asymmetric
column-only final-row phase. -/
noncomputable def negativeAsymmetricGridCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (s : ℕ) :
    Matrix (Fin s → F) (Fin s → F) ℂ :=
  phaseCoeff psi fun L x =>
    negativeFullGridPhase epsilon s L (negativeAllowedRight s x) +
      negativeLastRowPhase epsilon s (negativeAllowedRight s x)

/-- The extra final-row phase is one-sided, so the asymmetric literal grid
has the same entropy as the negative Fourier core. -/
theorem negativeAsymmetricGridCoeff_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s,
      epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    vonNeumannEntropy (negativeAsymmetricGridCoeff psi epsilon s) =
      (s : ℝ) * Real.log (Fintype.card F) := by
  rw [show vonNeumannEntropy (negativeAsymmetricGridCoeff psi epsilon s) =
      vonNeumannEntropy
        (fourierCoeff psi (negativeMixedHessian epsilon s)
          (negativeAllowedRight s)) by
    apply phaseCoeff_vonNeumannEntropy_eq_fourierCoeff
      psi (negativeMixedHessian epsilon s) (negativeAllowedRight s)
        (fun L => negativeFullGridPhase epsilon s L 0)
        (fun x => negativeFullGridPhase epsilon s 0
            (negativeAllowedRight s x) -
              negativeFullGridPhase epsilon s 0 0 +
            negativeLastRowPhase epsilon s (negativeAllowedRight s x))
    intro L x
    rw [negativeFullGridPhase_decompose]
    ring]
  exact negativeSourceHyperplane_vonNeumannEntropy_eq_mul
    psi hpsi epsilon s hodd hepsilon

/-- Include the independent spectator label as a repeated row index. -/
noncomputable def negativeLiteralGridCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (s : ℕ) :
    Matrix (F × (Fin s → F)) (Fin s → F) ℂ :=
  replicateRows (z := F) (negativeAsymmetricGridCoeff psi epsilon s)

theorem negativeLiteralGridCoeff_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s,
      epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    vonNeumannEntropy (negativeLiteralGridCoeff psi epsilon s) =
      (s : ℝ) * Real.log (Fintype.card F) := by
  rw [negativeLiteralGridCoeff, vonNeumannEntropy_replicateRows]
  exact negativeAsymmetricGridCoeff_vonNeumannEntropy
    psi hpsi epsilon s hodd hepsilon

/-- On the active Cartesian support, the literal extreme block is the
negative residual grid with its spectator row. -/
theorem pulledSourceSectorBlock_negativeExtreme_apply
    (psi : AddChar F ℂ) (s : ℕ)
    (p : F × (Fin s → F)) (x : Fin s → F) :
    pulledSourceSectorBlock F psi s 0 0
        (negativeExtremeRow (F := F) s p)
        (negativeExtremeColumn (F := F) s x) =
      negativeLiteralGridCoeff psi (negativeUnitEpsilon (F := F) s) s p x := by
  have hsector := negativeExtreme_sourceSector (F := F) s p x
  have hne : pulledSourceSectorBlock F psi s 0 0
      (negativeExtremeRow (F := F) s p)
      (negativeExtremeColumn (F := F) s x) ≠ 0 := by
    have hnorm := normSq_pulledSourceSectorBlock F psi s 0 0
      (negativeExtremeRow (F := F) s p)
      (negativeExtremeColumn (F := F) s x)
    rw [if_pos hsector] at hnorm
    intro hz
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
    norm_num at hnorm
  rw [pulledSourceSectorBlock_apply_eq_phaseDifference_of_ne_zero
    F psi s 0 0 _ _ hne]
  dsimp only
  rw [coeffOperatorPair_negativeExtreme,
    rectangularCircuitExponent_negative_difference]
  rfl

/-! ## Exhaustion and zero padding -/

abbrev NegativeExtremeSupport (s : ℕ) :=
  {z : CoeffIndexPair F s //
    SourceSectorPredicate F s 0 0 (coreSourcePairEquiv F s z)}

def negativeExtremeParamSupport (s : ℕ) :
    ((F × (Fin s → F)) × (Fin s → F)) →
      NegativeExtremeSupport (F := F) s :=
  fun p => ⟨(negativeExtremeRow (F := F) s p.1,
      negativeExtremeColumn (F := F) s p.2),
    negativeExtreme_sourceSector (F := F) s p.1 p.2⟩

theorem card_negativeExtremeSupport (s : ℕ) :
    Fintype.card (NegativeExtremeSupport (F := F) s) =
      (Fintype.card F) ^ (s + 1) * (Fintype.card F) ^ s := by
  calc
    Fintype.card (NegativeExtremeSupport (F := F) s) =
        Fintype.card {p : SourceIndexPair F s //
          SourceSectorPredicate F s 0 0 p} :=
      Fintype.card_congr
        (Equiv.subtypeEquivOfSubtype (coreSourcePairEquiv F s))
    _ = _ := by
      rw [card_sourceSectorPredicate]
      simp

theorem negativeExtremeParamSupport_bijective (s : ℕ) :
    Function.Bijective (negativeExtremeParamSupport (F := F) s) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro p q h
    have hv := congrArg Subtype.val h
    apply Prod.ext
    · apply negativeExtremeRow_injective (F := F) s
      exact congrArg Prod.fst hv
    · apply negativeExtremeColumn_injective (F := F) s
      exact congrArg Prod.snd hv
  · rw [card_negativeExtremeSupport]
    simp [Fintype.card_prod, Fintype.card_fun, pow_succ, mul_assoc]
    ac_rfl

theorem negativeExtreme_sourceSector_iff_ranges (s : ℕ)
    (a b : PacketBasis F (s + 1) × PacketBasis F (s + 1)) :
    SourceSectorPredicate F s 0 0 (coreSourcePairEquiv F s (a, b)) ↔
      (∃ p, negativeExtremeRow (F := F) s p = a) ∧
        ∃ x, negativeExtremeColumn (F := F) s x = b := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (negativeExtremeParamSupport_bijective
      (F := F) s).2 ⟨(a, b), h⟩
    have hv := congrArg Subtype.val hp
    exact ⟨⟨p.1, congrArg Prod.fst hv⟩,
      p.2, congrArg Prod.snd hv⟩
  · rintro ⟨⟨p, rfl⟩, x, rfl⟩
    exact negativeExtreme_sourceSector (F := F) s p x

theorem pulledSourceSectorBlock_negativeExtreme_eq_zero_of_not_support
    (psi : AddChar F ℂ) (s : ℕ)
    (a b : PacketBasis F (s + 1) × PacketBasis F (s + 1))
    (hnot : ¬ SourceSectorPredicate F s 0 0
      (coreSourcePairEquiv F s (a, b))) :
    pulledSourceSectorBlock F psi s 0 0 a b = 0 := by
  have hnorm := normSq_pulledSourceSectorBlock F psi s 0 0 a b
  change ‖pulledSourceSectorBlock F psi s 0 0 a b‖ ^ 2 =
    (if SourceSectorPredicate F s 0 0
      (coreSourcePairEquiv F s (a, b)) then 1 else 0) at hnorm
  rw [if_neg hnot] at hnorm
  exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hnorm)

abbrev NegativeExtremeRowPad (s : ℕ) :=
  {a : PacketBasis F (s + 1) × PacketBasis F (s + 1) //
    a ∉ Set.range (negativeExtremeRow (F := F) s)}

abbrev NegativeExtremeColumnPad (s : ℕ) :=
  {b : PacketBasis F (s + 1) × PacketBasis F (s + 1) //
    b ∉ Set.range (negativeExtremeColumn (F := F) s)}

noncomputable def negativeExtremeRowEquiv (s : ℕ) :
    ((F × (Fin s → F)) ⊕ NegativeExtremeRowPad (F := F) s) ≃
      (PacketBasis F (s + 1) × PacketBasis F (s + 1)) :=
  (Equiv.sumCongr
      (Equiv.ofInjective (negativeExtremeRow (F := F) s)
        (negativeExtremeRow_injective (F := F) s))
      (Equiv.refl _)).trans
    (Equiv.sumCompl (fun a => a ∈ Set.range (negativeExtremeRow (F := F) s)))

noncomputable def negativeExtremeColumnEquiv (s : ℕ) :
    ((Fin s → F) ⊕ NegativeExtremeColumnPad (F := F) s) ≃
      (PacketBasis F (s + 1) × PacketBasis F (s + 1)) :=
  (Equiv.sumCongr
      (Equiv.ofInjective (negativeExtremeColumn (F := F) s)
        (negativeExtremeColumn_injective (F := F) s))
      (Equiv.refl _)).trans
    (Equiv.sumCompl
      (fun b => b ∈ Set.range (negativeExtremeColumn (F := F) s)))

@[simp]
theorem negativeExtremeRowEquiv_inl (s : ℕ)
    (p : F × (Fin s → F)) :
    negativeExtremeRowEquiv (F := F) s (Sum.inl p) =
      negativeExtremeRow (F := F) s p := by
  simp [negativeExtremeRowEquiv]

@[simp]
theorem negativeExtremeRowEquiv_inr (s : ℕ)
    (a : NegativeExtremeRowPad (F := F) s) :
    negativeExtremeRowEquiv (F := F) s (Sum.inr a) = a := by
  simp [negativeExtremeRowEquiv]

@[simp]
theorem negativeExtremeColumnEquiv_inl (s : ℕ) (x : Fin s → F) :
    negativeExtremeColumnEquiv (F := F) s (Sum.inl x) =
      negativeExtremeColumn (F := F) s x := by
  simp [negativeExtremeColumnEquiv]

@[simp]
theorem negativeExtremeColumnEquiv_inr (s : ℕ)
    (b : NegativeExtremeColumnPad (F := F) s) :
    negativeExtremeColumnEquiv (F := F) s (Sum.inr b) = b := by
  simp [negativeExtremeColumnEquiv]

theorem reindex_pulledSourceSectorBlock_negativeExtreme
    (psi : AddChar F ℂ) (s : ℕ) :
    Matrix.reindex (negativeExtremeRowEquiv (F := F) s).symm
        (negativeExtremeColumnEquiv (F := F) s).symm
        (pulledSourceSectorBlock F psi s 0 0) =
      zeroPad
        (mPad := NegativeExtremeRowPad (F := F) s)
        (nPad := NegativeExtremeColumnPad (F := F) s)
        (negativeLiteralGridCoeff psi
          (negativeUnitEpsilon (F := F) s) s) := by
  classical
  ext i j
  rcases i with p | a <;> rcases j with x | b
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, negativeExtremeRowEquiv_inl,
      negativeExtremeColumnEquiv_inl]
    exact pulledSourceSectorBlock_negativeExtreme_apply psi s p x
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, negativeExtremeRowEquiv_inl,
      negativeExtremeColumnEquiv_inr, zeroPad, Matrix.fromBlocks_apply₁₂]
    apply pulledSourceSectorBlock_negativeExtreme_eq_zero_of_not_support
    intro hs
    obtain ⟨_, ⟨x', hx'⟩⟩ :=
      (negativeExtreme_sourceSector_iff_ranges (F := F) s _ _).mp hs
    exact b.2 ⟨x', hx'⟩
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, negativeExtremeRowEquiv_inr,
      negativeExtremeColumnEquiv_inl, zeroPad, Matrix.fromBlocks_apply₂₁]
    apply pulledSourceSectorBlock_negativeExtreme_eq_zero_of_not_support
    intro hs
    obtain ⟨⟨p', hp'⟩, _⟩ :=
      (negativeExtreme_sourceSector_iff_ranges (F := F) s _ _).mp hs
    exact a.2 ⟨p', hp'⟩
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, negativeExtremeRowEquiv_inr,
      negativeExtremeColumnEquiv_inr, zeroPad, Matrix.fromBlocks_apply₂₂]
    apply pulledSourceSectorBlock_negativeExtreme_eq_zero_of_not_support
    intro hs
    obtain ⟨⟨p', hp'⟩, _⟩ :=
      (negativeExtreme_sourceSector_iff_ranges (F := F) s _ _).mp hs
    exact a.2 ⟨p', hp'⟩

/-- The literal negative extreme count block has entropy `s * log q`. -/
theorem pulledSourceSectorBlock_negativeExtreme_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (s : ℕ)
    (hodd : ringChar F ≠ 2) :
    vonNeumannEntropy (pulledSourceSectorBlock F psi s 0 0) =
      (s : ℝ) * Real.log (Fintype.card F) := by
  rw [← vonNeumannEntropy_reindex_equiv
      (negativeExtremeRowEquiv (F := F) s).symm
      (negativeExtremeColumnEquiv (F := F) s).symm,
    reindex_pulledSourceSectorBlock_negativeExtreme,
    vonNeumannEntropy_zeroPad]
  exact negativeLiteralGridCoeff_vonNeumannEntropy
    psi hpsi (negativeUnitEpsilon (F := F) s) s hodd
      (negativeUnitEpsilon_col_one (F := F) s)

end SqrtOpEnt
