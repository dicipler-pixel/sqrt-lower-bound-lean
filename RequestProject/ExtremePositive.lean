import RequestProject.ResidualCircuit

/-!
# The concrete positive extreme sector

This file identifies the literal source-count block in which every input
left site has colour `B` and every source-left site has colour `A` with the
positive response-grid coefficient matrix.  The remaining ambient rows and
columns are zero padding.
-/

namespace SqrtOpEnt

open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Row coefficient index associated with positive boundary-left data. -/
def positiveExtremeRow (n : ℕ) (L : Fin (n + 1) → F) :
    PacketBasis F (n + 1) × PacketBasis F (n + 1) :=
  ((fun i => Sum.inr (L i + positiveUnitDeltaL (F := F) n i)),
    fun i => Sum.inr (L i))

/-- Column coefficient index associated with the parameterized positive
source hyperplane. -/
def positiveExtremeColumn (n : ℕ) (x : Fin n → F) :
    PacketBasis F (n + 1) × PacketBasis F (n + 1) :=
  let R := positiveAllowedRight n x
  ((fun i => Sum.inl (R i + positiveUnitDeltaR (F := F) n i)),
    fun i => Sum.inl (R i))

theorem positiveExtremeRow_injective (n : ℕ) :
    Function.Injective (positiveExtremeRow (F := F) n) := by
  intro L L' h
  funext i
  have hi := congrArg (fun z => siteLabel F (z.2 i)) h
  simpa [positiveExtremeRow, siteLabel] using hi

theorem positiveExtremeColumn_injective (n : ℕ) :
    Function.Injective (positiveExtremeColumn (F := F) n) := by
  intro x y h
  apply positiveAllowedRight_injective (F := F) n
  funext i
  have hi := congrArg (fun z => siteLabel F (z.2 i)) h
  simpa [positiveExtremeColumn, siteLabel] using hi

/-- Regrouping an active row and column produces the shifted ket boundary
and the unshifted bra boundary. -/
theorem coeffOperatorPair_positiveExtreme (n : ℕ)
    (L : Fin (n + 1) → F) (x : Fin n → F) :
    coeffOperatorPairEquiv F (n + 1)
        (positiveExtremeRow (F := F) n L,
          positiveExtremeColumn (F := F) n x) =
      (positiveBoundaryRect (n + 1)
          (L + positiveUnitDeltaL (F := F) n)
          (positiveAllowedRight n x + positiveUnitDeltaR (F := F) n),
        positiveBoundaryRect (n + 1) L (positiveAllowedRight n x)) := by
  rw [positiveBoundaryRect_eq, positiveBoundaryRect_eq]
  rfl

/-- In source coordinates, an active positive index pair is represented by
the two response-grid output edges. -/
theorem coreSourcePair_positiveExtreme (n : ℕ)
    (L : Fin (n + 1) → F) (x : Fin n → F) :
    coreSourcePairEquiv F n
        (positiveExtremeRow (F := F) n L,
          positiveExtremeColumn (F := F) n x) =
      (positiveSourceRect (n + 1)
          (L + positiveUnitDeltaL (F := F) n)
          (positiveAllowedRight n x + positiveUnitDeltaR (F := F) n),
        positiveSourceRect (n + 1) L (positiveAllowedRight n x)) := by
  change (Equiv.prodCongr (rectangularCircuitPerm F (n + 1))
      (rectangularCircuitPerm F (n + 1)))
        (coeffOperatorPairEquiv F (n + 1)
          (positiveExtremeRow (F := F) n L,
            positiveExtremeColumn (F := F) n x)) = _
  rw [coeffOperatorPair_positiveExtreme]
  change (rectangularCircuitPerm F (n + 1)
      (positiveBoundaryRect (n + 1)
        (L + positiveUnitDeltaL (F := F) n)
        (positiveAllowedRight n x + positiveUnitDeltaR (F := F) n)),
      rectangularCircuitPerm F (n + 1)
        (positiveBoundaryRect (n + 1) L (positiveAllowedRight n x))) = _
  rw [
    rectangularCircuitPerm_positiveBoundary,
    rectangularCircuitPerm_positiveBoundary]

/-- The unshifted positive grid satisfies the marked source equation. -/
theorem positiveBase_source_zero (n : ℕ)
    (L : Fin (n + 1) → F) (x : Fin n → F) :
    positiveBoundaryValue (n + 1) L (positiveAllowedRight n x) n 1 = 0 := by
  rw [positiveBoundaryValue_at_source]
  exact positiveAllowedRight_mem_sourceHyperplane n x

/-- The concrete source pair of an active positive row/column is exactly
the canonical source-support pair. -/
theorem coreSourcePair_positiveExtreme_eq_sourcePair (n : ℕ)
    (L : Fin (n + 1) → F) (x : Fin n → F) :
    coreSourcePairEquiv F n
        (positiveExtremeRow (F := F) n L,
          positiveExtremeColumn (F := F) n x) =
      sourcePairOfParameters F n
        ((positiveSourceRect (n + 1) L (positiveAllowedRight n x)).1,
          fun i => (positiveSourceRect (n + 1) L
            (positiveAllowedRight n x)).2 i.succ) := by
  rw [coreSourcePair_positiveExtreme]
  have hshift (i j : ℕ) :
      positiveBoundaryValue (n + 1)
          (L + positiveUnitDeltaL (F := F) n)
          (positiveAllowedRight n x + positiveUnitDeltaR (F := F) n) i j =
        positiveBoundaryValue (n + 1) L (positiveAllowedRight n x) i j +
          positiveUnitEpsilon (F := F) n i j := by
    exact positiveBoundaryValue_add (n + 1) L _ (positiveAllowedRight n x) _ i j
  have hzero : positiveBoundaryValue (n + 1) L
      (positiveAllowedRight n x) n 1 = 0 := by
    exact positiveBase_source_zero (F := F) n L x
  have hepsZero (i : Fin (n + 1)) :
      positiveUnitEpsilon (F := F) n i 0 = 0 :=
    positiveUnitEpsilon_col_zero (F := F) n i
  have hepsBottom (j : Fin (n + 1)) :
      positiveUnitEpsilon (F := F) n n (j + 1) =
        if j = 0 then 1 else 0 :=
    positiveUnitEpsilon_bottom (F := F) n j
  apply Prod.ext
  · apply Prod.ext
    · funext i
      simp only [positiveSourceRect, sourcePairOfParameters]
      rw [hshift, hepsZero]
      simp
    · funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [positiveSourceRect, sourcePairOfParameters, Fin.cons_zero,
          Nat.add_sub_cancel]
        rw [hshift]
        have hzero' : positiveBoundaryValue (n + 1) L
            (positiveAllowedRight n x) n ((0 : Fin (n + 1)) + 1) = 0 := by
          simpa using hzero
        have heps' : positiveUnitEpsilon (F := F) n n
            ((0 : Fin (n + 1)) + 1) = 1 := by
          simpa using hepsBottom (0 : Fin (n + 1))
        rw [hzero', heps']
        simp
      · simp only [positiveSourceRect, sourcePairOfParameters, Fin.cons_succ,
          Nat.add_sub_cancel]
        rw [hshift, hepsBottom]
        simp
  · apply Prod.ext
    · rfl
    · funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [positiveSourceRect, sourcePairOfParameters, Fin.cons_zero,
          Nat.add_sub_cancel]
        have hzero' : positiveBoundaryValue (n + 1) L
            (positiveAllowedRight n x) n ((0 : Fin (n + 1)) + 1) = 0 := by
          simpa using hzero
        rw [hzero']
      · simp [positiveSourceRect, sourcePairOfParameters]

/-- Every active positive row/column lies in the literal extreme sector. -/
theorem positiveExtreme_sourceSector (n : ℕ)
    (L : Fin (n + 1) → F) (x : Fin n → F) :
    SourceSectorPredicate F n n (n + 1)
      (coreSourcePairEquiv F n
        (positiveExtremeRow (F := F) n L,
          positiveExtremeColumn (F := F) n x)) := by
  rw [coreSourcePair_positiveExtreme_eq_sourcePair]
  refine ⟨sourcePairOfParameters_mem_support F n _, ?_, ?_⟩
  · simp [sourcePairOfParameters, positiveSourceRect, packetBCount, siteColour]
  · simp [sourcePairOfParameters, positiveSourceRect, packetACount, siteColour]

/-- On its active Cartesian support, the literal extreme block is exactly
the full positive response-grid phase matrix. -/
theorem pulledSourceSectorBlock_positiveExtreme_apply
    (psi : AddChar F ℂ) (n : ℕ)
    (L : Fin (n + 1) → F) (x : Fin n → F) :
    pulledSourceSectorBlock F psi n n (n + 1)
        (positiveExtremeRow (F := F) n L)
        (positiveExtremeColumn (F := F) n x) =
      positiveFullGridCoeff psi (positiveUnitEpsilon (F := F) n) n L x := by
  have hsector := positiveExtreme_sourceSector (F := F) n L x
  have hne : pulledSourceSectorBlock F psi n n (n + 1)
      (positiveExtremeRow (F := F) n L)
      (positiveExtremeColumn (F := F) n x) ≠ 0 := by
    have hnorm := normSq_pulledSourceSectorBlock F psi n n (n + 1)
      (positiveExtremeRow (F := F) n L)
      (positiveExtremeColumn (F := F) n x)
    rw [if_pos hsector] at hnorm
    intro hz
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
    norm_num at hnorm
  rw [pulledSourceSectorBlock_apply_eq_phaseDifference_of_ne_zero
    F psi n n (n + 1) _ _ hne]
  dsimp only
  rw [coeffOperatorPair_positiveExtreme]
  rw [rectangularCircuitExponent_positive_difference]
  rfl

/-! ## Exhaustion of the block support -/

/-- Support subtype of the positive extreme sector in coefficient
coordinates. -/
abbrev PositiveExtremeSupport (n : ℕ) :=
  {z : CoeffIndexPair F n //
    SourceSectorPredicate F n n (n + 1) (coreSourcePairEquiv F n z)}

/-- The explicit response-grid parameters map into the concrete sector
support. -/
def positiveExtremeParamSupport (n : ℕ) :
    ((Fin (n + 1) → F) × (Fin n → F)) → PositiveExtremeSupport (F := F) n :=
  fun p => ⟨(positiveExtremeRow (F := F) n p.1,
      positiveExtremeColumn (F := F) n p.2),
    positiveExtreme_sourceSector (F := F) n p.1 p.2⟩

theorem card_positiveExtremeSupport (n : ℕ) :
    Fintype.card (PositiveExtremeSupport (F := F) n) =
      (Fintype.card F) ^ (n + 1) * (Fintype.card F) ^ n := by
  calc
    Fintype.card (PositiveExtremeSupport (F := F) n) =
        Fintype.card {p : SourceIndexPair F n //
          SourceSectorPredicate F n n (n + 1) p} :=
      Fintype.card_congr
        (Equiv.subtypeEquivOfSubtype (coreSourcePairEquiv F n))
    _ = _ := by
      rw [card_sourceSectorPredicate]
      simp

theorem positiveExtremeParamSupport_bijective (n : ℕ) :
    Function.Bijective (positiveExtremeParamSupport (F := F) n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro p q h
    have hv := congrArg Subtype.val h
    apply Prod.ext
    · apply positiveExtremeRow_injective (F := F) n
      exact congrArg Prod.fst hv
    · apply positiveExtremeColumn_injective (F := F) n
      exact congrArg Prod.snd hv
  · rw [card_positiveExtremeSupport]
    simp [Fintype.card_prod, Fintype.card_fun]

/-- The sector support is exactly the Cartesian product of the active row
and column ranges. -/
theorem positiveExtreme_sourceSector_iff_ranges (n : ℕ)
    (a b : PacketBasis F (n + 1) × PacketBasis F (n + 1)) :
    SourceSectorPredicate F n n (n + 1) (coreSourcePairEquiv F n (a, b)) ↔
      (∃ L, positiveExtremeRow (F := F) n L = a) ∧
        ∃ x, positiveExtremeColumn (F := F) n x = b := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (positiveExtremeParamSupport_bijective (F := F) n).2
      ⟨(a, b), h⟩
    have hv := congrArg Subtype.val hp
    exact ⟨⟨p.1, congrArg Prod.fst hv⟩,
      p.2, congrArg Prod.snd hv⟩
  · rintro ⟨⟨L, rfl⟩, x, rfl⟩
    exact positiveExtreme_sourceSector (F := F) n L x

/-- Outside the explicit Cartesian support, the extreme sector block
vanishes. -/
theorem pulledSourceSectorBlock_positiveExtreme_eq_zero_of_not_support
    (psi : AddChar F ℂ) (n : ℕ)
    (a b : PacketBasis F (n + 1) × PacketBasis F (n + 1))
    (hnot : ¬ SourceSectorPredicate F n n (n + 1)
      (coreSourcePairEquiv F n (a, b))) :
    pulledSourceSectorBlock F psi n n (n + 1) a b = 0 := by
  have hnorm := normSq_pulledSourceSectorBlock F psi n n (n + 1) a b
  change ‖pulledSourceSectorBlock F psi n n (n + 1) a b‖ ^ 2 =
    (if SourceSectorPredicate F n n (n + 1)
      (coreSourcePairEquiv F n (a, b)) then 1 else 0) at hnorm
  rw [if_neg hnot] at hnorm
  exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hnorm)

/-! ## Zero-padding equivalence -/

abbrev PositiveExtremeRowPad (n : ℕ) :=
  {a : PacketBasis F (n + 1) × PacketBasis F (n + 1) //
    a ∉ Set.range (positiveExtremeRow (F := F) n)}

abbrev PositiveExtremeColumnPad (n : ℕ) :=
  {b : PacketBasis F (n + 1) × PacketBasis F (n + 1) //
    b ∉ Set.range (positiveExtremeColumn (F := F) n)}

/-- Split the ambient row basis into active response-grid rows and their
complement. -/
noncomputable def positiveExtremeRowEquiv (n : ℕ) :
    ((Fin (n + 1) → F) ⊕ PositiveExtremeRowPad (F := F) n) ≃
      (PacketBasis F (n + 1) × PacketBasis F (n + 1)) :=
  (Equiv.sumCongr
      (Equiv.ofInjective (positiveExtremeRow (F := F) n)
        (positiveExtremeRow_injective (F := F) n))
      (Equiv.refl _)).trans
    (Equiv.sumCompl (fun a => a ∈ Set.range (positiveExtremeRow (F := F) n)))

/-- Split the ambient column basis into active response-grid columns and
their complement. -/
noncomputable def positiveExtremeColumnEquiv (n : ℕ) :
    ((Fin n → F) ⊕ PositiveExtremeColumnPad (F := F) n) ≃
      (PacketBasis F (n + 1) × PacketBasis F (n + 1)) :=
  (Equiv.sumCongr
      (Equiv.ofInjective (positiveExtremeColumn (F := F) n)
        (positiveExtremeColumn_injective (F := F) n))
      (Equiv.refl _)).trans
    (Equiv.sumCompl (fun b => b ∈ Set.range (positiveExtremeColumn (F := F) n)))

@[simp]
theorem positiveExtremeRowEquiv_inl (n : ℕ) (L : Fin (n + 1) → F) :
    positiveExtremeRowEquiv (F := F) n (Sum.inl L) =
      positiveExtremeRow (F := F) n L := by
  simp [positiveExtremeRowEquiv]

@[simp]
theorem positiveExtremeRowEquiv_inr (n : ℕ)
    (a : PositiveExtremeRowPad (F := F) n) :
    positiveExtremeRowEquiv (F := F) n (Sum.inr a) = a := by
  simp [positiveExtremeRowEquiv]

@[simp]
theorem positiveExtremeColumnEquiv_inl (n : ℕ) (x : Fin n → F) :
    positiveExtremeColumnEquiv (F := F) n (Sum.inl x) =
      positiveExtremeColumn (F := F) n x := by
  simp [positiveExtremeColumnEquiv]

@[simp]
theorem positiveExtremeColumnEquiv_inr (n : ℕ)
    (b : PositiveExtremeColumnPad (F := F) n) :
    positiveExtremeColumnEquiv (F := F) n (Sum.inr b) = b := by
  simp [positiveExtremeColumnEquiv]

/-- After splitting off the inactive basis vectors, the concrete positive
extreme block is exactly the response-grid matrix with zero padding. -/
theorem reindex_pulledSourceSectorBlock_positiveExtreme
    (psi : AddChar F ℂ) (n : ℕ) :
    Matrix.reindex (positiveExtremeRowEquiv (F := F) n).symm
        (positiveExtremeColumnEquiv (F := F) n).symm
        (pulledSourceSectorBlock F psi n n (n + 1)) =
      zeroPad
        (mPad := PositiveExtremeRowPad (F := F) n)
        (nPad := PositiveExtremeColumnPad (F := F) n)
        (positiveFullGridCoeff psi (positiveUnitEpsilon (F := F) n) n) := by
  classical
  ext i j
  rcases i with L | a <;> rcases j with x | b
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, positiveExtremeRowEquiv_inl,
      positiveExtremeColumnEquiv_inl]
    exact pulledSourceSectorBlock_positiveExtreme_apply psi n L x
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, positiveExtremeRowEquiv_inl,
      positiveExtremeColumnEquiv_inr, zeroPad, Matrix.fromBlocks_apply₁₂]
    apply pulledSourceSectorBlock_positiveExtreme_eq_zero_of_not_support
    intro hs
    obtain ⟨_, ⟨x', hx'⟩⟩ :=
      (positiveExtreme_sourceSector_iff_ranges (F := F) n _ _).mp hs
    exact b.2 ⟨x', hx'⟩
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, positiveExtremeRowEquiv_inr,
      positiveExtremeColumnEquiv_inl, zeroPad, Matrix.fromBlocks_apply₂₁]
    apply pulledSourceSectorBlock_positiveExtreme_eq_zero_of_not_support
    intro hs
    obtain ⟨⟨L', hL'⟩, _⟩ :=
      (positiveExtreme_sourceSector_iff_ranges (F := F) n _ _).mp hs
    exact a.2 ⟨L', hL'⟩
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, positiveExtremeRowEquiv_inr,
      positiveExtremeColumnEquiv_inr, zeroPad, Matrix.fromBlocks_apply₂₂]
    apply pulledSourceSectorBlock_positiveExtreme_eq_zero_of_not_support
    intro hs
    obtain ⟨⟨L', hL'⟩, _⟩ :=
      (positiveExtreme_sourceSector_iff_ranges (F := F) n _ _).mp hs
    exact a.2 ⟨L', hL'⟩

/-- The literal positive extreme count block has entropy `n * log q`. -/
theorem pulledSourceSectorBlock_positiveExtreme_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (n : ℕ)
    (hodd : ringChar F ≠ 2) :
    vonNeumannEntropy (pulledSourceSectorBlock F psi n n (n + 1)) =
      (n : ℝ) * Real.log (Fintype.card F) := by
  rw [← vonNeumannEntropy_reindex_equiv
      (positiveExtremeRowEquiv (F := F) n).symm
      (positiveExtremeColumnEquiv (F := F) n).symm,
    reindex_pulledSourceSectorBlock_positiveExtreme,
    vonNeumannEntropy_zeroPad]
  exact positiveFullGridCoeff_vonNeumannEntropy psi hpsi
    (positiveUnitEpsilon (F := F) n) n hodd
    (positiveUnitEpsilon_col_one' (F := F) n)

end SqrtOpEnt
