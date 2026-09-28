import RequestProject.FibreReduction
import RequestProject.ConcreteEntropyAssembly

/-!
# Entropy of visible-word fibres

This file completes the linear-algebra part of the word-fibre reduction.
The first result packages the recurring operation: split off the range of
injective row and column parametrizations, identify the complement with zero
padding, and remove one-sided additive-character phases by diagonal
unitaries.
-/

namespace SqrtOpEnt

open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section PhaseEmbedding

variable {R C R₀ C₀ : Type*}
  [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]
  [Fintype R₀] [DecidableEq R₀] [Fintype C₀] [DecidableEq C₀]

abbrev EmbeddingRowPad (f : R₀ → R) :=
  {r : R // r ∉ Set.range f}

abbrev EmbeddingColumnPad (g : C₀ → C) :=
  {c : C // c ∉ Set.range g}

noncomputable def embeddingRowEquiv (f : R₀ → R)
    (hf : Function.Injective f) :
    (R₀ ⊕ EmbeddingRowPad f) ≃ R :=
  (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun r => r ∈ Set.range f))

noncomputable def embeddingColumnEquiv (g : C₀ → C)
    (hg : Function.Injective g) :
    (C₀ ⊕ EmbeddingColumnPad g) ≃ C :=
  (Equiv.sumCongr (Equiv.ofInjective g hg) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun c => c ∈ Set.range g))

@[simp] theorem embeddingRowEquiv_inl (f : R₀ → R)
    (hf : Function.Injective f) (r : R₀) :
    embeddingRowEquiv f hf (Sum.inl r) = f r := by
  simp [embeddingRowEquiv]

@[simp] theorem embeddingRowEquiv_inr (f : R₀ → R)
    (hf : Function.Injective f) (r : EmbeddingRowPad f) :
    embeddingRowEquiv f hf (Sum.inr r) = r := by
  simp [embeddingRowEquiv]

@[simp] theorem embeddingColumnEquiv_inl (g : C₀ → C)
    (hg : Function.Injective g) (c : C₀) :
    embeddingColumnEquiv g hg (Sum.inl c) = g c := by
  simp [embeddingColumnEquiv]

@[simp] theorem embeddingColumnEquiv_inr (g : C₀ → C)
    (hg : Function.Injective g) (c : EmbeddingColumnPad g) :
    embeddingColumnEquiv g hg (Sum.inr c) = c := by
  simp [embeddingColumnEquiv]

noncomputable def characterPhasedMatrix (psi : AddChar F ℂ)
    (rowPhase : R₀ → F) (columnPhase : C₀ → F)
    (N : Matrix R₀ C₀ ℂ) : Matrix R₀ C₀ ℂ :=
  fun r c => psi (rowPhase r) * N r c * psi (columnPhase c)

theorem characterPhasedMatrix_eq_mul (psi : AddChar F ℂ)
    (rowPhase : R₀ → F) (columnPhase : C₀ → F)
    (N : Matrix R₀ C₀ ℂ) :
    characterPhasedMatrix psi rowPhase columnPhase N =
      characterDiagonal psi rowPhase * N *
        characterDiagonal psi columnPhase := by
  classical
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · rw [Matrix.mul_apply, Finset.sum_eq_single r]
    · simp [characterPhasedMatrix, characterDiagonal]
    · intro z hz hzr
      simp [characterDiagonal, Ne.symm hzr]
    · simp
  · intro z hz hzc
    simp [characterDiagonal, hzc]
  · simp

theorem characterPhasedMatrix_vonNeumannEntropy (psi : AddChar F ℂ)
    (rowPhase : R₀ → F) (columnPhase : C₀ → F)
    (N : Matrix R₀ C₀ ℂ) :
    vonNeumannEntropy (characterPhasedMatrix psi rowPhase columnPhase N) =
      vonNeumannEntropy N := by
  rw [characterPhasedMatrix_eq_mul]
  rw [vonNeumannEntropy_mul_unitary _ _
      (characterDiagonal_mem_unitary psi columnPhase),
    vonNeumannEntropy_unitary_mul _ _
      (characterDiagonal_mem_unitary psi rowPhase)]

/-- An injectively embedded matrix with only row and column character phases
has exactly the entropy of its active core. -/
theorem vonNeumannEntropy_eq_of_supported_character_embedding
    (psi : AddChar F ℂ) (f : R₀ → R) (g : C₀ → C)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (M : Matrix R C ℂ) (N : Matrix R₀ C₀ ℂ)
    (rowPhase : R₀ → F) (columnPhase : C₀ → F)
    (hactive : ∀ r c, M (f r) (g c) =
      psi (rowPhase r) * N r c * psi (columnPhase c))
    (hsupport : ∀ r c, M r c ≠ 0 →
      r ∈ Set.range f ∧ c ∈ Set.range g) :
    vonNeumannEntropy M = vonNeumannEntropy N := by
  classical
  let er := embeddingRowEquiv f hf
  let ec := embeddingColumnEquiv g hg
  have hreindex : Matrix.reindex er.symm ec.symm M =
      zeroPad
        (mPad := EmbeddingRowPad f)
        (nPad := EmbeddingColumnPad g)
        (characterPhasedMatrix psi rowPhase columnPhase N) := by
    ext r c
    rcases r with r | r <;> rcases c with c | c
    · simpa [er, ec, characterPhasedMatrix] using hactive r c
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, er, ec, embeddingRowEquiv_inl,
        embeddingColumnEquiv_inr, zeroPad, Matrix.fromBlocks_apply₁₂]
      by_contra hne
      exact c.2 (hsupport _ _ hne).2
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, er, ec, embeddingRowEquiv_inr,
        embeddingColumnEquiv_inl, zeroPad, Matrix.fromBlocks_apply₂₁]
      by_contra hne
      exact r.2 (hsupport _ _ hne).1
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, er, ec, embeddingRowEquiv_inr,
        embeddingColumnEquiv_inr, zeroPad, Matrix.fromBlocks_apply₂₂]
      by_contra hne
      exact r.2 (hsupport _ _ hne).1
  calc
    vonNeumannEntropy M =
        vonNeumannEntropy (Matrix.reindex er.symm ec.symm M) := by
      symm
      exact vonNeumannEntropy_reindex_equiv er.symm ec.symm M
    _ = vonNeumannEntropy
          (characterPhasedMatrix psi rowPhase columnPhase N) := by
      rw [hreindex, vonNeumannEntropy_zeroPad]
    _ = vonNeumannEntropy N :=
      characterPhasedMatrix_vonNeumannEntropy psi rowPhase columnPhase N

end PhaseEmbedding

/-! ## Spectator labels after the input rearrangement -/

/-- Prefix spectator read after applying the chosen left input
rearrangement.  Reading only the ket leg is enough: source support will force
the bra spectator to agree with it. -/
def preSpectatorLabel (m s : ℕ) (inputWord : List ℕ)
    (r : PacketBasis F (m + s + 1) × PacketBasis F (m + s + 1)) :
    PacketBasis F m :=
  packetPrePart m s
    (spatialCircuitPerm F (m + s + 1) inputWord r.1)

/-- Suffix spectator read after applying the right input rearrangement. -/
def postSpectatorLabel (m s : ℕ) (inputWord : List ℕ)
    (c : PacketBasis F (m + s + 1) × PacketBasis F (m + s + 1)) :
    PacketBasis F m :=
  packetPostPart m s
    (spatialCircuitPerm F (m + s + 1) inputWord c.1)

theorem positiveTransportedRow_injective (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b)) :
    Function.Injective
      (positiveTransportedRow (F := F) a b s rowWord pre) := by
  intro L L' h
  apply positivePaddedRow_injective (F := F) (a + b) s pre
  let w := colourRearrangementWord (F := F) rowWord
    (positiveMiddleLeftWord a b s)
  have h' := congrArg
    (fun z =>
      (spatialCircuitPerm F (a + b + s + 1) w z.1,
        spatialCircuitPerm F (a + b + s + 1) w z.2)) h
  simpa [positiveTransportedRow, w, spatialCircuitPerm_reverse_right] using h'

theorem positiveTransportedColumn_injective (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b)) :
    Function.Injective
      (positiveTransportedColumn (F := F) a b s colWord post) := by
  intro x y h
  apply positivePaddedColumn_injective (F := F) (a + b) s post
  let w := colourRearrangementWord (F := F) colWord
    (positiveMiddleRightWord a b s)
  have h' := congrArg
    (fun z =>
      (spatialCircuitPerm F (a + b + s + 1) w z.1,
        spatialCircuitPerm F (a + b + s + 1) w z.2)) h
  simpa [positiveTransportedColumn, w,
    spatialCircuitPerm_reverse_right] using h'

theorem negativeTransportedRow_injective (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b)) :
    Function.Injective
      (negativeTransportedRow (F := F) a b s rowWord pre) := by
  intro p q h
  apply negativePaddedRow_injective (F := F) (a + b) s pre
  let w := colourRearrangementWord (F := F) rowWord
    (negativeMiddleLeftWord a b s)
  have h' := congrArg
    (fun z =>
      (spatialCircuitPerm F (a + b + s + 1) w z.1,
        spatialCircuitPerm F (a + b + s + 1) w z.2)) h
  simpa [negativeTransportedRow, w,
    spatialCircuitPerm_reverse_right] using h'

theorem negativeTransportedColumn_injective (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b)) :
    Function.Injective
      (negativeTransportedColumn (F := F) a b s colWord post) := by
  intro x y h
  apply negativePaddedColumn_injective (F := F) (a + b) s post
  let w := colourRearrangementWord (F := F) colWord
    (negativeMiddleRightWord a b s)
  have h' := congrArg
    (fun z =>
      (spatialCircuitPerm F (a + b + s + 1) w z.1,
        spatialCircuitPerm F (a + b + s + 1) w z.2)) h
  simpa [negativeTransportedColumn, w,
    spatialCircuitPerm_reverse_right] using h'

@[simp] theorem preSpectatorLabel_positiveTransportedRow (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b))
    (L : Fin (s + 1) → F) :
    preSpectatorLabel (F := F) (a + b) s
        (colourRearrangementWord (F := F) rowWord
          (positiveMiddleLeftWord a b s))
        (positiveTransportedRow (F := F) a b s rowWord pre L) = pre := by
  simp [preSpectatorLabel, positiveTransportedRow,
    spatialCircuitPerm_reverse_right, positivePaddedRow]

@[simp] theorem postSpectatorLabel_positiveTransportedColumn (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b))
    (x : Fin s → F) :
    postSpectatorLabel (F := F) (a + b) s
        (colourRearrangementWord (F := F) colWord
          (positiveMiddleRightWord a b s))
        (positiveTransportedColumn (F := F) a b s colWord post x) = post := by
  simp [postSpectatorLabel, positiveTransportedColumn,
    spatialCircuitPerm_reverse_right, positivePaddedColumn]

@[simp] theorem preSpectatorLabel_negativeTransportedRow (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b))
    (p : F × (Fin s → F)) :
    preSpectatorLabel (F := F) (a + b) s
        (colourRearrangementWord (F := F) rowWord
          (negativeMiddleLeftWord a b s))
        (negativeTransportedRow (F := F) a b s rowWord pre p) = pre := by
  simp [preSpectatorLabel, negativeTransportedRow,
    spatialCircuitPerm_reverse_right, negativePaddedRow]

@[simp] theorem postSpectatorLabel_negativeTransportedColumn (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b))
    (x : Fin s → F) :
    postSpectatorLabel (F := F) (a + b) s
        (colourRearrangementWord (F := F) colWord
          (negativeMiddleRightWord a b s))
        (negativeTransportedColumn (F := F) a b s colWord post x) = post := by
  simp [postSpectatorLabel, negativeTransportedColumn,
    spatialCircuitPerm_reverse_right, negativePaddedColumn]

/-! ## Consequences of nonzero source support -/

/-- Source support forces the ket and bra coefficient indices to carry the
same two visible input words. -/
theorem coefficient_visibleWords_eq_of_source (n : ℕ)
    (r c : PacketBasis F (n + 1) × PacketBasis F (n + 1))
    (hs : rectangularSource F (succPNat n)
      (coreSourcePairEquiv F n (r, c)).1
      (coreSourcePairEquiv F n (r, c)).2 ≠ 0) :
    visibleWordList (F := F) (List.ofFn r.1) =
        visibleWordList (F := F) (List.ofFn r.2) ∧
      visibleWordList (F := F) (List.ofFn c.1) =
        visibleWordList (F := F) (List.ofFn c.2) := by
  let u : RectBasis F (n + 1) := (r.1, c.1)
  let v : RectBasis F (n + 1) := (r.2, c.2)
  have hs' : rectangularSource F (succPNat n)
      (rectangularCircuitPerm F (n + 1) u)
      (rectangularCircuitPerm F (n + 1) v) ≠ 0 := by
    simpa [u, v, coreSourcePairEquiv, coeffOperatorPairEquiv] using hs
  have hsource := (rectangularSource_ne_zero_iff F (succPNat n) _ _).mp hs'
  constructor
  · rw [visibleWordList_ofFn, visibleWordList_ofFn]
    congr 1
    funext i
    have hcol := source_right_colours_eq F n
      (rectangularCircuitPerm F (n + 1) u)
      (rectangularCircuitPerm F (n + 1) v) hs' i
    rw [siteColour_rectangularCircuitPerm_snd,
      siteColour_rectangularCircuitPerm_snd] at hcol
    exact hcol
  · rw [visibleWordList_ofFn, visibleWordList_ofFn]
    congr 1
    funext i
    have hleft := congrFun hsource.1 i
    have hu := siteColour_rectangularCircuitPerm_fst F (n + 1) u i
    have hv := siteColour_rectangularCircuitPerm_fst F (n + 1) v i
    rw [hleft] at hu
    exact hu.symm.trans hv

theorem packetACount_eq_visibleWordList_count (n : ℕ)
    (u : PacketBasis F n) :
    packetACount F u =
      (visibleWordList (F := F) (List.ofFn u)).count .A := by
  induction n with
  | zero => simp [packetACount, visibleWordList]
  | succ n ih =>
    unfold packetACount
    rw [Fin.card_filter_univ_succ]
    rw [visibleWordList, List.ofFn_succ, List.map_cons]
    simp only [List.count_cons]
    have ht := ih (fun i : Fin n => u i.succ)
    rw [visibleWordList] at ht
    unfold packetACount at ht
    rw [ht]
    by_cases h : siteColour F (u 0) = .A <;> simp [h]

theorem packetBCount_eq_visibleWordList_count (n : ℕ)
    (u : PacketBasis F n) :
    packetBCount F u =
      (visibleWordList (F := F) (List.ofFn u)).count .B := by
  induction n with
  | zero => simp [packetBCount, visibleWordList]
  | succ n ih =>
    unfold packetBCount
    rw [Fin.card_filter_univ_succ]
    rw [visibleWordList, List.ofFn_succ, List.map_cons]
    simp only [List.count_cons]
    have ht := ih (fun i : Fin n => u i.succ)
    rw [visibleWordList] at ht
    unfold packetBCount at ht
    rw [ht]
    by_cases h : siteColour F (u 0) = .B <;> simp [h]

theorem visibleWordList_preCore_parts (m s : ℕ)
    (u : PacketBasis F (m + s + 1)) :
    visibleWordList (F := F) (List.ofFn u) =
      visibleWordList (F := F) (List.ofFn (packetPrePart m s u)) ++
        visibleWordList (F := F)
          (List.ofFn (packetPreCorePart m s u)) := by
  conv_lhs => rw [← packetPreCore_parts (F := F) m s u]
  rw [ofFn_packetPreCore, visibleWordList_append]

theorem visibleWordList_postCore_parts (m s : ℕ)
    (u : PacketBasis F (m + s + 1)) :
    visibleWordList (F := F) (List.ofFn u) =
      visibleWordList (F := F)
          (List.ofFn (packetPostCorePart m s u)) ++
        visibleWordList (F := F) (List.ofFn (packetPostPart m s u)) := by
  conv_lhs => rw [← packetPostCore_parts (F := F) m s u]
  rw [ofFn_packetPostCore, visibleWordList_append]

/-! ## Classification of an embedded residual support -/

theorem positive_embedded_source_ranges (a b s : ℕ)
    (pre post : PacketBasis F (a + b))
    (u v : RectBasis F (a + b + s + 1))
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) =
      normalColourWord a b ++ List.replicate (s + 1) .B)
    (hvLeft : visibleWordList (F := F) (List.ofFn v.1) =
      normalColourWord a b ++ List.replicate (s + 1) .B)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) =
      List.replicate (s + 1) .A ++ normalColourWord a b)
    (hvRight : visibleWordList (F := F) (List.ofFn v.2) =
      List.replicate (s + 1) .A ++ normalColourWord a b)
    (huPre : packetPrePart (F := F) (a + b) s u.1 = pre)
    (huPost : packetPostPart (F := F) (a + b) s u.2 = post)
    (hsource : rectangularSource F (succPNat (a + b + s))
      (embeddedRectangularCircuitPerm (F := F) (a + b) s u)
      (embeddedRectangularCircuitPerm (F := F) (a + b) s v) ≠ 0) :
    (∃ L, positivePaddedRow (F := F) (a + b) s pre L = (u.1, v.1)) ∧
      ∃ x, positivePaddedColumn (F := F) (a + b) s post x = (u.2, v.2) := by
  let m := a + b
  let uL := packetPreCorePart (F := F) m s u.1
  let uR := packetPostCorePart (F := F) m s u.2
  let vL := packetPreCorePart (F := F) m s v.1
  let vR := packetPostCorePart (F := F) m s v.2
  let preV := packetPrePart (F := F) m s v.1
  let postV := packetPostPart (F := F) m s v.2
  have huPre' : packetPrePart (F := F) m s u.1 = pre := by
    simpa [m] using huPre
  have huPost' : packetPostPart (F := F) m s u.2 = post := by
    simpa [m] using huPost
  have huDecomp :
      (packetPreCore m s pre uL, packetPostCore m s uR post) = u := by
    apply Prod.ext
    · rw [← huPre']
      exact packetPreCore_parts (F := F) m s u.1
    · rw [← huPost']
      exact packetPostCore_parts (F := F) m s u.2
  have hvDecomp :
      (packetPreCore m s preV vL, packetPostCore m s vR postV) = v := by
    apply Prod.ext
    · exact packetPreCore_parts (F := F) m s v.1
    · exact packetPostCore_parts (F := F) m s v.2
  have heu : embeddedRectangularCircuitPerm (F := F) m s u =
      (packetPreCore m s pre
          (rectangularCircuitPerm F (s + 1) (uL, uR)).1,
        packetPostCore m s
          (rectangularCircuitPerm F (s + 1) (uL, uR)).2 post) := by
    rw [← huDecomp]
    exact embeddedRectangularCircuitPerm_apply (F := F) m s _ _ _ _
  have hev : embeddedRectangularCircuitPerm (F := F) m s v =
      (packetPreCore m s preV
          (rectangularCircuitPerm F (s + 1) (vL, vR)).1,
        packetPostCore m s
          (rectangularCircuitPerm F (s + 1) (vL, vR)).2 postV) := by
    rw [← hvDecomp]
    exact embeddedRectangularCircuitPerm_apply (F := F) m s _ _ _ _
  rw [heu, hev] at hsource
  obtain ⟨hpreV, hpostV, hcore⟩ :=
    (rectangularSource_ne_zero_pad_iff (F := F) m s pre preV post postV
      (rectangularCircuitPerm F (s + 1) (uL, uR))
      (rectangularCircuitPerm F (s + 1) (vL, vR))).mp hsource
  dsimp [preV] at hpreV
  dsimp [postV] at hpostV
  have huLword : visibleWordList (F := F) (List.ofFn uL) =
      List.replicate (s + 1) .B := by
    have hparts := visibleWordList_preCore_parts (F := F) m s u.1
    rw [huPre', hpre, huLeft] at hparts
    exact List.append_right_injective (normalColourWord a b) (by
      simpa [uL] using hparts.symm)
  have hvLword : visibleWordList (F := F) (List.ofFn vL) =
      List.replicate (s + 1) .B := by
    have hparts := visibleWordList_preCore_parts (F := F) m s v.1
    rw [← hpreV, hpre, hvLeft] at hparts
    exact List.append_right_injective (normalColourWord a b) (by
      simpa [vL] using hparts.symm)
  have huRword : visibleWordList (F := F) (List.ofFn uR) =
      List.replicate (s + 1) .A := by
    have hparts := visibleWordList_postCore_parts (F := F) m s u.2
    rw [huPost', hpost, huRight] at hparts
    exact List.append_left_injective (normalColourWord a b) (by
      simpa [uR] using hparts.symm)
  have hvRword : visibleWordList (F := F) (List.ofFn vR) =
      List.replicate (s + 1) .A := by
    have hparts := visibleWordList_postCore_parts (F := F) m s v.2
    rw [← hpostV, hpost, hvRight] at hparts
    exact List.append_left_injective (normalColourWord a b) (by
      simpa [vR] using hparts.symm)
  have hsector : SourceSectorPredicate F s s (s + 1)
      (coreSourcePairEquiv F s ((uL, vL), (uR, vR))) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [coreSourcePairEquiv, coeffOperatorPairEquiv] using hcore
    · change packetBCount F
        (fun i => (rectangularCircuitPerm F (s + 1) (uL, uR)).2 i.succ) = s
      rw [packetBCount_eq_visibleWordList_count]
      rw [visibleWordList_ofFn_succ,
        visibleWordList_rectangularCircuitPerm_snd, huLword]
      simp [List.replicate_succ]
    · change packetACount F
        (rectangularCircuitPerm F (s + 1) (uL, uR)).1 = s + 1
      rw [packetACount_eq_visibleWordList_count,
        visibleWordList_rectangularCircuitPerm_fst, huRword]
      simp [List.count_replicate,
        show VisibleColour.B ≠ VisibleColour.A by decide]
  obtain ⟨⟨L, hL⟩, x, hx⟩ :=
    (positiveExtreme_sourceSector_iff_ranges (F := F) s _ _).mp hsector
  constructor
  · refine ⟨L, ?_⟩
    apply Prod.ext
    · rw [positivePaddedRow]
      change packetPreCore m s pre (positiveExtremeRow (F := F) s L).1 = u.1
      rw [hL]
      rw [← huPre']
      exact packetPreCore_parts (F := F) m s u.1
    · rw [positivePaddedRow]
      change packetPreCore m s pre (positiveExtremeRow (F := F) s L).2 = v.1
      rw [hL, hpreV]
      simpa [vL] using packetPreCore_parts (F := F) m s v.1
  · refine ⟨x, ?_⟩
    apply Prod.ext
    · rw [positivePaddedColumn]
      change packetPostCore m s (positiveExtremeColumn (F := F) s x).1 post = u.2
      rw [hx]
      rw [← huPost']
      exact packetPostCore_parts (F := F) m s u.2
    · rw [positivePaddedColumn]
      change packetPostCore m s (positiveExtremeColumn (F := F) s x).2 post = v.2
      rw [hx, hpostV]
      simpa [vR] using packetPostCore_parts (F := F) m s v.2

theorem negative_embedded_source_ranges (a b s : ℕ)
    (pre post : PacketBasis F (a + b))
    (u v : RectBasis F (a + b + s + 1))
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) =
      negativeMiddleLeftWord a b s)
    (hvLeft : visibleWordList (F := F) (List.ofFn v.1) =
      negativeMiddleLeftWord a b s)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) =
      negativeMiddleRightWord a b s)
    (hvRight : visibleWordList (F := F) (List.ofFn v.2) =
      negativeMiddleRightWord a b s)
    (huPre : packetPrePart (F := F) (a + b) s u.1 = pre)
    (huPost : packetPostPart (F := F) (a + b) s u.2 = post)
    (hsource : rectangularSource F (succPNat (a + b + s))
      (embeddedRectangularCircuitPerm (F := F) (a + b) s u)
      (embeddedRectangularCircuitPerm (F := F) (a + b) s v) ≠ 0) :
    (∃ p, negativePaddedRow (F := F) (a + b) s pre p = (u.1, v.1)) ∧
      ∃ x, negativePaddedColumn (F := F) (a + b) s post x = (u.2, v.2) := by
  let m := a + b
  let uL := packetPreCorePart (F := F) m s u.1
  let uR := packetPostCorePart (F := F) m s u.2
  let vL := packetPreCorePart (F := F) m s v.1
  let vR := packetPostCorePart (F := F) m s v.2
  let preV := packetPrePart (F := F) m s v.1
  let postV := packetPostPart (F := F) m s v.2
  have huPre' : packetPrePart (F := F) m s u.1 = pre := by
    simpa [m] using huPre
  have huPost' : packetPostPart (F := F) m s u.2 = post := by
    simpa [m] using huPost
  have huDecomp :
      (packetPreCore m s pre uL, packetPostCore m s uR post) = u := by
    apply Prod.ext
    · rw [← huPre']
      exact packetPreCore_parts (F := F) m s u.1
    · rw [← huPost']
      exact packetPostCore_parts (F := F) m s u.2
  have hvDecomp :
      (packetPreCore m s preV vL, packetPostCore m s vR postV) = v := by
    apply Prod.ext
    · exact packetPreCore_parts (F := F) m s v.1
    · exact packetPostCore_parts (F := F) m s v.2
  have heu : embeddedRectangularCircuitPerm (F := F) m s u =
      (packetPreCore m s pre
          (rectangularCircuitPerm F (s + 1) (uL, uR)).1,
        packetPostCore m s
          (rectangularCircuitPerm F (s + 1) (uL, uR)).2 post) := by
    rw [← huDecomp]
    exact embeddedRectangularCircuitPerm_apply (F := F) m s _ _ _ _
  have hev : embeddedRectangularCircuitPerm (F := F) m s v =
      (packetPreCore m s preV
          (rectangularCircuitPerm F (s + 1) (vL, vR)).1,
        packetPostCore m s
          (rectangularCircuitPerm F (s + 1) (vL, vR)).2 postV) := by
    rw [← hvDecomp]
    exact embeddedRectangularCircuitPerm_apply (F := F) m s _ _ _ _
  rw [heu, hev] at hsource
  obtain ⟨hpreV, hpostV, hcore⟩ :=
    (rectangularSource_ne_zero_pad_iff (F := F) m s pre preV post postV
      (rectangularCircuitPerm F (s + 1) (uL, uR))
      (rectangularCircuitPerm F (s + 1) (vL, vR))).mp hsource
  dsimp [preV] at hpreV
  dsimp [postV] at hpostV
  have huLword : visibleWordList (F := F) (List.ofFn uL) =
      .B :: List.replicate s .A := by
    have hparts := visibleWordList_preCore_parts (F := F) m s u.1
    rw [huPre', hpre, huLeft] at hparts
    exact List.append_right_injective (normalColourWord a b) (by
      simpa [uL, negativeMiddleLeftWord] using hparts.symm)
  have hvLword : visibleWordList (F := F) (List.ofFn vL) =
      .B :: List.replicate s .A := by
    have hparts := visibleWordList_preCore_parts (F := F) m s v.1
    rw [← hpreV, hpre, hvLeft] at hparts
    exact List.append_right_injective (normalColourWord a b) (by
      simpa [vL, negativeMiddleLeftWord] using hparts.symm)
  have huRword : visibleWordList (F := F) (List.ofFn uR) =
      List.replicate (s + 1) .B := by
    have hparts := visibleWordList_postCore_parts (F := F) m s u.2
    rw [huPost', hpost, huRight] at hparts
    exact List.append_left_injective (normalColourWord a b) (by
      simpa [uR, negativeMiddleRightWord] using hparts.symm)
  have hvRword : visibleWordList (F := F) (List.ofFn vR) =
      List.replicate (s + 1) .B := by
    have hparts := visibleWordList_postCore_parts (F := F) m s v.2
    rw [← hpostV, hpost, hvRight] at hparts
    exact List.append_left_injective (normalColourWord a b) (by
      simpa [vR, negativeMiddleRightWord] using hparts.symm)
  have hsector : SourceSectorPredicate F s 0 0
      (coreSourcePairEquiv F s ((uL, vL), (uR, vR))) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [coreSourcePairEquiv, coeffOperatorPairEquiv] using hcore
    · change packetBCount F
        (fun i => (rectangularCircuitPerm F (s + 1) (uL, uR)).2 i.succ) = 0
      rw [packetBCount_eq_visibleWordList_count]
      rw [visibleWordList_ofFn_succ,
        visibleWordList_rectangularCircuitPerm_snd, huLword]
      simp [List.count_replicate,
        show VisibleColour.A ≠ VisibleColour.B by decide]
    · change packetACount F
        (rectangularCircuitPerm F (s + 1) (uL, uR)).1 = 0
      rw [packetACount_eq_visibleWordList_count,
        visibleWordList_rectangularCircuitPerm_fst, huRword]
      simp [List.count_replicate,
        show VisibleColour.A ≠ VisibleColour.B by decide]
  obtain ⟨⟨p, hp⟩, x, hx⟩ :=
    (negativeExtreme_sourceSector_iff_ranges (F := F) s _ _).mp hsector
  constructor
  · refine ⟨p, ?_⟩
    apply Prod.ext
    · rw [negativePaddedRow]
      change packetPreCore m s pre (negativeExtremeRow (F := F) s p).1 = u.1
      rw [hp, ← huPre']
      exact packetPreCore_parts (F := F) m s u.1
    · rw [negativePaddedRow]
      change packetPreCore m s pre (negativeExtremeRow (F := F) s p).2 = v.1
      rw [hp, hpreV]
      simpa [vL] using packetPreCore_parts (F := F) m s v.1
  · refine ⟨x, ?_⟩
    apply Prod.ext
    · rw [negativePaddedColumn]
      change packetPostCore m s (negativeExtremeColumn (F := F) s x).1 post = u.2
      rw [hx, ← huPost']
      exact packetPostCore_parts (F := F) m s u.2
    · rw [negativePaddedColumn]
      change packetPostCore m s (negativeExtremeColumn (F := F) s x).2 post = v.2
      rw [hx, hpostV]
      simpa [vR] using packetPostCore_parts (F := F) m s v.2

/-! ## Transport back to an arbitrary visible word -/

theorem positive_source_ranges_of_words (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (pre post : PacketBasis F (a + b))
    (r c : PacketBasis F (a + b + s + 1) ×
      PacketBasis F (a + b + s + 1))
    (hpreWord : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpostWord : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowBra : visibleWordList (F := F) (List.ofFn r.2) = rowWord)
    (hcolBra : visibleWordList (F := F) (List.ofFn c.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a + s + 1)
    (hpreLabel : preSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (positiveMiddleLeftWord a b s)) r = pre)
    (hpostLabel : postSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) colWord
        (positiveMiddleRightWord a b s)) c = post)
    (hsource : rectangularSource F (succPNat (a + b + s))
      (coreSourcePairEquiv F (a + b + s) (r, c)).1
      (coreSourcePairEquiv F (a + b + s) (r, c)).2 ≠ 0) :
    (∃ L, positiveTransportedRow (F := F) a b s rowWord pre L = r) ∧
      ∃ x, positiveTransportedColumn (F := F) a b s colWord post x = c := by
  let n := a + b + s
  let wL := colourRearrangementWord (F := F) rowWord
    (positiveMiddleLeftWord a b s)
  let wR := colourRearrangementWord (F := F) colWord
    (positiveMiddleRightWord a b s)
  let outL := colourRearrangementWord (F := F)
    (positiveSourceLeftWord a b s) colWord
  let outR := colourRearrangementWord (F := F)
    (positiveSourceRightTailWord a b s) rowWord.tail
  let u : RectBasis F (n + 1) := (r.1, c.1)
  let v : RectBasis F (n + 1) := (r.2, c.2)
  let midU := boundaryLocalPerm (F := F) n wL wR u
  let midV := boundaryLocalPerm (F := F) n wL wR v
  have hs : rectangularSource F (succPNat n)
      (rectangularCircuitPerm F (n + 1) u)
      (rectangularCircuitPerm F (n + 1) v) ≠ 0 := by
    simpa [n, u, v, coreSourcePairEquiv, coeffOperatorPairEquiv] using hsource
  have hwords := coefficient_visibleWords_eq_of_source (F := F) n r c (by
    simpa [n] using hsource)
  have hrowKet : visibleWordList (F := F) (List.ofFn r.1) = rowWord :=
    hwords.1.trans hrowBra
  have hcolKet : visibleWordList (F := F) (List.ofFn c.1) = colWord :=
    hwords.2.trans hcolBra
  have hrowTargetLen : rowWord.length =
      (positiveMiddleLeftWord a b s).length := by
    simp [positiveMiddleLeftWord, hrowLen]
    omega
  have hrowTargetA : rowWord.count .A =
      (positiveMiddleLeftWord a b s).count .A := by
    simp [positiveMiddleLeftWord, List.count_replicate, hrowA]
  have hcolTargetLen : colWord.length =
      (positiveMiddleRightWord a b s).length := by
    simp [positiveMiddleRightWord, hcolLen]
    omega
  have hcolTargetA : colWord.count .A =
      (positiveMiddleRightWord a b s).count .A := by
    simp [positiveMiddleRightWord, List.count_replicate, hcolA]
    omega
  have hmidUL : visibleWordList (F := F) (List.ofFn midU.1) =
      positiveMiddleLeftWord a b s := by
    dsimp [midU, boundaryLocalPerm]
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord rowWord _ _ hrowKet
      hrowTargetLen hrowTargetA
  have hmidVL : visibleWordList (F := F) (List.ofFn midV.1) =
      positiveMiddleLeftWord a b s := by
    dsimp [midV, boundaryLocalPerm]
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord rowWord _ _ hrowBra
      hrowTargetLen hrowTargetA
  have hmidUR : visibleWordList (F := F) (List.ofFn midU.2) =
      positiveMiddleRightWord a b s := by
    dsimp [midU, boundaryLocalPerm]
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord colWord _ _ hcolKet
      hcolTargetLen hcolTargetA
  have hmidVR : visibleWordList (F := F) (List.ofFn midV.2) =
      positiveMiddleRightWord a b s := by
    dsimp [midV, boundaryLocalPerm]
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord colWord _ _ hcolBra
      hcolTargetLen hcolTargetA
  have hpermU := rectangularCircuitPerm_eq_positiveReductionOutput
    (F := F) a b s rowWord colWord u (by simpa [u] using hrowKet)
      (by simpa [u] using hcolKet) hrowLen hrowA hrowHead hcolLen hcolA
  have hpermV := rectangularCircuitPerm_eq_positiveReductionOutput
    (F := F) a b s rowWord colWord v (by simpa [v] using hrowBra)
      (by simpa [v] using hcolBra) hrowLen hrowA hrowHead hcolLen hcolA
  have hmidSource : rectangularSource F (succPNat n)
      (embeddedRectangularCircuitPerm (F := F) (a + b) s midU)
      (embeddedRectangularCircuitPerm (F := F) (a + b) s midV) ≠ 0 := by
    rw [hpermU, hpermV] at hs
    exact (sourceLocalFun_source_ne_zero_iff (F := F) n outL outR _ _).mp (by
      simpa [n, midU, midV, paddedReductionOutput, wL, wR, outL, outR] using hs)
  have hpreMid : packetPrePart (F := F) (a + b) s midU.1 = pre := by
    simpa [preSpectatorLabel, midU, u, n, boundaryLocalPerm, wL] using hpreLabel
  have hpostMid : packetPostPart (F := F) (a + b) s midU.2 = post := by
    simpa [postSpectatorLabel, midU, u, n, boundaryLocalPerm, wR] using hpostLabel
  obtain ⟨⟨L, hL⟩, x, hx⟩ := positive_embedded_source_ranges
    (F := F) a b s pre post midU midV hpreWord hpostWord
    (by simpa [positiveMiddleLeftWord] using hmidUL)
    (by simpa [positiveMiddleLeftWord] using hmidVL)
    (by simpa [positiveMiddleRightWord] using hmidUR)
    (by simpa [positiveMiddleRightWord] using hmidVR)
    hpreMid hpostMid (by simpa [n] using hmidSource)
  constructor
  · refine ⟨L, ?_⟩
    apply Prod.ext
    · have h := congrArg Prod.fst hL
      simpa [positiveTransportedRow, midU, boundaryLocalPerm, u, n, wL,
        spatialCircuitPerm_reverse_left] using congrArg
          (spatialCircuitPerm F (n + 1) wL.reverse) h
    · have h := congrArg Prod.snd hL
      simpa [positiveTransportedRow, midV, boundaryLocalPerm, v, n, wL,
        spatialCircuitPerm_reverse_left] using congrArg
          (spatialCircuitPerm F (n + 1) wL.reverse) h
  · refine ⟨x, ?_⟩
    apply Prod.ext
    · have h := congrArg Prod.fst hx
      simpa [positiveTransportedColumn, midU, boundaryLocalPerm, u, n, wR,
        spatialCircuitPerm_reverse_left] using congrArg
          (spatialCircuitPerm F (n + 1) wR.reverse) h
    · have h := congrArg Prod.snd hx
      simpa [positiveTransportedColumn, midV, boundaryLocalPerm, v, n, wR,
        spatialCircuitPerm_reverse_left] using congrArg
          (spatialCircuitPerm F (n + 1) wR.reverse) h

theorem negative_source_ranges_of_words (a b s : ℕ)
    (rowWord colWord : List VisibleColour)
    (pre post : PacketBasis F (a + b))
    (r c : PacketBasis F (a + b + s + 1) ×
      PacketBasis F (a + b + s + 1))
    (hpreWord : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpostWord : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowBra : visibleWordList (F := F) (List.ofFn r.2) = rowWord)
    (hcolBra : visibleWordList (F := F) (List.ofFn c.2) = colWord)
    (hrowLen : rowWord.length = a + b + s + 1)
    (hrowA : rowWord.count .A = a + s)
    (hrowHead : .B ∈ rowWord.head?)
    (hcolLen : colWord.length = a + b + s + 1)
    (hcolA : colWord.count .A = a)
    (hpreLabel : preSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (negativeMiddleLeftWord a b s)) r = pre)
    (hpostLabel : postSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) colWord
        (negativeMiddleRightWord a b s)) c = post)
    (hsource : rectangularSource F (succPNat (a + b + s))
      (coreSourcePairEquiv F (a + b + s) (r, c)).1
      (coreSourcePairEquiv F (a + b + s) (r, c)).2 ≠ 0) :
    (∃ p, negativeTransportedRow (F := F) a b s rowWord pre p = r) ∧
      ∃ x, negativeTransportedColumn (F := F) a b s colWord post x = c := by
  let n := a + b + s
  let wL := colourRearrangementWord (F := F) rowWord
    (negativeMiddleLeftWord a b s)
  let wR := colourRearrangementWord (F := F) colWord
    (negativeMiddleRightWord a b s)
  let outL := colourRearrangementWord (F := F)
    (negativeSourceLeftWord a b s) colWord
  let outR := colourRearrangementWord (F := F)
    (negativeSourceRightTailWord a b s) rowWord.tail
  let u : RectBasis F (n + 1) := (r.1, c.1)
  let v : RectBasis F (n + 1) := (r.2, c.2)
  let midU := boundaryLocalPerm (F := F) n wL wR u
  let midV := boundaryLocalPerm (F := F) n wL wR v
  have hs : rectangularSource F (succPNat n)
      (rectangularCircuitPerm F (n + 1) u)
      (rectangularCircuitPerm F (n + 1) v) ≠ 0 := by
    simpa [n, u, v, coreSourcePairEquiv, coeffOperatorPairEquiv] using hsource
  have hwords := coefficient_visibleWords_eq_of_source (F := F) n r c (by
    simpa [n] using hsource)
  have hrowKet : visibleWordList (F := F) (List.ofFn r.1) = rowWord :=
    hwords.1.trans hrowBra
  have hcolKet : visibleWordList (F := F) (List.ofFn c.1) = colWord :=
    hwords.2.trans hcolBra
  have hrowTargetLen : rowWord.length =
      (negativeMiddleLeftWord a b s).length := by
    simp [negativeMiddleLeftWord, hrowLen]
    omega
  have hrowTargetA : rowWord.count .A =
      (negativeMiddleLeftWord a b s).count .A := by
    simp [negativeMiddleLeftWord, List.count_replicate, hrowA]
  have hcolTargetLen : colWord.length =
      (negativeMiddleRightWord a b s).length := by
    simp [negativeMiddleRightWord, hcolLen]
    omega
  have hcolTargetA : colWord.count .A =
      (negativeMiddleRightWord a b s).count .A := by
    simp [negativeMiddleRightWord, List.count_replicate, hcolA]
  have hmidUL : visibleWordList (F := F) (List.ofFn midU.1) =
      negativeMiddleLeftWord a b s := by
    dsimp [midU, boundaryLocalPerm]
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord rowWord _ _ hrowKet
      hrowTargetLen hrowTargetA
  have hmidVL : visibleWordList (F := F) (List.ofFn midV.1) =
      negativeMiddleLeftWord a b s := by
    dsimp [midV, boundaryLocalPerm]
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord rowWord _ _ hrowBra
      hrowTargetLen hrowTargetA
  have hmidUR : visibleWordList (F := F) (List.ofFn midU.2) =
      negativeMiddleRightWord a b s := by
    dsimp [midU, boundaryLocalPerm]
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord colWord _ _ hcolKet
      hcolTargetLen hcolTargetA
  have hmidVR : visibleWordList (F := F) (List.ofFn midV.2) =
      negativeMiddleRightWord a b s := by
    dsimp [midV, boundaryLocalPerm]
    rw [ofFn_spatialCircuitPerm]
    exact visibleWordList_colourRearrangementWord colWord _ _ hcolBra
      hcolTargetLen hcolTargetA
  have hpermU := rectangularCircuitPerm_eq_negativeReductionOutput
    (F := F) a b s rowWord colWord u (by simpa [u] using hrowKet)
      (by simpa [u] using hcolKet) hrowLen hrowA hrowHead hcolLen hcolA
  have hpermV := rectangularCircuitPerm_eq_negativeReductionOutput
    (F := F) a b s rowWord colWord v (by simpa [v] using hrowBra)
      (by simpa [v] using hcolBra) hrowLen hrowA hrowHead hcolLen hcolA
  have hmidSource : rectangularSource F (succPNat n)
      (embeddedRectangularCircuitPerm (F := F) (a + b) s midU)
      (embeddedRectangularCircuitPerm (F := F) (a + b) s midV) ≠ 0 := by
    rw [hpermU, hpermV] at hs
    exact (sourceLocalFun_source_ne_zero_iff (F := F) n outL outR _ _).mp (by
      simpa [n, midU, midV, paddedReductionOutput, wL, wR, outL, outR] using hs)
  have hpreMid : packetPrePart (F := F) (a + b) s midU.1 = pre := by
    simpa [preSpectatorLabel, midU, u, n, boundaryLocalPerm, wL] using hpreLabel
  have hpostMid : packetPostPart (F := F) (a + b) s midU.2 = post := by
    simpa [postSpectatorLabel, midU, u, n, boundaryLocalPerm, wR] using hpostLabel
  obtain ⟨⟨p, hp⟩, x, hx⟩ := negative_embedded_source_ranges
    (F := F) a b s pre post midU midV hpreWord hpostWord
    hmidUL hmidVL hmidUR hmidVR hpreMid hpostMid
    (by simpa [n] using hmidSource)
  constructor
  · refine ⟨p, ?_⟩
    apply Prod.ext
    · have h := congrArg Prod.fst hp
      simpa [negativeTransportedRow, midU, boundaryLocalPerm, u, n, wL,
        spatialCircuitPerm_reverse_left] using congrArg
          (spatialCircuitPerm F (n + 1) wL.reverse) h
    · have h := congrArg Prod.snd hp
      simpa [negativeTransportedRow, midV, boundaryLocalPerm, v, n, wL,
        spatialCircuitPerm_reverse_left] using congrArg
          (spatialCircuitPerm F (n + 1) wL.reverse) h
  · refine ⟨x, ?_⟩
    apply Prod.ext
    · have h := congrArg Prod.fst hx
      simpa [negativeTransportedColumn, midU, boundaryLocalPerm, u, n, wR,
        spatialCircuitPerm_reverse_left] using congrArg
          (spatialCircuitPerm F (n + 1) wR.reverse) h
    · have h := congrArg Prod.snd hx
      simpa [negativeTransportedColumn, midV, boundaryLocalPerm, v, n, wR,
        spatialCircuitPerm_reverse_left] using congrArg
          (spatialCircuitPerm F (n + 1) wR.reverse) h

theorem tail_count_B_of_head_B (rowWord : List VisibleColour)
    (a rest : ℕ) (hlen : rowWord.length = a + rest + 1)
    (hA : rowWord.count .A = a) (hhead : .B ∈ rowWord.head?) :
    rowWord.tail.count .B = rest := by
  have hcons : .B :: rowWord.tail = rowWord :=
    List.cons_head?_tail hhead
  have htotal := count_A_add_count_B rowWord
  have hcount := congrArg (List.count .B) hcons
  simp at hcount
  omega

theorem positiveTransported_sourceSector (a b s : ℕ)
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
    SourceSectorPredicate F (a + b + s) (b + s) (a + s + 1)
      (coreSourcePairEquiv F (a + b + s)
        (positiveTransportedRow (F := F) a b s rowWord pre L,
          positiveTransportedColumn (F := F) a b s colWord post x)) := by
  let row := positiveTransportedRow (F := F) a b s rowWord pre L
  let col := positiveTransportedColumn (F := F) a b s colWord post x
  have hr := positiveTransportedRow_visibleWord (F := F)
    a b s rowWord pre L hpre (by
      simp [positiveMiddleLeftWord, hrowLen]
      omega) (by
        simp [positiveMiddleLeftWord, hrowA, List.count_replicate,
          show VisibleColour.A ≠ VisibleColour.B by decide])
  have hc := positiveTransportedColumn_visibleWord (F := F)
    a b s colWord post x hpost (by
      simp [positiveMiddleRightWord, hcolLen]
      omega) (by
        simp [positiveMiddleRightWord, hcolA]
        omega)
  change visibleWordList (F := F) (List.ofFn row.1) = rowWord ∧
      visibleWordList (F := F) (List.ofFn row.2) = rowWord at hr
  change visibleWordList (F := F) (List.ofFn col.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn col.2) = colWord at hc
  have hpKet := rectangularCircuitPerm_eq_positiveReductionOutput
    (F := F) a b s rowWord colWord (row.1, col.1)
      hr.1 hc.1 hrowLen hrowA hrowHead hcolLen hcolA
  have hpBra := rectangularCircuitPerm_eq_positiveReductionOutput
    (F := F) a b s rowWord colWord (row.2, col.2)
      hr.2 hc.2 hrowLen hrowA hrowHead hcolLen hcolA
  have hsPath := positiveTransported_reduction_source (F := F)
    a b s rowWord colWord pre post L x
  have hs : rectangularSource F (succPNat (a + b + s))
      (rectangularCircuitPerm F (a + b + s + 1) (row.1, col.1))
      (rectangularCircuitPerm F (a + b + s + 1) (row.2, col.2)) ≠ 0 := by
    rw [hpKet, hpBra]
    simpa [row, col] using hsPath
  refine ⟨?_, ?_, ?_⟩
  · simpa [row, col, coreSourcePairEquiv, coeffOperatorPairEquiv] using hs
  · change packetBCount F
      (fun i => (rectangularCircuitPerm F (a + b + s + 1)
        (row.1, col.1)).2 i.succ) = b + s
    rw [packetBCount_eq_visibleWordList_count,
      visibleWordList_ofFn_succ,
      visibleWordList_rectangularCircuitPerm_snd, hr.1]
    exact tail_count_B_of_head_B rowWord a (b + s) (by omega) hrowA hrowHead
  · change packetACount F
      (rectangularCircuitPerm F (a + b + s + 1) (row.1, col.1)).1 =
        a + s + 1
    rw [packetACount_eq_visibleWordList_count,
      visibleWordList_rectangularCircuitPerm_fst, hc.1, hcolA]

theorem negativeTransported_sourceSector (a b s : ℕ)
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
    SourceSectorPredicate F (a + b + s) b a
      (coreSourcePairEquiv F (a + b + s)
        (negativeTransportedRow (F := F) a b s rowWord pre p,
          negativeTransportedColumn (F := F) a b s colWord post x)) := by
  let row := negativeTransportedRow (F := F) a b s rowWord pre p
  let col := negativeTransportedColumn (F := F) a b s colWord post x
  have hr := negativeTransportedRow_visibleWord (F := F)
    a b s rowWord pre p hpre (by
      simp [negativeMiddleLeftWord, hrowLen]
      omega) (by simp [negativeMiddleLeftWord, hrowA])
  have hc := negativeTransportedColumn_visibleWord (F := F)
    a b s colWord post x hpost (by
      simp [negativeMiddleRightWord, hcolLen]
      omega) (by
        simp [negativeMiddleRightWord, hcolA, List.count_replicate,
          show VisibleColour.A ≠ VisibleColour.B by decide])
  change visibleWordList (F := F) (List.ofFn row.1) = rowWord ∧
      visibleWordList (F := F) (List.ofFn row.2) = rowWord at hr
  change visibleWordList (F := F) (List.ofFn col.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn col.2) = colWord at hc
  have hpKet := rectangularCircuitPerm_eq_negativeReductionOutput
    (F := F) a b s rowWord colWord (row.1, col.1)
      hr.1 hc.1 hrowLen hrowA hrowHead hcolLen hcolA
  have hpBra := rectangularCircuitPerm_eq_negativeReductionOutput
    (F := F) a b s rowWord colWord (row.2, col.2)
      hr.2 hc.2 hrowLen hrowA hrowHead hcolLen hcolA
  have hsPath := negativeTransported_reduction_source (F := F)
    a b s rowWord colWord pre post p x
  have hs : rectangularSource F (succPNat (a + b + s))
      (rectangularCircuitPerm F (a + b + s + 1) (row.1, col.1))
      (rectangularCircuitPerm F (a + b + s + 1) (row.2, col.2)) ≠ 0 := by
    rw [hpKet, hpBra]
    simpa [row, col] using hsPath
  refine ⟨?_, ?_, ?_⟩
  · simpa [row, col, coreSourcePairEquiv, coeffOperatorPairEquiv] using hs
  · change packetBCount F
      (fun i => (rectangularCircuitPerm F (a + b + s + 1)
        (row.1, col.1)).2 i.succ) = b
    rw [packetBCount_eq_visibleWordList_count,
      visibleWordList_ofFn_succ,
      visibleWordList_rectangularCircuitPerm_snd, hr.1]
    exact tail_count_B_of_head_B rowWord (a + s) b (by omega) hrowA hrowHead
  · change packetACount F
      (rectangularCircuitPerm F (a + b + s + 1) (row.1, col.1)).1 = a
    rw [packetACount_eq_visibleWordList_count,
      visibleWordList_rectangularCircuitPerm_fst, hc.1, hcolA]

/-! ## Separation of the transported phase -/

def positiveTransportedRowPhase (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b))
    (L : Fin (s + 1) → F) : F :=
  let row := positiveTransportedRow (F := F) a b s rowWord pre L
  let w := colourRearrangementWord (F := F) rowWord
    (positiveMiddleLeftWord a b s)
  spatialCircuitExponent F (a + b + s + 1) w row.2 -
    spatialCircuitExponent F (a + b + s + 1) w row.1

def positiveTransportedColumnPhase (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b))
    (x : Fin s → F) : F :=
  let col := positiveTransportedColumn (F := F) a b s colWord post x
  let w := colourRearrangementWord (F := F) colWord
    (positiveMiddleRightWord a b s)
  spatialCircuitExponent F (a + b + s + 1) w col.2 -
    spatialCircuitExponent F (a + b + s + 1) w col.1

def negativeTransportedRowPhase (a b s : ℕ)
    (rowWord : List VisibleColour) (pre : PacketBasis F (a + b))
    (p : F × (Fin s → F)) : F :=
  let row := negativeTransportedRow (F := F) a b s rowWord pre p
  let w := colourRearrangementWord (F := F) rowWord
    (negativeMiddleLeftWord a b s)
  spatialCircuitExponent F (a + b + s + 1) w row.2 -
    spatialCircuitExponent F (a + b + s + 1) w row.1

def negativeTransportedColumnPhase (a b s : ℕ)
    (colWord : List VisibleColour) (post : PacketBasis F (a + b))
    (x : Fin s → F) : F :=
  let col := negativeTransportedColumn (F := F) a b s colWord post x
  let w := colourRearrangementWord (F := F) colWord
    (negativeMiddleRightWord a b s)
  spatialCircuitExponent F (a + b + s + 1) w col.2 -
    spatialCircuitExponent F (a + b + s + 1) w col.1

theorem positiveTransported_exponent_difference (a b s : ℕ)
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
    let row := positiveTransportedRow (F := F) a b s rowWord pre L
    let col := positiveTransportedColumn (F := F) a b s colWord post x
    rectangularCircuitExponent F (a + b + s + 1) (row.2, col.2) -
        rectangularCircuitExponent F (a + b + s + 1) (row.1, col.1) =
      (rectangularCircuitExponent F (s + 1)
          ((positiveExtremeRow (F := F) s L).2,
            (positiveExtremeColumn (F := F) s x).2) -
        rectangularCircuitExponent F (s + 1)
          ((positiveExtremeRow (F := F) s L).1,
            (positiveExtremeColumn (F := F) s x).1)) +
      positiveTransportedRowPhase (F := F) a b s rowWord pre L +
      positiveTransportedColumnPhase (F := F) a b s colWord post x := by
  dsimp only
  let row := positiveTransportedRow (F := F) a b s rowWord pre L
  let col := positiveTransportedColumn (F := F) a b s colWord post x
  let wL := colourRearrangementWord (F := F) rowWord
    (positiveMiddleLeftWord a b s)
  let wR := colourRearrangementWord (F := F) colWord
    (positiveMiddleRightWord a b s)
  let outL := colourRearrangementWord (F := F)
    (positiveSourceLeftWord a b s) colWord
  let outR := colourRearrangementWord (F := F)
    (positiveSourceRightTailWord a b s) rowWord.tail
  have hr := positiveTransportedRow_visibleWord (F := F)
    a b s rowWord pre L hpre (by
      simp [positiveMiddleLeftWord, hrowLen]
      omega) (by
        simp [positiveMiddleLeftWord, hrowA, List.count_replicate,
          show VisibleColour.A ≠ VisibleColour.B by decide])
  have hc := positiveTransportedColumn_visibleWord (F := F)
    a b s colWord post x hpost (by
      simp [positiveMiddleRightWord, hcolLen]
      omega) (by
        simp [positiveMiddleRightWord, hcolA]
        omega)
  change visibleWordList (F := F) (List.ofFn row.1) = rowWord ∧
      visibleWordList (F := F) (List.ofFn row.2) = rowWord at hr
  change visibleWordList (F := F) (List.ofFn col.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn col.2) = colWord at hc
  have hin : ∀ i ∈ wL, i + 1 < a + b + s + 1 := by
    intro i hi
    have h := mem_colourRearrangementWord_lt rowWord
      (positiveMiddleLeftWord a b s) (by
        simp [positiveMiddleLeftWord, hrowLen]
        omega) hi
    simpa [wL, hrowLen] using h
  have hout : ∀ i ∈ outL, i + 1 < a + b + s + 1 := by
    intro i hi
    have h := mem_colourRearrangementWord_lt
      (positiveSourceLeftWord a b s) colWord (by
        simp [positiveSourceLeftWord, hcolLen]
        omega) hi
    simp [outL, positiveSourceLeftWord] at h
    omega
  have heKet := rectangularCircuitExponent_eq_positiveReductionWord
    (F := F) a b s rowWord colWord (row.1, col.1)
      hr.1 hc.1 hrowLen hrowA hrowHead hcolLen hcolA
  have heBra := rectangularCircuitExponent_eq_positiveReductionWord
    (F := F) a b s rowWord colWord (row.2, col.2)
      hr.2 hc.2 hrowLen hrowA hrowHead hcolLen hcolA
  unfold positiveReductionWord at heKet heBra
  rw [spatialCircuitExponent_paddedReductionWord (F := F)
      (a + b) s wL wR outL outR (row.1, col.1) hin hout] at heKet
  rw [spatialCircuitExponent_paddedReductionWord (F := F)
      (a + b) s wL wR outL outR (row.2, col.2) hin hout] at heBra
  have hb := boundaryLocalPerm_positiveTransported (F := F)
    a b s rowWord colWord pre post L x
  change boundaryLocalPerm (F := F) (a + b + s) wL wR (row.1, col.1) =
      ((positivePaddedRow (F := F) (a + b) s pre L).1,
        (positivePaddedColumn (F := F) (a + b) s post x).1) ∧
    boundaryLocalPerm (F := F) (a + b + s) wL wR (row.2, col.2) =
      ((positivePaddedRow (F := F) (a + b) s pre L).2,
        (positivePaddedColumn (F := F) (a + b) s post x).2) at hb
  rw [hb.1] at heKet
  rw [hb.2] at heBra
  have hs := positivePadded_embedded_source (F := F)
    (a + b) s pre post L x
  have houtEq := sourceLocalExponent_eq (F := F) (a + b + s)
    outL outR
    (embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((positivePaddedRow (F := F) (a + b) s pre L).1,
        (positivePaddedColumn (F := F) (a + b) s post x).1))
    (embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((positivePaddedRow (F := F) (a + b) s pre L).2,
        (positivePaddedColumn (F := F) (a + b) s post x).2)) hs
  dsimp only at heKet heBra
  simp only [positivePaddedRow, positivePaddedColumn] at heKet heBra
  rw [embeddedRectangularCircuitExponent_apply] at heKet heBra
  change rectangularCircuitExponent F (a + b + s + 1) (row.2, col.2) -
      rectangularCircuitExponent F (a + b + s + 1) (row.1, col.1) = _
  rw [heBra, heKet]
  dsimp [positivePaddedRow, positivePaddedColumn,
    positiveTransportedRowPhase, positiveTransportedColumnPhase,
    row, col, wL, wR] at houtEq ⊢
  rw [houtEq]
  ring

theorem negativeTransported_exponent_difference (a b s : ℕ)
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
    let row := negativeTransportedRow (F := F) a b s rowWord pre p
    let col := negativeTransportedColumn (F := F) a b s colWord post x
    rectangularCircuitExponent F (a + b + s + 1) (row.2, col.2) -
        rectangularCircuitExponent F (a + b + s + 1) (row.1, col.1) =
      (rectangularCircuitExponent F (s + 1)
          ((negativeExtremeRow (F := F) s p).2,
            (negativeExtremeColumn (F := F) s x).2) -
        rectangularCircuitExponent F (s + 1)
          ((negativeExtremeRow (F := F) s p).1,
            (negativeExtremeColumn (F := F) s x).1)) +
      negativeTransportedRowPhase (F := F) a b s rowWord pre p +
      negativeTransportedColumnPhase (F := F) a b s colWord post x := by
  dsimp only
  let row := negativeTransportedRow (F := F) a b s rowWord pre p
  let col := negativeTransportedColumn (F := F) a b s colWord post x
  let wL := colourRearrangementWord (F := F) rowWord
    (negativeMiddleLeftWord a b s)
  let wR := colourRearrangementWord (F := F) colWord
    (negativeMiddleRightWord a b s)
  let outL := colourRearrangementWord (F := F)
    (negativeSourceLeftWord a b s) colWord
  let outR := colourRearrangementWord (F := F)
    (negativeSourceRightTailWord a b s) rowWord.tail
  have hr := negativeTransportedRow_visibleWord (F := F)
    a b s rowWord pre p hpre (by
      simp [negativeMiddleLeftWord, hrowLen]
      omega) (by simp [negativeMiddleLeftWord, hrowA])
  have hc := negativeTransportedColumn_visibleWord (F := F)
    a b s colWord post x hpost (by
      simp [negativeMiddleRightWord, hcolLen]
      omega) (by
        simp [negativeMiddleRightWord, hcolA, List.count_replicate,
          show VisibleColour.A ≠ VisibleColour.B by decide])
  change visibleWordList (F := F) (List.ofFn row.1) = rowWord ∧
      visibleWordList (F := F) (List.ofFn row.2) = rowWord at hr
  change visibleWordList (F := F) (List.ofFn col.1) = colWord ∧
      visibleWordList (F := F) (List.ofFn col.2) = colWord at hc
  have hin : ∀ i ∈ wL, i + 1 < a + b + s + 1 := by
    intro i hi
    have h := mem_colourRearrangementWord_lt rowWord
      (negativeMiddleLeftWord a b s) (by
        simp [negativeMiddleLeftWord, hrowLen]
        omega) hi
    simpa [wL, hrowLen] using h
  have hout : ∀ i ∈ outL, i + 1 < a + b + s + 1 := by
    intro i hi
    have h := mem_colourRearrangementWord_lt
      (negativeSourceLeftWord a b s) colWord (by
        simp [negativeSourceLeftWord, hcolLen]
        omega) hi
    simp [outL, negativeSourceLeftWord] at h
    omega
  have heKet := rectangularCircuitExponent_eq_negativeReductionWord
    (F := F) a b s rowWord colWord (row.1, col.1)
      hr.1 hc.1 hrowLen hrowA hrowHead hcolLen hcolA
  have heBra := rectangularCircuitExponent_eq_negativeReductionWord
    (F := F) a b s rowWord colWord (row.2, col.2)
      hr.2 hc.2 hrowLen hrowA hrowHead hcolLen hcolA
  unfold negativeReductionWord at heKet heBra
  rw [spatialCircuitExponent_paddedReductionWord (F := F)
      (a + b) s wL wR outL outR (row.1, col.1) hin hout] at heKet
  rw [spatialCircuitExponent_paddedReductionWord (F := F)
      (a + b) s wL wR outL outR (row.2, col.2) hin hout] at heBra
  have hb := boundaryLocalPerm_negativeTransported (F := F)
    a b s rowWord colWord pre post p x
  change boundaryLocalPerm (F := F) (a + b + s) wL wR (row.1, col.1) =
      ((negativePaddedRow (F := F) (a + b) s pre p).1,
        (negativePaddedColumn (F := F) (a + b) s post x).1) ∧
    boundaryLocalPerm (F := F) (a + b + s) wL wR (row.2, col.2) =
      ((negativePaddedRow (F := F) (a + b) s pre p).2,
        (negativePaddedColumn (F := F) (a + b) s post x).2) at hb
  rw [hb.1] at heKet
  rw [hb.2] at heBra
  have hs := negativePadded_embedded_source (F := F)
    (a + b) s pre post p x
  have houtEq := sourceLocalExponent_eq (F := F) (a + b + s)
    outL outR
    (embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((negativePaddedRow (F := F) (a + b) s pre p).1,
        (negativePaddedColumn (F := F) (a + b) s post x).1))
    (embeddedRectangularCircuitPerm (F := F) (a + b) s
      ((negativePaddedRow (F := F) (a + b) s pre p).2,
        (negativePaddedColumn (F := F) (a + b) s post x).2)) hs
  dsimp only at heKet heBra
  simp only [negativePaddedRow, negativePaddedColumn] at heKet heBra
  rw [embeddedRectangularCircuitExponent_apply] at heKet heBra
  change rectangularCircuitExponent F (a + b + s + 1) (row.2, col.2) -
      rectangularCircuitExponent F (a + b + s + 1) (row.1, col.1) = _
  rw [heBra, heKet]
  dsimp [negativePaddedRow, negativePaddedColumn,
    negativeTransportedRowPhase, negativeTransportedColumnPhase,
    row, col, wL, wR] at houtEq ⊢
  rw [houtEq]
  ring

/-! ## The measured spectator blocks -/

theorem pulledSourceSectorBlock_apply_ne_zero_of_predicate
    (psi : AddChar F ℂ) (n j l : ℕ)
    (r c : PacketBasis F (n + 1) × PacketBasis F (n + 1))
    (h : SourceSectorPredicate F n j l
      (coreSourcePairEquiv F n (r, c))) :
    pulledSourceSectorBlock F psi n j l r c ≠ 0 := by
  intro hz
  have hn := normSq_pulledSourceSectorBlock F psi n j l r c
  rw [hz] at hn
  simp [h] at hn

theorem coefficientRowWord_eq_of_visibleWordList (n : ℕ)
    (r : PacketBasis F (n + 1) × PacketBasis F (n + 1))
    (word : Fin (n + 1) → VisibleColour)
    (h : visibleWordList (F := F) (List.ofFn r.2) = List.ofFn word) :
    coefficientRowWord (F := F) n r = word := by
  rw [visibleWordList_ofFn] at h
  exact List.ofFn_injective h

theorem coefficientColumnWord_eq_of_visibleWordList (n : ℕ)
    (c : PacketBasis F (n + 1) × PacketBasis F (n + 1))
    (word : Fin (n + 1) → VisibleColour)
    (h : visibleWordList (F := F) (List.ofFn c.2) = List.ofFn word) :
    coefficientColumnWord (F := F) n c = word := by
  rw [visibleWordList_ofFn] at h
  exact List.ofFn_injective h

noncomputable def positiveSpectatorBlock (psi : AddChar F ℂ)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b)) :=
  let rowWord := List.ofFn rowColours
  let colWord := List.ofFn colColours
  twoSidedMeasurementBlock
    (preSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (positiveMiddleLeftWord a b s)))
    (postSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) colWord
        (positiveMiddleRightWord a b s)))
    (pulledSourceWordFibreBlock (F := F) psi (a + b + s)
      (b + s) (a + s + 1) rowColours colColours) pre post

noncomputable def negativeSpectatorBlock (psi : AddChar F ℂ)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b)) :=
  let rowWord := List.ofFn rowColours
  let colWord := List.ofFn colColours
  twoSidedMeasurementBlock
    (preSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (negativeMiddleLeftWord a b s)))
    (postSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) colWord
        (negativeMiddleRightWord a b s)))
    (pulledSourceWordFibreBlock (F := F) psi (a + b + s)
      b a rowColours colColours) pre post

theorem positiveSpectatorBlock_apply_active (psi : AddChar F ℂ)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b))
    (L : Fin (s + 1) → F) (x : Fin s → F)
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowA : (List.ofFn rowColours).count .A = a)
    (hrowHead : .B ∈ (List.ofFn rowColours).head?)
    (hcolA : (List.ofFn colColours).count .A = a + s + 1) :
    positiveSpectatorBlock (F := F) psi a b s rowColours colColours pre post
        (positiveTransportedRow (F := F) a b s
          (List.ofFn rowColours) pre L)
        (positiveTransportedColumn (F := F) a b s
          (List.ofFn colColours) post x) =
      psi (positiveTransportedRowPhase (F := F) a b s
          (List.ofFn rowColours) pre L) *
        pulledSourceSectorBlock F psi s s (s + 1)
          (positiveExtremeRow (F := F) s L)
          (positiveExtremeColumn (F := F) s x) *
        psi (positiveTransportedColumnPhase (F := F) a b s
          (List.ofFn colColours) post x) := by
  let rowWord := List.ofFn rowColours
  let colWord := List.ofFn colColours
  let row := positiveTransportedRow (F := F) a b s rowWord pre L
  let col := positiveTransportedColumn (F := F) a b s colWord post x
  change positiveSpectatorBlock (F := F) psi a b s rowColours colColours pre post
      row col =
    psi (positiveTransportedRowPhase (F := F) a b s rowWord pre L) *
      pulledSourceSectorBlock F psi s s (s + 1)
        (positiveExtremeRow (F := F) s L)
        (positiveExtremeColumn (F := F) s x) *
      psi (positiveTransportedColumnPhase (F := F) a b s colWord post x)
  have hrowLen : rowWord.length = a + b + s + 1 := by simp [rowWord]
  have hcolLen : colWord.length = a + b + s + 1 := by simp [colWord]
  have hrowA' : rowWord.count .A = a := by simpa [rowWord] using hrowA
  have hrowHead' : .B ∈ rowWord.head? := by simpa [rowWord] using hrowHead
  have hcolA' : colWord.count .A = a + s + 1 := by
    simpa [colWord] using hcolA
  have hsector := positiveTransported_sourceSector (F := F)
    a b s rowWord colWord pre post L x hpre hpost
      hrowLen hrowA' hrowHead' hcolLen hcolA'
  have hfull := pulledSourceSectorBlock_apply_ne_zero_of_predicate
    (F := F) psi (a + b + s) (b + s) (a + s + 1) row col (by
      simpa [row, col] using hsector)
  have hresPred := positiveExtreme_sourceSector (F := F) s L x
  have hres := pulledSourceSectorBlock_apply_ne_zero_of_predicate
    (F := F) psi s s (s + 1)
      (positiveExtremeRow (F := F) s L)
      (positiveExtremeColumn (F := F) s x) (by
        simpa using hresPred)
  have hr := positiveTransportedRow_visibleWord (F := F)
    a b s rowWord pre L hpre (by
      simp [positiveMiddleLeftWord, hrowLen]
      omega) (by
        simp [positiveMiddleLeftWord, hrowA',
          List.count_replicate,
          show VisibleColour.A ≠ VisibleColour.B by decide])
  have hc := positiveTransportedColumn_visibleWord (F := F)
    a b s colWord post x hpost (by
      simp [positiveMiddleRightWord, hcolLen]
      omega) (by
        simp [positiveMiddleRightWord, hcolA']
        omega)
  have hrowCoeff : coefficientRowWord (F := F) (a + b + s) row =
      rowColours := coefficientRowWord_eq_of_visibleWordList
        (F := F) (a + b + s) row rowColours (by
          simpa [rowWord, row] using hr.2)
  have hcolCoeff : coefficientColumnWord (F := F) (a + b + s) col =
      colColours := coefficientColumnWord_eq_of_visibleWordList
        (F := F) (a + b + s) col colColours (by
          simpa [colWord, col] using hc.2)
  have hpreActive : preSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (positiveMiddleLeftWord a b s)) row = pre := by
    simpa [row] using preSpectatorLabel_positiveTransportedRow
      (F := F) a b s rowWord pre L
  have hpostActive : postSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) colWord
        (positiveMiddleRightWord a b s)) col = post := by
    simpa [col] using postSpectatorLabel_positiveTransportedColumn
      (F := F) a b s colWord post x
  have hselected :
      positiveSpectatorBlock (F := F) psi a b s rowColours colColours pre post
          row col =
        pulledSourceSectorBlock F psi (a + b + s)
          (b + s) (a + s + 1) row col := by
    unfold positiveSpectatorBlock pulledSourceWordFibreBlock
    unfold twoSidedMeasurementBlock rowMeasurementBlock columnMeasurementBlock
    rw [if_pos hpreActive, if_pos hpostActive]
    change (if coefficientRowWord (F := F) (a + b + s) row = rowColours then
        if coefficientColumnWord (F := F) (a + b + s) col = colColours then
          pulledSourceSectorBlock F psi (a + b + s)
            (b + s) (a + s + 1) row col
        else 0 else 0) = _
    rw [if_pos hrowCoeff, if_pos hcolCoeff]
  have hfullPhase := pulledSourceSectorBlock_apply_eq_phaseDifference_of_ne_zero
    F psi (a + b + s) (b + s) (a + s + 1) row col hfull
  have hresPhase := pulledSourceSectorBlock_apply_eq_phaseDifference_of_ne_zero
    F psi s s (s + 1)
      (positiveExtremeRow (F := F) s L)
      (positiveExtremeColumn (F := F) s x) hres
  have hdiff := positiveTransported_exponent_difference (F := F)
    a b s rowWord colWord pre post L x hpre hpost hrowLen
      hrowA' hrowHead' hcolLen hcolA'
  have hfullPhase' :
      pulledSourceSectorBlock F psi (a + b + s) (b + s) (a + s + 1)
          row col =
        psi (rectangularCircuitExponent F (a + b + s + 1) (row.2, col.2) -
          rectangularCircuitExponent F (a + b + s + 1) (row.1, col.1)) := by
    simpa [coeffOperatorPairEquiv] using hfullPhase
  have hresPhase' :
      pulledSourceSectorBlock F psi s s (s + 1)
          (positiveExtremeRow (F := F) s L)
          (positiveExtremeColumn (F := F) s x) =
        psi (rectangularCircuitExponent F (s + 1)
            ((positiveExtremeRow (F := F) s L).2,
              (positiveExtremeColumn (F := F) s x).2) -
          rectangularCircuitExponent F (s + 1)
            ((positiveExtremeRow (F := F) s L).1,
              (positiveExtremeColumn (F := F) s x).1)) := by
    simpa [coeffOperatorPairEquiv] using hresPhase
  rw [hselected]
  rw [hfullPhase', hresPhase']
  rw [hdiff, psi.map_add_eq_mul, psi.map_add_eq_mul]
  ring

theorem positiveSpectatorBlock_support (psi : AddChar F ℂ)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b))
    (r c : PacketBasis F (a + b + s + 1) ×
      PacketBasis F (a + b + s + 1))
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowA : (List.ofFn rowColours).count .A = a)
    (hrowHead : .B ∈ (List.ofFn rowColours).head?)
    (hcolA : (List.ofFn colColours).count .A = a + s + 1)
    (hM : positiveSpectatorBlock (F := F) psi a b s
      rowColours colColours pre post r c ≠ 0) :
    r ∈ Set.range (positiveTransportedRow (F := F) a b s
        (List.ofFn rowColours) pre) ∧
      c ∈ Set.range (positiveTransportedColumn (F := F) a b s
        (List.ofFn colColours) post) := by
  let rowWord := List.ofFn rowColours
  let colWord := List.ofFn colColours
  have hraw := hM
  unfold positiveSpectatorBlock pulledSourceWordFibreBlock at hraw
  unfold twoSidedMeasurementBlock rowMeasurementBlock columnMeasurementBlock at hraw
  split_ifs at hraw with hpreLabel hpostLabel
  · change (if coefficientRowWord (F := F) (a + b + s) r = rowColours then
        if coefficientColumnWord (F := F) (a + b + s) c = colColours then
          pulledSourceSectorBlock F psi (a + b + s)
            (b + s) (a + s + 1) r c
        else 0 else 0) ≠ 0 at hraw
    split_ifs at hraw with hrowCoeff hcolCoeff
    · have hfull : pulledSourceSectorBlock F psi (a + b + s)
          (b + s) (a + s + 1) r c ≠ 0 := hraw
      have hcoeff := hfull
      unfold pulledSourceSectorBlock at hcoeff
      dsimp only at hcoeff
      split_ifs at hcoeff with hcount
      · have hsource :=
          (rectCoeff_rectangularCore_ne_zero_iff_source
            F psi (a + b + s) r c).mp hcoeff
        have hrowBra : visibleWordList (F := F) (List.ofFn r.2) = rowWord := by
          rw [visibleWordList_ofFn]
          exact congrArg List.ofFn (by
            simpa [coefficientRowWord, rowWord] using hrowCoeff)
        have hcolBra : visibleWordList (F := F) (List.ofFn c.2) = colWord := by
          rw [visibleWordList_ofFn]
          exact congrArg List.ofFn (by
            simpa [coefficientColumnWord, colWord] using hcolCoeff)
        exact positive_source_ranges_of_words (F := F)
          a b s rowWord colWord pre post r c hpre hpost hrowBra hcolBra
          (by simp [rowWord]) (by simpa [rowWord] using hrowA)
          (by simpa [rowWord] using hrowHead) (by simp [colWord])
          (by simpa [colWord] using hcolA)
          (by simpa [rowWord] using hpreLabel)
          (by simpa [colWord] using hpostLabel) hsource
      · exact (hcoeff rfl).elim
    all_goals exact (hraw rfl).elim
  all_goals exact (hraw rfl).elim

theorem positiveSpectatorBlock_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (hodd : ringChar F ≠ 2)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b))
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowA : (List.ofFn rowColours).count .A = a)
    (hrowHead : .B ∈ (List.ofFn rowColours).head?)
    (hcolA : (List.ofFn colColours).count .A = a + s + 1) :
    vonNeumannEntropy
        (positiveSpectatorBlock (F := F) psi a b s
          rowColours colColours pre post) =
      (s : ℝ) * Real.log (Fintype.card F) := by
  let N : Matrix (Fin (s + 1) → F) (Fin s → F) ℂ :=
    fun L x => pulledSourceSectorBlock F psi s s (s + 1)
      (positiveExtremeRow (F := F) s L)
      (positiveExtremeColumn (F := F) s x)
  rw [vonNeumannEntropy_eq_of_supported_character_embedding
    (F := F) psi
    (positiveTransportedRow (F := F) a b s (List.ofFn rowColours) pre)
    (positiveTransportedColumn (F := F) a b s (List.ofFn colColours) post)
    (positiveTransportedRow_injective (F := F) a b s
      (List.ofFn rowColours) pre)
    (positiveTransportedColumn_injective (F := F) a b s
      (List.ofFn colColours) post)
    (positiveSpectatorBlock (F := F) psi a b s
      rowColours colColours pre post)
    N
    (positiveTransportedRowPhase (F := F) a b s
      (List.ofFn rowColours) pre)
    (positiveTransportedColumnPhase (F := F) a b s
      (List.ofFn colColours) post)
    (fun L x => by
      simpa [N] using positiveSpectatorBlock_apply_active (F := F)
        psi a b s rowColours colColours pre post L x
        hpre hpost hrowA hrowHead hcolA)
    (fun r c hM => positiveSpectatorBlock_support (F := F) psi a b s
      rowColours colColours pre post r c hpre hpost hrowA hrowHead hcolA hM)]
  have hN : N =
      positiveFullGridCoeff psi (positiveUnitEpsilon (F := F) s) s := by
    ext L x
    exact pulledSourceSectorBlock_positiveExtreme_apply psi s L x
  rw [hN]
  exact positiveFullGridCoeff_vonNeumannEntropy psi hpsi
    (positiveUnitEpsilon (F := F) s) s hodd
    (positiveUnitEpsilon_col_one' (F := F) s)

theorem negativeSpectatorBlock_apply_active (psi : AddChar F ℂ)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b))
    (p : F × (Fin s → F)) (x : Fin s → F)
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowA : (List.ofFn rowColours).count .A = a + s)
    (hrowHead : .B ∈ (List.ofFn rowColours).head?)
    (hcolA : (List.ofFn colColours).count .A = a) :
    negativeSpectatorBlock (F := F) psi a b s rowColours colColours pre post
        (negativeTransportedRow (F := F) a b s
          (List.ofFn rowColours) pre p)
        (negativeTransportedColumn (F := F) a b s
          (List.ofFn colColours) post x) =
      psi (negativeTransportedRowPhase (F := F) a b s
          (List.ofFn rowColours) pre p) *
        pulledSourceSectorBlock F psi s 0 0
          (negativeExtremeRow (F := F) s p)
          (negativeExtremeColumn (F := F) s x) *
        psi (negativeTransportedColumnPhase (F := F) a b s
          (List.ofFn colColours) post x) := by
  let rowWord := List.ofFn rowColours
  let colWord := List.ofFn colColours
  let row := negativeTransportedRow (F := F) a b s rowWord pre p
  let col := negativeTransportedColumn (F := F) a b s colWord post x
  change negativeSpectatorBlock (F := F) psi a b s rowColours colColours pre post
      row col =
    psi (negativeTransportedRowPhase (F := F) a b s rowWord pre p) *
      pulledSourceSectorBlock F psi s 0 0
        (negativeExtremeRow (F := F) s p)
        (negativeExtremeColumn (F := F) s x) *
      psi (negativeTransportedColumnPhase (F := F) a b s colWord post x)
  have hrowLen : rowWord.length = a + b + s + 1 := by simp [rowWord]
  have hcolLen : colWord.length = a + b + s + 1 := by simp [colWord]
  have hrowA' : rowWord.count .A = a + s := by simpa [rowWord] using hrowA
  have hrowHead' : .B ∈ rowWord.head? := by simpa [rowWord] using hrowHead
  have hcolA' : colWord.count .A = a := by simpa [colWord] using hcolA
  have hsector := negativeTransported_sourceSector (F := F)
    a b s rowWord colWord pre post p x hpre hpost
      hrowLen hrowA' hrowHead' hcolLen hcolA'
  have hfull := pulledSourceSectorBlock_apply_ne_zero_of_predicate
    (F := F) psi (a + b + s) b a row col (by
      simpa [row, col] using hsector)
  have hresPred := negativeExtreme_sourceSector (F := F) s p x
  have hres := pulledSourceSectorBlock_apply_ne_zero_of_predicate
    (F := F) psi s 0 0
      (negativeExtremeRow (F := F) s p)
      (negativeExtremeColumn (F := F) s x) (by
        simpa using hresPred)
  have hr := negativeTransportedRow_visibleWord (F := F)
    a b s rowWord pre p hpre (by
      simp [negativeMiddleLeftWord, hrowLen]
      omega) (by simp [negativeMiddleLeftWord, hrowA'])
  have hc := negativeTransportedColumn_visibleWord (F := F)
    a b s colWord post x hpost (by
      simp [negativeMiddleRightWord, hcolLen]
      omega) (by
        simp [negativeMiddleRightWord, hcolA', List.count_replicate,
          show VisibleColour.A ≠ VisibleColour.B by decide])
  have hrowCoeff : coefficientRowWord (F := F) (a + b + s) row =
      rowColours := coefficientRowWord_eq_of_visibleWordList
        (F := F) (a + b + s) row rowColours (by
          simpa [rowWord, row] using hr.2)
  have hcolCoeff : coefficientColumnWord (F := F) (a + b + s) col =
      colColours := coefficientColumnWord_eq_of_visibleWordList
        (F := F) (a + b + s) col colColours (by
          simpa [colWord, col] using hc.2)
  have hpreActive : preSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) rowWord
        (negativeMiddleLeftWord a b s)) row = pre := by
    simpa [row] using preSpectatorLabel_negativeTransportedRow
      (F := F) a b s rowWord pre p
  have hpostActive : postSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) colWord
        (negativeMiddleRightWord a b s)) col = post := by
    simpa [col] using postSpectatorLabel_negativeTransportedColumn
      (F := F) a b s colWord post x
  have hselected :
      negativeSpectatorBlock (F := F) psi a b s rowColours colColours pre post
          row col =
        pulledSourceSectorBlock F psi (a + b + s) b a row col := by
    unfold negativeSpectatorBlock pulledSourceWordFibreBlock
    unfold twoSidedMeasurementBlock rowMeasurementBlock columnMeasurementBlock
    rw [if_pos hpreActive, if_pos hpostActive]
    change (if coefficientRowWord (F := F) (a + b + s) row = rowColours then
        if coefficientColumnWord (F := F) (a + b + s) col = colColours then
          pulledSourceSectorBlock F psi (a + b + s) b a row col
        else 0 else 0) = _
    rw [if_pos hrowCoeff, if_pos hcolCoeff]
  have hfullPhase := pulledSourceSectorBlock_apply_eq_phaseDifference_of_ne_zero
    F psi (a + b + s) b a row col hfull
  have hresPhase := pulledSourceSectorBlock_apply_eq_phaseDifference_of_ne_zero
    F psi s 0 0
      (negativeExtremeRow (F := F) s p)
      (negativeExtremeColumn (F := F) s x) hres
  have hdiff := negativeTransported_exponent_difference (F := F)
    a b s rowWord colWord pre post p x hpre hpost hrowLen
      hrowA' hrowHead' hcolLen hcolA'
  have hfullPhase' :
      pulledSourceSectorBlock F psi (a + b + s) b a row col =
        psi (rectangularCircuitExponent F (a + b + s + 1) (row.2, col.2) -
          rectangularCircuitExponent F (a + b + s + 1) (row.1, col.1)) := by
    simpa [coeffOperatorPairEquiv] using hfullPhase
  have hresPhase' :
      pulledSourceSectorBlock F psi s 0 0
          (negativeExtremeRow (F := F) s p)
          (negativeExtremeColumn (F := F) s x) =
        psi (rectangularCircuitExponent F (s + 1)
            ((negativeExtremeRow (F := F) s p).2,
              (negativeExtremeColumn (F := F) s x).2) -
          rectangularCircuitExponent F (s + 1)
            ((negativeExtremeRow (F := F) s p).1,
              (negativeExtremeColumn (F := F) s x).1)) := by
    simpa [coeffOperatorPairEquiv] using hresPhase
  rw [hselected, hfullPhase', hresPhase']
  rw [hdiff, psi.map_add_eq_mul, psi.map_add_eq_mul]
  ring

theorem negativeSpectatorBlock_support (psi : AddChar F ℂ)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b))
    (r c : PacketBasis F (a + b + s + 1) ×
      PacketBasis F (a + b + s + 1))
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowA : (List.ofFn rowColours).count .A = a + s)
    (hrowHead : .B ∈ (List.ofFn rowColours).head?)
    (hcolA : (List.ofFn colColours).count .A = a)
    (hM : negativeSpectatorBlock (F := F) psi a b s
      rowColours colColours pre post r c ≠ 0) :
    r ∈ Set.range (negativeTransportedRow (F := F) a b s
        (List.ofFn rowColours) pre) ∧
      c ∈ Set.range (negativeTransportedColumn (F := F) a b s
        (List.ofFn colColours) post) := by
  let rowWord := List.ofFn rowColours
  let colWord := List.ofFn colColours
  have hraw := hM
  unfold negativeSpectatorBlock pulledSourceWordFibreBlock at hraw
  unfold twoSidedMeasurementBlock rowMeasurementBlock columnMeasurementBlock at hraw
  split_ifs at hraw with hpreLabel hpostLabel
  · change (if coefficientRowWord (F := F) (a + b + s) r = rowColours then
        if coefficientColumnWord (F := F) (a + b + s) c = colColours then
          pulledSourceSectorBlock F psi (a + b + s) b a r c
        else 0 else 0) ≠ 0 at hraw
    split_ifs at hraw with hrowCoeff hcolCoeff
    · have hfull : pulledSourceSectorBlock F psi (a + b + s) b a r c ≠ 0 := hraw
      have hcoeff := hfull
      unfold pulledSourceSectorBlock at hcoeff
      dsimp only at hcoeff
      split_ifs at hcoeff with hcount
      · have hsource :=
          (rectCoeff_rectangularCore_ne_zero_iff_source
            F psi (a + b + s) r c).mp hcoeff
        have hrowBra : visibleWordList (F := F) (List.ofFn r.2) = rowWord := by
          rw [visibleWordList_ofFn]
          exact congrArg List.ofFn (by
            simpa [coefficientRowWord, rowWord] using hrowCoeff)
        have hcolBra : visibleWordList (F := F) (List.ofFn c.2) = colWord := by
          rw [visibleWordList_ofFn]
          exact congrArg List.ofFn (by
            simpa [coefficientColumnWord, colWord] using hcolCoeff)
        exact negative_source_ranges_of_words (F := F)
          a b s rowWord colWord pre post r c hpre hpost hrowBra hcolBra
          (by simp [rowWord]) (by simpa [rowWord] using hrowA)
          (by simpa [rowWord] using hrowHead) (by simp [colWord])
          (by simpa [colWord] using hcolA)
          (by simpa [rowWord] using hpreLabel)
          (by simpa [colWord] using hpostLabel) hsource
      · exact (hcoeff rfl).elim
    all_goals exact (hraw rfl).elim
  all_goals exact (hraw rfl).elim

theorem negativeSpectatorBlock_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (hodd : ringChar F ≠ 2)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b))
    (hpre : visibleWordList (F := F) (List.ofFn pre) =
      normalColourWord a b)
    (hpost : visibleWordList (F := F) (List.ofFn post) =
      normalColourWord a b)
    (hrowA : (List.ofFn rowColours).count .A = a + s)
    (hrowHead : .B ∈ (List.ofFn rowColours).head?)
    (hcolA : (List.ofFn colColours).count .A = a) :
    vonNeumannEntropy
        (negativeSpectatorBlock (F := F) psi a b s
          rowColours colColours pre post) =
      (s : ℝ) * Real.log (Fintype.card F) := by
  let N : Matrix (F × (Fin s → F)) (Fin s → F) ℂ :=
    fun p x => pulledSourceSectorBlock F psi s 0 0
      (negativeExtremeRow (F := F) s p)
      (negativeExtremeColumn (F := F) s x)
  rw [vonNeumannEntropy_eq_of_supported_character_embedding
    (F := F) psi
    (negativeTransportedRow (F := F) a b s (List.ofFn rowColours) pre)
    (negativeTransportedColumn (F := F) a b s (List.ofFn colColours) post)
    (negativeTransportedRow_injective (F := F) a b s
      (List.ofFn rowColours) pre)
    (negativeTransportedColumn_injective (F := F) a b s
      (List.ofFn colColours) post)
    (negativeSpectatorBlock (F := F) psi a b s
      rowColours colColours pre post)
    N
    (negativeTransportedRowPhase (F := F) a b s
      (List.ofFn rowColours) pre)
    (negativeTransportedColumnPhase (F := F) a b s
      (List.ofFn colColours) post)
    (fun p x => by
      simpa [N] using negativeSpectatorBlock_apply_active (F := F)
        psi a b s rowColours colColours pre post p x
        hpre hpost hrowA hrowHead hcolA)
    (fun r c hM => negativeSpectatorBlock_support (F := F) psi a b s
      rowColours colColours pre post r c hpre hpost hrowA hrowHead hcolA hM)]
  have hN : N =
      negativeLiteralGridCoeff psi (negativeUnitEpsilon (F := F) s) s := by
    ext p x
    exact pulledSourceSectorBlock_negativeExtreme_apply psi s p x
  rw [hN]
  exact negativeLiteralGridCoeff_vonNeumannEntropy psi hpsi
    (negativeUnitEpsilon (F := F) s) s hodd
    (negativeUnitEpsilon_col_one (F := F) s)

/-! ## Recovering the canonical spectator words -/

theorem spectator_visibleWords_of_middle (a b s : ℕ)
    (pre post : PacketBasis F (a + b))
    (u : RectBasis F (a + b + s + 1))
    (leftCoreWord rightCoreWord : List VisibleColour)
    (hleftCoreLen : leftCoreWord.length = s + 1)
    (hrightCoreLen : rightCoreWord.length = s + 1)
    (huLeft : visibleWordList (F := F) (List.ofFn u.1) =
      normalColourWord a b ++ leftCoreWord)
    (huRight : visibleWordList (F := F) (List.ofFn u.2) =
      rightCoreWord ++ normalColourWord a b)
    (huPre : packetPrePart (F := F) (a + b) s u.1 = pre)
    (huPost : packetPostPart (F := F) (a + b) s u.2 = post) :
    visibleWordList (F := F) (List.ofFn pre) = normalColourWord a b ∧
      visibleWordList (F := F) (List.ofFn post) = normalColourWord a b := by
  constructor
  · have hp := visibleWordList_preCore_parts (F := F) (a + b) s u.1
    rw [huPre, huLeft] at hp
    have ht := congrArg (List.take (a + b)) hp
    calc
      visibleWordList (F := F) (List.ofFn pre) =
          List.take (a + b)
            (visibleWordList (F := F) (List.ofFn pre) ++
              visibleWordList (F := F)
                (List.ofFn (packetPreCorePart (F := F) (a + b) s u.1))) := by
        simp [visibleWordList]
      _ = List.take (a + b) (normalColourWord a b ++ leftCoreWord) :=
        ht.symm
      _ = normalColourWord a b := by
        rw [List.take_append_of_le_length]
        · simp [normalColourWord]
        · simp [normalColourWord]
  · have hp := visibleWordList_postCore_parts (F := F) (a + b) s u.2
    rw [huPost, huRight] at hp
    have hd := congrArg (List.drop (s + 1)) hp
    simpa [normalColourWord, visibleWordList, hleftCoreLen,
      hrightCoreLen] using hd.symm

theorem exists_matrix_entry_ne_zero {R C : Type*}
    (M : Matrix R C ℂ) (hM : M ≠ 0) :
    ∃ r c, M r c ≠ 0 := by
  by_contra h
  push_neg at h
  apply hM
  ext r c
  exact h r c

/-! ## Data carried by a nonzero visible-word fibre -/

theorem pulledSourceWordFibreBlock_entry_data (psi : AddChar F ℂ)
    (n j l : ℕ) (rowColours colColours : Fin (n + 1) → VisibleColour)
    (r c : PacketBasis F (n + 1) × PacketBasis F (n + 1))
    (hentry : pulledSourceWordFibreBlock (F := F) psi n j l
      rowColours colColours r c ≠ 0) :
    coefficientRowWord (F := F) n r = rowColours ∧
      coefficientColumnWord (F := F) n c = colColours ∧
      SourceSectorPredicate F n j l
        (coreSourcePairEquiv F n (r, c)) := by
  have hraw := hentry
  unfold pulledSourceWordFibreBlock at hraw
  unfold twoSidedMeasurementBlock rowMeasurementBlock columnMeasurementBlock at hraw
  change (if coefficientRowWord (F := F) n r = rowColours then
      if coefficientColumnWord (F := F) n c = colColours then
        pulledSourceSectorBlock F psi n j l r c
      else 0 else 0) ≠ 0 at hraw
  split_ifs at hraw with hrow hcol
  · have hcoeff := hraw
    unfold pulledSourceSectorBlock at hcoeff
    dsimp only at hcoeff
    split_ifs at hcoeff with hcount
    · refine ⟨hrow, hcol, ?_, hcount.1, hcount.2⟩
      exact (rectCoeff_rectangularCore_ne_zero_iff_source
        F psi n r c).mp hcoeff
    · exact (hcoeff rfl).elim
  all_goals exact (hraw rfl).elim

theorem pulledSourceWordFibreBlock_word_properties (psi : AddChar F ℂ)
    (n j l : ℕ) (rowColours colColours : Fin (n + 1) → VisibleColour)
    (r c : PacketBasis F (n + 1) × PacketBasis F (n + 1))
    (hentry : pulledSourceWordFibreBlock (F := F) psi n j l
      rowColours colColours r c ≠ 0) :
    rectangularSource F (succPNat n)
        (coreSourcePairEquiv F n (r, c)).1
        (coreSourcePairEquiv F n (r, c)).2 ≠ 0 ∧
      (List.ofFn rowColours).count .A = n - j ∧
      .B ∈ (List.ofFn rowColours).head? ∧
      (List.ofFn colColours).count .A = l := by
  obtain ⟨hrowCoeff, hcolCoeff, hsource, hcountB, hcountA⟩ :=
    pulledSourceWordFibreBlock_entry_data (F := F) psi n j l
      rowColours colColours r c hentry
  have hwords := coefficient_visibleWords_eq_of_source (F := F) n r c hsource
  have hrowBra : visibleWordList (F := F) (List.ofFn r.2) =
      List.ofFn rowColours := by
    rw [visibleWordList_ofFn]
    exact congrArg List.ofFn hrowCoeff
  have hcolBra : visibleWordList (F := F) (List.ofFn c.2) =
      List.ofFn colColours := by
    rw [visibleWordList_ofFn]
    exact congrArg List.ofFn hcolCoeff
  have htailB : (List.ofFn rowColours).tail.count .B = j := by
    rw [← hrowBra, ← hwords.1]
    change packetBCount F
      (fun i => (rectangularCircuitPerm F (n + 1) (r.1, c.1)).2 i.succ) = j at hcountB
    rw [packetBCount_eq_visibleWordList_count,
      visibleWordList_ofFn_succ,
      visibleWordList_rectangularCircuitPerm_snd] at hcountB
    exact hcountB
  have hcolA : (List.ofFn colColours).count .A = l := by
    rw [← hcolBra, ← hwords.2]
    change packetACount F
      (rectangularCircuitPerm F (n + 1) (r.1, c.1)).1 = l at hcountA
    rw [packetACount_eq_visibleWordList_count,
      visibleWordList_rectangularCircuitPerm_fst] at hcountA
    exact hcountA
  have hsource' : rectangularSource F (succPNat n)
      (rectangularCircuitPerm F (n + 1) (r.1, c.1))
      (rectangularCircuitPerm F (n + 1) (r.2, c.2)) ≠ 0 := by
    simpa [coreSourcePairEquiv, coeffOperatorPairEquiv] using hsource
  have hmarked :=
    ((rectangularSource_ne_zero_iff F (succPNat n) _ _).mp hsource').2.2.2
  have hmarkedColour := congrArg (siteColour F) hmarked
  have hheadSite : siteColour F (r.2 0) = .B := by
    rw [siteColour_rectangularCircuitPerm_snd] at hmarkedColour
    simpa [siteColour] using hmarkedColour
  have hrowHead : .B ∈ (List.ofFn rowColours).head? := by
    rw [← hrowBra]
    simp [visibleWordList, List.ofFn_succ, hheadSite]
  have hcons : .B :: (List.ofFn rowColours).tail = List.ofFn rowColours :=
    List.cons_head?_tail hrowHead
  have hcountBFull : (List.ofFn rowColours).count .B = j + 1 := by
    calc
      (List.ofFn rowColours).count .B =
          (.B :: (List.ofFn rowColours).tail).count .B := by rw [hcons]
      _ = (List.ofFn rowColours).tail.count .B + 1 := by simp
      _ = j + 1 := by rw [htailB]
  have htotal := count_A_add_count_B (List.ofFn rowColours)
  have hrowLen : (List.ofFn rowColours).length = n + 1 := by simp
  refine ⟨hsource, ?_, hrowHead, hcolA⟩
  omega

theorem positiveSpectatorBlock_normal_words (psi : AddChar F ℂ)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b))
    (hrowA : (List.ofFn rowColours).count .A = a)
    (hcolA : (List.ofFn colColours).count .A = a + s + 1)
    (hblock : positiveSpectatorBlock (F := F) psi a b s
      rowColours colColours pre post ≠ 0) :
    visibleWordList (F := F) (List.ofFn pre) = normalColourWord a b ∧
      visibleWordList (F := F) (List.ofFn post) = normalColourWord a b := by
  obtain ⟨r, c, hentry⟩ := exists_matrix_entry_ne_zero _ hblock
  have hraw := hentry
  unfold positiveSpectatorBlock at hraw
  unfold twoSidedMeasurementBlock rowMeasurementBlock columnMeasurementBlock at hraw
  split_ifs at hraw with hpreLabel hpostLabel
  · have hfibre : pulledSourceWordFibreBlock (F := F) psi (a + b + s)
        (b + s) (a + s + 1) rowColours colColours r c ≠ 0 := hraw
    obtain ⟨hrowCoeff, hcolCoeff, hsector⟩ :=
      pulledSourceWordFibreBlock_entry_data (F := F) psi (a + b + s)
        (b + s) (a + s + 1) rowColours colColours r c hfibre
    let rowWord := List.ofFn rowColours
    let colWord := List.ofFn colColours
    let n := a + b + s
    let wL := colourRearrangementWord (F := F) rowWord
      (positiveMiddleLeftWord a b s)
    let wR := colourRearrangementWord (F := F) colWord
      (positiveMiddleRightWord a b s)
    let u : RectBasis F (n + 1) := (r.1, c.1)
    let midU := boundaryLocalPerm (F := F) n wL wR u
    have hwords := coefficient_visibleWords_eq_of_source (F := F) n r c (by
      simpa [n] using hsector.1)
    have hrowBra : visibleWordList (F := F) (List.ofFn r.2) = rowWord := by
      rw [visibleWordList_ofFn]
      exact congrArg List.ofFn (by simpa [n, rowWord] using hrowCoeff)
    have hcolBra : visibleWordList (F := F) (List.ofFn c.2) = colWord := by
      rw [visibleWordList_ofFn]
      exact congrArg List.ofFn (by simpa [n, colWord] using hcolCoeff)
    have hrowKet : visibleWordList (F := F) (List.ofFn r.1) = rowWord :=
      hwords.1.trans hrowBra
    have hcolKet : visibleWordList (F := F) (List.ofFn c.1) = colWord :=
      hwords.2.trans hcolBra
    have hrowA' : rowWord.count .A = a := by
      simpa only [rowWord] using hrowA
    have hcolA' : colWord.count .A = a + s + 1 := by
      simpa only [colWord] using hcolA
    have hrowTargetLen : rowWord.length =
        (positiveMiddleLeftWord a b s).length := by
      simp [rowWord, positiveMiddleLeftWord]
      omega
    have hrowTargetA : rowWord.count .A =
        (positiveMiddleLeftWord a b s).count .A := by
      simp [positiveMiddleLeftWord, List.count_replicate, hrowA']
    have hcolTargetLen : colWord.length =
        (positiveMiddleRightWord a b s).length := by
      simp [colWord, positiveMiddleRightWord]
      omega
    have hcolTargetA : colWord.count .A =
        (positiveMiddleRightWord a b s).count .A := by
      simp [positiveMiddleRightWord, List.count_replicate, hcolA']
      omega
    have hmidLeft : visibleWordList (F := F) (List.ofFn midU.1) =
        positiveMiddleLeftWord a b s := by
      dsimp [midU, boundaryLocalPerm]
      rw [ofFn_spatialCircuitPerm]
      exact visibleWordList_colourRearrangementWord rowWord _ _ hrowKet
        hrowTargetLen hrowTargetA
    have hmidRight : visibleWordList (F := F) (List.ofFn midU.2) =
        positiveMiddleRightWord a b s := by
      dsimp [midU, boundaryLocalPerm]
      rw [ofFn_spatialCircuitPerm]
      exact visibleWordList_colourRearrangementWord colWord _ _ hcolKet
        hcolTargetLen hcolTargetA
    apply spectator_visibleWords_of_middle (F := F) a b s pre post midU
      (List.replicate (s + 1) .B) (List.replicate (s + 1) .A)
      (by simp) (by simp)
    · simpa [positiveMiddleLeftWord] using hmidLeft
    · simpa [positiveMiddleRightWord] using hmidRight
    · change packetPrePart (F := F) (a + b) s
          (spatialCircuitPerm F (n + 1) wL r.1) = pre at hpreLabel
      simpa [midU, u, n, boundaryLocalPerm] using hpreLabel
    · change packetPostPart (F := F) (a + b) s
          (spatialCircuitPerm F (n + 1) wR c.1) = post at hpostLabel
      simpa [midU, u, n, boundaryLocalPerm] using hpostLabel
  all_goals exact (hraw rfl).elim

theorem negativeSpectatorBlock_normal_words (psi : AddChar F ℂ)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (pre post : PacketBasis F (a + b))
    (hrowA : (List.ofFn rowColours).count .A = a + s)
    (hcolA : (List.ofFn colColours).count .A = a)
    (hblock : negativeSpectatorBlock (F := F) psi a b s
      rowColours colColours pre post ≠ 0) :
    visibleWordList (F := F) (List.ofFn pre) = normalColourWord a b ∧
      visibleWordList (F := F) (List.ofFn post) = normalColourWord a b := by
  obtain ⟨r, c, hentry⟩ := exists_matrix_entry_ne_zero _ hblock
  have hraw := hentry
  unfold negativeSpectatorBlock at hraw
  unfold twoSidedMeasurementBlock rowMeasurementBlock columnMeasurementBlock at hraw
  split_ifs at hraw with hpreLabel hpostLabel
  · have hfibre : pulledSourceWordFibreBlock (F := F) psi (a + b + s)
        b a rowColours colColours r c ≠ 0 := hraw
    obtain ⟨hrowCoeff, hcolCoeff, hsector⟩ :=
      pulledSourceWordFibreBlock_entry_data (F := F) psi (a + b + s)
        b a rowColours colColours r c hfibre
    let rowWord := List.ofFn rowColours
    let colWord := List.ofFn colColours
    let n := a + b + s
    let wL := colourRearrangementWord (F := F) rowWord
      (negativeMiddleLeftWord a b s)
    let wR := colourRearrangementWord (F := F) colWord
      (negativeMiddleRightWord a b s)
    let u : RectBasis F (n + 1) := (r.1, c.1)
    let midU := boundaryLocalPerm (F := F) n wL wR u
    have hwords := coefficient_visibleWords_eq_of_source (F := F) n r c (by
      simpa [n] using hsector.1)
    have hrowBra : visibleWordList (F := F) (List.ofFn r.2) = rowWord := by
      rw [visibleWordList_ofFn]
      exact congrArg List.ofFn (by simpa [n, rowWord] using hrowCoeff)
    have hcolBra : visibleWordList (F := F) (List.ofFn c.2) = colWord := by
      rw [visibleWordList_ofFn]
      exact congrArg List.ofFn (by simpa [n, colWord] using hcolCoeff)
    have hrowKet : visibleWordList (F := F) (List.ofFn r.1) = rowWord :=
      hwords.1.trans hrowBra
    have hcolKet : visibleWordList (F := F) (List.ofFn c.1) = colWord :=
      hwords.2.trans hcolBra
    have hrowA' : rowWord.count .A = a + s := by
      simpa only [rowWord] using hrowA
    have hcolA' : colWord.count .A = a := by
      simpa only [colWord] using hcolA
    have hrowTargetLen : rowWord.length =
        (negativeMiddleLeftWord a b s).length := by
      simp [rowWord, negativeMiddleLeftWord]
      omega
    have hrowTargetA : rowWord.count .A =
        (negativeMiddleLeftWord a b s).count .A := by
      simp [negativeMiddleLeftWord, List.count_replicate, hrowA']
    have hcolTargetLen : colWord.length =
        (negativeMiddleRightWord a b s).length := by
      simp [colWord, negativeMiddleRightWord]
      omega
    have hcolTargetA : colWord.count .A =
        (negativeMiddleRightWord a b s).count .A := by
      simp [negativeMiddleRightWord, List.count_replicate, hcolA']
    have hmidLeft : visibleWordList (F := F) (List.ofFn midU.1) =
        negativeMiddleLeftWord a b s := by
      dsimp [midU, boundaryLocalPerm]
      rw [ofFn_spatialCircuitPerm]
      exact visibleWordList_colourRearrangementWord rowWord _ _ hrowKet
        hrowTargetLen hrowTargetA
    have hmidRight : visibleWordList (F := F) (List.ofFn midU.2) =
        negativeMiddleRightWord a b s := by
      dsimp [midU, boundaryLocalPerm]
      rw [ofFn_spatialCircuitPerm]
      exact visibleWordList_colourRearrangementWord colWord _ _ hcolKet
        hcolTargetLen hcolTargetA
    apply spectator_visibleWords_of_middle (F := F) a b s pre post midU
      (.B :: List.replicate s .A) (List.replicate (s + 1) .B)
      (by simp) (by simp)
    · simpa [negativeMiddleLeftWord] using hmidLeft
    · simpa [negativeMiddleRightWord] using hmidRight
    · change packetPrePart (F := F) (a + b) s
          (spatialCircuitPerm F (n + 1) wL r.1) = pre at hpreLabel
      simpa [midU, u, n, boundaryLocalPerm] using hpreLabel
    · change packetPostPart (F := F) (a + b) s
          (spatialCircuitPerm F (n + 1) wR c.1) = post at hpostLabel
      simpa [midU, u, n, boundaryLocalPerm] using hpostLabel
  all_goals exact (hraw rfl).elim

/-! ## Entropy of a complete visible-word fibre -/

theorem positiveWordFibre_vonNeumannEntropy_lower
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (hodd : ringChar F ≠ 2)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (hfibre : pulledSourceWordFibreBlock (F := F) psi (a + b + s)
      (b + s) (a + s + 1) rowColours colColours ≠ 0) :
    (s : ℝ) * Real.log (Fintype.card F) ≤
      vonNeumannEntropy
        (pulledSourceWordFibreBlock (F := F) psi (a + b + s)
          (b + s) (a + s + 1) rowColours colColours) := by
  obtain ⟨r, c, hentry⟩ := exists_matrix_entry_ne_zero _ hfibre
  obtain ⟨_, hrowAraw, hrowHead, hcolA⟩ :=
    pulledSourceWordFibreBlock_word_properties (F := F) psi
      (a + b + s) (b + s) (a + s + 1)
      rowColours colColours r c hentry
  have hrowA : (List.ofFn rowColours).count .A = a := by omega
  apply le_vonNeumannEntropy_of_twoSidedMeasurement
    (preSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) (List.ofFn rowColours)
        (positiveMiddleLeftWord a b s)))
    (postSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) (List.ofFn colColours)
        (positiveMiddleRightWord a b s)))
    (pulledSourceWordFibreBlock (F := F) psi (a + b + s)
      (b + s) (a + s + 1) rowColours colColours)
    hfibre ((s : ℝ) * Real.log (Fintype.card F))
  intro pre post hblock
  change positiveSpectatorBlock (F := F) psi a b s
    rowColours colColours pre post ≠ 0 at hblock
  obtain ⟨hpre, hpost⟩ := positiveSpectatorBlock_normal_words (F := F)
    psi a b s rowColours colColours pre post hrowA hcolA hblock
  change (s : ℝ) * Real.log (Fintype.card F) ≤
    vonNeumannEntropy (positiveSpectatorBlock (F := F) psi a b s
      rowColours colColours pre post)
  rw [positiveSpectatorBlock_vonNeumannEntropy (F := F)
    psi hpsi hodd a b s rowColours colColours pre post
    hpre hpost hrowA hrowHead hcolA]

theorem negativeWordFibre_vonNeumannEntropy_lower
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (hodd : ringChar F ≠ 2)
    (a b s : ℕ)
    (rowColours colColours : Fin (a + b + s + 1) → VisibleColour)
    (hfibre : pulledSourceWordFibreBlock (F := F) psi (a + b + s)
      b a rowColours colColours ≠ 0) :
    (s : ℝ) * Real.log (Fintype.card F) ≤
      vonNeumannEntropy
        (pulledSourceWordFibreBlock (F := F) psi (a + b + s)
          b a rowColours colColours) := by
  obtain ⟨r, c, hentry⟩ := exists_matrix_entry_ne_zero _ hfibre
  obtain ⟨_, hrowAraw, hrowHead, hcolA⟩ :=
    pulledSourceWordFibreBlock_word_properties (F := F) psi
      (a + b + s) b a rowColours colColours r c hentry
  have hrowA : (List.ofFn rowColours).count .A = a + s := by omega
  apply le_vonNeumannEntropy_of_twoSidedMeasurement
    (preSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) (List.ofFn rowColours)
        (negativeMiddleLeftWord a b s)))
    (postSpectatorLabel (F := F) (a + b) s
      (colourRearrangementWord (F := F) (List.ofFn colColours)
        (negativeMiddleRightWord a b s)))
    (pulledSourceWordFibreBlock (F := F) psi (a + b + s)
      b a rowColours colColours)
    hfibre ((s : ℝ) * Real.log (Fintype.card F))
  intro pre post hblock
  change negativeSpectatorBlock (F := F) psi a b s
    rowColours colColours pre post ≠ 0 at hblock
  obtain ⟨hpre, hpost⟩ := negativeSpectatorBlock_normal_words (F := F)
    psi a b s rowColours colColours pre post hrowA hcolA hblock
  change (s : ℝ) * Real.log (Fintype.card F) ≤
    vonNeumannEntropy (negativeSpectatorBlock (F := F) psi a b s
      rowColours colColours pre post)
  rw [negativeSpectatorBlock_vonNeumannEntropy (F := F)
    psi hpsi hodd a b s rowColours colColours pre post
    hpre hpost hrowA hrowHead hcolA]

theorem imbEntropy_le_pulledSourceWordFibreBlock
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (hodd : ringChar F ≠ 2)
    (n j l : ℕ) (hj : j < n + 1) (hl : l < n + 2)
    (rowColours colColours : Fin (n + 1) → VisibleColour)
    (hfibre : pulledSourceWordFibreBlock (F := F) psi n j l
      rowColours colColours ≠ 0) :
    imbEntropy (Fintype.card F) ((j : ℤ) + l + 1 - (n + 1)) ≤
      vonNeumannEntropy
        (pulledSourceWordFibreBlock (F := F) psi n j l
          rowColours colColours) := by
  by_cases hpos : n < j + l
  · obtain ⟨a, b, s, rfl, rfl, rfl⟩ : ∃ a b s : ℕ,
        n = a + b + s ∧ j = b + s ∧ l = a + s + 1 := by
      refine ⟨n - j, n + 1 - l, j + l - n - 1, ?_, ?_, ?_⟩ <;> omega
    have hcore := positiveWordFibre_vonNeumannEntropy_lower (F := F)
      psi hpsi hodd a b s rowColours colColours hfibre
    have himb : imbEntropy (Fintype.card F)
        (((b + s : ℕ) : ℤ) + ((a + s + 1 : ℕ) : ℤ) + 1 -
          ((a + b + s : ℕ) + 1)) =
        (s : ℝ) * Real.log (Fintype.card F) := by
      rw [imbEntropy, gImb_of_pos (by omega)]
      push_cast
      ring
    rw [himb]
    exact hcore
  · have hnonpos : j + l ≤ n := by omega
    obtain ⟨a, b, s, rfl, rfl, rfl⟩ : ∃ a b s : ℕ,
        n = a + b + s ∧ j = b ∧ l = a := by
      refine ⟨l, j, n - j - l, ?_, rfl, rfl⟩
      omega
    have hcore := negativeWordFibre_vonNeumannEntropy_lower (F := F)
      psi hpsi hodd l j s rowColours colColours hfibre
    have himb : imbEntropy (Fintype.card F)
        (((j : ℕ) : ℤ) + ((l : ℕ) : ℤ) + 1 -
          ((l + j + s : ℕ) + 1)) =
        (s : ℝ) * Real.log (Fintype.card F) := by
      rw [imbEntropy, gImb_of_nonpos (by omega)]
      push_cast
      ring
    rw [himb]
    exact hcore

/-! ## Count sectors and the square-root lower bound -/

theorem pulledSourceSectorBlock_imbEntropy_lower
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (hodd : ringChar F ≠ 2)
    (n j l : ℕ) (hj : j < n + 1) (hl : l < n + 2) :
    imbEntropy (Fintype.card F) ((j : ℤ) + l + 1 - (n + 1)) ≤
      vonNeumannEntropy (pulledSourceSectorBlock F psi n j l) := by
  apply imbEntropy_le_pulledSourceSectorBlock_of_wordFibres
    (F := F) psi n j l hj hl
  intro rowColours colColours hfibre
  exact imbEntropy_le_pulledSourceWordFibreBlock (F := F)
    psi hpsi hodd n j l hj hl rowColours colColours hfibre

/-- The fully discharged square-root lower bound for the rectangular core.
All branch hypotheses in `rectangularVonNeumann_sqrt_lower_bound_of_pulledSource`
are supplied by the visible-word fibre reduction above. -/
theorem rectangularVonNeumann_sqrt_lower_bound_proved
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (hodd : ringChar F ≠ 2)
    (n : ℕ) :
    Real.log (Fintype.card F) *
          Real.sqrt (((n + 1 : ℕ) : ℝ) / Real.pi) -
        (3 / 2) * Real.log (Fintype.card F) ≤
      rectangularVonNeumannEntropy F psi (succPNat n) := by
  apply rectangularVonNeumann_sqrt_lower_bound_of_pulledSource
    (F := F) psi _ n
  intro m j l hj hl
  exact pulledSourceSectorBlock_imbEntropy_lower (F := F)
    psi hpsi hodd m j l hj hl

end SqrtOpEnt
