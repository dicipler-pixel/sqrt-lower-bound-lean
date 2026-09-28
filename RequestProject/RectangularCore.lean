import RequestProject.Gate

/-!
# The finite rectangular core

This file starts the formalization at the boundary allowed by Lemma 4.1 of the
manuscript.  No infinite brickwork circuit is introduced.  Instead we define the
finite block-transposition circuit `Wₜ`, the one-site source `Sₜ`, and

`Xₜ = Wₜᴴ * Sₜ * Wₜ`.

The last part of the file reshapes an operator into the coefficient matrix for
the bipartition between the two length-`t` packets.  Consequently
`rectCoeff (rectangularCore ...)` is the concrete matrix whose normalized Gram
matrix carries the operator-Schmidt probabilities studied in Sections 5--8.
-/

namespace SqrtOpEnt

open Matrix

/-! A reusable unitary criterion for the monomial matrices from `Gate.lean`. -/

section MonomialUnitary

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

theorem mono_mem_unitary (σ : Equiv.Perm Y) (φ : Y → ℂ)
    (hφ : ∀ v, star (φ v) * φ v = 1) : mono σ φ ∈ unitary (Matrix Y Y ℂ) := by
  constructor
  · change (mono σ φ)ᴴ * mono σ φ = 1
    rw [mono_conjTranspose, mono_mul]
    refine mono_eq_one (fun v => by simp) (fun v => ?_)
    simpa using hφ v
  · change mono σ φ * (mono σ φ)ᴴ = 1
    rw [mono_conjTranspose, mono_mul]
    refine mono_eq_one (fun v => by simp) (fun v => ?_)
    simpa [mul_comm] using hφ (σ.symm v)

/-- Matrix entries of a conjugated operator under a monomial unitary. -/
theorem mono_conjugate_apply (σ : Equiv.Perm Y) (φ : Y → ℂ)
    (S : Matrix Y Y ℂ) (u v : Y) :
    ((mono σ φ)ᴴ * S * mono σ φ) u v =
      star (φ u) * S (σ u) (σ v) * φ v := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ v)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (σ u)]
    · simp [mono, mul_assoc]
    · intro a ha hane
      simp [mono, hane]
    · simp
  · intro b hb hbne
    simp [mono, hbne]
  · simp

end MonomialUnitary

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-! ## Packet and spatial bases -/

/-- Basis configurations of a packet containing `t` folded sites. -/
abbrev PacketBasis (t : ℕ) := Fin t → Vq F

/-- The two packet factors on the two sides of the rectangular cut. -/
abbrev RectBasis (t : ℕ) := PacketBasis F t × PacketBasis F t

/-- Spatial basis used while evaluating the adjacent-gate network. -/
abbrev SpatialBasis (n : ℕ) := Fin n → Vq F

/-- The two visible colours, forgetting the finite-field label. -/
inductive VisibleColour
  | A
  | B
  deriving DecidableEq, Fintype

/-- Colour of a local basis label. -/
def siteColour : Vq F → VisibleColour
  | Sum.inl _ => .A
  | Sum.inr _ => .B

omit [Fintype F] [DecidableEq F] in
/-- On colours, every triangular crossing is just a swap. -/
@[simp] theorem siteColour_gateFun_fst (u v : Vq F) :
    siteColour F (gateFun F (u, v)).1 = siteColour F v := by
  rcases u <;> rcases v <;> rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem siteColour_gateFun_snd (u v : Vq F) :
    siteColour F (gateFun F (u, v)).2 = siteColour F u := by
  rcases u <;> rcases v <;> rfl

/-- Concatenate the two packet configurations into their spatial ordering. -/
def packetsToSpatial {t : ℕ} : RectBasis F t ≃ SpatialBasis F (t + t) :=
  Fin.appendEquiv t t

/-! ## A gate at adjacent spatial positions -/

/-- Replace adjacent entries `i,i+1` by the output of the triangular gate.
For an out-of-range `i` this is defined to be the identity; the crossing
schedule below is proved to contain only in-range indices. -/
def gateAtFun (n i : ℕ) (v : SpatialBasis F n) : SpatialBasis F n := by
  classical
  by_cases h : i + 1 < n
  · let il : Fin n := ⟨i, Nat.lt_of_succ_lt h⟩
    let ir : Fin n := ⟨i + 1, h⟩
    let p := gateFun F (v il, v ir)
    exact Function.update (Function.update v il p.1) ir p.2
  · exact v

omit [Fintype F] [DecidableEq F] in
/-- The local support update is an involution. -/
theorem gateAtFun_involutive (n i : ℕ) : Function.Involutive (gateAtFun F n i) := by
  classical
  intro v
  unfold gateAtFun
  split_ifs with h
  · let il : Fin n := ⟨i, Nat.lt_of_succ_lt h⟩
    let ir : Fin n := ⟨i + 1, h⟩
    have hilr : il ≠ ir := by
      intro heq
      have := congrArg Fin.val heq
      simp [il, ir] at this
    have hril : ir ≠ il := Ne.symm hilr
    funext j
    by_cases hjr : j = ir
    · subst j
      simp [il, ir, hilr, gateFun_involutive F (v il, v ir)]
    · by_cases hjl : j = il
      · subst j
        simp [il, ir, hilr, gateFun_involutive F (v il, v ir)]
      · simp [il, ir, hjl, hjr, gateFun_involutive F (v il, v ir)]
  · rfl

omit [Fintype F] [DecidableEq F] in
/-- At a valid crossing, the colour on the left comes from the right input. -/
theorem siteColour_gateAtFun_left (n i : ℕ) (h : i + 1 < n)
    (v : SpatialBasis F n) :
    siteColour F (gateAtFun F n i v ⟨i, Nat.lt_of_succ_lt h⟩) =
      siteColour F (v ⟨i + 1, h⟩) := by
  classical
  unfold gateAtFun
  rw [dif_pos h]
  simp [siteColour_gateFun_fst]

omit [Fintype F] [DecidableEq F] in
/-- At a valid crossing, the colour on the right comes from the left input. -/
theorem siteColour_gateAtFun_right (n i : ℕ) (h : i + 1 < n)
    (v : SpatialBasis F n) :
    siteColour F (gateAtFun F n i v ⟨i + 1, h⟩) =
      siteColour F (v ⟨i, Nat.lt_of_succ_lt h⟩) := by
  classical
  unfold gateAtFun
  rw [dif_pos h]
  have hne : (⟨i, Nat.lt_of_succ_lt h⟩ : Fin n) ≠ ⟨i + 1, h⟩ := by
    intro heq
    have := congrArg Fin.val heq
    simp at this
  simp [siteColour_gateFun_snd]

omit [Fintype F] [DecidableEq F] in
/-- A valid crossing leaves every other site's colour unchanged. -/
theorem siteColour_gateAtFun_of_ne (n i : ℕ) (h : i + 1 < n)
    (v : SpatialBasis F n) (j : Fin n)
    (hjl : j ≠ ⟨i, Nat.lt_of_succ_lt h⟩) (hjr : j ≠ ⟨i + 1, h⟩) :
    siteColour F (gateAtFun F n i v j) = siteColour F (v j) := by
  classical
  unfold gateAtFun
  rw [dif_pos h]
  simp [hjl, hjr]

/-- Pure adjacent swap on a finite tuple, totalized by the identity outside its range. -/
def swapAtFun {α : Type*} (n i : ℕ) (v : Fin n → α) : Fin n → α := by
  classical
  by_cases h : i + 1 < n
  · let il : Fin n := ⟨i, Nat.lt_of_succ_lt h⟩
    let ir : Fin n := ⟨i + 1, h⟩
    exact Function.update (Function.update v il (v ir)) ir (v il)
  · exact v

omit [Fintype F] [DecidableEq F] in
/-- The full colour configuration of a lifted triangular gate is the corresponding
pure adjacent swap. -/
theorem colour_gateAtFun (n i : ℕ) (v : SpatialBasis F n) :
    (fun j => siteColour F (gateAtFun F n i v j)) =
      swapAtFun n i (fun j => siteColour F (v j)) := by
  classical
  by_cases h : i + 1 < n
  · funext j
    by_cases hjl : j = ⟨i, Nat.lt_of_succ_lt h⟩
    · subst j
      rw [siteColour_gateAtFun_left F n i h]
      simp [swapAtFun, h]
    · by_cases hjr : j = ⟨i + 1, h⟩
      · subst j
        rw [siteColour_gateAtFun_right F n i h]
        simp [swapAtFun, h]
      · rw [siteColour_gateAtFun_of_ne F n i h v j hjl hjr]
        simp [swapAtFun, h, hjl, hjr]
  · simp [gateAtFun, swapAtFun, h]

/-- The support permutation of a gate at positions `i,i+1`. -/
def gateAtPerm (n i : ℕ) : Equiv.Perm (SpatialBasis F n) :=
  Function.Involutive.toPerm _ (gateAtFun_involutive F n i)

/-- Phase contributed by the adjacent crossing. -/
noncomputable def gateAtPhase (ψ : AddChar F ℂ) (n i : ℕ)
    (v : SpatialBasis F n) : ℂ := by
  by_cases h : i + 1 < n
  · exact gatePhase F ψ (v ⟨i, Nat.lt_of_succ_lt h⟩, v ⟨i + 1, h⟩)
  · exact 1

/-- The triangular gate lifted to positions `i,i+1` of an `n`-site basis. -/
noncomputable def gateAtMat (ψ : AddChar F ℂ) (n i : ℕ) :
    Matrix (SpatialBasis F n) (SpatialBasis F n) ℂ :=
  mono (gateAtPerm F n i) (gateAtPhase F ψ n i)

omit [DecidableEq F] in
theorem gateAtPhase_star_mul_self (ψ : AddChar F ℂ) (n i : ℕ)
    (v : SpatialBasis F n) :
    star (gateAtPhase F ψ n i v) * gateAtPhase F ψ n i v = 1 := by
  unfold gateAtPhase
  split_ifs with h
  · obtain ⟨x, y⟩ := (v ⟨i, Nat.lt_of_succ_lt h⟩, v ⟨i + 1, h⟩)
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [gatePhase, star_one, one_mul]
    · have hc : star (ψ (a * b ^ 2)) = (ψ (a * b ^ 2))⁻¹ := by
        simpa only [starRingEnd_apply] using (AddChar.inv_apply_eq_conj ψ (a * b ^ 2)).symm
      rw [hc]
      exact inv_mul_cancel₀ (AddChar.val_isUnit ψ _).ne_zero
    · have hc : star (ψ (-((a - b) * b ^ 2))) = (ψ (-((a - b) * b ^ 2)))⁻¹ := by
        simpa only [starRingEnd_apply] using
          (AddChar.inv_apply_eq_conj ψ (-((a - b) * b ^ 2))).symm
      rw [hc]
      exact inv_mul_cancel₀ (AddChar.val_isUnit ψ _).ne_zero
  · simp

/-- Every lifted adjacent gate is unitary. -/
theorem gateAtMat_mem_unitary (ψ : AddChar F ℂ) (n i : ℕ) :
    gateAtMat F ψ n i ∈ unitary (Matrix (SpatialBasis F n) (SpatialBasis F n) ℂ) := by
  exact mono_mem_unitary _ _ (gateAtPhase_star_mul_self F ψ n i)

/-! ## The block-transposition network -/

/-- Crossing word for transposing two packets of length `t`.

For each right-packet strand `b`, the positions `b+t-1,...,b` move that strand
leftward across all `t` strands of the left packet.  For `t=2` the word is
`[1,0,2,1]`. -/
def crossingSchedule (t : ℕ) : List ℕ :=
  (List.range t).flatMap fun b => (List.range t).reverse.map fun j => b + j

@[simp] theorem crossingSchedule_length (t : ℕ) :
    (crossingSchedule t).length = t * t := by
  simp [crossingSchedule]

/-- Every crossing in the block-transposition word addresses two valid sites. -/
theorem mem_crossingSchedule_lt {t i : ℕ} (hi : i ∈ crossingSchedule t) :
    i + 1 < t + t := by
  simp only [crossingSchedule, List.mem_flatMap, List.mem_map, List.mem_reverse,
    List.mem_range] at hi
  obtain ⟨b, hb, j, hj, rfl⟩ := hi
  omega

/-- Evaluate a word of adjacent gates.  The accumulator convention makes the
head of the list act first on a column vector. -/
noncomputable def spatialCircuit (ψ : AddChar F ℂ) (n : ℕ) (word : List ℕ) :
    Matrix (SpatialBasis F n) (SpatialBasis F n) ℂ :=
  match word with
  | [] => 1
  | i :: tail => spatialCircuit ψ n tail * gateAtMat F ψ n i

/-- Support permutation of an adjacent-gate word. -/
def spatialCircuitPerm (n : ℕ) : List ℕ → Equiv.Perm (SpatialBasis F n)
  | [] => Equiv.refl _
  | i :: tail => (gateAtPerm F n i).trans (spatialCircuitPerm n tail)

/-- Accumulated phase of an adjacent-gate word. -/
noncomputable def spatialCircuitPhase (ψ : AddChar F ℂ) (n : ℕ) :
    List ℕ → SpatialBasis F n → ℂ
  | [], _ => 1
  | i :: tail, v =>
      spatialCircuitPhase ψ n tail (gateAtPerm F n i v) * gateAtPhase F ψ n i v

/-- Pure colour evolution of an adjacent-swap word. -/
def colourCircuit (n : ℕ) : List ℕ → (Fin n → VisibleColour) → (Fin n → VisibleColour)
  | [], c => c
  | i :: tail, c => colourCircuit n tail (swapAtFun n i c)

omit [Fintype F] [DecidableEq F] in
/-- The support of the full triangular circuit acts on colours by `colourCircuit`. -/
theorem colour_spatialCircuitPerm (n : ℕ) (word : List ℕ) (v : SpatialBasis F n) :
    (fun j => siteColour F (spatialCircuitPerm F n word v j)) =
      colourCircuit n word (fun j => siteColour F (v j)) := by
  induction word generalizing v with
  | nil => rfl
  | cons i tail ih =>
      simp only [spatialCircuitPerm, Equiv.trans_apply, colourCircuit]
      rw [ih]
      congr 1
      exact colour_gateAtFun F n i v

/-- A word of triangular gates is itself a single monomial matrix, with the
explicit support and accumulated phase above. -/
theorem spatialCircuit_eq_mono (ψ : AddChar F ℂ) (n : ℕ) (word : List ℕ) :
    spatialCircuit F ψ n word =
      mono (spatialCircuitPerm F n word) (spatialCircuitPhase F ψ n word) := by
  induction word with
  | nil =>
      simp only [spatialCircuit, spatialCircuitPerm, spatialCircuitPhase]
      symm
      exact mono_eq_one (fun _ => rfl) (fun _ => rfl)
  | cons i tail ih =>
      simp only [spatialCircuit, spatialCircuitPerm, spatialCircuitPhase, ih]
      rw [gateAtMat, mono_mul]

omit [DecidableEq F] in
/-- Every accumulated circuit phase has unit modulus. -/
theorem spatialCircuitPhase_star_mul_self (ψ : AddChar F ℂ) (n : ℕ)
    (word : List ℕ) (v : SpatialBasis F n) :
    star (spatialCircuitPhase F ψ n word v) * spatialCircuitPhase F ψ n word v = 1 := by
  induction word generalizing v with
  | nil => simp [spatialCircuitPhase]
  | cons i tail ih =>
      simp only [spatialCircuitPhase]
      rw [StarMul.star_mul]
      have htail := ih (gateAtPerm F n i v)
      have hgate := gateAtPhase_star_mul_self F ψ n i v
      calc
        (star (gateAtPhase F ψ n i v) *
            star (spatialCircuitPhase F ψ n tail (gateAtPerm F n i v))) *
            (spatialCircuitPhase F ψ n tail (gateAtPerm F n i v) *
              gateAtPhase F ψ n i v) =
          (star (spatialCircuitPhase F ψ n tail (gateAtPerm F n i v)) *
            spatialCircuitPhase F ψ n tail (gateAtPerm F n i v)) *
              (star (gateAtPhase F ψ n i v) * gateAtPhase F ψ n i v) := by ring
        _ = 1 := by rw [htail, hgate, one_mul]

/-- A circuit made from any word of adjacent gates is unitary. -/
theorem spatialCircuit_mem_unitary (ψ : AddChar F ℂ) (n : ℕ) (word : List ℕ) :
    spatialCircuit F ψ n word ∈
      unitary (Matrix (SpatialBasis F n) (SpatialBasis F n) ℂ) := by
  induction word with
  | nil => exact Submonoid.one_mem _
  | cons i tail ih =>
      exact Submonoid.mul_mem _ ih (gateAtMat_mem_unitary F ψ n i)

/-- Support permutation of the rectangle after regrouping its sites into two packets. -/
def rectangularCircuitPerm (t : ℕ) : Equiv.Perm (RectBasis F t) :=
  (packetsToSpatial F).trans
    ((spatialCircuitPerm F (t + t) (crossingSchedule t)).trans (packetsToSpatial F).symm)

/-- Accumulated rectangle phase in packet coordinates. -/
noncomputable def rectangularCircuitPhase (ψ : AddChar F ℂ) (t : ℕ)
    (v : RectBasis F t) : ℂ :=
  spatialCircuitPhase F ψ (t + t) (crossingSchedule t) (packetsToSpatial F v)

omit [DecidableEq F] in
/-- The accumulated rectangle phase has unit modulus. -/
theorem rectangularCircuitPhase_star_mul_self (ψ : AddChar F ℂ) (t : ℕ)
    (v : RectBasis F t) :
    star (rectangularCircuitPhase F ψ t v) * rectangularCircuitPhase F ψ t v = 1 :=
  spatialCircuitPhase_star_mul_self F ψ _ _ _

omit [DecidableEq F] in
/-- Unit-modulus reformulation of `rectangularCircuitPhase_star_mul_self`. -/
theorem norm_rectangularCircuitPhase (ψ : AddChar F ℂ) (t : ℕ)
    (v : RectBasis F t) : ‖rectangularCircuitPhase F ψ t v‖ = 1 := by
  have h := congrArg norm (rectangularCircuitPhase_star_mul_self F ψ t v)
  simp only [norm_mul, norm_star, norm_one] at h
  nlinarith [norm_nonneg (rectangularCircuitPhase F ψ t v)]

/-- `Wₜ`, the `t × t` crossing rectangle which transposes the two packets. -/
noncomputable def rectangularCircuit (ψ : AddChar F ℂ) (t : ℕ) :
    Matrix (RectBasis F t) (RectBasis F t) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (packetsToSpatial F).symm
    (spatialCircuit F ψ (t + t) (crossingSchedule t))

/-- The complete rectangle is a concrete monomial matrix in packet coordinates. -/
theorem rectangularCircuit_eq_mono (ψ : AddChar F ℂ) (t : ℕ) :
    rectangularCircuit F ψ t =
      mono (rectangularCircuitPerm F t) (rectangularCircuitPhase F ψ t) := by
  rw [rectangularCircuit, spatialCircuit_eq_mono]
  ext u v
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix,
    mono, rectangularCircuitPerm, rectangularCircuitPhase]
  split_ifs with h₁ h₂ <;>
    simp_all [Equiv.apply_eq_iff_eq_symm_apply]

/-- The rectangle `Wₜ` is unitary. -/
theorem rectangularCircuit_mem_unitary (ψ : AddChar F ℂ) (t : ℕ) :
    rectangularCircuit F ψ t ∈ unitary (Matrix (RectBasis F t) (RectBasis F t) ℂ) := by
  let e : SpatialBasis F (t + t) ≃ RectBasis F t :=
    (packetsToSpatial F (t := t)).symm
  let W := spatialCircuit F ψ (t + t) (crossingSchedule t)
  have hW := spatialCircuit_mem_unitary F ψ (t + t) (crossingSchedule t)
  have hWleft : Wᴴ * W = 1 := by simpa [W] using hW.1
  have hWright : W * Wᴴ = 1 := by simpa [W] using hW.2
  constructor
  · change (Matrix.reindex e e W)ᴴ * Matrix.reindex e e W = 1
    rw [Matrix.conjTranspose_reindex]
    change Matrix.reindexAlgEquiv ℂ ℂ e Wᴴ * Matrix.reindexAlgEquiv ℂ ℂ e W = 1
    rw [← Matrix.reindexAlgEquiv_mul, hWleft, map_one]
  · change Matrix.reindex e e W * (Matrix.reindex e e W)ᴴ = 1
    rw [Matrix.conjTranspose_reindex]
    change Matrix.reindexAlgEquiv ℂ ℂ e W * Matrix.reindexAlgEquiv ℂ ℂ e Wᴴ = 1
    rw [← Matrix.reindexAlgEquiv_mul, hWright, map_one]

/-! ## The source and Eq. (4.1) -/

/-- The one-site matrix unit `O_q = |1_B><0_B|` of Eq. (3.12). -/
noncomputable def sourceMatrixUnit : Matrix (Vq F) (Vq F) ℂ :=
  fun u v => if u = Sum.inr 1 ∧ v = Sum.inr 0 then 1 else 0

omit [Fintype F] in
@[simp] theorem sourceMatrixUnit_selected :
    sourceMatrixUnit F (Sum.inr 1) (Sum.inr 0) = 1 := by
  simp [sourceMatrixUnit]

/-- Lift a one-site operator to site `j` of a packet, acting identically elsewhere. -/
noncomputable def packetSiteOperator {t : ℕ} (j : Fin t)
    (O : Matrix (Vq F) (Vq F) ℂ) :
    Matrix (PacketBasis F t) (PacketBasis F t) ℂ :=
  fun u v => if ∀ k, k ≠ j → u k = v k then O (u j) (v j) else 0

/-- `Sₜ = 1_A^⊗t ⊗ O_{B₀} ⊗ 1_{B₁...B_{t-1}}`.
The positive-natural index makes the distinguished site `B₀` total. -/
noncomputable def rectangularSource (t : ℕ+) :
    Matrix (RectBasis F t) (RectBasis F t) ℂ :=
  fun u v => if u.1 = v.1 then
    packetSiteOperator F (0 : Fin (t : ℕ)) (sourceMatrixUnit F) u.2 v.2
  else 0

omit [Fintype F] in
/-- Exact support of the source matrix: the left packet is diagonal, the right
packet is diagonal away from `B₀`, and `B₀` carries `|1_B><0_B|`. -/
theorem rectangularSource_ne_zero_iff (t : ℕ+) (u v : RectBasis F t) :
    rectangularSource F t u v ≠ 0 ↔
      u.1 = v.1 ∧
      (∀ k, k ≠ (0 : Fin (t : ℕ)) → u.2 k = v.2 k) ∧
      u.2 0 = Sum.inr 1 ∧ v.2 0 = Sum.inr 0 := by
  simp [rectangularSource, packetSiteOperator, sourceMatrixUnit]

omit [Fintype F] in
/-- The source in Eq. (4.1) is nonzero. -/
theorem rectangularSource_ne_zero (t : ℕ+) : rectangularSource F t ≠ 0 := by
  classical
  let vacuum : PacketBasis F t := fun _ => Sum.inl 0
  let ket : PacketBasis F t := Function.update vacuum 0 (Sum.inr 1)
  let bra : PacketBasis F t := Function.update vacuum 0 (Sum.inr 0)
  intro hzero
  have hentry := congrArg
    (fun M : Matrix (RectBasis F t) (RectBasis F t) ℂ =>
      M (vacuum, ket) (vacuum, bra)) hzero
  have houtside : ∀ k : Fin (t : ℕ), k ≠ 0 → ket k = bra k := by
    intro k hk
    simp [ket, bra, hk]
  have hpacket :
      packetSiteOperator F (0 : Fin (t : ℕ)) (sourceMatrixUnit F) ket bra = 1 := by
    rw [packetSiteOperator, if_pos houtside]
    simp [ket, bra, sourceMatrixUnit]
  have hsource : rectangularSource F t (vacuum, ket) (vacuum, bra) = 1 := by
    rw [rectangularSource, if_pos rfl, hpacket]
  change rectangularSource F t (vacuum, ket) (vacuum, bra) = 0 at hentry
  rw [hsource] at hentry
  simp at hentry

/-- The rectangular-core operator `Xₜ = Wₜᴴ Sₜ Wₜ`, Eq. (4.1). -/
noncomputable def rectangularCore (ψ : AddChar F ℂ) (t : ℕ+) :
    Matrix (RectBasis F t) (RectBasis F t) ℂ :=
  let W := rectangularCircuit F ψ t
  Wᴴ * rectangularSource F t * W

/-- Explicit entries of `Xₜ`: its support is the pullback of the one-site
source by the rectangle permutation, while the two accumulated phases occur
on the bra and ket sides. -/
theorem rectangularCore_apply (ψ : AddChar F ℂ) (t : ℕ+) (u v : RectBasis F t) :
    rectangularCore F ψ t u v =
      star (rectangularCircuitPhase F ψ t u) *
        rectangularSource F t (rectangularCircuitPerm F t u) (rectangularCircuitPerm F t v) *
          rectangularCircuitPhase F ψ t v := by
  rw [rectangularCore, rectangularCircuit_eq_mono]
  exact mono_conjugate_apply _ _ _ _ _

/-- Phases do not affect entry magnitudes: the support and squared weights of
`Xₜ` are inherited exactly from the pulled-back source. -/
theorem norm_rectangularCore_apply (ψ : AddChar F ℂ) (t : ℕ+)
    (u v : RectBasis F t) :
    ‖rectangularCore F ψ t u v‖ =
      ‖rectangularSource F t (rectangularCircuitPerm F t u)
        (rectangularCircuitPerm F t v)‖ := by
  rw [rectangularCore_apply, norm_mul, norm_mul, norm_star,
    norm_rectangularCircuitPhase, norm_rectangularCircuitPhase]
  simp

/-- Exact support of `Xₜ` before spelling out the source constraints. -/
theorem rectangularCore_ne_zero_apply_iff (ψ : AddChar F ℂ) (t : ℕ+)
    (u v : RectBasis F t) :
    rectangularCore F ψ t u v ≠ 0 ↔
      rectangularSource F t (rectangularCircuitPerm F t u)
        (rectangularCircuitPerm F t v) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_rectangularCore_apply, norm_ne_zero_iff]

/-- Unitary conjugation cannot annihilate the source, so `Xₜ` is nonzero. -/
theorem rectangularCore_ne_zero (ψ : AddChar F ℂ) (t : ℕ+) :
    rectangularCore F ψ t ≠ 0 := by
  let W := rectangularCircuit F ψ (t : ℕ)
  have hW := rectangularCircuit_mem_unitary F ψ (t : ℕ)
  have hWleft : Wᴴ * W = 1 := by simpa [W] using hW.1
  have hWright : W * Wᴴ = 1 := by simpa [W] using hW.2
  intro hzero
  have hconj : W * rectangularCore F ψ t * Wᴴ = rectangularSource F t := by
    change W * (Wᴴ * rectangularSource F t * W) * Wᴴ = rectangularSource F t
    calc
      _ = (W * Wᴴ) * rectangularSource F t * (W * Wᴴ) := by
        simp only [mul_assoc]
      _ = rectangularSource F t := by rw [hWright]; simp
  rw [hzero] at hconj
  simp only [mul_zero, zero_mul] at hconj
  exact rectangularSource_ne_zero F t hconj.symm

/-! ## Operator-Schmidt coefficient matrix -/

/-- Regroup the four indices of an operator as
`(left-output,left-input) | (right-output,right-input)`.
This is the coefficient matrix whose singular values are the operator-Schmidt
coefficients across the packet cut. -/
def rectCoeff {t : ℕ}
    (X : Matrix (RectBasis F t) (RectBasis F t) ℂ) :
    Matrix (PacketBasis F t × PacketBasis F t)
      (PacketBasis F t × PacketBasis F t) ℂ :=
  fun li ro => X (li.1, ro.1) (li.2, ro.2)

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Reshaping into left/right operator indices is injective. -/
theorem rectCoeff_injective {t : ℕ} :
    Function.Injective (@rectCoeff F t) := by
  intro X Y h
  ext u v
  have hentry := congrArg
    (fun M => M (u.1, v.1) (u.2, v.2)) h
  exact hentry

/-- The operator-Schmidt coefficient matrix of `Xₜ` is nonzero. -/
theorem rectCoeff_rectangularCore_ne_zero (ψ : AddChar F ℂ) (t : ℕ+) :
    rectCoeff F (rectangularCore F ψ t) ≠ 0 := by
  intro hzero
  apply rectangularCore_ne_zero F ψ t
  apply rectCoeff_injective F
  simpa using hzero

/-- The unnormalized reduced Gram matrix of the vectorized operator. -/
noncomputable def schmidtGram {m n : Type*} [Fintype m]
    (M : Matrix m n ℂ) : Matrix n n ℂ :=
  Mᴴ * M

/-- Squared Hilbert--Schmidt norm of a coefficient matrix. -/
noncomputable def schmidtNormSq {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- Normalized reduced Gram matrix.  It is `0` for the zero operator. -/
noncomputable def normalizedSchmidtGram {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : Matrix n n ℂ :=
  (schmidtNormSq M)⁻¹ • schmidtGram M

/-- The concrete normalized Gram matrix attached to the object `Xₜ` of Eq. (4.1). -/
noncomputable def rectangularDensity (ψ : AddChar F ℂ) (t : ℕ+) :=
  normalizedSchmidtGram (rectCoeff F (rectangularCore F ψ t))

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem rectCoeff_apply {t : ℕ}
    (X : Matrix (RectBasis F t) (RectBasis F t) ℂ)
    (leftOut leftIn rightOut rightIn : PacketBasis F t) :
    rectCoeff F X (leftOut, leftIn) (rightOut, rightIn) =
      X (leftOut, rightOut) (leftIn, rightIn) := rfl

theorem schmidtNormSq_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : 0 ≤ schmidtNormSq M := by
  classical
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖M i j‖

end SqrtOpEnt
