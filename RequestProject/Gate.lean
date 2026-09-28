import Mathlib

/-!
# The triangular finite-field Yang–Baxter gate

This file formalizes Section 3 of the manuscript: the gate `R` of Eqs. (3.6)–(3.9)
on the two-colour local space `V_q = H_A ⊕ H_B` with `H_A ≅ H_B ≅ F_q`,

* equal colours pass trivially,
* an `A`–`B` collision performs the triangular shear `(a,b) ↦ (a+b, b)` and picks up the
  cubic phase `χ_q(a b²)`, exchanging the two colour spaces,
* a `B`–`A` collision is the adjoint crossing, Eq. (6.7).

Since the gate is monomial we represent it by the general construction `mono σ φ` — a
permutation of basis states dressed by phases — and prove the four positive structural
properties of Lemma 3.1 (unitary, Hermitian, involutive, braid relation), as well as
failure of dual unitarity (Proposition 3.2).  We also record the additional LPW
partial-trace identity `TR = q·1`; it is not used by the standalone lower bound.
-/

namespace SqrtOpEnt

open Matrix

/-! ### Monomial matrices -/

section Monomial

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The monomial matrix with support the permutation `σ` and phases `φ`. -/
noncomputable def mono (σ : Equiv.Perm Y) (φ : Y → ℂ) : Matrix Y Y ℂ :=
  fun u v => if u = σ v then φ v else 0

theorem mono_mul (σ τ : Equiv.Perm Y) (φ ψ : Y → ℂ) :
    mono σ φ * mono τ ψ = mono (τ.trans σ) (fun v => φ (τ v) * ψ v) := by
  ext u v
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ v)]
  · simp only [mono, Equiv.trans_apply]
    by_cases h : u = σ (τ v) <;> simp [h]
  · intro w _ hw
    simp only [mono]
    rw [if_neg hw, mul_zero]
  · intro h; simp at h

omit [Fintype Y] in
theorem mono_congr {σ τ : Equiv.Perm Y} {φ ψ : Y → ℂ} (hst : ∀ v, σ v = τ v)
    (hpq : ∀ v, φ v = ψ v) : mono σ φ = mono τ ψ := by
  ext u v
  simp only [mono, hst v, hpq v]

omit [Fintype Y] in
theorem mono_eq_one {σ : Equiv.Perm Y} {φ : Y → ℂ} (hσ : ∀ v, σ v = v)
    (hφ : ∀ v, φ v = 1) : mono σ φ = 1 := by
  ext u v
  simp [mono, hσ v, hφ v, Matrix.one_apply]

omit [Fintype Y] in
theorem mono_conjTranspose (σ : Equiv.Perm Y) (φ : Y → ℂ) :
    (mono σ φ)ᴴ = mono σ.symm (fun v => star (φ (σ.symm v))) := by
  ext u v
  simp only [Matrix.conjTranspose_apply, mono]
  by_cases h : u = σ.symm v
  · subst h; simp
  · rw [if_neg h]
    have hv : ¬ (v = σ u) := fun hv => h (by simp [hv])
    simp [hv]

end Monomial

/-! ### The gate -/

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The local space `V_q = H_A ⊕ H_B`, of dimension `D = 2q`, Eq. (3.4). -/
abbrev Vq := F ⊕ F

/-- Three-site configuration space. -/
abbrev Vq3 := Vq F × Vq F × Vq F

/-- The support map of the gate, Eqs. (3.6), (3.7), (3.9), and (6.7):
the identity on equal colours and the triangular shear on mixed colours. -/
def gateFun : Vq F × Vq F → Vq F × Vq F
  | (Sum.inl a, Sum.inl b) => (Sum.inl a, Sum.inl b)
  | (Sum.inr a, Sum.inr b) => (Sum.inr a, Sum.inr b)
  | (Sum.inl a, Sum.inr b) => (Sum.inr (a+b), Sum.inl b)
  | (Sum.inr c, Sum.inl d) => (Sum.inl (c-d), Sum.inr d)

omit [Fintype F] [DecidableEq F] in
theorem gateFun_involutive : Function.Involutive (gateFun F) := by
  rintro ⟨x, y⟩
  rcases x with a | a <;> rcases y with b | b <;> simp [gateFun]

/-- The support permutation of the gate. -/
def gatePerm : Equiv.Perm (Vq F × Vq F) :=
  Function.Involutive.toPerm _ (gateFun_involutive F)

omit [Fintype F] [DecidableEq F] in
@[simp] lemma gatePerm_apply (v : Vq F × Vq F) : gatePerm F v = gateFun F v := rfl

/-- The cubic phase of the active crossing, Eq. (3.9), and its adjoint, Eq. (6.7). -/
noncomputable def gatePhase (ψ : AddChar F ℂ) : Vq F × Vq F → ℂ
  | (Sum.inl _, Sum.inl _) => 1
  | (Sum.inr _, Sum.inr _) => 1
  | (Sum.inl a, Sum.inr b) => ψ (a * b^2)
  | (Sum.inr c, Sum.inl d) => ψ (-((c-d) * d^2))

/-- The gate `R` of Eq. (3.8). -/
noncomputable def gateMat (ψ : AddChar F ℂ) : Matrix (Vq F × Vq F) (Vq F × Vq F) ℂ :=
  mono (gatePerm F) (gatePhase F ψ)

/-- Support of the crossing acting on sites 1,2. -/
def gate12Fun (w : Vq3 F) : Vq3 F :=
  ((gateFun F (w.1, w.2.1)).1, (gateFun F (w.1, w.2.1)).2, w.2.2)

/-- Support of the crossing acting on sites 2,3. -/
def gate23Fun (w : Vq3 F) : Vq3 F :=
  (w.1, (gateFun F (w.2.1, w.2.2)).1, (gateFun F (w.2.1, w.2.2)).2)

omit [Fintype F] [DecidableEq F] in
theorem gate12Fun_involutive : Function.Involutive (gate12Fun F) := by
  rintro ⟨x, y, z⟩
  simp only [gate12Fun]
  rcases x with a | a <;> rcases y with b | b <;> simp [gateFun]

omit [Fintype F] [DecidableEq F] in
theorem gate23Fun_involutive : Function.Involutive (gate23Fun F) := by
  rintro ⟨x, y, z⟩
  simp only [gate23Fun]
  rcases y with b | b <;> rcases z with c | c <;> simp [gateFun]

noncomputable def gate12Phase (ψ : AddChar F ℂ) (w : Vq3 F) : ℂ := gatePhase F ψ (w.1, w.2.1)

noncomputable def gate23Phase (ψ : AddChar F ℂ) (w : Vq3 F) : ℂ := gatePhase F ψ (w.2.1, w.2.2)

/-- `R₁₂`, the gate acting on the first two sites of `V ⊗ V ⊗ V`. -/
noncomputable def gate12 (ψ : AddChar F ℂ) : Matrix (Vq3 F) (Vq3 F) ℂ :=
  mono (Function.Involutive.toPerm _ (gate12Fun_involutive F)) (gate12Phase F ψ)

/-- `R₂₃`, the gate acting on the last two sites of `V ⊗ V ⊗ V`. -/
noncomputable def gate23 (ψ : AddChar F ℂ) : Matrix (Vq3 F) (Vq3 F) ℂ :=
  mono (Function.Involutive.toPerm _ (gate23Fun_involutive F)) (gate23Phase F ψ)

/-- The reshuffled gate `R^Γ` of Eq. (2.9). -/
noncomputable def gateReshuffle (ψ : AddChar F ℂ) :
    Matrix (Vq F × Vq F) (Vq F × Vq F) ℂ :=
  fun p r => gateMat F ψ (p.2, r.2) (p.1, r.1)

/-- The unnormalized partial trace `TR = (1 ⊗ Tr) R`. -/
noncomputable def gatePartialTrace (ψ : AddChar F ℂ) : Matrix (Vq F) (Vq F) ℂ :=
  fun x' x => ∑ z : Vq F, gateMat F ψ (x', z) (x, z)

variable {F}

/-! ### Lemma 3.1: the positive structural properties -/

omit [Fintype F] in
/-- The active crossing, Eq. (3.9): `R |a⟩_A |b⟩_B = χ_q(a b²) |a+b⟩_B |b⟩_A`. -/
theorem gateMat_apply_active (ψ : AddChar F ℂ) (a b : F) :
    gateMat F ψ (Sum.inr (a+b), Sum.inl b) (Sum.inl a, Sum.inr b) = ψ (a * b^2) := by
  simp [gateMat, mono, gateFun, gatePhase]

omit [Fintype F] in
/-- Equal colours pass trivially, Eq. (3.6). -/
theorem gateMat_apply_equal (ψ : AddChar F ℂ) (a b : F) :
    gateMat F ψ (Sum.inl a, Sum.inl b) (Sum.inl a, Sum.inl b) = 1 := by
  simp [gateMat, mono, gateFun, gatePhase]

omit [Fintype F] [DecidableEq F] in
/-- Phases along the involution cancel. -/
theorem gatePhase_mul_gateFun (ψ : AddChar F ℂ) (v : Vq F × Vq F) :
    gatePhase F ψ (gateFun F v) * gatePhase F ψ v = 1 := by
  obtain ⟨x, y⟩ := v
  rcases x with a | a <;> rcases y with b | b <;>
    simp [gateFun, gatePhase, ← ψ.map_add_eq_mul]

/-- **Lemma 3.1 (involutivity).**  `R² = 1`. -/
theorem gateMat_mul_self (ψ : AddChar F ℂ) : gateMat F ψ * gateMat F ψ = 1 := by
  rw [gateMat, mono_mul]
  refine mono_eq_one (fun v => ?_) (fun v => ?_)
  · simp [gateFun_involutive F v]
  · simpa using gatePhase_mul_gateFun ψ v

/-- **Lemma 3.1 (Hermiticity).**  `R† = R`. -/
theorem gateMat_conjTranspose (ψ : AddChar F ℂ) : (gateMat F ψ)ᴴ = gateMat F ψ := by
  rw [gateMat, mono_conjTranspose]
  refine mono_congr (fun v => rfl) (fun v => ?_)
  have hsymm : (gatePerm F).symm v = gateFun F v := rfl
  rw [hsymm]
  obtain ⟨x, y⟩ := v
  rcases x with a | a <;> rcases y with b | b <;>
    simp [gateFun, gatePhase, ← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv]

/-- **Lemma 3.1 (unitarity).** -/
theorem gateMat_unitary (ψ : AddChar F ℂ) : (gateMat F ψ)ᴴ * gateMat F ψ = 1 := by
  rw [gateMat_conjTranspose, gateMat_mul_self]

omit [Fintype F] in
/-- `R₁₂` really is `R ⊗ 1`: its entries are those of `R` on the first two sites times a
Kronecker delta on the third. -/
theorem gate12_apply (ψ : AddChar F ℂ) (u v : Vq3 F) :
    gate12 F ψ u v
      = gateMat F ψ (u.1, u.2.1) (v.1, v.2.1) * (if u.2.2 = v.2.2 then 1 else 0) := by
  obtain ⟨u1, u2, u3⟩ := u
  obtain ⟨v1, v2, v3⟩ := v
  simp only [gate12, gateMat, mono, gate12Phase, Function.Involutive.coe_toPerm, gate12Fun,
    gatePerm_apply, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

omit [Fintype F] in
/-- `R₂₃` really is `1 ⊗ R`. -/
theorem gate23_apply (ψ : AddChar F ℂ) (u v : Vq3 F) :
    gate23 F ψ u v
      = (if u.1 = v.1 then 1 else 0) * gateMat F ψ (u.2.1, u.2.2) (v.2.1, v.2.2) := by
  obtain ⟨u1, u2, u3⟩ := u
  obtain ⟨v1, v2, v3⟩ := v
  simp only [gate23, gateMat, mono, gate23Phase, Function.Involutive.coe_toPerm, gate23Fun,
    gatePerm_apply, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

/-- **Lemma 3.1 (braid relation).**  `R₁₂ R₂₃ R₁₂ = R₂₃ R₁₂ R₂₃`, Eq. (2.8). -/
theorem gate_braid (ψ : AddChar F ℂ) :
    gate12 F ψ * gate23 F ψ * gate12 F ψ = gate23 F ψ * gate12 F ψ * gate23 F ψ := by
  simp only [gate12, gate23, mono_mul]
  refine mono_congr (fun w => ?_) (fun w => ?_)
  · simp only [Equiv.trans_apply, Function.Involutive.coe_toPerm]
    obtain ⟨x, y, z⟩ := w
    rcases x with a | a <;> rcases y with b | b <;> rcases z with c | c <;>
      simp [gate12Fun, gate23Fun, gateFun]
  · simp only [Function.Involutive.coe_toPerm]
    obtain ⟨x, y, z⟩ := w
    rcases x with a | a <;> rcases y with b | b <;> rcases z with c | c <;>
      simp [gate12Fun, gate23Fun, gateFun, gate12Phase, gate23Phase, gatePhase,
        ← ψ.map_add_eq_mul]

/-! ### Failure of dual unitarity, Proposition 3.2 -/

omit [Fintype F] in
/-- The reshuffled matrix has a zero row: with two distinct `A`-labels `a ≠ c`, the row
indexed by `(a, c)` vanishes identically, Eq. (3.14). -/
theorem gateReshuffle_row_zero (ψ : AddChar F ℂ) (a c : F) (hac : a ≠ c) (r : Vq F × Vq F) :
    gateReshuffle F ψ (Sum.inl a, Sum.inl c) r = 0 := by
  obtain ⟨y, v⟩ := r
  simp only [gateReshuffle, gateMat, mono, gatePerm_apply]
  rcases y with y | y <;> rcases v with v | v <;>
    simp [gateFun, Prod.ext_iff, Ne.symm hac]

/-- **Proposition 3.2.**  The gate is not dual-unitary. -/
theorem not_dual_unitary (ψ : AddChar F ℂ) :
    gateReshuffle F ψ * (gateReshuffle F ψ)ᴴ ≠ 1 := by
  intro h
  have h1 : (gateReshuffle F ψ * (gateReshuffle F ψ)ᴴ)
      (Sum.inl 0, Sum.inl 1) (Sum.inl 0, Sum.inl 1) = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rw [gateReshuffle_row_zero ψ 0 1 (by norm_num) r, zero_mul]
  rw [h] at h1
  simp at h1

/-! ### An additional LPW partial-trace identity -/

/-- Only the equal-colour identity sectors close the traced strand:
`TR = q·1`, so the LPW data are two positive blocks of size `q`. -/
theorem gatePartialTrace_eq (ψ : AddChar F ℂ) :
    gatePartialTrace F ψ = (Fintype.card F : ℂ) • (1 : Matrix (Vq F) (Vq F) ℂ) := by
  ext x' x
  simp only [gatePartialTrace, gateMat, mono, gatePerm_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [Fintype.sum_sum_type]
  rcases x' with a' | a' <;> rcases x with a | a <;>
    simp [gateFun, gatePhase, Prod.ext_iff, Finset.card_univ, eq_comm]

end SqrtOpEnt
