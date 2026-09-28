import Mathlib

/-!
# Finite-field character orthogonality and flat Schmidt spectra

This file formalizes the algebraic mechanism of Section 6 of the manuscript.

After the reduction of Section 5 the coefficient matrix of the imbalance core is,
up to left-only and right-only phases (which are diagonal unitaries on one side of
the cut and do not change the Schmidt spectrum), the finite-field Fourier matrix

`M(L, R) = χ_q(Lᵀ K R)`,

where `K` is the mixed Hessian of the quadratic phase difference, Eq. (6.2).
The content of Eq. (6.3) and its application in Eqs. (6.34)–(6.35) is that
**injectivity of the mixed map `K` on the allowed right-coordinate space forces the
nonzero Schmidt spectrum to be flat**: `Mᴴ M = q^{n_L} 1`, so every independent
allowed right coordinate contributes one q-ary unit `log q` of operator entanglement.

The only character identity used is Eq. (3.3), `∑_z χ_q(u z) = q 1{u = 0}`, which
holds over every finite field, so the argument is insensitive to whether `q` is prime.
-/

namespace SqrtOpEnt

open Finset Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Eq. (3.3).**  Additive character orthogonality over a finite field. -/
theorem char_sum_field (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (u : F) :
    ∑ z : F, ψ (u * z) = if u = 0 then (Fintype.card F : ℂ) else 0 := by
  classical
  by_cases hu : u = 0
  · simp [hu]
  · have hcomp : ∑ z : F, ψ (u * z) = ∑ w : F, ψ w :=
      Fintype.sum_equiv (Equiv.mulLeft₀ u hu) _ _ (fun z => rfl)
    rw [hcomp, AddChar.sum_eq_zero_of_ne_one hψ, if_neg hu]

/-- Character orthogonality for a linear form on `F^n`: the sum of `χ(x ⬝ v)` over all
`x` vanishes unless the vector `v` is zero. -/
theorem char_sum_vec {n : ℕ} (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (v : Fin n → F) :
    ∑ x : Fin n → F, ψ (x ⬝ᵥ v) = if v = 0 then (Fintype.card F : ℂ)^n else 0 := by
  classical
  by_cases hv : v = 0
  · subst hv
    simp [dotProduct]
  · rw [if_neg hv]
    -- the map `x ↦ ψ (x ⬝ᵥ v)` is a nontrivial additive character of `F^n`
    set φ : AddChar (Fin n → F) ℂ :=
      { toFun := fun x => ψ (x ⬝ᵥ v)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := by
          intro x y
          simp [add_dotProduct, ψ.map_add_eq_mul] } with hφ
    have hφne : φ ≠ 1 := by
      obtain ⟨c, hc⟩ : ∃ c : F, ψ c ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact hψ (by ext c; simpa using hcon c)
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv (funext hcon)
      intro hone
      apply hc
      have hx : (Pi.single i (c / v i) : Fin n → F) ⬝ᵥ v = c := by
        rw [single_dotProduct]
        field_simp
      have := congrArg (fun f : AddChar (Fin n → F) ℂ => f (Pi.single i (c / v i))) hone
      simpa [hφ, hx] using this
    have := AddChar.sum_eq_zero_of_ne_one hφne
    simpa [hφ] using this

/-- The coefficient matrix `M(L, R) = χ_q(Lᵀ K R)` arising from Eqs. (6.1)–(6.2),
with the allowed right configurations indexed by `S`. -/
noncomputable def fourierCoeff {nL nR : ℕ} {S : Type*} (ψ : AddChar F ℂ)
    (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F)) :
    Matrix (Fin nL → F) S ℂ :=
  fun x s => ψ (x ⬝ᵥ K.mulVec (y s))

/-- **Eq. (6.3) (flatness criterion).**  If the mixed map `K` is injective on the allowed
right-coordinate space, then the columns of the coefficient matrix are orthogonal and of
equal norm: `Mᴴ M = q^{n_L} 1`.  Hence all nonzero singular values coincide. -/
theorem fourierCoeff_conjTranspose_mul {nL nR : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F))
    (hinj : ∀ s s' : S, K.mulVec (y s) = K.mulVec (y s') → s = s') :
    (fourierCoeff ψ K y)ᴴ * (fourierCoeff ψ K y)
      = ((Fintype.card F : ℂ)^nL) • (1 : Matrix S S ℂ) := by
  classical
  ext s s'
  rw [Matrix.mul_apply]
  have hterm : ∀ x : Fin nL → F,
      (fourierCoeff ψ K y)ᴴ s x * (fourierCoeff ψ K y) x s'
        = ψ (x ⬝ᵥ K.mulVec (y s' - y s)) := by
    intro x
    have hconj : star (ψ (x ⬝ᵥ K.mulVec (y s))) = ψ (-(x ⬝ᵥ K.mulVec (y s))) := by
      rw [← starRingEnd_apply, ← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv]
    simp only [fourierCoeff, Matrix.conjTranspose_apply]
    rw [hconj, ← ψ.map_add_eq_mul]
    congr 1
    rw [Matrix.mulVec_sub, dotProduct_sub]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [char_sum_vec ψ hψ (K.mulVec (y s' - y s))]
  by_cases hss : s = s'
  · subst hss
    simp
  · have hne : K.mulVec (y s' - y s) ≠ 0 := by
      intro h
      rw [Matrix.mulVec_sub, sub_eq_zero] at h
      exact hss (hinj s s' h.symm)
    rw [if_neg hne]
    simp [hss]

/-- The normalized Gram matrix (the reduced density matrix of the imbalance core) is
maximally mixed on the allowed right-coordinate space: the Schmidt spectrum is flat of
rank `|S|`. -/
theorem fourierCoeff_density {nL nR : ℕ} {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (K : Matrix (Fin nL) (Fin nR) F) (y : S → (Fin nR → F))
    (hinj : ∀ s s' : S, K.mulVec (y s) = K.mulVec (y s') → s = s') :
    (((Fintype.card S : ℂ) * (Fintype.card F : ℂ)^nL)⁻¹) •
        ((fourierCoeff ψ K y)ᴴ * (fourierCoeff ψ K y))
      = ((Fintype.card S : ℂ)⁻¹) • (1 : Matrix S S ℂ) := by
  have hcard : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [fourierCoeff_conjTranspose_mul ψ hψ K y hinj, smul_smul]
  congr 1
  field_simp

/-- A flat spectrum of rank `N` has von Neumann (and every Rényi) entropy `log N`.
Combined with `fourierCoeff_density` and `N = q^{r-1}` (positive branch) resp. `N = q^s`
(negative branch), this is the entropy statement of Theorem 6.5. -/
theorem flat_entropy (N : ℕ) (hN : 0 < N) :
    -∑ _i ∈ range N, (1/(N:ℝ)) * Real.log (1/(N:ℝ)) = Real.log N := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [one_div, Real.log_inv]
  field_simp

/-- A flat spectrum of rank `N` has Rényi entropy `log N` at every index `α ≠ 1`; together
with `flat_entropy` this is the statement `S_α(Ξ_d) = g(d) log q` of Theorem 6.5 for all `α`. -/
theorem flat_renyi (N : ℕ) (hN : 0 < N) (α : ℝ) (hα : α ≠ 1) :
    (1/(1-α)) * Real.log (∑ _i ∈ range N, ((N:ℝ)⁻¹) ^ α) = Real.log N := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have h1 : (1:ℝ) - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  have hsum : ∑ _i ∈ range N, ((N:ℝ)⁻¹) ^ α = (N:ℝ) ^ (1 - α) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Real.inv_rpow hN'.le, Real.rpow_sub hN', Real.rpow_one]
    field_simp
  rw [hsum, Real.log_rpow hN']
  field_simp

omit [Fintype F] [DecidableEq F] in
/-- Injectivity of the mixed map on the allowed right space in the two cases used in
Theorem 6.5: an invertible `K` (positive branch, Eq. (6.27)) is injective on every
subset of right configurations. -/
theorem mulVec_injective_of_isUnit {n : ℕ} {K : Matrix (Fin n) (Fin n) F} (hK : IsUnit K.det)
    (y y' : Fin n → F) (h : K.mulVec y = K.mulVec y') : y = y' := by
  have := congrArg (fun v => K⁻¹.mulVec v) h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hK] using this

omit [Fintype F] [DecidableEq F] in
/-- Negative branch (Eq. (6.27)): `K` has a one-dimensional kernel which is transversal to
the source hyperplane, so `K` is injective on the allowed right space. -/
theorem mulVec_injective_of_ker_transversal {nL nR : ℕ} {K : Matrix (Fin nL) (Fin nR) F}
    {S : Type*} (y : S → (Fin nR → F))
    (hker : ∀ v : Fin nR → F, K.mulVec v = 0 → ∀ s s' : S, y s - y s' = v → s = s') :
    ∀ s s' : S, K.mulVec (y s) = K.mulVec (y s') → s = s' := by
  intro s s' h
  refine hker (y s - y s') ?_ s s' rfl
  rw [Matrix.mulVec_sub, h, sub_self]

end SqrtOpEnt
