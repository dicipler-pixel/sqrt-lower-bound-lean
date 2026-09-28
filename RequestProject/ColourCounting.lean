import RequestProject.RectangularCore
import Mathlib.Data.Finset.Powerset

/-!
# Exact finite colour counts

This file supplies the elementary counting step behind Eq. (5.17).  A packet
label in `Vq F = F ⊕ F` is split bijectively into a visible colour and an
independent field label.  Consequently the number of length-`n` packet labels
with exactly `k` visible `B` sites is `C(n,k) * |F|^n`.
-/

namespace SqrtOpEnt

open Finset

variable (F : Type*) [Fintype F] [DecidableEq F]

/-- The internal finite-field label, forgetting whether it belongs to `A` or `B`. -/
def siteLabel : Vq F → F
  | Sum.inl a => a
  | Sum.inr b => b

/-- Splitting a local label into visible colour and internal field label is bijective. -/
def vqColourLabelEquiv : Vq F ≃ VisibleColour × F where
  toFun z := (siteColour F z, siteLabel F z)
  invFun p := match p.1 with
    | .A => Sum.inl p.2
    | .B => Sum.inr p.2
  left_inv z := by cases z <;> rfl
  right_inv p := by rcases p with ⟨c, a⟩; cases c <;> rfl

/-- Split all sites of a packet into its colour word and independent labels. -/
def packetColourLabelEquiv (n : ℕ) :
    (Fin n → Vq F) ≃ (Fin n → VisibleColour) × (Fin n → F) where
  toFun u := (fun i => (vqColourLabelEquiv F (u i)).1,
    fun i => (vqColourLabelEquiv F (u i)).2)
  invFun p i := (vqColourLabelEquiv F).symm (p.1 i, p.2 i)
  left_inv u := by
    funext i
    exact (vqColourLabelEquiv F).symm_apply_apply (u i)
  right_inv p := by
    rcases p with ⟨c, a⟩
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst ((vqColourLabelEquiv F).apply_symm_apply (c i, a i))
    · exact congrArg Prod.snd ((vqColourLabelEquiv F).apply_symm_apply (c i, a i))

/-- Number of `B` sites in a pure visible-colour word. -/
def visibleBCount {n : ℕ} (c : Fin n → VisibleColour) : ℕ :=
  (Finset.univ.filter fun i => c i = .B).card

/-- Number of visible `B` sites in a packet basis label. -/
def packetBCount {n : ℕ} (u : Fin n → Vq F) : ℕ :=
  (Finset.univ.filter fun i => siteColour F (u i) = .B).card

omit [Fintype F] [DecidableEq F] in
theorem packetBCount_le {n : ℕ} (u : Fin n → Vq F) : packetBCount F u ≤ n := by
  simpa [packetBCount] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => siteColour F (u i) = .B))

/-- A Boolean colour word is equivalently the set of positions carrying `B`. -/
def colourWordFinsetEquiv (n : ℕ) :
    (Fin n → VisibleColour) ≃ Finset (Fin n) where
  toFun c := Finset.univ.filter fun i => c i = .B
  invFun s i := if i ∈ s then .B else .A
  left_inv c := by
    funext i
    cases h : c i <;> simp [h]
  right_inv s := by
    ext i
    simp

/-- Exactly `C(n,k)` visible-colour words have `k` sites of colour `B`. -/
theorem card_visibleBCount_eq (n k : ℕ) :
    Fintype.card {c : Fin n → VisibleColour // visibleBCount c = k} = n.choose k := by
  let P : Finset (Finset (Fin n)) := Finset.univ.powersetCard k
  letI : Fintype {s : Finset (Fin n) // s ∈ P} := Finset.Subtype.fintype P
  let e := (colourWordFinsetEquiv n).subtypeEquiv
    (p := fun c => visibleBCount c = k)
    (q := fun s => s ∈ P) (fun c => by
      simp [P, visibleBCount, colourWordFinsetEquiv, Finset.mem_powersetCard])
  calc
    Fintype.card {c : Fin n → VisibleColour // visibleBCount c = k} =
        Fintype.card {s : Finset (Fin n) // s ∈ P} :=
      Fintype.card_congr e
    _ = P.card := Fintype.card_coe _
    _ = n.choose k := by
      dsimp [P]
      rw [Finset.card_powersetCard]
      simp

/-- Restricting the packet split to a fixed colour count leaves an arbitrary
field label at every site. -/
def packetBCountEquiv (n k : ℕ) :
    {u : Fin n → Vq F // packetBCount F u = k} ≃
      {c : Fin n → VisibleColour // visibleBCount c = k} × (Fin n → F) where
  toFun u :=
    (⟨(packetColourLabelEquiv F n u).1, by
      simpa [packetBCount, visibleBCount, packetColourLabelEquiv,
        vqColourLabelEquiv] using u.property⟩,
      (packetColourLabelEquiv F n u).2)
  invFun p :=
    ⟨(packetColourLabelEquiv F n).symm (p.1.1, p.2), by
      change (Finset.univ.filter fun i =>
        siteColour F ((vqColourLabelEquiv F).symm (p.1.1 i, p.2 i)) = .B).card = k
      have heq : (Finset.univ.filter fun i =>
          siteColour F ((vqColourLabelEquiv F).symm (p.1.1 i, p.2 i)) = .B) =
          Finset.univ.filter fun i => p.1.1 i = .B := by
        ext i
        cases h : p.1.1 i <;> simp [h, vqColourLabelEquiv, siteColour]
      rw [heq]
      exact p.1.property⟩
  left_inv u := by
    apply Subtype.ext
    exact (packetColourLabelEquiv F n).symm_apply_apply u
  right_inv p := by
    rcases p with ⟨⟨c, hc⟩, a⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((packetColourLabelEquiv F n).apply_symm_apply (c, a))
    · change ((packetColourLabelEquiv F n)
          ((packetColourLabelEquiv F n).symm (c, a))).2 = a
      exact congrArg Prod.snd ((packetColourLabelEquiv F n).apply_symm_apply (c, a))

omit [DecidableEq F] in
/-- Exact packet count: choose the `B` positions, then choose one field label
independently at every site. -/
theorem card_packetBCount_eq (n k : ℕ) :
    Fintype.card {u : Fin n → Vq F // packetBCount F u = k} =
      n.choose k * (Fintype.card F) ^ n := by
  rw [Fintype.card_congr (packetBCountEquiv F n k), Fintype.card_prod,
    card_visibleBCount_eq]
  simp

/-- Number of `A` sites in a pure visible-colour word. -/
def visibleACount {n : ℕ} (c : Fin n → VisibleColour) : ℕ :=
  (Finset.univ.filter fun i => c i = .A).card

/-- Number of visible `A` sites in a packet basis label. -/
def packetACount {n : ℕ} (u : Fin n → Vq F) : ℕ :=
  (Finset.univ.filter fun i => siteColour F (u i) = .A).card

omit [Fintype F] [DecidableEq F] in
theorem packetACount_le {n : ℕ} (u : Fin n → Vq F) : packetACount F u ≤ n := by
  simpa [packetACount] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => siteColour F (u i) = .A))

/-- A colour word is equivalently the set of positions carrying `A`. -/
def colourWordAFinsetEquiv (n : ℕ) :
    (Fin n → VisibleColour) ≃ Finset (Fin n) where
  toFun c := Finset.univ.filter fun i => c i = .A
  invFun s i := if i ∈ s then .A else .B
  left_inv c := by
    funext i
    cases h : c i <;> simp [h]
  right_inv s := by
    ext i
    simp

/-- Exactly `C(n,l)` visible-colour words have `l` sites of colour `A`. -/
theorem card_visibleACount_eq (n l : ℕ) :
    Fintype.card {c : Fin n → VisibleColour // visibleACount c = l} = n.choose l := by
  let P : Finset (Finset (Fin n)) := Finset.univ.powersetCard l
  letI : Fintype {s : Finset (Fin n) // s ∈ P} := Finset.Subtype.fintype P
  let e := (colourWordAFinsetEquiv n).subtypeEquiv
    (p := fun c => visibleACount c = l)
    (q := fun s => s ∈ P) (fun c => by
      simp [P, visibleACount, colourWordAFinsetEquiv, Finset.mem_powersetCard])
  calc
    Fintype.card {c : Fin n → VisibleColour // visibleACount c = l} =
        Fintype.card {s : Finset (Fin n) // s ∈ P} := Fintype.card_congr e
    _ = P.card := Fintype.card_coe _
    _ = n.choose l := by
      dsimp [P]
      rw [Finset.card_powersetCard]
      simp

/-- Split a packet of fixed `A` count into its colour word and free labels. -/
def packetACountEquiv (n l : ℕ) :
    {u : Fin n → Vq F // packetACount F u = l} ≃
      {c : Fin n → VisibleColour // visibleACount c = l} × (Fin n → F) where
  toFun u :=
    (⟨(packetColourLabelEquiv F n u).1, by
      simpa [packetACount, visibleACount, packetColourLabelEquiv,
        vqColourLabelEquiv] using u.property⟩,
      (packetColourLabelEquiv F n u).2)
  invFun p :=
    ⟨(packetColourLabelEquiv F n).symm (p.1.1, p.2), by
      change (Finset.univ.filter fun i =>
        siteColour F ((vqColourLabelEquiv F).symm (p.1.1 i, p.2 i)) = .A).card = l
      have heq : (Finset.univ.filter fun i =>
          siteColour F ((vqColourLabelEquiv F).symm (p.1.1 i, p.2 i)) = .A) =
          Finset.univ.filter fun i => p.1.1 i = .A := by
        ext i
        cases h : p.1.1 i <;> simp [h, vqColourLabelEquiv, siteColour]
      rw [heq]
      exact p.1.property⟩
  left_inv u := by
    apply Subtype.ext
    exact (packetColourLabelEquiv F n).symm_apply_apply u
  right_inv p := by
    rcases p with ⟨⟨c, hc⟩, a⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((packetColourLabelEquiv F n).apply_symm_apply (c, a))
    · change ((packetColourLabelEquiv F n)
          ((packetColourLabelEquiv F n).symm (c, a))).2 = a
      exact congrArg Prod.snd ((packetColourLabelEquiv F n).apply_symm_apply (c, a))

omit [DecidableEq F] in
/-- Exact packet count for colour `A`. -/
theorem card_packetACount_eq (n l : ℕ) :
    Fintype.card {u : Fin n → Vq F // packetACount F u = l} =
      n.choose l * (Fintype.card F) ^ n := by
  rw [Fintype.card_congr (packetACountEquiv F n l), Fintype.card_prod,
    card_visibleACount_eq]
  simp

end SqrtOpEnt
