import RequestProject.MeanAbsDeviation

/-!
# The square-root law for the von Neumann operator entanglement

This file contains the probabilistic half of Section 7 of the manuscript, and the
final assembly of Theorem 7.1

`S₁^op(O_q(t)) = (log q / √π) √t + O_q(log t)`.

The two inputs coming from the *quantum* part of the paper are used exactly in the
form of Corollary 5.5 (the entropy sandwich)

`E f₁(Δ_t) ≤ S₁(Ω_t) ≤ H(K_t) + H(L_t) + E f₁(Δ_t)`,

which is taken as a hypothesis of the final theorem: the manuscript derives the
lower bound from a local measurement of the two colour counts (Proposition 5.3) and
the upper bound from pinching (Proposition 5.4), and identifies the branch entropies
by the flat-spectrum theorem `S₁(Ξ_d) = g(d) log q` (Theorem 6.5).

Everything else is proved here:

* `expImbEntropy_eq` : the *exact* value of `E f₁(Δ_t)` at every finite time, Eq. (7.3);
* `expImbEntropy_bounds` : its sharp `√(t/π) log q + O(1)` form, Eq. (7.4);
* `binEntropy_le_log` : the count-label entropies are `O(log t)`, the size of the
  coherence correction in Eq. (7.6);
* `vonNeumann_sqrt_law` and `vonNeumann_sqrt_law_isBigO` : Theorem 7.1.
-/

namespace SqrtOpEnt

open Finset

/-! ### The imbalance entropy `f₁` -/

/-- `g(d) = |d - 1/2| - 1/2`, the number of unmatched boundary directions of the
imbalance core `Ξ_d`, Eq. (5.45). -/
noncomputable def gImb (d : ℤ) : ℝ := |(d:ℝ) - 1/2| - 1/2

/-- `f₁(d) = S₁(Ξ_d) = g(d) log q`, the exact branch entropy of Theorem 6.5. -/
noncomputable def imbEntropy (q : ℝ) (d : ℤ) : ℝ := gImb d * Real.log q

lemma gImb_of_pos {d : ℤ} (hd : 1 ≤ d) : gImb d = (d : ℝ) - 1 := by
  have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  rw [gImb, abs_of_nonneg (by linarith)]
  ring

lemma gImb_of_nonpos {d : ℤ} (hd : d ≤ 0) : gImb d = -(d : ℝ) := by
  have : (d:ℝ) ≤ 0 := by exact_mod_cast hd
  rw [gImb, abs_of_nonpos (by linarith)]
  ring

/-! ### The colour-count sectors -/

/-- The colour-count sector weight `π_t(j+1, l) = 2^{-(2t-1)} C(t-1,j) C(t,l)`, Eq. (5.17).
Here `j = k - 1` runs over the `t - 1` free spectators of the source packet. -/
noncomputable def sectorWeight (t j l : ℕ) : ℝ :=
  (((t-1).choose j : ℝ) * (t.choose l : ℝ)) / 2^(2*t-1)

/-- `E f₁(Δ_t)`, the average branch entropy of Proposition 5.3, with signed imbalance
`d = k + l - t = j + l + 1 - t`. -/
noncomputable def expImbEntropy (q : ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ range t, ∑ l ∈ range (t+1), sectorWeight t j l * imbEntropy q ((j:ℤ) + l + 1 - t)

/-- Vandermonde convolution restricted to the count rectangle. -/
theorem sum_filter_choose_mul_choose (m b : ℕ) :
    ∑ p ∈ (range (m+1) ×ˢ range (m+2)).filter (fun p => p.1 + p.2 = b),
      (m.choose p.1 * (m+1).choose p.2) = (2*m+1).choose b := by
  classical
  have hv : (2*m+1).choose b
      = ∑ ij ∈ Finset.antidiagonal b, m.choose ij.1 * (m+1).choose ij.2 := by
    have h := Nat.add_choose_eq m (m+1) b
    rw [show m + (m+1) = 2*m+1 by ring] at h
    exact h
  rw [hv]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_antidiagonal]
    exact hp.2
  · intro p hp hnot
    simp only [Finset.mem_antidiagonal] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, hp, and_true,
      not_and, not_lt] at hnot
    rcases Nat.lt_or_ge p.1 (m+1) with h1 | h1
    · have h2 := hnot h1
      simp [Nat.choose_eq_zero_of_lt (by omega : m+1 < p.2)]
    · simp [Nat.choose_eq_zero_of_lt (by omega : m < p.1)]

/-- The two independent binomial counts combine into a single `Bin(2t-1, 1/2)`, Eq. (7.2). -/
theorem double_sum_eq_single (m : ℕ) (F : ℕ → ℝ) :
    ∑ j ∈ range (m+1), ∑ l ∈ range (m+2), ((m.choose j : ℝ) * ((m+1).choose l)) * F (j+l)
      = ∑ b ∈ range (2*m+2), ((2*m+1).choose b : ℝ) * F b := by
  classical
  have hmaps : ∀ p ∈ range (m+1) ×ˢ range (m+2), p.1 + p.2 ∈ range (2*m+2) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_range]
    omega
  have h1 := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p : ℕ × ℕ => ((m.choose p.1 : ℝ) * ((m+1).choose p.2)) * F (p.1+p.2))
  rw [Finset.sum_product] at h1
  rw [← h1]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hb : ∀ p ∈ (range (m+1) ×ˢ range (m+2)).filter (fun p => p.1 + p.2 = b),
      ((m.choose p.1 : ℝ) * ((m+1).choose p.2)) * F (p.1+p.2)
        = ((m.choose p.1 : ℝ) * ((m+1).choose p.2)) * F b := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [hp.2]
  rw [Finset.sum_congr rfl hb, ← Finset.sum_mul]
  congr 1
  have hcast : ((∑ p ∈ (range (m+1) ×ˢ range (m+2)).filter (fun p => p.1 + p.2 = b),
      (m.choose p.1 * (m+1).choose p.2) : ℕ) : ℝ) = (((2*m+1).choose b : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n:ℝ)) (sum_filter_choose_mul_choose m b)
  push_cast at hcast
  exact hcast

/-- The count sectors carry total weight one. -/
theorem sectorWeight_sum (t : ℕ) (ht : 1 ≤ t) :
    ∑ j ∈ range t, ∑ l ∈ range (t+1), sectorWeight t j l = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have h := double_sum_eq_single m (fun _ => (1:ℝ) / 2^(2*m+1))
  have hidx1 : (m+1) - 1 = m := by omega
  have hidx2 : 2*(m+1) - 1 = 2*m+1 := by omega
  have hidx3 : (m+1) + 1 = m + 2 := by omega
  simp only [sectorWeight, hidx1, hidx2, hidx3]
  have hl : ∀ j ∈ range (m+1), ∀ l ∈ range (m+2),
      ((m.choose j : ℝ) * ((m+1).choose l)) / 2^(2*m+1)
        = ((m.choose j : ℝ) * ((m+1).choose l)) * ((1:ℝ)/2^(2*m+1)) := by
    intro j _ l _; ring
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun l hl' => hl j hj l hl'))]
  rw [h]
  rw [← Finset.sum_mul]
  have hchoose : ∑ b ∈ range (2*m+2), ((2*m+1).choose b : ℝ) = 2^(2*m+1) := by
    have := Nat.sum_range_choose (2*m+1)
    have h2 : ((∑ b ∈ range (2*m+2), (2*m+1).choose b : ℕ) : ℝ) = ((2^(2*m+1) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n:ℝ)) this
    push_cast at h2
    exact h2
  rw [hchoose]
  field_simp

/-- **Eq. (7.3).**  The exact average branch entropy at every finite time:
`E f₁(Δ_t) = (t C(2t,t)/4^t - 1/2) log q`. -/
theorem expImbEntropy_eq (q : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    expImbEntropy q t = ((t : ℝ) * cr t - 1/2) * Real.log q := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hidx1 : (m+1) - 1 = m := by omega
  have hidx2 : 2*(m+1) - 1 = 2*m+1 := by omega
  have hidx3 : (m+1) + 1 = m + 2 := by omega
  -- rewrite the double sum as a single binomial sum
  have hred := double_sum_eq_single m
    (fun b => imbEntropy q ((b:ℤ) + 1 - (m+1)) / 2^(2*m+1))
  have hstep : expImbEntropy q (m+1)
      = ∑ b ∈ range (2*m+2), ((2*m+1).choose b : ℝ)
          * (imbEntropy q ((b:ℤ) + 1 - (m+1)) / 2^(2*m+1)) := by
    rw [← hred]
    simp only [expImbEntropy, sectorWeight, hidx1, hidx3]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    push_cast
    rw [hidx2]
    ring
  rw [hstep]
  -- identify the summand with the mean absolute deviation
  have hterm : ∀ b ∈ range (2*m+2), ((2*m+1).choose b : ℝ)
        * (imbEntropy q ((b:ℤ) + 1 - (m+1)) / 2^(2*m+1))
      = Real.log q * (((2*m+1).choose b : ℝ) / 2^(2*m+1)
          * |(b:ℝ) - ((2*((m:ℝ)+1)-1)/2)|)
        - Real.log q * (1/2) * (((2*m+1).choose b : ℝ) / 2^(2*m+1)) := by
    intro b _
    have habs : |((((b:ℤ) + 1 - (m+1) : ℤ)):ℝ) - 1/2| = |(b:ℝ) - ((2*((m:ℝ)+1)-1)/2)| := by
      congr 1
      push_cast
      ring
    simp only [imbEntropy, gImb, habs]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hmad : ∑ b ∈ range (2*m+2), (((2*m+1).choose b : ℝ) / 2^(2*m+1)
      * |(b:ℝ) - ((2*((m:ℝ)+1)-1)/2)|) = madBin (m+1) := by
    unfold madBin
    rw [hidx2, show 2*(m+1) = 2*m+2 by ring]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  have hone : ∑ b ∈ range (2*m+2), (((2*m+1).choose b : ℝ) / 2^(2*m+1)) = 1 := by
    rw [← Finset.sum_div]
    have hchoose : ∑ b ∈ range (2*m+2), ((2*m+1).choose b : ℝ) = 2^(2*m+1) := by
      have h := Nat.sum_range_choose (2*m+1)
      have h2 : ((∑ b ∈ range (2*m+2), (2*m+1).choose b : ℕ) : ℝ) = ((2^(2*m+1) : ℕ) : ℝ) :=
        congrArg (fun n : ℕ => (n:ℝ)) h
      push_cast at h2
      exact h2
    rw [hchoose]
    field_simp
  rw [hmad, hone, madBin_eq (m+1) (by omega)]
  push_cast
  ring

/-- **Eq. (7.4).**  Sharp form of the average branch entropy. -/
theorem expImbEntropy_bounds (q : ℝ) (hq : 1 ≤ q) (t : ℕ) (ht : 1 ≤ t) :
    Real.sqrt ((t:ℝ)/Real.pi) * Real.log q - (3/2) * Real.log q ≤ expImbEntropy q t ∧
      expImbEntropy q t ≤ Real.sqrt ((t:ℝ)/Real.pi) * Real.log q := by
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  rw [expImbEntropy_eq q t ht]
  constructor
  · have h := sqrt_sub_one_le_mul_cr t
    nlinarith [h, hlogq]
  · have h := mul_cr_le_sqrt t
    nlinarith [h, hlogq]

/-! ### Shannon entropy of the count labels -/

/-- Shannon entropy is at most the logarithm of the number of outcomes. -/
theorem shannon_le_log_card {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) (hsum : ∑ i ∈ s, p i = 1) :
    -∑ i ∈ s, p i * Real.log (p i) ≤ Real.log s.card := by
  have hne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · simp at hsum
    · exact h
  have hN : (0:ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have key : ∀ i ∈ s, -(p i * Real.log (p i)) - p i * Real.log (s.card : ℝ)
      ≤ 1/(s.card : ℝ) - p i := by
    intro i hi
    have hpi := hp i hi
    have h1 : Real.log (1/(p i * (s.card:ℝ))) ≤ 1/(p i * (s.card:ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (1/(p i * (s.card:ℝ))) = -(Real.log (p i)) - Real.log (s.card:ℝ) := by
      rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hpi) (ne_of_gt hN)]
      ring
    rw [h2] at h1
    have h3 : p i * (-(Real.log (p i)) - Real.log (s.card:ℝ))
        ≤ p i * (1/(p i * (s.card:ℝ)) - 1) := by
      exact mul_le_mul_of_nonneg_left h1 hpi.le
    have h4 : p i * (1/(p i * (s.card:ℝ)) - 1) = 1/(s.card:ℝ) - p i := by
      field_simp
    nlinarith [h3, h4]
  have hsum2 := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum,
    Finset.sum_const, nsmul_eq_mul] at hsum2
  have hcard : (s.card : ℝ) * (1/(s.card:ℝ)) = 1 := by field_simp
  rw [hcard] at hsum2
  rw [← Finset.sum_neg_distrib]
  linarith [hsum2]

/-- The Shannon entropy of `Bin(n, 1/2)`, i.e. `H(K_t)` and `H(L_t)` of Section 7. -/
noncomputable def binEntropy (n : ℕ) : ℝ :=
  -∑ j ∈ range (n+1), ((n.choose j : ℝ) / 2^n) * Real.log ((n.choose j : ℝ) / 2^n)

/-- The count-label entropies are logarithmic, Eq. (7.6) in the weak form needed. -/
theorem binEntropy_le_log (n : ℕ) : binEntropy n ≤ Real.log (n+1) := by
  have hpos : ∀ j ∈ range (n+1), (0:ℝ) < ((n.choose j : ℝ) / 2^n) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have : 0 < n.choose j := Nat.choose_pos (by omega)
    have : (0:ℝ) < (n.choose j : ℝ) := by exact_mod_cast this
    positivity
  have hsum : ∑ j ∈ range (n+1), ((n.choose j : ℝ) / 2^n) = 1 := by
    rw [← Finset.sum_div]
    have h := Nat.sum_range_choose n
    have h2 : ((∑ j ∈ range (n+1), n.choose j : ℕ) : ℝ) = ((2^n : ℕ) : ℝ) :=
      congrArg (fun k : ℕ => (k:ℝ)) h
    push_cast at h2
    rw [h2]
    field_simp
  have h := shannon_le_log_card (range (n+1)) (fun j => ((n.choose j : ℝ) / 2^n)) hpos hsum
  simpa [binEntropy, Finset.card_range] using h

theorem binEntropy_nonneg (n : ℕ) : 0 ≤ binEntropy n := by
  rw [binEntropy, ← Finset.sum_neg_distrib]
  refine Finset.sum_nonneg (fun j hj => ?_)
  simp only [Finset.mem_range] at hj
  have hc : (0:ℝ) < (n.choose j : ℝ) := by
    have : 0 < n.choose j := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hp : (0:ℝ) < (n.choose j : ℝ) / 2^n := by positivity
  have hle : ((n.choose j : ℝ)) / 2^n ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.choose_le_two_pow (n := n) (k := j)
  have hlog := Real.log_nonpos hp.le hle
  nlinarith [hlog, hp]

/-! ### Theorem 7.1 -/

/-- **Theorem 7.1 (leading square-root coefficient).**

Let `q ≥ 1` and let `S₁ t` be the von Neumann operator entanglement of the evolved
operator `O_q(t)` across the fixed cut.  Assume the entropy sandwich of Corollary 5.5:
the average branch entropy `E f₁(Δ_t)` is a lower bound (Proposition 5.3, local count
measurement) and adding the Shannon entropies of the two count labels gives an upper
bound (Proposition 5.4, pinching).  Then

`|S₁(t) - (log q) √(t/π)| ≤ 2 log q + 2 log (t+1)`,

i.e. `S₁^op(O_q(t)) = (log q/√π) √t + O_q(log t)`. -/
theorem vonNeumann_sqrt_law (q : ℝ) (hq : 1 ≤ q) (S1 : ℕ → ℝ)
    (hlow : ∀ t, 1 ≤ t → expImbEntropy q t ≤ S1 t)
    (hupp : ∀ t, 1 ≤ t → S1 t ≤ binEntropy (t-1) + binEntropy t + expImbEntropy q t)
    (t : ℕ) (ht : 1 ≤ t) :
    |S1 t - Real.log q * Real.sqrt ((t:ℝ)/Real.pi)| ≤ 2 * Real.log q + 2 * Real.log (t+1) := by
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  obtain ⟨hE1, hE2⟩ := expImbEntropy_bounds q hq t ht
  have hlow' := hlow t ht
  have hupp' := hupp t ht
  have hH1 : binEntropy (t-1) ≤ Real.log ((t:ℝ)) := by
    have h := binEntropy_le_log (t-1)
    have : ((t-1 : ℕ) : ℝ) + 1 = (t:ℝ) := by
      have : (1:ℕ) ≤ t := ht
      push_cast [Nat.cast_sub this]
      ring
    rwa [this] at h
  have hH2 : binEntropy t ≤ Real.log ((t:ℝ)+1) := by
    have h := binEntropy_le_log t
    push_cast at h
    exact h
  have hmono : Real.log ((t:ℝ)) ≤ Real.log ((t:ℝ)+1) := by
    apply Real.log_le_log (by exact_mod_cast ht) (by linarith)
  rw [abs_le]
  constructor
  · nlinarith [hlow', hE1, hlogq]
  · nlinarith [hupp', hE2, hH1, hH2, hmono]

/-- The sandwich hypotheses of `vonNeumann_sqrt_law` are consistent (they are satisfied,
for instance, by the average branch entropy itself), so the theorem is not vacuous. -/
theorem sandwich_satisfiable (q : ℝ) :
    ∃ S1 : ℕ → ℝ, (∀ t, 1 ≤ t → expImbEntropy q t ≤ S1 t) ∧
      (∀ t, 1 ≤ t → S1 t ≤ binEntropy (t-1) + binEntropy t + expImbEntropy q t) :=
  ⟨expImbEntropy q, fun _ _ => le_refl _,
    fun t _ => by linarith [binEntropy_nonneg (t-1), binEntropy_nonneg t]⟩

/-- **Eq. (7.5).**  The local count measurement alone already forces square-root growth:
the post-measurement average entanglement is at least `(log q) √(t/π) - (3/2) log q`, which
rules out logarithmic growth without any statement about inter-sector coherence. -/
theorem vonNeumann_sqrt_lower_bound (q : ℝ) (hq : 1 ≤ q) (S1 : ℕ → ℝ)
    (hlow : ∀ t, 1 ≤ t → expImbEntropy q t ≤ S1 t) (t : ℕ) (ht : 1 ≤ t) :
    Real.log q * Real.sqrt ((t:ℝ)/Real.pi) - (3/2) * Real.log q ≤ S1 t := by
  obtain ⟨hE1, _⟩ := expImbEntropy_bounds q hq t ht
  have := hlow t ht
  nlinarith [hE1, this]

/-- The square-root law in the form of Eq. (1.1):
`S₁(t) - (log q/√π) √t` is `O(log t)`. -/
theorem vonNeumann_sqrt_law_isBigO (q : ℝ) (hq : 1 ≤ q) (S1 : ℕ → ℝ)
    (hlow : ∀ t, 1 ≤ t → expImbEntropy q t ≤ S1 t)
    (hupp : ∀ t, 1 ≤ t → S1 t ≤ binEntropy (t-1) + binEntropy t + expImbEntropy q t) :
    (fun t : ℕ => S1 t - (Real.log q / Real.sqrt Real.pi) * Real.sqrt t)
      =O[Filter.atTop] (fun t : ℕ => Real.log (t+1)) := by
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  refine Asymptotics.IsBigO.of_bound (2 * Real.log q + 2) ?_
  filter_upwards [Filter.eventually_ge_atTop 3] with t ht
  have ht1 : 1 ≤ t := by omega
  have hkey := vonNeumann_sqrt_law q hq S1 hlow hupp t ht1
  have hsplit : Real.sqrt ((t:ℝ)/Real.pi) = Real.sqrt t / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by positivity)]
  rw [hsplit] at hkey
  have heq : Real.log q * (Real.sqrt t / Real.sqrt Real.pi)
      = Real.log q / Real.sqrt Real.pi * Real.sqrt t := by ring
  rw [heq] at hkey
  have hlog1 : (1:ℝ) ≤ Real.log ((t:ℝ)+1) := by
    have h4 : (4:ℝ) ≤ (t:ℝ) + 1 := by
      have : (3:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
      linarith
    calc (1:ℝ) ≤ Real.log 4 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
          push_cast
          nlinarith [Real.log_two_gt_d9]
      _ ≤ Real.log ((t:ℝ)+1) := Real.log_le_log (by norm_num) h4
  have hnn : 0 ≤ Real.log ((t:ℝ)+1) := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
  calc |S1 t - Real.log q / Real.sqrt Real.pi * Real.sqrt t|
      ≤ 2 * Real.log q + 2 * Real.log ((t:ℝ)+1) := hkey
    _ ≤ (2 * Real.log q + 2) * Real.log ((t:ℝ)+1) := by nlinarith [hlogq, hlog1]

end SqrtOpEnt
