import RequestProject.CentralBinomial

/-!
# The exact mean absolute deviation of an odd symmetric binomial

This file proves the binomial identity of Appendix B of the manuscript:
if `B ~ Bin(2t-1, 1/2)` then

`E |B - (2t-1)/2| = t * C(2t,t) / 4^t`.

The combinatorial heart is the integer identity

`∑_{b=0}^{2m+1} C(2m+1, b) |2b - (2m+1)| = 2 (2m+1) C(2m, m)`,

proved by telescoping with the two standard absorption identities.
-/

namespace SqrtOpEnt

open Finset

/-- Absorption identity `(i+1) C(2m+1, i+1) = (2m+1) C(2m, i)`. -/
theorem choose_absorb_left (m i : ℕ) :
    ((i:ℤ)+1) * ((2*m+1).choose (i+1) : ℤ) = (2*m+1) * ((2*m).choose i : ℤ) := by
  have h : (2*m+1) * ((2*m).choose i) = ((2*m+1).choose (i+1)) * (i+1) :=
    Nat.add_one_mul_choose_eq (2*m) i
  have h' : (((2*m+1) * ((2*m).choose i) : ℕ) : ℤ) = ((((2*m+1).choose (i+1)) * (i+1) : ℕ) : ℤ) :=
    congrArg _ h
  push_cast at h'
  linarith [h']

/-- Absorption identity `((2m+1) - b) C(2m+1, b) = (2m+1) C(2m, b)`. -/
theorem choose_absorb_right (m b : ℕ) (h : b ≤ 2*m+1) :
    ((2*m+1 : ℤ) - b) * ((2*m+1).choose b : ℤ) = (2*m+1) * ((2*m).choose b : ℤ) := by
  have h1 : ((2*m+1).choose b) * ((2*m+1) - b) = ((2*m+1).choose (b+1)) * (b+1) :=
    (Nat.choose_succ_right_eq (2*m+1) b).symm
  have h1' : ((((2*m+1).choose b) * ((2*m+1) - b) : ℕ) : ℤ)
      = ((((2*m+1).choose (b+1)) * (b+1) : ℕ) : ℤ) := congrArg _ h1
  rw [Nat.cast_mul, Nat.cast_sub h] at h1'
  push_cast at h1' ⊢
  have h2 := choose_absorb_left m b
  push_cast at h2
  linarith [h1', h2]

/-- The unnormalized mean absolute deviation of `Bin(2m+1, 1/2)`, in exact integer form. -/
theorem sum_choose_mul_abs (m : ℕ) :
    ∑ b ∈ range (2*m+2), ((2*m+1).choose b : ℤ) * |2*(b:ℤ) - (2*m+1)|
      = 2*(2*m+1)*((2*m).choose m : ℤ) := by
  classical
  set v : ℕ → ℤ := fun i => if i = 0 then 0 else ((2*m).choose (i-1) : ℤ) with hv
  set G : ℕ → ℤ := fun i => ((2*m).choose (m+i) : ℤ) with hG
  rw [show 2*m+2 = (m+1)+(m+1) by ring, Finset.sum_range_add]
  have part1 : ∑ b ∈ range (m+1), ((2*m+1).choose b : ℤ) * |2*(b:ℤ) - (2*m+1)|
      = (2*m+1) * ((2*m).choose m : ℤ) := by
    have hterm : ∀ b ∈ range (m+1),
        ((2*m+1).choose b : ℤ) * |2*(b:ℤ) - (2*m+1)| = (2*m+1) * (v (b+1) - v b) := by
      intro b hb
      simp only [Finset.mem_range] at hb
      have habs : |2*(b:ℤ) - (2*m+1)| = (2*m+1) - 2*b := by
        rw [abs_of_nonpos (by omega)]; ring
      rw [habs]
      have h2 := choose_absorb_right m b (by omega)
      have hvb1 : v (b+1) = ((2*m).choose b : ℤ) := by simp [hv]
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · subst hb0
        simp [hv]
      · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        have h1 := choose_absorb_left m c
        have hvb : v (c+1) = ((2*m).choose c : ℤ) := by simp [hv]
        rw [hvb1, hvb]
        push_cast at h1 h2 ⊢
        linear_combination h2 - h1
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_range_sub v (m+1)]
    simp [hv]
  have part2 : ∑ i ∈ range (m+1), ((2*m+1).choose ((m+1)+i) : ℤ)
        * |2*(((m+1)+i : ℕ):ℤ) - (2*m+1)| = (2*m+1) * ((2*m).choose m : ℤ) := by
    have hterm : ∀ i ∈ range (m+1),
        ((2*m+1).choose ((m+1)+i) : ℤ) * |2*(((m+1)+i : ℕ):ℤ) - (2*m+1)|
          = (2*m+1) * (G i - G (i+1)) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      have habs : |2*(((m+1)+i : ℕ):ℤ) - (2*m+1)| = 2*((m:ℤ)+1+i) - (2*m+1) := by
        rw [abs_of_nonneg (by push_cast; omega)]; push_cast; ring
      rw [habs]
      have h2 := choose_absorb_right m ((m+1)+i) (by omega)
      have h1 := choose_absorb_left m (m+i)
      have hgi1 : G (i+1) = ((2*m).choose (m+i+1) : ℤ) := by
        simp [hG, show m+(i+1) = m+i+1 by ring]
      rw [hgi1, show G i = ((2*m).choose (m+i) : ℤ) from rfl,
        show (m+1)+i = m+i+1 from by omega]
      rw [show (m+1)+i = m+i+1 from by omega] at h2
      push_cast at h1 h2 ⊢
      linear_combination h1 - h2
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_range_sub' G (m+1)]
    have hz : G (m+1) = 0 := by
      simp [hG, Nat.choose_eq_zero_of_lt (by omega : 2*m < m + (m+1))]
    rw [hz]
    simp [hG]
  rw [part1, part2]
  ring

/-- The mean absolute deviation of `Bin(2t-1, 1/2)` about its mean `(2t-1)/2`. -/
noncomputable def madBin (t : ℕ) : ℝ :=
  ∑ b ∈ range (2*t), ((2*t-1).choose b : ℝ) / 2^(2*t-1) * |(b:ℝ) - ((2*(t:ℝ)-1)/2)|

/-- **Appendix B, Eq. (B.3).**  Exact mean absolute deviation of an odd symmetric binomial:
`E |B - (2t-1)/2| = t C(2t,t) / 4^t` for `B ~ Bin(2t-1, 1/2)`. -/
theorem madBin_eq (t : ℕ) (ht : 1 ≤ t) : madBin t = (t : ℝ) * cr t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hint := sum_choose_mul_abs m
  have hreal : ∑ b ∈ range (2*m+2), ((2*m+1).choose b : ℝ) * |2*(b:ℝ) - (2*(m:ℝ)+1)|
      = 2*(2*(m:ℝ)+1)*((2*m).choose m : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hint
    push_cast at this
    exact this
  have hidx1 : 2*(m+1) - 1 = 2*m+1 := by omega
  have hidx2 : 2*(m+1) = 2*m+2 := by omega
  unfold madBin
  rw [hidx1, hidx2]
  have hstep : ∀ b : ℕ, ((2*m+1).choose b : ℝ) / 2^(2*m+1) * |(b:ℝ) - ((2*((m:ℝ)+1)-1)/2)|
      = (1 / 2^(2*m+2)) * (((2*m+1).choose b : ℝ) * |2*(b:ℝ) - (2*(m:ℝ)+1)|) := by
    intro b
    have habs : |(b:ℝ) - ((2*((m:ℝ)+1)-1)/2)| = |2*(b:ℝ) - (2*(m:ℝ)+1)| / 2 := by
      rw [show (b:ℝ) - ((2*((m:ℝ)+1)-1)/2) = (2*(b:ℝ) - (2*(m:ℝ)+1))/2 by ring,
        abs_div]
      norm_num
    rw [habs]
    have h2 : (2:ℝ)^(2*m+2) = 2^(2*m+1) * 2 := by ring
    rw [h2]
    field_simp
  push_cast
  rw [Finset.sum_congr rfl (fun b _ => hstep b), ← Finset.mul_sum, hreal]
  -- now compare with `(m+1) * cr (m+1)`
  have hc : ((m:ℝ)+1) * (Nat.centralBinom (m+1) : ℝ) = 2*(2*(m:ℝ)+1)*((2*m).choose m : ℝ) := by
    have h := Nat.succ_mul_centralBinom_succ m
    rw [Nat.centralBinom_eq_two_mul_choose m] at h
    have h' : (((m+1) * Nat.centralBinom (m+1) : ℕ) : ℝ)
        = ((2 * (2*m+1) * ((2*m).choose m) : ℕ) : ℝ) := congrArg _ h
    push_cast at h'
    linarith [h']
  rw [cr, ← hc]
  have h4 : (4:ℝ)^(m+1) = 2^(2*m+2) := by
    rw [show 2*m+2 = 2*(m+1) by ring, pow_mul]; norm_num
  rw [h4]
  field_simp

/-- Sharp asymptotics of the mean absolute deviation:
`|E|B - (2t-1)/2| - √(t/π)| ≤ 1`, the quantitative form of Eq. (7.4). -/
theorem madBin_sub_sqrt_le (t : ℕ) (ht : 1 ≤ t) :
    |madBin t - Real.sqrt ((t:ℝ)/Real.pi)| ≤ 1 := by
  rw [madBin_eq t ht, abs_le]
  constructor
  · linarith [sqrt_sub_one_le_mul_cr t]
  · linarith [mul_cr_le_sqrt t]

end SqrtOpEnt
