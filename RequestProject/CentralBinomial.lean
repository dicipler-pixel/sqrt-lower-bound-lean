import Mathlib

/-!
# Central binomial ratio and its sharp asymptotics

This file develops the analytic input needed for the square-root entropy law of the
manuscript: sharp two-sided bounds for the normalized central binomial coefficient

`cr t = C(2t, t) / 4 ^ t`.

We prove `1 / (π (t + 1/2)) ≤ cr t ^ 2 ≤ 1 / (π t)` for `t ≥ 1` and deduce
`√(t/π) - 1 ≤ t * cr t ≤ √(t/π)`, which is the quantitative form of the
Stirling estimate `C(2t,t)/4^t = 1/√(π t) (1 + O(1/t))` used in Eq. (7.4)
of the manuscript.
-/

open Real Stirling Filter Topology

namespace SqrtOpEnt

/-- The normalized central binomial coefficient `C(2t,t)/4^t`. -/
noncomputable def cr (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

lemma cr_pos (n : ℕ) : 0 < cr n := by
  have : 0 < (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos n
  unfold cr; positivity

lemma cr_zero : cr 0 = 1 := by simp [cr, Nat.centralBinom]

/-- The recursion `cr (n+1) = cr n * (2n+1)/(2n+2)`. -/
lemma cr_succ (n : ℕ) : cr (n + 1) = cr n * (2 * n + 1) / (2 * (n + 1)) := by
  have h : ((n : ℝ) + 1) * (Nat.centralBinom (n+1) : ℝ)
      = 2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (Nat.succ_mul_centralBinom_succ n)
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  unfold cr
  field_simp
  ring_nf
  ring_nf at h
  nlinarith [h, pow_pos (show (0:ℝ) < 4 by norm_num) n]

/-- Stirling form of the central binomial ratio. -/
theorem cr_stirling (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt n * cr n = stirlingSeq (2 * n) / (stirlingSeq n) ^ 2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by positivity
  have hpow : (0:ℝ) < ((n:ℝ) / Real.exp 1) ^ (2*n) := by positivity
  have hfac2 : ((2*n).factorial : ℝ) = (Nat.centralBinom n : ℝ) * (n.factorial * n.factorial) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
    have h2 : (2*n) - n = n := by omega
    rw [h2] at h
    rw [← mul_assoc]
    exact_mod_cast h.symm
  have hs4 : Real.sqrt (2 * ((2*n : ℕ) : ℝ)) = 2 * Real.sqrt n := by
    push_cast
    rw [show (2 * (2 * (n:ℝ))) = 2^2 * n by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hp2 : ((((2*n : ℕ)):ℝ) / Real.exp 1) ^ (2*n) = 2 ^ (2*n) * ((n:ℝ) / Real.exp 1) ^ (2*n) := by
    push_cast
    rw [← mul_pow]
    ring_nf
  unfold stirlingSeq cr
  rw [hfac2, hs4, hp2]
  have hs2 : Real.sqrt (2 * (n:ℝ)) ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  have h4 : (4:ℝ)^n = 2^(2*n) := by rw [pow_mul]; norm_num
  field_simp
  rw [h4, Real.sq_sqrt hn0.le, hs2, ← pow_mul]
  ring

/-- The increasing sequence `A n = n * cr n ^ 2`. -/
noncomputable def crA (n : ℕ) : ℝ := (n : ℝ) * (cr n) ^ 2

/-- The decreasing sequence `B n = (n + 1/2) * cr n ^ 2`. -/
noncomputable def crB (n : ℕ) : ℝ := ((n : ℝ) + 1/2) * (cr n) ^ 2

theorem tendsto_crA : Tendsto crA atTop (𝓝 (1 / Real.pi)) := by
  have h2 : Tendsto (fun n : ℕ => stirlingSeq (2 * n)) atTop (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_stirlingSeq_sqrt_pi.comp
      (Filter.tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by norm_num))
        Filter.tendsto_id)
  have h3 : Tendsto (fun n : ℕ => stirlingSeq (2*n) / (stirlingSeq n)^2) atTop
      (𝓝 (Real.sqrt Real.pi / (Real.sqrt Real.pi)^2)) :=
    h2.div (tendsto_stirlingSeq_sqrt_pi.pow 2) (by positivity)
  have h4 : Real.sqrt Real.pi / (Real.sqrt Real.pi)^2 = 1 / Real.sqrt Real.pi := by
    rw [sq]; field_simp
  rw [h4] at h3
  have h5 : Tendsto (fun n : ℕ => (Real.sqrt n * cr n)^2) atTop (𝓝 ((1/Real.sqrt Real.pi)^2)) := by
    refine (h3.congr' ?_).pow 2
    filter_upwards [eventually_ge_atTop 1] with n hn using (cr_stirling n hn).symm
  have h6 : ((1:ℝ)/Real.sqrt Real.pi)^2 = 1 / Real.pi := by
    rw [div_pow, Real.sq_sqrt Real.pi_pos.le]; norm_num
  rw [h6] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n _
  have h : (0:ℝ) ≤ n := Nat.cast_nonneg n
  rw [crA, mul_pow, Real.sq_sqrt h]

lemma tendsto_cr_sq_zero : Tendsto (fun n : ℕ => (cr n)^2) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => crA n * (1 / (n:ℝ))) atTop (𝓝 ((1/Real.pi) * 0)) :=
    tendsto_crA.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [crA]
  field_simp

theorem tendsto_crB : Tendsto crB atTop (𝓝 (1 / Real.pi)) := by
  have h : Tendsto (fun n : ℕ => crA n + (1/2) * (cr n)^2) atTop (𝓝 (1/Real.pi + (1/2) * 0)) :=
    tendsto_crA.add (tendsto_cr_sq_zero.const_mul (1/2))
  rw [mul_zero, add_zero] at h
  refine h.congr' (Eventually.of_forall ?_)
  intro n; simp [crA, crB]; ring

theorem monotone_crA : Monotone crA := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hc := (cr_pos n).le
  have h := cr_succ n
  have hn : (0:ℝ) < 2 * ((n:ℝ) + 1) := by positivity
  rw [crA, crA, h]
  push_cast
  rw [div_pow, mul_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (cr n), Nat.cast_nonneg (α := ℝ) n, sq_nonneg ((n:ℝ) * cr n)]

theorem antitone_crB : Antitone crB := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have h := cr_succ n
  rw [crB, crB, h]
  push_cast
  rw [div_pow, mul_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (cr n), Nat.cast_nonneg (α := ℝ) n]

/-- `π t (C(2t,t)/4^t)^2 ≤ 1`. -/
theorem crA_le : ∀ n : ℕ, crA n ≤ 1 / Real.pi :=
  monotone_crA.ge_of_tendsto tendsto_crA

/-- `1 ≤ π (t + 1/2) (C(2t,t)/4^t)^2`. -/
theorem le_crB : ∀ n : ℕ, 1 / Real.pi ≤ crB n :=
  antitone_crB.le_of_tendsto tendsto_crB

/-- Upper bound: `t * C(2t,t)/4^t ≤ √(t/π)`. -/
theorem mul_cr_le_sqrt (n : ℕ) : (n : ℝ) * cr n ≤ Real.sqrt ((n : ℝ) / Real.pi) := by
  have hA := crA_le n
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : ((n : ℝ) * cr n)^2 ≤ (n : ℝ) / Real.pi := by
    have : ((n : ℝ) * cr n)^2 = (n:ℝ) * crA n := by rw [crA]; ring
    rw [this]
    calc (n:ℝ) * crA n ≤ (n:ℝ) * (1/Real.pi) := by nlinarith
    _ = (n:ℝ)/Real.pi := by ring
  have h2 : (0:ℝ) ≤ (n : ℝ) * cr n := mul_nonneg hn (cr_pos n).le
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ)/Real.pi by positivity),
    Real.sqrt_nonneg ((n:ℝ)/Real.pi)]

/-- Lower bound: `√(t/π) - 1 ≤ t * C(2t,t)/4^t`. -/
theorem sqrt_sub_one_le_mul_cr (n : ℕ) :
    Real.sqrt ((n : ℝ) / Real.pi) - 1 ≤ (n : ℝ) * cr n := by
  set s := Real.sqrt ((n : ℝ) / Real.pi) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = (n : ℝ) / Real.pi := Real.sq_sqrt (by positivity)
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : (0:ℝ) ≤ (n : ℝ) * cr n := mul_nonneg hn (cr_pos n).le
  rcases le_or_gt s 1 with hle | hgt
  · linarith
  · -- here s > 1, so n/π > 1
    have hB := le_crB n
    have hkey : ((n : ℝ) * cr n)^2 ≥ (n:ℝ)^2 / (Real.pi * ((n:ℝ) + 1/2)) := by
      have hcr2 : (cr n)^2 ≥ 1 / (Real.pi * ((n:ℝ) + 1/2)) := by
        rw [crB] at hB
        rw [ge_iff_le, div_le_iff₀ (by positivity)]
        have hpos : (0:ℝ) < (n:ℝ) + 1/2 := by positivity
        calc (1:ℝ) = Real.pi * (1/Real.pi) := by field_simp
        _ ≤ Real.pi * (((n:ℝ) + 1/2) * (cr n)^2) := by nlinarith
        _ = (cr n)^2 * (Real.pi * ((n:ℝ) + 1/2)) := by ring
      have : ((n : ℝ) * cr n)^2 = (n:ℝ)^2 * (cr n)^2 := by ring
      rw [this]
      have hn2 : (0:ℝ) ≤ (n:ℝ)^2 := sq_nonneg _
      calc (n:ℝ)^2 / (Real.pi * ((n:ℝ) + 1/2)) = (n:ℝ)^2 * (1 / (Real.pi * ((n:ℝ)+1/2))) := by
            ring
      _ ≤ (n:ℝ)^2 * (cr n)^2 := by nlinarith
    -- s > 1 means n > π
    have hnpi : (n:ℝ) = Real.pi * s^2 := by rw [hsq]; field_simp
    have hn1 : (0:ℝ) < (n:ℝ) := by nlinarith [Real.pi_gt_three]
    -- reduce to a polynomial inequality
    by_contra hcon
    push_neg at hcon
    have hlt : ((n : ℝ) * cr n)^2 < (s - 1)^2 := by
      have h1 : (0:ℝ) ≤ s - 1 := by linarith
      nlinarith
    have hcomb : (n:ℝ)^2 / (Real.pi * ((n:ℝ) + 1/2)) < (s-1)^2 := lt_of_le_of_lt hkey hlt
    rw [div_lt_iff₀ (by positivity)] at hcomb
    -- (s-1)^2 = n/π - 2 s + 1
    have hexp : (s-1)^2 = (n:ℝ)/Real.pi - 2*s + 1 := by rw [← hsq]; ring
    have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
    have hs2gt : 1 < s^2 := by nlinarith
    have h1 : (s-1)^2 ≤ s^2 - 1 := by nlinarith
    have key : (s-1)^2 * (Real.pi * ((n:ℝ) + 1/2)) ≤ (n:ℝ)^2 := by
      rw [hnpi]
      calc (s-1)^2 * (Real.pi * (Real.pi * s^2 + 1/2))
          ≤ (s^2-1) * (Real.pi * (Real.pi * s^2 + 1/2)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (Real.pi * s^2)^2 := by nlinarith [hs2gt, hpi3]
    linarith

end SqrtOpEnt
