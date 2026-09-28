import RequestProject.CentralBinomial
-- Deliberately false: one layer's central-binomial weight 1 * C(2,1) / 4 is 1/2, not 1.
example : (1 : ℝ) * (Nat.choose 2 1 : ℝ) / 4 ^ 1 = 1 := by
  norm_num
