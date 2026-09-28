import RequestProject.PhasedFourier

/-!
# Quadratic phase on the residual boundary grids

This file turns the cellwise cubic finite difference into the precise
bilinear-plus-one-sided decomposition used by the Fourier flatness theorem.
It is the algebraic bridge between `MixedHessian.lean` and the actual phase
coefficient matrix of a residual grid.
-/

namespace SqrtOpEnt

open Finset Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A separated double sum is the product of its two one-variable sums. -/
theorem boundary_double_sum
    {r s : ℕ} (L : Fin r → F) (R : Fin s → F)
    (u : Fin r → F) (v : Fin s → F) :
    (∑ m : Fin r, ∑ n : Fin s, L m * u m * v n * R n) =
      (∑ m : Fin r, u m * L m) * (∑ n : Fin s, v n * R n) := by
  calc
    (∑ m : Fin r, ∑ n : Fin s, L m * u m * v n * R n) =
        ∑ m : Fin r, (L m * u m) * ∑ n : Fin s, v n * R n := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = (∑ m : Fin r, L m * u m) *
        (∑ n : Fin s, v n * R n) := by rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      ring

/-- Constant coefficients can be pulled out of a separated double sum. -/
theorem boundary_double_sum_const
    {r s : ℕ} (c : F) (L : Fin r → F) (R : Fin s → F)
    (u : Fin r → F) (v : Fin s → F) :
    (∑ m : Fin r, ∑ n : Fin s,
        L m * (c * (u m * v n)) * R n) =
      c * (∑ m : Fin r, u m * L m) *
        (∑ n : Fin s, v n * R n) := by
  calc
    (∑ m : Fin r, ∑ n : Fin s,
        L m * (c * (u m * v n)) * R n) =
      c * ∑ m : Fin r, ∑ n : Fin s, L m * u m * v n * R n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
    _ = _ := by
      rw [boundary_double_sum]
      ring

/-- Quadratic phase contributed by one cell of the positive residual grid. -/
def positiveCellPhase (epsilon : ℕ → ℕ → F) (r : ℕ)
    (L R : Fin r → F) (i j : ℕ) : F :=
  epsilon i j * (positiveBoundaryValue r L R i (j + 1)) ^ 2 +
    2 * epsilon i (j + 1) * positiveBoundaryValue r L R i j *
      positiveBoundaryValue r L R i (j + 1)

/-- Accumulated quadratic phase difference on the positive `r × r` grid. -/
def positiveGridPhase (epsilon : ℕ → ℕ → F) (r : ℕ)
    (L R : Fin r → F) : F :=
  ∑ i : Fin r, ∑ j : Fin r, positiveCellPhase epsilon r L R i j

/-- The full cubic finite difference at one positive-grid cell. -/
def positiveFullCellPhase (epsilon : ℕ → ℕ → F) (r : ℕ)
    (L R : Fin r → F) (i j : ℕ) : F :=
  (positiveBoundaryValue r L R i j + epsilon i j) *
      (positiveBoundaryValue r L R i (j + 1) + epsilon i (j + 1)) ^ 2 -
    positiveBoundaryValue r L R i j *
      (positiveBoundaryValue r L R i (j + 1)) ^ 2

/-- Sum of the full cubic finite difference over the positive response grid. -/
def positiveFullGridPhase (epsilon : ℕ → ℕ → F) (r : ℕ)
    (L R : Fin r → F) : F :=
  ∑ i : Fin r, ∑ j : Fin r, positiveFullCellPhase epsilon r L R i j

/-- Boundary reconstruction is the sum of its left-only and right-only
parts. -/
theorem positiveBoundaryValue_split (r : ℕ) (L R : Fin r → F)
    (i j : ℕ) :
    positiveBoundaryValue r L R i j =
      positiveBoundaryValue r L 0 i j + positiveBoundaryValue r 0 R i j := by
  classical
  simp [positiveBoundaryValue, Finset.mul_sum, Finset.sum_add_distrib]

theorem positiveBoundaryValue_add (r : ℕ)
    (L₁ L₂ R₁ R₂ : Fin r → F) (i j : ℕ) :
    positiveBoundaryValue r (L₁ + L₂) (R₁ + R₂) i j =
      positiveBoundaryValue r L₁ R₁ i j +
        positiveBoundaryValue r L₂ R₂ i j := by
  classical
  simp only [positiveBoundaryValue, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  ring

@[simp]
theorem positiveBoundaryValue_zero (r i j : ℕ) :
    positiveBoundaryValue (F := F) r 0 0 i j = 0 := by
  simp [positiveBoundaryValue]

/-- The full cubic difference is the quadratic phase used by the Hessian
calculation plus a term affine in the unshifted response field. -/
theorem positiveFullCellPhase_eq_quadratic_add
    (epsilon : ℕ → ℕ → F) (r : ℕ)
    (L R : Fin r → F) (i j : ℕ) :
    positiveFullCellPhase epsilon r L R i j =
      positiveCellPhase epsilon r L R i j +
        (epsilon i (j + 1)) ^ 2 * positiveBoundaryValue r L R i j +
        2 * epsilon i j * epsilon i (j + 1) *
          positiveBoundaryValue r L R i (j + 1) +
        epsilon i j * (epsilon i (j + 1)) ^ 2 := by
  unfold positiveFullCellPhase positiveCellPhase
  ring

/-- One positive cell contains exactly the mixed coefficient recorded in
`positiveCellMixed`; all other terms depend on only one boundary side. -/
theorem positiveCellPhase_decompose
    (epsilon : ℕ → ℕ → F) (r : ℕ)
    (L R : Fin r → F) (i j : ℕ) :
    positiveCellPhase epsilon r L R i j =
      positiveCellPhase epsilon r L 0 i j +
        positiveCellPhase epsilon r 0 R i j -
        positiveCellPhase epsilon r 0 0 i j +
        ∑ m : Fin r, ∑ n : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n := by
  classical
  have hcross :
      (∑ m : Fin r, ∑ n : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n) =
        epsilon i j * 2 *
            ((∑ m : Fin r, UposF (F := F) m i (j + 1) * L m) *
              ∑ n : Fin r, VposF (F := F) r n i (j + 1) * R n) +
          2 * epsilon i (j + 1) *
            ((∑ m : Fin r, UposF (F := F) m i j * L m) *
                ∑ n : Fin r, VposF (F := F) r n i (j + 1) * R n +
              (∑ n : Fin r, VposF (F := F) r n i j * R n) *
                ∑ m : Fin r, UposF (F := F) m i (j + 1) * L m) := by
    have hreverse :
        (∑ m : Fin r, ∑ n : Fin r,
            L m * (2 * epsilon i (j + 1) *
              (VposF (F := F) r n i j *
                UposF (F := F) m i (j + 1))) * R n) =
          2 * epsilon i (j + 1) *
            (∑ m : Fin r, UposF (F := F) m i (j + 1) * L m) *
            (∑ n : Fin r, VposF (F := F) r n i j * R n) := by
      calc
        (∑ m : Fin r, ∑ n : Fin r,
            L m * (2 * epsilon i (j + 1) *
              (VposF (F := F) r n i j *
                UposF (F := F) m i (j + 1))) * R n) =
            ∑ m : Fin r, ∑ n : Fin r,
              L m * (2 * epsilon i (j + 1) *
                (UposF (F := F) m i (j + 1) *
                  VposF (F := F) r n i j)) * R n := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := boundary_double_sum_const (2 * epsilon i (j + 1)) L R
          (fun m => UposF (F := F) m i (j + 1))
          (fun n => VposF (F := F) r n i j)
    unfold positiveCellMixed
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    rw [boundary_double_sum_const (epsilon i j * 2) L R
        (fun m => UposF (F := F) m i (j + 1))
        (fun n => VposF (F := F) r n i (j + 1)),
      boundary_double_sum_const (2 * epsilon i (j + 1)) L R
        (fun m => UposF (F := F) m i j)
        (fun n => VposF (F := F) r n i (j + 1)), hreverse]
    ring
  simp only [positiveCellPhase, positiveBoundaryValue, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  rw [hcross]
  ring

/-- Adding back the affine and constant terms of the actual cubic finite
difference leaves the same mixed Hessian. -/
theorem positiveFullCellPhase_decompose
    (epsilon : ℕ → ℕ → F) (r : ℕ)
    (L R : Fin r → F) (i j : ℕ) :
    positiveFullCellPhase epsilon r L R i j =
      positiveFullCellPhase epsilon r L 0 i j +
        positiveFullCellPhase epsilon r 0 R i j -
        positiveFullCellPhase epsilon r 0 0 i j +
        ∑ m : Fin r, ∑ n : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n := by
  rw [positiveFullCellPhase_eq_quadratic_add,
    positiveFullCellPhase_eq_quadratic_add,
    positiveFullCellPhase_eq_quadratic_add,
    positiveFullCellPhase_eq_quadratic_add,
    positiveCellPhase_decompose,
    positiveBoundaryValue_split r L R i j,
    positiveBoundaryValue_split r L R i (j + 1)]
  simp only [positiveBoundaryValue_zero]
  ring

/-- Addition distributes through two nested finite sums. -/
theorem sum_bisum_add {r : ℕ} (f g : Fin r → Fin r → F) :
    (∑ i : Fin r, ∑ j : Fin r, (f i j + g i j)) =
      (∑ i : Fin r, ∑ j : Fin r, f i j) +
        ∑ i : Fin r, ∑ j : Fin r, g i j := by
  simp only [Finset.sum_add_distrib]

/-- Subtraction distributes through two nested finite sums. -/
theorem sum_bisum_sub {r : ℕ} (f g : Fin r → Fin r → F) :
    (∑ i : Fin r, ∑ j : Fin r, (f i j - g i j)) =
      (∑ i : Fin r, ∑ j : Fin r, f i j) -
        ∑ i : Fin r, ∑ j : Fin r, g i j := by
  simp only [Finset.sum_sub_distrib]

/-- Constants can be pulled through two nested finite sums. -/
theorem sum_bisum_mul {r : ℕ} (a b : F) (f : Fin r → Fin r → F) :
    (∑ i : Fin r, ∑ j : Fin r, a * f i j * b) =
      a * (∑ i : Fin r, ∑ j : Fin r, f i j) * b := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Reorder the four finite sums arising from the cell expansion. -/
theorem positive_mixed_sum_comm
    (epsilon : ℕ → ℕ → F) (r : ℕ) (L R : Fin r → F) :
    (∑ i : Fin r, ∑ j : Fin r, ∑ m : Fin r, ∑ n : Fin r,
        L m * positiveCellMixed epsilon r m n i j * R n) =
      ∑ m : Fin r, ∑ n : Fin r, ∑ i : Fin r, ∑ j : Fin r,
        L m * positiveCellMixed epsilon r m n i j * R n := by
  calc
    (∑ i : Fin r, ∑ j : Fin r, ∑ m : Fin r, ∑ n : Fin r,
        L m * positiveCellMixed epsilon r m n i j * R n) =
        ∑ i : Fin r, ∑ m : Fin r, ∑ j : Fin r, ∑ n : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ m : Fin r, ∑ i : Fin r, ∑ j : Fin r, ∑ n : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n := by
      rw [Finset.sum_comm]
    _ = ∑ m : Fin r, ∑ i : Fin r, ∑ n : Fin r, ∑ j : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ m : Fin r, ∑ n : Fin r, ∑ i : Fin r, ∑ j : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]

/-- The accumulated positive-grid phase is its mixed-Hessian bilinear form
plus a left-only and a right-only phase. -/
theorem positiveGridPhase_decompose
    (epsilon : ℕ → ℕ → F) (r : ℕ) (L R : Fin r → F) :
    positiveGridPhase epsilon r L R =
      positiveGridPhase epsilon r L 0 +
        L ⬝ᵥ (positiveMixedHessian epsilon r).mulVec R +
        (positiveGridPhase epsilon r 0 R -
          positiveGridPhase epsilon r 0 0) := by
  classical
  have hmixed :
      (∑ i : Fin r, ∑ j : Fin r, ∑ m : Fin r, ∑ n : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n) =
        L ⬝ᵥ (positiveMixedHessian epsilon r).mulVec R := by
    simp only [Matrix.mulVec, dotProduct, positiveMixedHessian]
    rw [positive_mixed_sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simpa [mul_assoc] using sum_bisum_mul (L m) (R n)
      (fun i j => positiveCellMixed epsilon r m n i j)
  simp only [positiveGridPhase]
  calc
    (∑ i : Fin r, ∑ j : Fin r, positiveCellPhase epsilon r L R i j) =
        ∑ i : Fin r, ∑ j : Fin r,
          (positiveCellPhase epsilon r L 0 i j +
            positiveCellPhase epsilon r 0 R i j -
            positiveCellPhase epsilon r 0 0 i j +
            ∑ m : Fin r, ∑ n : Fin r,
              L m * positiveCellMixed epsilon r m n i j * R n) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact positiveCellPhase_decompose epsilon r L R i j
    _ = (∑ i : Fin r, ∑ j : Fin r,
          positiveCellPhase epsilon r L 0 i j) +
        L ⬝ᵥ (positiveMixedHessian epsilon r).mulVec R +
        ((∑ i : Fin r, ∑ j : Fin r,
          positiveCellPhase epsilon r 0 R i j) -
        ∑ i : Fin r, ∑ j : Fin r,
          positiveCellPhase epsilon r 0 0 i j) := by
      rw [sum_bisum_add, sum_bisum_sub, sum_bisum_add, hmixed]
      ring

/-- The literal full cubic finite difference has the same bilinear mixed
part as `positiveGridPhase`; all extra terms are one-sided phases. -/
theorem positiveFullGridPhase_decompose
    (epsilon : ℕ → ℕ → F) (r : ℕ) (L R : Fin r → F) :
    positiveFullGridPhase epsilon r L R =
      positiveFullGridPhase epsilon r L 0 +
        L ⬝ᵥ (positiveMixedHessian epsilon r).mulVec R +
        (positiveFullGridPhase epsilon r 0 R -
          positiveFullGridPhase epsilon r 0 0) := by
  classical
  have hmixed :
      (∑ i : Fin r, ∑ j : Fin r, ∑ m : Fin r, ∑ n : Fin r,
          L m * positiveCellMixed epsilon r m n i j * R n) =
        L ⬝ᵥ (positiveMixedHessian epsilon r).mulVec R := by
    simp only [Matrix.mulVec, dotProduct, positiveMixedHessian]
    rw [positive_mixed_sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simpa [mul_assoc] using sum_bisum_mul (L m) (R n)
      (fun i j => positiveCellMixed epsilon r m n i j)
  simp only [positiveFullGridPhase]
  calc
    (∑ i : Fin r, ∑ j : Fin r,
        positiveFullCellPhase epsilon r L R i j) =
      ∑ i : Fin r, ∑ j : Fin r,
        (positiveFullCellPhase epsilon r L 0 i j +
          positiveFullCellPhase epsilon r 0 R i j -
          positiveFullCellPhase epsilon r 0 0 i j +
          ∑ m : Fin r, ∑ n : Fin r,
            L m * positiveCellMixed epsilon r m n i j * R n) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact positiveFullCellPhase_decompose epsilon r L R i j
    _ = _ := by
      rw [sum_bisum_add, sum_bisum_sub, sum_bisum_add, hmixed]
      ring

/-- Positive response-grid coefficient matrix, with the source hyperplane
parameterized by `positiveAllowedRight`. -/
noncomputable def positiveGridCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (n : ℕ) :
    Matrix (Fin (n + 1) → F) (Fin n → F) ℂ :=
  phaseCoeff psi fun L x =>
    positiveGridPhase epsilon (n + 1) L (positiveAllowedRight n x)

/-- Removing its one-sided phases identifies the positive response-grid
matrix with the mixed-Hessian Fourier core. -/
theorem positiveGridCoeff_vonNeumannEntropy_eq_fourierCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (n : ℕ) :
    vonNeumannEntropy (positiveGridCoeff psi epsilon n) =
      vonNeumannEntropy
        (fourierCoeff psi (positiveMixedHessian epsilon (n + 1))
          (positiveAllowedRight n)) := by
  apply phaseCoeff_vonNeumannEntropy_eq_fourierCoeff
    psi (positiveMixedHessian epsilon (n + 1))
      (positiveAllowedRight n)
      (fun L => positiveGridPhase epsilon (n + 1) L 0)
      (fun x => positiveGridPhase epsilon (n + 1) 0
        (positiveAllowedRight n x) - positiveGridPhase epsilon (n + 1) 0 0)
  exact fun L x => positiveGridPhase_decompose epsilon (n + 1) L _

/-- The positive response-grid phase matrix has entropy `n log q`. -/
theorem positiveGridCoeff_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    vonNeumannEntropy (positiveGridCoeff psi epsilon n) =
      (n : ℝ) * Real.log (Fintype.card F) := by
  rw [positiveGridCoeff_vonNeumannEntropy_eq_fourierCoeff]
  exact positiveSourceHyperplane_vonNeumannEntropy_eq_mul
    psi hpsi epsilon n hodd hepsilon

/-- Coefficient matrix of the full positive cubic finite difference. -/
noncomputable def positiveFullGridCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (n : ℕ) :
    Matrix (Fin (n + 1) → F) (Fin n → F) ℂ :=
  phaseCoeff psi fun L x =>
    positiveFullGridPhase epsilon (n + 1) L (positiveAllowedRight n x)

/-- The full cubic difference and its quadratic mixed part have identical
normalized Schmidt spectra. -/
theorem positiveFullGridCoeff_vonNeumannEntropy_eq_fourierCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (n : ℕ) :
    vonNeumannEntropy (positiveFullGridCoeff psi epsilon n) =
      vonNeumannEntropy
        (fourierCoeff psi (positiveMixedHessian epsilon (n + 1))
          (positiveAllowedRight n)) := by
  apply phaseCoeff_vonNeumannEntropy_eq_fourierCoeff
    psi (positiveMixedHessian epsilon (n + 1))
      (positiveAllowedRight n)
      (fun L => positiveFullGridPhase epsilon (n + 1) L 0)
      (fun x => positiveFullGridPhase epsilon (n + 1) 0
        (positiveAllowedRight n x) - positiveFullGridPhase epsilon (n + 1) 0 0)
  exact fun L x => positiveFullGridPhase_decompose epsilon (n + 1) L _

/-- The actual positive cubic finite-difference matrix has entropy
`n * log q`. -/
theorem positiveFullGridCoeff_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (n : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < n + 1, epsilon m 1 = 1) :
    vonNeumannEntropy (positiveFullGridCoeff psi epsilon n) =
      (n : ℝ) * Real.log (Fintype.card F) := by
  rw [positiveFullGridCoeff_vonNeumannEntropy_eq_fourierCoeff]
  exact positiveSourceHyperplane_vonNeumannEntropy_eq_mul
    psi hpsi epsilon n hodd hepsilon

/-! ## Negative imbalance -/

/-- Quadratic phase contributed by one cell of the negative residual grid. -/
def negativeCellPhase (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) (i j : ℕ) : F :=
  (3 * epsilon i (j + 1) - epsilon i j) *
      (negativeBoundaryValue s L R i (j + 1)) ^ 2 -
    2 * epsilon i (j + 1) * negativeBoundaryValue s L R i j *
      negativeBoundaryValue s L R i (j + 1)

/-- Accumulated quadratic phase difference on the negative grid. -/
def negativeGridPhase (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) : F :=
  ∑ i : Fin s, ∑ j : Fin s, negativeCellPhase epsilon s L R i j

/-- Boundary reconstruction for the negative grid is additive in its two
boundary inputs. -/
theorem negativeBoundaryValue_split (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) (i j : ℕ) :
    negativeBoundaryValue s L R i j =
      negativeBoundaryValue s L 0 i j + negativeBoundaryValue s 0 R i j := by
  classical
  simp [negativeBoundaryValue]

theorem negativeBoundaryValue_add (s : ℕ)
    (L₁ L₂ : Fin s → F) (R₁ R₂ : Fin (s + 1) → F) (i j : ℕ) :
    negativeBoundaryValue s (L₁ + L₂) (R₁ + R₂) i j =
      negativeBoundaryValue s L₁ R₁ i j +
        negativeBoundaryValue s L₂ R₂ i j := by
  classical
  simp only [negativeBoundaryValue, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  ring

@[simp]
theorem negativeBoundaryValue_zero (s i j : ℕ) :
    negativeBoundaryValue (F := F) s 0 0 i j = 0 := by
  simp [negativeBoundaryValue]

/-- The full literal phase difference at one negative-grid cell.  The local
circuit exponent is `(c-d)d²`, while the coefficient phase is bra minus ket. -/
def negativeFullCellPhase (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) (i j : ℕ) : F :=
  let c := negativeBoundaryValue s L R i j
  let d := negativeBoundaryValue s L R i (j + 1)
  (c - d) * d ^ 2 -
    ((c + epsilon i j) - (d + epsilon i (j + 1))) *
      (d + epsilon i (j + 1)) ^ 2

/-- Sum of the full negative cubic phase difference. -/
def negativeFullGridPhase (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) : F :=
  ∑ i : Fin s, ∑ j : Fin s, negativeFullCellPhase epsilon s L R i j

/-- The literal negative cubic difference is its quadratic Hessian phase
plus a term affine in the unshifted response field. -/
theorem negativeFullCellPhase_eq_quadratic_add
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) (i j : ℕ) :
    negativeFullCellPhase epsilon s L R i j =
      negativeCellPhase epsilon s L R i j -
        (epsilon i (j + 1)) ^ 2 * negativeBoundaryValue s L R i j +
        (3 * (epsilon i (j + 1)) ^ 2 -
          2 * epsilon i j * epsilon i (j + 1)) *
            negativeBoundaryValue s L R i (j + 1) +
        (epsilon i (j + 1)) ^ 3 -
          epsilon i j * (epsilon i (j + 1)) ^ 2 := by
  unfold negativeFullCellPhase negativeCellPhase
  dsimp only
  ring

/-- One negative cell contains exactly the mixed coefficient recorded in
`negativeCellMixed`; all remaining terms are one-sided. -/
theorem negativeCellPhase_decompose
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) (i j : ℕ) :
    negativeCellPhase epsilon s L R i j =
      negativeCellPhase epsilon s L 0 i j +
        negativeCellPhase epsilon s 0 R i j -
        negativeCellPhase epsilon s 0 0 i j +
        ∑ m : Fin s, ∑ n : Fin (s + 1),
          L m * negativeCellMixed epsilon s m n i j * R n := by
  classical
  have hcross :
      (∑ m : Fin s, ∑ n : Fin (s + 1),
          L m * negativeCellMixed epsilon s m n i j * R n) =
        2 * (3 * epsilon i (j + 1) - epsilon i j) *
            ((∑ m : Fin s, UnegF (F := F) m i (j + 1) * L m) *
              ∑ n : Fin (s + 1), VnegF (F := F) s n i (j + 1) * R n) -
          2 * epsilon i (j + 1) *
            ((∑ m : Fin s, UnegF (F := F) m i j * L m) *
                ∑ n : Fin (s + 1), VnegF (F := F) s n i (j + 1) * R n +
              (∑ n : Fin (s + 1), VnegF (F := F) s n i j * R n) *
                ∑ m : Fin s, UnegF (F := F) m i (j + 1) * L m) := by
    have hreverse :
        (∑ m : Fin s, ∑ n : Fin (s + 1),
            L m * (2 * epsilon i (j + 1) *
              (VnegF (F := F) s n i j *
                UnegF (F := F) m i (j + 1))) * R n) =
          2 * epsilon i (j + 1) *
            (∑ m : Fin s, UnegF (F := F) m i (j + 1) * L m) *
            (∑ n : Fin (s + 1), VnegF (F := F) s n i j * R n) := by
      calc
        (∑ m : Fin s, ∑ n : Fin (s + 1),
            L m * (2 * epsilon i (j + 1) *
              (VnegF (F := F) s n i j *
                UnegF (F := F) m i (j + 1))) * R n) =
            ∑ m : Fin s, ∑ n : Fin (s + 1),
              L m * (2 * epsilon i (j + 1) *
                (UnegF (F := F) m i (j + 1) *
                  VnegF (F := F) s n i j)) * R n := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := boundary_double_sum_const (2 * epsilon i (j + 1)) L R
          (fun m => UnegF (F := F) m i (j + 1))
          (fun n => VnegF (F := F) s n i j)
    unfold negativeCellMixed
    calc
      (∑ m : Fin s, ∑ n : Fin (s + 1),
          L m *
            (2 * (3 * epsilon i (j + 1) - epsilon i j) *
                (UnegF (F := F) m i (j + 1) *
                  VnegF (F := F) s n i (j + 1)) -
              2 * epsilon i (j + 1) *
                (UnegF (F := F) m i j *
                    VnegF (F := F) s n i (j + 1) +
                  VnegF (F := F) s n i j *
                    UnegF (F := F) m i (j + 1))) * R n) =
          ∑ m : Fin s, ∑ n : Fin (s + 1),
            (L m * (2 * (3 * epsilon i (j + 1) - epsilon i j) *
              (UnegF (F := F) m i (j + 1) *
                VnegF (F := F) s n i (j + 1))) * R n -
             L m * (2 * epsilon i (j + 1) *
              (UnegF (F := F) m i j *
                VnegF (F := F) s n i (j + 1))) * R n -
             L m * (2 * epsilon i (j + 1) *
              (VnegF (F := F) s n i j *
                UnegF (F := F) m i (j + 1))) * R n) := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ =
          (∑ m : Fin s, ∑ n : Fin (s + 1),
            L m * (2 * (3 * epsilon i (j + 1) - epsilon i j) *
              (UnegF (F := F) m i (j + 1) *
                VnegF (F := F) s n i (j + 1))) * R n) -
          (∑ m : Fin s, ∑ n : Fin (s + 1),
            L m * (2 * epsilon i (j + 1) *
              (UnegF (F := F) m i j *
                VnegF (F := F) s n i (j + 1))) * R n) -
          (∑ m : Fin s, ∑ n : Fin (s + 1),
            L m * (2 * epsilon i (j + 1) *
              (VnegF (F := F) s n i j *
                UnegF (F := F) m i (j + 1))) * R n) := by
        simp only [Finset.sum_sub_distrib]
      _ = _ := by
        rw [boundary_double_sum_const
            (2 * (3 * epsilon i (j + 1) - epsilon i j)) L R
            (fun m => UnegF (F := F) m i (j + 1))
            (fun n => VnegF (F := F) s n i (j + 1)),
          boundary_double_sum_const (2 * epsilon i (j + 1)) L R
            (fun m => UnegF (F := F) m i j)
            (fun n => VnegF (F := F) s n i (j + 1)), hreverse]
        ring
  simp only [negativeCellPhase, negativeBoundaryValue, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  rw [hcross]
  ring

/-- The extra affine terms in the full negative cubic difference do not
alter its mixed Hessian. -/
theorem negativeFullCellPhase_decompose
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) (i j : ℕ) :
    negativeFullCellPhase epsilon s L R i j =
      negativeFullCellPhase epsilon s L 0 i j +
        negativeFullCellPhase epsilon s 0 R i j -
        negativeFullCellPhase epsilon s 0 0 i j +
        ∑ m : Fin s, ∑ n : Fin (s + 1),
          L m * negativeCellMixed epsilon s m n i j * R n := by
  rw [negativeFullCellPhase_eq_quadratic_add,
    negativeFullCellPhase_eq_quadratic_add,
    negativeFullCellPhase_eq_quadratic_add,
    negativeFullCellPhase_eq_quadratic_add,
    negativeCellPhase_decompose,
    negativeBoundaryValue_split s L R i j,
    negativeBoundaryValue_split s L R i (j + 1)]
  simp only [negativeBoundaryValue_zero]
  ring

/-- Reorder the four finite sums in the negative mixed term. -/
theorem negative_mixed_sum_comm
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    (∑ i : Fin s, ∑ j : Fin s, ∑ m : Fin s, ∑ n : Fin (s + 1),
        L m * negativeCellMixed epsilon s m n i j * R n) =
      ∑ m : Fin s, ∑ n : Fin (s + 1), ∑ i : Fin s, ∑ j : Fin s,
        L m * negativeCellMixed epsilon s m n i j * R n := by
  calc
    (∑ i : Fin s, ∑ j : Fin s, ∑ m : Fin s, ∑ n : Fin (s + 1),
        L m * negativeCellMixed epsilon s m n i j * R n) =
        ∑ i : Fin s, ∑ m : Fin s, ∑ j : Fin s, ∑ n : Fin (s + 1),
          L m * negativeCellMixed epsilon s m n i j * R n := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ m : Fin s, ∑ i : Fin s, ∑ j : Fin s, ∑ n : Fin (s + 1),
          L m * negativeCellMixed epsilon s m n i j * R n := by
      rw [Finset.sum_comm]
    _ = ∑ m : Fin s, ∑ i : Fin s, ∑ n : Fin (s + 1), ∑ j : Fin s,
          L m * negativeCellMixed epsilon s m n i j * R n := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ m : Fin s, ∑ n : Fin (s + 1), ∑ i : Fin s, ∑ j : Fin s,
          L m * negativeCellMixed epsilon s m n i j * R n := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]

/-- The accumulated negative-grid phase is its mixed-Hessian bilinear form
plus one-sided phases. -/
theorem negativeGridPhase_decompose
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    negativeGridPhase epsilon s L R =
      negativeGridPhase epsilon s L 0 +
        L ⬝ᵥ (negativeMixedHessian epsilon s).mulVec R +
        (negativeGridPhase epsilon s 0 R -
          negativeGridPhase epsilon s 0 0) := by
  classical
  have hmixed :
      (∑ i : Fin s, ∑ j : Fin s, ∑ m : Fin s, ∑ n : Fin (s + 1),
          L m * negativeCellMixed epsilon s m n i j * R n) =
        L ⬝ᵥ (negativeMixedHessian epsilon s).mulVec R := by
    simp only [Matrix.mulVec, dotProduct, negativeMixedHessian]
    rw [negative_mixed_sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simpa [mul_assoc] using sum_bisum_mul (L m) (R n)
      (fun i j => negativeCellMixed epsilon s m n i j)
  simp only [negativeGridPhase]
  calc
    (∑ i : Fin s, ∑ j : Fin s, negativeCellPhase epsilon s L R i j) =
        ∑ i : Fin s, ∑ j : Fin s,
          (negativeCellPhase epsilon s L 0 i j +
            negativeCellPhase epsilon s 0 R i j -
            negativeCellPhase epsilon s 0 0 i j +
            ∑ m : Fin s, ∑ n : Fin (s + 1),
              L m * negativeCellMixed epsilon s m n i j * R n) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact negativeCellPhase_decompose epsilon s L R i j
    _ = (∑ i : Fin s, ∑ j : Fin s,
          negativeCellPhase epsilon s L 0 i j) +
        L ⬝ᵥ (negativeMixedHessian epsilon s).mulVec R +
        ((∑ i : Fin s, ∑ j : Fin s,
          negativeCellPhase epsilon s 0 R i j) -
        ∑ i : Fin s, ∑ j : Fin s,
          negativeCellPhase epsilon s 0 0 i j) := by
      rw [sum_bisum_add, sum_bisum_sub, sum_bisum_add, hmixed]
      ring

/-- The full literal negative phase has the same bilinear mixed part. -/
theorem negativeFullGridPhase_decompose
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (L : Fin s → F) (R : Fin (s + 1) → F) :
    negativeFullGridPhase epsilon s L R =
      negativeFullGridPhase epsilon s L 0 +
        L ⬝ᵥ (negativeMixedHessian epsilon s).mulVec R +
        (negativeFullGridPhase epsilon s 0 R -
          negativeFullGridPhase epsilon s 0 0) := by
  classical
  have hmixed :
      (∑ i : Fin s, ∑ j : Fin s, ∑ m : Fin s, ∑ n : Fin (s + 1),
          L m * negativeCellMixed epsilon s m n i j * R n) =
        L ⬝ᵥ (negativeMixedHessian epsilon s).mulVec R := by
    simp only [Matrix.mulVec, dotProduct, negativeMixedHessian]
    rw [negative_mixed_sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simpa [mul_assoc] using sum_bisum_mul (L m) (R n)
      (fun i j => negativeCellMixed epsilon s m n i j)
  simp only [negativeFullGridPhase]
  calc
    (∑ i : Fin s, ∑ j : Fin s,
        negativeFullCellPhase epsilon s L R i j) =
      ∑ i : Fin s, ∑ j : Fin s,
        (negativeFullCellPhase epsilon s L 0 i j +
          negativeFullCellPhase epsilon s 0 R i j -
          negativeFullCellPhase epsilon s 0 0 i j +
          ∑ m : Fin s, ∑ n : Fin (s + 1),
            L m * negativeCellMixed epsilon s m n i j * R n) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact negativeFullCellPhase_decompose epsilon s L R i j
    _ = _ := by
      rw [sum_bisum_add, sum_bisum_sub, sum_bisum_add, hmixed]
      ring

/-- Negative response-grid coefficient matrix on the allowed right source
hyperplane. -/
noncomputable def negativeGridCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (s : ℕ) :
    Matrix (Fin s → F) (Fin s → F) ℂ :=
  phaseCoeff psi fun L x =>
    negativeGridPhase epsilon s L (negativeAllowedRight s x)

/-- Removing its one-sided phases identifies the negative response-grid
matrix with its mixed-Hessian Fourier core. -/
theorem negativeGridCoeff_vonNeumannEntropy_eq_fourierCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (s : ℕ) :
    vonNeumannEntropy (negativeGridCoeff psi epsilon s) =
      vonNeumannEntropy
        (fourierCoeff psi (negativeMixedHessian epsilon s)
          (negativeAllowedRight s)) := by
  apply phaseCoeff_vonNeumannEntropy_eq_fourierCoeff
    psi (negativeMixedHessian epsilon s) (negativeAllowedRight s)
      (fun L => negativeGridPhase epsilon s L 0)
      (fun x => negativeGridPhase epsilon s 0 (negativeAllowedRight s x) -
        negativeGridPhase epsilon s 0 0)
  exact fun L x => negativeGridPhase_decompose epsilon s L _

/-- The negative response-grid phase matrix has entropy `s log q`. -/
theorem negativeGridCoeff_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s,
      epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    vonNeumannEntropy (negativeGridCoeff psi epsilon s) =
      (s : ℝ) * Real.log (Fintype.card F) := by
  rw [negativeGridCoeff_vonNeumannEntropy_eq_fourierCoeff]
  exact negativeSourceHyperplane_vonNeumannEntropy_eq_mul
    psi hpsi epsilon s hodd hepsilon

/-- Coefficient matrix of the full negative cubic phase difference. -/
noncomputable def negativeFullGridCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (s : ℕ) :
    Matrix (Fin s → F) (Fin s → F) ℂ :=
  phaseCoeff psi fun L x =>
    negativeFullGridPhase epsilon s L (negativeAllowedRight s x)

theorem negativeFullGridCoeff_vonNeumannEntropy_eq_fourierCoeff
    (psi : AddChar F ℂ) (epsilon : ℕ → ℕ → F) (s : ℕ) :
    vonNeumannEntropy (negativeFullGridCoeff psi epsilon s) =
      vonNeumannEntropy
        (fourierCoeff psi (negativeMixedHessian epsilon s)
          (negativeAllowedRight s)) := by
  apply phaseCoeff_vonNeumannEntropy_eq_fourierCoeff
    psi (negativeMixedHessian epsilon s) (negativeAllowedRight s)
      (fun L => negativeFullGridPhase epsilon s L 0)
      (fun x => negativeFullGridPhase epsilon s 0 (negativeAllowedRight s x) -
        negativeFullGridPhase epsilon s 0 0)
  exact fun L x => negativeFullGridPhase_decompose epsilon s L _

/-- The actual negative cubic finite-difference matrix has entropy
`s * log q`. -/
theorem negativeFullGridCoeff_vonNeumannEntropy
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (epsilon : ℕ → ℕ → F) (s : ℕ)
    (hodd : ringChar F ≠ 2)
    (hepsilon : ∀ m < s,
      epsilon m 1 = (-1 : F) ^ (s - 1 - m)) :
    vonNeumannEntropy (negativeFullGridCoeff psi epsilon s) =
      (s : ℝ) * Real.log (Fintype.card F) := by
  rw [negativeFullGridCoeff_vonNeumannEntropy_eq_fourierCoeff]
  exact negativeSourceHyperplane_vonNeumannEntropy_eq_mul
    psi hpsi epsilon s hodd hepsilon

end SqrtOpEnt
