import RequestProject.FibreEntropy

/-!
# Standalone endpoint

This module exposes only the fully proved lower square-root bound.  It does
not import the later binomial-entropy or bounded-saturation development.
-/

namespace SqrtOpEnt

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Standalone form of the proved lower square-root bound for the concrete
rectangular core. -/
theorem standalone_rectangular_lower_sqrt_bound
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) (hodd : ringChar F ≠ 2)
    (n : ℕ) :
    Real.log (Fintype.card F) *
          Real.sqrt (((n + 1 : ℕ) : ℝ) / Real.pi) -
        (3 / 2) * Real.log (Fintype.card F) ≤
      rectangularVonNeumannEntropy F psi (succPNat n) := by
  exact rectangularVonNeumann_sqrt_lower_bound_proved
    (F := F) psi hpsi hodd n

end SqrtOpEnt
