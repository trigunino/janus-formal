import Mathlib

namespace JanusFormal
namespace P0EFTJanusSquareRootEvolutionTube

set_option autoImplicit false

theorem positive_margin_from_budget
    (c initialRadius integratedSpeed : ℝ)
    (hBudget : initialRadius + integratedSpeed < c ^ 2) :
    0 < c ^ 2 - initialRadius - integratedSpeed := by
  linarith

theorem budget_composition
    (c r0 r1 r2 : ℝ)
    (hBudget : r0 + r1 + r2 < c ^ 2) :
    r0 + (r1 + r2) < c ^ 2 := by
  linarith

theorem strict_boundary_not_certified (c r0 speed : ℝ)
    (hBoundary : r0 + speed = c ^ 2) :
    ¬ (r0 + speed < c ^ 2) := by
  linarith

end P0EFTJanusSquareRootEvolutionTube
end JanusFormal
