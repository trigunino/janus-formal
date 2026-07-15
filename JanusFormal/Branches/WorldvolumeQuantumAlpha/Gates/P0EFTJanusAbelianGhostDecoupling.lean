import Mathlib

namespace JanusFormal.P0EFTJanusAbelianGhostDecoupling

set_option autoImplicit false

structure NonzeroMomentum where
  normSquared : ℝ
  normSquaredPositive : 0 < normSquared

/-- Faddeev--Popov principal symbol for linear Lorenz gauge in an Abelian
theory: `delta(div A)/delta omega = |xi|^2`. -/
def abelianGhostSymbol (momentum : NonzeroMomentum) (ghost : ℝ) : ℝ :=
  momentum.normSquared * ghost

/-- The Abelian ghost symbol has no nonzero-momentum kernel. -/
theorem abelian_ghost_symbol_kernel_trivial
    (momentum : NonzeroMomentum)
    (ghost : ℝ) (hKernel : abelianGhostSymbol momentum ghost = 0) :
    ghost = 0 := by
  unfold abelianGhostSymbol at hKernel
  exact (mul_eq_zero.mp hKernel).resolve_left
    (ne_of_gt momentum.normSquaredPositive)

/-- In the neutral-scalar candidate the linear Abelian FP operator is
background-field independent, hence it has no scalar--ghost interaction
vertex. Global zero modes still require separate treatment. -/
structure AbelianGhostSectorStatus where
  linearLorenzGaugeFixed : Prop
  scalarNeutral : Prop
  fpOperatorIsScalarLaplacian : Prop
  localGhostMatterVerticesAbsent : Prop
  globalZeroModesSeparated : Prop
  determinantPrimeDefined : Prop

def abelianGhostSectorClosed (s : AbelianGhostSectorStatus) : Prop :=
  s.linearLorenzGaugeFixed ∧
  s.scalarNeutral ∧
  s.fpOperatorIsScalarLaplacian ∧
  s.localGhostMatterVerticesAbsent ∧
  s.globalZeroModesSeparated ∧
  s.determinantPrimeDefined

end JanusFormal.P0EFTJanusAbelianGhostDecoupling
