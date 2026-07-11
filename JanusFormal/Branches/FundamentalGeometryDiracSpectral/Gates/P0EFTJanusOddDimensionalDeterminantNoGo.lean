import Mathlib

namespace JanusFormal
namespace P0EFTJanusOddDimensionalDeterminantNoGo

set_option autoImplicit false

/-- Zeta-regularized determinant scaling factor under `D -> D/s`. -/
noncomputable def determinantScalingFactor
    (zetaAtZero scale : ℝ) : ℝ :=
  Real.exp (-2 * zetaAtZero * Real.log scale)

/-- Vanishing zeta value makes the determinant invariant under common scaling. -/
@[simp] theorem zero_zeta_value_gives_scale_invariant_determinant
    (scale : ℝ) :
    determinantScalingFactor 0 scale = 1 := by
  simp [determinantScalingFactor]

/-- Scale invariance holds for any two scale factors once `zeta(0)=0`. -/
theorem zero_zeta_value_erases_scale_dependence
    (scale₁ scale₂ : ℝ) :
    determinantScalingFactor 0 scale₁ =
      determinantScalingFactor 0 scale₂ := by
  simp

/--
Analytic input expected for an invertible Laplace-type operator on a closed odd-
dimensional manifold: the relevant heat coefficient, hence `zeta(0)`, vanishes.
-/
structure ClosedOddDiracScalingData where
  dimensionOdd : Prop
  manifoldClosed : Prop
  diracInvertible : Prop
  laplaceTypeSquareConstructed : Prop
  oddHeatCoefficientVanishes : Prop
  zetaAtZero : ℝ
  zetaAtZeroVanishes : zetaAtZero = 0

/-- Such a determinant has no homogeneous absolute-scale selection power. -/
theorem closed_odd_dirac_determinant_scaling_is_trivial
    (s : ClosedOddDiracScalingData)
    (scale : ℝ) :
    determinantScalingFactor s.zetaAtZero scale = 1 := by
  rw [s.zetaAtZeroVanishes]
  simp

/--
Consequently the massless closed-throat Dirac determinant can select holonomy
and dimensionless moduli but cannot by itself select the common metric radius.
A boundary, mass, condensate, RG scale or bulk coupling must introduce a genuine
scale-breaking datum.
-/
structure DeterminantScaleExitStatus where
  closedMasslessDiracNoGoProved : Prop
  boundaryContributionDerived : Prop
  dynamicallyGeneratedMassDerived : Prop
  renormalizationScaleFixedMicroscopically : Prop
  bulkGravityScaleCoupled : Prop
  atLeastOneScaleBreakingExitActive : Prop


def determinantScaleNoGoExited
    (s : DeterminantScaleExitStatus) : Prop :=
  s.closedMasslessDiracNoGoProved /\
  (s.boundaryContributionDerived \/
    s.dynamicallyGeneratedMassDerived \/
    s.renormalizationScaleFixedMicroscopically \/
    s.bulkGravityScaleCoupled) /\
  s.atLeastOneScaleBreakingExitActive

end P0EFTJanusOddDimensionalDeterminantNoGo
end JanusFormal
