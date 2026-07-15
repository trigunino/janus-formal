import Mathlib
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalPinLiftBoundaryConditions

namespace JanusFormal
namespace P0EFTJanusGlobalSeparatedDiracModel

set_option autoImplicit false

open P0EFTJanusNormalPinLiftBoundaryConditions

/-- Global separated mode labels for the monopole sphere times the compact circle. -/
structure ProductDiracMode where
  sphereLevel : ℕ
  circleMode : ℤ
  rootChoice : NormalRootChoice
  deriving DecidableEq

structure ProductThroatSpectralData where
  sphereRadius : ℝ
  circlePeriod : ℝ
  sphereRadiusPositive : 0 < sphereRadius
  circlePeriodPositive : 0 < circlePeriod
  monopoleCharge : ℤ

noncomputable def sphereEigenvalueSquared
    (data : ProductThroatSpectralData) (level : ℕ) : ℝ :=
  ((level + 1 : ℕ) : ℝ) ^ 2 / data.sphereRadius ^ 2

noncomputable def circleEigenvalue
    (data : ProductThroatSpectralData) (choice : NormalRootChoice)
    (mode : ℤ) : ℝ :=
  Real.pi * (normalRootModeNumerator choice mode : ℝ) /
    (2 * data.circlePeriod)

/-- Squared eigenvalue of the separated product Dirac operator. -/
noncomputable def productDiracEigenvalueSquared
    (data : ProductThroatSpectralData) (mode : ProductDiracMode) : ℝ :=
  sphereEigenvalueSquared data mode.sphereLevel +
    circleEigenvalue data mode.rootChoice mode.circleMode ^ 2

theorem sphere_eigenvalue_squared_positive
    (data : ProductThroatSpectralData) (level : ℕ) :
    0 < sphereEigenvalueSquared data level := by
  have hRadius : data.sphereRadius ^ 2 > 0 := sq_pos_of_pos data.sphereRadiusPositive
  have hLevel : (0 : ℝ) < ((level + 1 : ℕ) : ℝ) := by positivity
  exact div_pos (sq_pos_of_pos hLevel) hRadius

theorem circle_eigenvalue_nonzero
    (data : ProductThroatSpectralData) (choice : NormalRootChoice)
    (mode : ℤ) : circleEigenvalue data choice mode ≠ 0 := by
  unfold circleEigenvalue
  have hPi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hMode : (normalRootModeNumerator choice mode : ℝ) ≠ 0 := by
    exact_mod_cast normal_root_mode_numerator_nonzero choice mode
  exact div_ne_zero (mul_ne_zero hPi hMode)
    (mul_ne_zero (by norm_num) (ne_of_gt data.circlePeriodPositive))

theorem product_spectrum_has_positive_gap
    (data : ProductThroatSpectralData) (mode : ProductDiracMode) :
    0 < productDiracEigenvalueSquared data mode := by
  unfold productDiracEigenvalueSquared
  exact add_pos_of_pos_of_nonneg
    (sphere_eigenvalue_squared_positive data mode.sphereLevel) (sq_nonneg _)

/-- PT sends the positive-quarter tower to the negative-quarter tower. -/
def ptMode (mode : ProductDiracMode) : ProductDiracMode :=
  { sphereLevel := mode.sphereLevel
    circleMode := -mode.circleMode
    rootChoice := oppositeRoot mode.rootChoice }

@[simp] theorem pt_mode_involutive (mode : ProductDiracMode) :
    ptMode (ptMode mode) = mode := by
  cases mode
  simp [ptMode, opposite_root_involutive]

theorem pt_preserves_squared_spectrum
    (data : ProductThroatSpectralData) (mode : ProductDiracMode) :
    productDiracEigenvalueSquared data (ptMode mode) =
      productDiracEigenvalueSquared data mode := by
  cases mode with
  | mk level circle choice =>
      cases choice <;>
        simp [productDiracEigenvalueSquared, ptMode, circleEigenvalue,
          oppositeRoot, normalRootModeNumerator] <;> ring

/-- Analytic promotion obligations for the completed global mode operator. -/
structure GlobalDiracAnalyticStatus where
  spinorHilbertSpaceCompleted : Prop
  diagonalOperatorDenselyDefined : Prop
  diagonalDomainClosed : Prop
  selfAdjointnessProved : Prop
  compactResolventProved : Prop
  separatedSpectrumComplete : Prop
  finiteMultiplicityProved : Prop

def globalDiracAnalyticClosed (s : GlobalDiracAnalyticStatus) : Prop :=
  s.spinorHilbertSpaceCompleted ∧ s.diagonalOperatorDenselyDefined ∧
  s.diagonalDomainClosed ∧ s.selfAdjointnessProved ∧
  s.compactResolventProved ∧ s.separatedSpectrumComplete ∧
  s.finiteMultiplicityProved

end P0EFTJanusGlobalSeparatedDiracModel
end JanusFormal
