import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLHigherTaylorZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLHessianExplicitAdditivity4D

namespace JanusFormal
namespace P0EFTJanusFullLLMixedZero4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusIntegratedPTFullLLFirstVariationZero4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

private theorem neg_zeroFullDirection :
    negDirection period hPeriod (zeroFullDirection period hPeriod) =
      zeroFullDirection period hPeriod := by
  simp [negDirection, zeroFullDirection,
    P0EFTJanusProgramPCommonLLActionVariation4D.zeroSmoothDiagonalMetricVariation]

@[simp] theorem fullLLHessian_zero_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTFullLLHessianForm period hPeriod frame fields
      (zeroFullDirection period hPeriod) direction mu = 0 := by
  have h := fullLLHessian_neg_first period hPeriod frame fields
    (zeroFullDirection period hPeriod) direction mu
  change globalPTFullLLHessianForm period hPeriod frame fields
      (negDirection period hPeriod (zeroFullDirection period hPeriod)) direction mu =
    -globalPTFullLLHessianForm period hPeriod frame fields
      (zeroFullDirection period hPeriod) direction mu at h
  rw [neg_zeroFullDirection] at h
  linarith

@[simp] theorem fullLLHessian_zero_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTFullLLHessianForm period hPeriod frame fields direction
      (zeroFullDirection period hPeriod) mu = 0 := by
  rw [globalPTFullLLHessianForm_symmetric]
  exact fullLLHessian_zero_left period hPeriod frame fields direction mu

theorem zeroEulerAlong_hasDerivAt_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fullLLEulerAlong period hPeriod frame fields
      (zeroFullDirection period hPeriod) direction mu) 0 0 := by
  have h := fullLLEuler_second_direction_hasDerivAt period hPeriod frame fields
    (zeroFullDirection period hPeriod) direction mu
  rw [show fullLLHessian period hPeriod frame fields (zeroFullDirection period hPeriod)
      direction mu = 0 by
    unfold fullLLHessian
    exact fullLLHessian_zero_left period hPeriod frame fields direction mu] at h
  exact h

theorem EulerAlong_zeroDirection_hasDerivAt_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fullLLEulerAlong period hPeriod frame fields direction
      (zeroFullDirection period hPeriod) mu) 0 0 := by
  have h := fullLLEuler_second_direction_hasDerivAt period hPeriod frame fields
    direction (zeroFullDirection period hPeriod) mu
  rw [show fullLLHessian period hPeriod frame fields direction
      (zeroFullDirection period hPeriod) mu = 0 by
    unfold fullLLHessian
    exact fullLLHessian_zero_right period hPeriod frame fields direction mu] at h
  exact h

end
end P0EFTJanusFullLLMixedZero4D
end JanusFormal
