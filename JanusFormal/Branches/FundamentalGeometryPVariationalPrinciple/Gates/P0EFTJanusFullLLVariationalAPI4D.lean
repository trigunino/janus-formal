import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusTruePTFullLLFirstVariationBridge4D

/-! Compact variational API for the full PT LL direction packet. -/

namespace JanusFormal
namespace P0EFTJanusFullLLVariationalAPI4D

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
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusTruePTFullLLFirstVariationBridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Full PT Euler/first-variation functional on the common direction packet. -/
def fullLLEuler
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  globalPTFullLLFirstVariation period hPeriod frame fields direction mu

/-- Full PT Hessian form on two common direction packets. -/
def fullLLHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  globalPTFullLLHessianForm period hPeriod frame fields first second mu

/-- The actual independent-field curve carrying all LL slots used by the API. -/
def fullLLFieldCurve
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) (t : Real) :
    IndependentFields period hPeriod :=
  { fields with
    llAuxMetric := fields.llAuxMetric + t • direction.llAuxMetric
    llMeasure := fields.llMeasure + t • direction.llMeasure
    llField := fields.llField + t • direction.common.ll }

/-- The full Euler functional evaluated along a second full LL direction. -/
def fullLLEulerAlong
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (t : Real) : Real :=
  (∫ p, ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
      (fields.llAuxMetric + t • second.llAuxMetric)
      (fields.llField + t • second.common.ll)
      first.llAuxMetric first.common.ll p ∂mu) +
    globalPTLLFirstVariation period hPeriod
      (llMeasureFieldCurve period hPeriod fields
        (fullDirectionLLVariation period hPeriod second) t t)
      (fullDirectionLLVariation period hPeriod first) mu

theorem truePTAction_fullCurve_hasDerivAt_fullLLEuler
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalPTSymmetricDifferentialLLAction
      period hPeriod frame
      (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
        direction.llMeasure direction.common.ll t) mu)
      (fullLLEuler period hPeriod frame fields direction mu) 0 := by
  exact truePTAction_fullCurve_hasDerivAt_fullFirstVariation
    period hPeriod frame fields direction mu

theorem fullLLEuler_second_direction_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fullLLEulerAlong period hPeriod frame fields first second mu)
      (fullLLHessian period hPeriod frame fields first second mu) 0 := by
  unfold fullLLEulerAlong fullLLHessian
  change HasDerivAt
    ((fun t : Real =>
      ∫ p, ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
        (fields.llAuxMetric + t • second.llAuxMetric)
        (fields.llField + t • second.common.ll)
        first.llAuxMetric first.common.ll p ∂mu) +
      (fun t : Real => globalPTLLFirstVariation period hPeriod
        (llMeasureFieldCurve period hPeriod fields
          (fullDirectionLLVariation period hPeriod second) t t)
        (fullDirectionLLVariation period hPeriod first) mu))
    (globalPTFullLLHessianForm period hPeriod frame fields first second mu) 0
  exact globalPTFullLLFirstVariation_second_direction_hasDerivAt
    period hPeriod frame fields first second mu

theorem fullLLHessian_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    fullLLHessian period hPeriod frame fields first second mu =
      fullLLHessian period hPeriod frame fields second first mu := by
  exact globalPTFullLLHessianForm_symmetric
    period hPeriod frame fields first second mu

end
end P0EFTJanusFullLLVariationalAPI4D
end JanusFormal
