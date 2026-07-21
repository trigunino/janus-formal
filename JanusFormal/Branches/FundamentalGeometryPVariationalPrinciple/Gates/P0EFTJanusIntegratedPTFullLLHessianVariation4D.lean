import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLHessianAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticHessianVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D

/-! Actual variation origin of the assembled full PT LL Hessian. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTFullLLHessianVariation4D

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
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticHessianVariation4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D

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

/-- First variation of both terms of the full PT LL action. -/
def globalPTFullLLFirstVariation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (∫ p, ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
      fields.llAuxMetric fields.llField direction.llAuxMetric direction.common.ll p ∂mu) +
    globalPTLLFirstVariation period hPeriod fields
      (fullDirectionLLVariation period hPeriod direction) mu

theorem globalPTFullLLFirstVariation_second_direction_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      ((fun t : Real =>
        ∫ p, ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
          (fields.llAuxMetric + t • second.llAuxMetric)
          (fields.llField + t • second.common.ll)
          first.llAuxMetric first.common.ll p ∂mu) +
       (fun t : Real =>
        globalPTLLFirstVariation period hPeriod
          (llMeasureFieldCurve period hPeriod fields
            (fullDirectionLLVariation period hPeriod second) t t)
          (fullDirectionLLVariation period hPeriod first) mu))
      (globalPTFullLLHessianForm period hPeriod frame fields first second mu) 0 := by
  have hK :=
    globalPTDifferentialLLKineticFirstVariation_second_direction_hasDerivAt
      period hPeriod frame fields.llAuxMetric first.llAuxMetric second.llAuxMetric
      fields.llField first.common.ll second.common.ll mu
  have hW := globalPTLLFirstVariation_second_direction_hasDerivAt
    period hPeriod fields (fullDirectionLLVariation period hPeriod first)
      (fullDirectionLLVariation period hPeriod second) mu
  simpa only [globalPTFullLLHessianForm] using hK.add hW

end
end P0EFTJanusIntegratedPTFullLLHessianVariation4D
end JanusFormal
