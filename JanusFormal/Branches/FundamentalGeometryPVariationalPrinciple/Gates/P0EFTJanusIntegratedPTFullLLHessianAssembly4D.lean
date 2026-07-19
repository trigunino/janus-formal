import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinLLDirections4D

/-! Symmetric assembly of the two proved integrated PT LL Hessian forms. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTFullLLHessianAssembly4D

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
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D

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

/-- The actual LL field/measure pair carried by the full common direction. -/
def fullDirectionLLVariation
    (direction : FullMatterRobinLLDirections period hPeriod) :
    LLVariation period hPeriod where
  measureDirection := direction.llMeasure
  fieldDirection := direction.common.ll

/-- Sum of the already proved kinetic and worldvolume integrated PT bilinear
forms. This definition alone is not claimed to be an actual Hessian. -/
def globalPTFullLLHessianForm
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  globalPTDifferentialLLKineticMixedHessian period hPeriod frame
      fields.llAuxMetric fields.llField first.llAuxMetric second.llAuxMetric
      first.common.ll second.common.ll mu +
    globalPTLLWorldvolumeHessian period hPeriod fields
      (fullDirectionLLVariation period hPeriod first)
      (fullDirectionLLVariation period hPeriod second) mu

theorem globalPTFullLLHessianForm_formula
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTFullLLHessianForm period hPeriod frame fields first second mu =
      globalPTDifferentialLLKineticMixedHessian period hPeriod frame
        fields.llAuxMetric fields.llField first.llAuxMetric second.llAuxMetric
        first.common.ll second.common.ll mu +
      globalPTLLWorldvolumeHessian period hPeriod fields
        (fullDirectionLLVariation period hPeriod first)
        (fullDirectionLLVariation period hPeriod second) mu :=
  rfl

theorem globalPTFullLLHessianForm_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTFullLLHessianForm period hPeriod frame fields first second mu =
      globalPTFullLLHessianForm period hPeriod frame fields second first mu := by
  unfold globalPTFullLLHessianForm
  rw [globalPTDifferentialLLKineticMixedHessian_symmetric,
    globalPTLLWorldvolumeHessian_symmetric]

end
end P0EFTJanusIntegratedPTFullLLHessianAssembly4D
end JanusFormal
