import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessianLinearity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTLLWorldvolumeHessianLinearity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLVariationalAPI4D

namespace JanusFormal
namespace P0EFTJanusFullLLHessianExplicitAdditivity4D

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
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessianLinearity4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessianLinearity4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullLLVariationalAPI4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def addDirection (x y : FullMatterRobinLLDirections period hPeriod) : FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric :=
        { plusLogDirection := x.common.metric.plusLogDirection + y.common.metric.plusLogDirection
          minusLogDirection := x.common.metric.minusLogDirection + y.common.metric.minusLogDirection }
      matter := x.common.matter + y.common.matter
      gauge := x.common.gauge + y.common.gauge
      ghost := x.common.ghost + y.common.ghost
      auxiliary := x.common.auxiliary + y.common.auxiliary
      ll := x.common.ll + y.common.ll }
  robin := x.robin + y.robin
  llAuxMetric := x.llAuxMetric + y.llAuxMetric
  llMeasure := x.llMeasure + y.llMeasure

def negDirection (x : FullMatterRobinLLDirections period hPeriod) : FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric :=
        { plusLogDirection := -x.common.metric.plusLogDirection
          minusLogDirection := -x.common.metric.minusLogDirection }
      matter := -x.common.matter
      gauge := -x.common.gauge
      ghost := -x.common.ghost
      auxiliary := -x.common.auxiliary
      ll := -x.common.ll }
  robin := -x.robin
  llAuxMetric := -x.llAuxMetric
  llMeasure := -x.llMeasure

@[simp] theorem fullDirectionLLVariation_addDirection
    (x y : FullMatterRobinLLDirections period hPeriod) :
    fullDirectionLLVariation period hPeriod (addDirection period hPeriod x y) =
      addVariation period hPeriod (fullDirectionLLVariation period hPeriod x)
        (fullDirectionLLVariation period hPeriod y) := by
  rfl

theorem fullLLHessian_add_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (x y z : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    fullLLHessian period hPeriod frame fields (addDirection period hPeriod x y) z mu =
      fullLLHessian period hPeriod frame fields x z mu +
        fullLLHessian period hPeriod frame fields y z mu := by
  unfold fullLLHessian globalPTFullLLHessianForm
  change
    P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D.globalPTDifferentialLLKineticMixedHessian
        period hPeriod frame fields.llAuxMetric fields.llField
        (x.llAuxMetric + y.llAuxMetric) z.llAuxMetric (x.common.ll + y.common.ll) z.common.ll mu +
      globalPTLLWorldvolumeHessian period hPeriod fields
        (addVariation period hPeriod (fullDirectionLLVariation period hPeriod x)
          (fullDirectionLLVariation period hPeriod y))
        (fullDirectionLLVariation period hPeriod z) mu = _
  rw [globalPTMixedHessian_add_first]
  rw [globalPTLLWorldvolumeHessian_add_first]
  ring

@[simp] theorem fullDirectionLLVariation_negDirection
    (x : FullMatterRobinLLDirections period hPeriod) :
    fullDirectionLLVariation period hPeriod (negDirection period hPeriod x) =
      negVariation period hPeriod (fullDirectionLLVariation period hPeriod x) := by
  rfl

theorem fullLLHessian_neg_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (x z : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    fullLLHessian period hPeriod frame fields (negDirection period hPeriod x) z mu =
      -fullLLHessian period hPeriod frame fields x z mu := by
  unfold fullLLHessian globalPTFullLLHessianForm
  change
    P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D.globalPTDifferentialLLKineticMixedHessian
        period hPeriod frame fields.llAuxMetric fields.llField
        (-x.llAuxMetric) z.llAuxMetric (-x.common.ll) z.common.ll mu +
      globalPTLLWorldvolumeHessian period hPeriod fields
        (negVariation period hPeriod (fullDirectionLLVariation period hPeriod x))
        (fullDirectionLLVariation period hPeriod z) mu = _
  rw [globalPTMixedHessian_neg_first, globalPTLLWorldvolumeHessian_neg_first]
  ring

end
end P0EFTJanusFullLLHessianExplicitAdditivity4D
end JanusFormal
