import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusThroatLinearOperationsZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLHessianVariation4D

namespace JanusFormal
namespace P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
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
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusThroatLinearOperationsZero4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def zeroLLVariation : LLVariation period hPeriod where
  measureDirection := 0
  fieldDirection := 0

def zeroFullDirection : FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := P0EFTJanusProgramPCommonLLActionVariation4D.zeroSmoothDiagonalMetricVariation period hPeriod
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := 0 }
  robin := 0
  llAuxMetric := 0
  llMeasure := 0

@[simp] theorem smoothThroatField_zero_apply
    (Fiber : Type) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (point : EffectiveThroat period hPeriod) :
    (0 : SmoothThroatField period hPeriod Fiber) point = 0 := rfl

@[simp] theorem llFirstVariationDensity_zero
    (fields : IndependentFields period hPeriod) (point : EffectiveThroat period hPeriod) :
    llFirstVariationDensity period hPeriod fields (zeroLLVariation period hPeriod) point = 0 := by
  unfold llFirstVariationDensity zeroLLVariation
  change (0 : Real) * _ + 2 * _ * inner Real _ 0 = 0
  simp

@[simp] theorem differentialLLKineticFirstVariation_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    P0EFTJanusDifferentialLLKineticSimultaneousVariation4D.differentialLLKineticFirstVariation
      period hPeriod frame aux field 0 0 point = 0 := by
  unfold P0EFTJanusDifferentialLLKineticSimultaneousVariation4D.differentialLLKineticFirstVariation
    throatDerivativePairing
  simp

@[simp] theorem ptSymmetricDifferentialLLKineticFirstVariation_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D.ptSymmetricDifferentialLLKineticFirstVariation
      period hPeriod frame aux field 0 0 point = 0 := by
  unfold P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D.ptSymmetricDifferentialLLKineticFirstVariation
    P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D.differentialLLAuxMetricDirectionPT
    P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D.differentialLLFluxDirectionPT
  simp

@[simp] theorem globalPTLLFirstVariation_zero
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) :
    P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D.globalPTLLFirstVariation
      period hPeriod fields (zeroLLVariation period hPeriod) mu = 0 := by
  unfold P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D.globalPTLLFirstVariation
    P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D.ptLLFirstVariationDensity
    P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D.ptAverage
  simp [zeroLLVariation, llFirstVariationDensity]

@[simp] theorem globalPTFullLLFirstVariation_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTFullLLFirstVariation period hPeriod frame fields
      (zeroFullDirection period hPeriod) mu = 0 := by
  unfold globalPTFullLLFirstVariation
  change (∫ p,
      P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D.ptSymmetricDifferentialLLKineticFirstVariation
        period hPeriod frame fields.llAuxMetric fields.llField 0 0 p ∂mu) +
      P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D.globalPTLLFirstVariation
        period hPeriod fields (zeroLLVariation period hPeriod) mu = 0
  simp [zeroFullDirection]

end
end P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
end JanusFormal
