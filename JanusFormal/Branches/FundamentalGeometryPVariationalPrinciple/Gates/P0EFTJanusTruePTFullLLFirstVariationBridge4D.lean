import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusTruePTDifferentialLLSimultaneousVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLHessianVariation4D

namespace JanusFormal
namespace P0EFTJanusTruePTFullLLFirstVariationBridge4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusTruePTDifferentialLLSimultaneousVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

private theorem llFirstVariationDensity_pt
    (fields : IndependentFields period hPeriod) (variation : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) :
    llFirstVariationDensity period hPeriod fields variation
        (fixedThroatPT period hPeriod p) =
      llFirstVariationDensity period hPeriod (llPTPullback period hPeriod fields)
        (llVariationPT period hPeriod variation) p := by
  rfl

theorem globalPTLLFirstVariation_eq_orbit_average
    (fields : IndependentFields period hPeriod) (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTLLFirstVariation period hPeriod fields variation mu =
      (1 / 2 : Real) *
        (globalLLFirstVariation period hPeriod fields variation mu +
          globalLLFirstVariation period hPeriod (llPTPullback period hPeriod fields)
            (llVariationPT period hPeriod variation) mu) := by
  have h0 : Integrable (llFirstVariationDensity period hPeriod fields variation) mu :=
    (llFirstVariationDensity_continuous period hPeriod fields variation).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have h1 : Continuous (fun p => llFirstVariationDensity period hPeriod fields variation
      (fixedThroatPT period hPeriod p)) :=
    (llFirstVariationDensity_continuous period hPeriod fields variation).comp
    (continuous_fixedThroatPT period hPeriod)
  have hi1 : Integrable (fun p => llFirstVariationDensity period hPeriod fields variation
      (fixedThroatPT period hPeriod p)) mu :=
    h1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold globalPTLLFirstVariation ptLLFirstVariationDensity ptAverage
    globalLLFirstVariation
  rw [integral_const_mul]
  congr 1
  rw [integral_add h0 hi1]
  congr 1

theorem globalPTFullLLFirstVariation_eq_true_coefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : P0EFTJanusFullMatterRobinLLDirections4D.FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTFullLLFirstVariation period hPeriod frame fields direction mu =
      (∫ p, P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D.ptSymmetricDifferentialLLKineticFirstVariation
        period hPeriod frame fields.llAuxMetric fields.llField direction.llAuxMetric
          direction.common.ll p ∂mu) +
      (1 / 2 : Real) *
        (globalLLFirstVariation period hPeriod fields
            (fullDirectionLLVariation period hPeriod direction) mu +
          globalLLFirstVariation period hPeriod (llPTPullback period hPeriod fields)
            (llVariationPT period hPeriod
              (fullDirectionLLVariation period hPeriod direction)) mu) := by
  unfold globalPTFullLLFirstVariation
  rw [globalPTLLFirstVariation_eq_orbit_average]

theorem truePTAction_fullCurve_hasDerivAt_fullFirstVariation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : P0EFTJanusFullMatterRobinLLDirections4D.FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D.globalPTSymmetricDifferentialLLAction
      period hPeriod frame
      (P0EFTJanusDifferentialLLFullCurveActionDecomposition4D.differentialLLFullCurve
        period hPeriod fields direction.llAuxMetric direction.llMeasure direction.common.ll t) mu)
      (globalPTFullLLFirstVariation period hPeriod frame fields direction mu) 0 := by
  rw [globalPTFullLLFirstVariation_eq_true_coefficient]
  exact truePTAction_fullCurve_hasDerivAt period hPeriod frame fields
    (fullDirectionLLVariation period hPeriod direction) direction.llAuxMetric mu

end
end P0EFTJanusTruePTFullLLFirstVariationBridge4D
end JanusFormal
