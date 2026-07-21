import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLFullCurveActionDecomposition4D

namespace JanusFormal
namespace P0EFTJanusTruePTDifferentialLLSimultaneousVariation4D

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
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem fullLLCurve_eq_differentialLLFullCurve
    (fields : IndependentFields period hPeriod)
    (variation : P0EFTJanusMappingTorusGlobalLLVariation4D.LLVariation period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) (t : Real) :
    fullLLCurve period hPeriod fields variation dAux t =
      differentialLLFullCurve period hPeriod fields dAux variation.measureDirection
        variation.fieldDirection t := by rfl

private theorem kineticAction_eq
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTDifferentialLLKineticAction period hPeriod frame fields.llAuxMetric
        fields.llField mu =
      globalPTSymmetricDifferentialLLKineticAction period hPeriod frame fields mu := by
  have hRaw (a : SmoothThroatField period hPeriod LLMetricFiber)
      (f : SmoothThroatField period hPeriod LLFieldFiber) :
      Integrable (differentialLLKineticDensity period hPeriod frame a f) mu := by
    have hc : Continuous (differentialLLKineticDensity period hPeriod frame a f) := by
      unfold differentialLLKineticDensity
      exact ((continuous_const.mul
        (continuous_const.add (a.contMDiff_toFun.continuous.norm.pow 2))).mul
          (throatDerivativeEnergy_continuous period hPeriod frame f))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold globalPTDifferentialLLKineticAction
    P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D.ptSymmetricDifferentialLLKineticDensity
    globalPTSymmetricDifferentialLLKineticAction
  rw [integral_const_mul]
  rw [← integral_add
    (hRaw fields.llAuxMetric fields.llField)
    (hRaw (P0EFTJanusMappingTorusGlobalLLCovariance4D.llPTPullback period hPeriod fields).llAuxMetric
      (P0EFTJanusMappingTorusGlobalLLCovariance4D.llPTPullback period hPeriod fields).llField)]
  rfl

theorem globalPTFullDifferentialLLAction_eq_true
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTFullDifferentialLLAction period hPeriod frame fields mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu := by
  have h := globalPTSymmetricDifferentialLLAction_fullCurve_decomposition
    period hPeriod frame fields 0 0 0 0 mu
  calc
    _ = globalPTSymmetricDifferentialLLKineticAction period hPeriod frame fields mu +
        globalPTSymmetricLLWorldvolumeAction period hPeriod fields mu := by
      unfold globalPTFullDifferentialLLAction globalPTLLWorldvolumeAction
        globalPTSymmetricLLWorldvolumeAction
        P0EFTJanusMappingTorusGlobalLLWorldvolume4D.globalLLAction
      rw [kineticAction_eq period hPeriod frame fields mu]
    _ = _ := by simpa [differentialLLFullCurve] using h.symm

theorem truePTAction_fullCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : P0EFTJanusMappingTorusGlobalLLVariation4D.LLVariation period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields dAux variation.measureDirection
        variation.fieldDirection t) mu)
      ((∫ p, P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D.ptSymmetricDifferentialLLKineticFirstVariation
        period hPeriod frame fields.llAuxMetric fields.llField dAux variation.fieldDirection p ∂mu) +
       (1 / 2 : Real) *
        (P0EFTJanusMappingTorusGlobalLLVariation4D.globalLLFirstVariation period hPeriod fields variation mu +
         P0EFTJanusMappingTorusGlobalLLVariation4D.globalLLFirstVariation period hPeriod
          (P0EFTJanusMappingTorusGlobalLLCovariance4D.llPTPullback period hPeriod fields)
          (llVariationPT period hPeriod variation) mu)) 0 := by
  rw [show (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields dAux variation.measureDirection
        variation.fieldDirection t) mu) =
    (fun t : Real => globalPTFullDifferentialLLAction period hPeriod frame
      (fullLLCurve period hPeriod fields variation dAux t) mu) by
      funext t
      rw [fullLLCurve_eq_differentialLLFullCurve period hPeriod]
      exact (globalPTFullDifferentialLLAction_eq_true period hPeriod frame _ mu).symm]
  exact globalPTFullDifferentialLLAction_simultaneous_hasDerivAt period hPeriod
    frame fields variation dAux mu

end
end P0EFTJanusTruePTDifferentialLLSimultaneousVariation4D
end JanusFormal
