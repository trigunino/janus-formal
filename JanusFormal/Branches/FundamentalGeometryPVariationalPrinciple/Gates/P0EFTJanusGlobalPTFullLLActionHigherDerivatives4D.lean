import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D

namespace JanusFormal
namespace P0EFTJanusGlobalPTFullLLActionHigherDerivatives4D
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
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

private theorem fullCurve_action_function
    (frame : SmoothThroatGeneratingFrame period hPeriod) (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields dAux variation.measureDirection variation.fieldDirection t) mu) =
    fun t => globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu +
      t * globalPTFullLLTaylorEuler period hPeriod frame fields dAux variation mu +
      (t^2 / 2) * globalPTFullLLTaylorHessianDiagonal period hPeriod frame fields dAux variation mu +
      t^3 * globalPTFullLLTaylorCubic period hPeriod frame fields dAux variation mu +
      t^4 * globalPTFullLLTaylorQuartic period hPeriod frame fields dAux variation mu := by
  funext t
  exact globalPTAction_fullCurve_exact_taylor period hPeriod frame fields dAux variation t mu

theorem globalPTAction_fullCurve_third_iteratedDeriv
    (frame : SmoothThroatGeneratingFrame period hPeriod) (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    iteratedDeriv 3 (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields dAux variation.measureDirection variation.fieldDirection t) mu) 0 =
      6 * globalPTFullLLTaylorCubic period hPeriod frame fields dAux variation mu := by
  rw [fullCurve_action_function period hPeriod frame fields dAux variation mu]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_mul,
    iteratedDeriv_const, iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  norm_num [Finset.sum_range_succ]

theorem globalPTAction_fullCurve_fourth_iteratedDeriv
    (frame : SmoothThroatGeneratingFrame period hPeriod) (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    iteratedDeriv 4 (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields dAux variation.measureDirection variation.fieldDirection t) mu) 0 =
      24 * globalPTFullLLTaylorQuartic period hPeriod frame fields dAux variation mu := by
  rw [fullCurve_action_function period hPeriod frame fields dAux variation mu]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_mul,
    iteratedDeriv_const, iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  norm_num [Finset.sum_range_succ]

end
end P0EFTJanusGlobalPTFullLLActionHigherDerivatives4D
end JanusFormal
