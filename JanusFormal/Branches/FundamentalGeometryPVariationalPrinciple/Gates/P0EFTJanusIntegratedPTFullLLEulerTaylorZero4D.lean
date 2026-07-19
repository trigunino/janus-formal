import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLTaylorCoefficient12Bridge4D

namespace JanusFormal
namespace P0EFTJanusIntegratedPTFullLLEulerTaylorZero4D
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
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
open P0EFTJanusIntegratedPTFullLLTaylorCoefficient12Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

@[simp] theorem fullLLEuler_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) :
    fullLLEuler period hPeriod frame fields (zeroFullDirection period hPeriod) mu = 0 := by
  unfold fullLLEuler
  exact globalPTFullLLFirstVariation_zero period hPeriod frame fields mu

@[simp] theorem integrated_taylor_coefficient_one_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] :
    (∫ p, ptTaylorCoeff period hPeriod 1 frame fields
      (zeroFullDirection period hPeriod).llAuxMetric
      (fullDirectionLLVariation period hPeriod (zeroFullDirection period hPeriod)) p ∂mu) = 0 := by
  rw [integral_coefficient_one_eq_fullLLEuler, fullLLEuler_zero]

@[simp] theorem globalPTFullLLTaylorEuler_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] :
    globalPTFullLLTaylorEuler period hPeriod frame fields
      (zeroFullDirection period hPeriod).llAuxMetric
      (fullDirectionLLVariation period hPeriod (zeroFullDirection period hPeriod)) mu = 0 := by
  rw [globalPTFullLLTaylorEuler_eq_actual, fullLLEuler_zero]

theorem truePTAction_zeroCurve_hasDerivAt_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields
        (zeroFullDirection period hPeriod).llAuxMetric
        (zeroFullDirection period hPeriod).llMeasure
        (zeroFullDirection period hPeriod).common.ll t) mu) 0 0 := by
  have h := truePTAction_fullCurve_hasDerivAt_fullLLEuler period hPeriod frame fields
    (zeroFullDirection period hPeriod) mu
  rw [fullLLEuler_zero] at h
  exact h

end
end P0EFTJanusIntegratedPTFullLLEulerTaylorZero4D
end JanusFormal
