import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLEulerTaylorZero4D

namespace JanusFormal
namespace P0EFTJanusIntegratedPTFullLLHigherTaylorZero4D
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
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
open P0EFTJanusIntegratedPTFullLLTaylorCoefficient12Bridge4D
open P0EFTJanusIntegratedPTFullLLEulerTaylorZero4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

@[simp] theorem differentialLLFullCurve_zero
    (fields : IndependentFields period hPeriod) (t : Real) :
    differentialLLFullCurve period hPeriod fields 0 0 0 t = fields := by
  cases fields
  simp [differentialLLFullCurve]

theorem truePTAction_zeroCurve_constant
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    (t : Real) :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields 0 0 0 t) mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu := by
  rw [differentialLLFullCurve_zero]

private theorem higher_coefficients_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] :
    globalPTFullLLHessianForm period hPeriod frame fields
        (zeroFullDirection period hPeriod) (zeroFullDirection period hPeriod) mu = 0 ∧
      globalPTFullLLTaylorCubic period hPeriod frame fields 0
        (zeroLLVariation period hPeriod) mu = 0 ∧
      globalPTFullLLTaylorQuartic period hPeriod frame fields 0
        (zeroLLVariation period hPeriod) mu = 0 := by
  have h1 := globalPTAction_fullDirection_exact_taylor period hPeriod frame fields
    (zeroFullDirection period hPeriod) 1 mu
  have hn := globalPTAction_fullDirection_exact_taylor period hPeriod frame fields
    (zeroFullDirection period hPeriod) (-1) mu
  have h2 := globalPTAction_fullDirection_exact_taylor period hPeriod frame fields
    (zeroFullDirection period hPeriod) 2 mu
  have hv : fullDirectionLLVariation period hPeriod (zeroFullDirection period hPeriod) =
      zeroLLVariation period hPeriod := by rfl
  rw [hv] at h1 hn h2
  have haux : (zeroFullDirection period hPeriod).llAuxMetric = 0 := rfl
  have hmu : (zeroFullDirection period hPeriod).llMeasure = 0 := rfl
  have hfield : (zeroFullDirection period hPeriod).common.ll = 0 := rfl
  rw [haux, hmu, hfield, differentialLLFullCurve_zero, fullLLEuler_zero] at h1 hn h2
  norm_num at h1 hn h2
  constructor
  · linarith
  constructor <;> linarith

@[simp] theorem fullLLHessian_zero_diagonal
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] :
    globalPTFullLLHessianForm period hPeriod frame fields
      (zeroFullDirection period hPeriod) (zeroFullDirection period hPeriod) mu = 0 :=
  (higher_coefficients_zero period hPeriod frame fields mu).1

@[simp] theorem integrated_taylor_coefficient_two_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] :
    (∫ p, ptTaylorCoeff period hPeriod 2 frame fields
      (zeroFullDirection period hPeriod).llAuxMetric
      (fullDirectionLLVariation period hPeriod (zeroFullDirection period hPeriod)) p ∂mu) = 0 := by
  rw [integral_coefficient_two_eq_half_fullLLHessian]
  simp [P0EFTJanusFullLLVariationalAPI4D.fullLLHessian]

@[simp] theorem globalPTFullLLTaylorCubic_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] :
    globalPTFullLLTaylorCubic period hPeriod frame fields 0
      (zeroLLVariation period hPeriod) mu = 0 :=
  (higher_coefficients_zero period hPeriod frame fields mu).2.1

@[simp] theorem globalPTFullLLTaylorQuartic_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] :
    globalPTFullLLTaylorQuartic period hPeriod frame fields 0
      (zeroLLVariation period hPeriod) mu = 0 :=
  (higher_coefficients_zero period hPeriod frame fields mu).2.2

theorem truePTAction_zeroDirection_exact_taylor
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] (t : Real) :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields
        (zeroFullDirection period hPeriod).llAuxMetric
        (zeroFullDirection period hPeriod).llMeasure
        (zeroFullDirection period hPeriod).common.ll t) mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu := by
  simpa [zeroFullDirection] using truePTAction_zeroCurve_constant period hPeriod frame fields mu t

end
end P0EFTJanusIntegratedPTFullLLHigherTaylorZero4D
end JanusFormal
