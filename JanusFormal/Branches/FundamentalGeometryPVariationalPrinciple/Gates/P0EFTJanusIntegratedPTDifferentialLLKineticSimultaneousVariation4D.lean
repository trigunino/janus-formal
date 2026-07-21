import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegrableQuarticPolynomial

namespace JanusFormal
namespace P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D

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
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegrableQuarticPolynomial

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

private def rawCoeff (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) : Real :=
  let A0 := 1 + ‖a p‖ ^ 2
  let A1 := 2 * inner Real (a p) (da p)
  let A2 := ‖da p‖ ^ 2
  let E0 := throatDerivativeEnergy period hPeriod frame f p
  let E1 := 2 * throatDerivativePairing period hPeriod frame f df p
  let E2 := throatDerivativeEnergy period hPeriod frame df p
  (1 / 2 : Real) * match degree with
    | 0 => A0 * E0
    | 1 => A0 * E1 + A1 * E0
    | 2 => A0 * E2 + A1 * E1 + A2 * E0
    | 3 => A1 * E2 + A2 * E1
    | 4 => A2 * E2

private def ptCoeff (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * (rawCoeff period hPeriod degree frame a da f df p +
    rawCoeff period hPeriod degree frame
      (throatPTPullback period hPeriod LLMetricFiber a)
      (differentialLLAuxMetricDirectionPT period hPeriod da)
      (throatPTPullback period hPeriod LLFieldFiber f)
      (differentialLLFluxDirectionPT period hPeriod df) p)

private theorem density_quartic (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber) (t : Real)
    (p : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticDensity period hPeriod frame
        (a + t • da) (f + t • df) p =
      ptCoeff period hPeriod 0 frame a da f df p +
      t * ptCoeff period hPeriod 1 frame a da f df p +
      t^2 * ptCoeff period hPeriod 2 frame a da f df p +
      t^3 * ptCoeff period hPeriod 3 frame a da f df p +
      t^4 * ptCoeff period hPeriod 4 frame a da f df p := by
  rw [ptSymmetricDifferentialLLKineticDensity_simultaneous_polynomial]
  unfold ptCoeff rawCoeff
  simp only
  ring

private theorem rawCoeff_continuous (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (rawCoeff period hPeriod degree frame a da f df) := by
  have A0 : Continuous (fun p => 1 + ‖a p‖ ^ 2) :=
    continuous_const.add (a.contMDiff_toFun.continuous.norm.pow 2)
  have A1 : Continuous (fun p => 2 * inner Real (a p) (da p)) :=
    continuous_const.mul (a.contMDiff_toFun.continuous.inner da.contMDiff_toFun.continuous)
  have A2 : Continuous (fun p => ‖da p‖ ^ 2) := da.contMDiff_toFun.continuous.norm.pow 2
  have E0 := throatDerivativeEnergy_continuous period hPeriod frame f
  have E1 : Continuous (fun p => 2 * throatDerivativePairing period hPeriod frame f df p) :=
    continuous_const.mul (throatDerivativePairing_continuous period hPeriod frame f df)
  have E2 := throatDerivativeEnergy_continuous period hPeriod frame df
  unfold rawCoeff
  fin_cases degree <;> simp only <;>
    first | exact continuous_const.mul (A0.mul E0)
          | exact continuous_const.mul ((A0.mul E1).add (A1.mul E0))
          | exact continuous_const.mul (((A0.mul E2).add (A1.mul E1)).add (A2.mul E0))
          | exact continuous_const.mul ((A1.mul E2).add (A2.mul E1))
          | exact continuous_const.mul (A2.mul E2)

private theorem ptCoeff_integrable (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptCoeff period hPeriod degree frame a da f df) mu := by
  have h : Continuous (ptCoeff period hPeriod degree frame a da f df) := by
    unfold ptCoeff
    exact continuous_const.mul ((rawCoeff_continuous period hPeriod degree frame a da f df).add
      (rawCoeff_continuous period hPeriod degree frame
        (throatPTPullback period hPeriod LLMetricFiber a)
        (differentialLLAuxMetricDirectionPT period hPeriod da)
        (throatPTPullback period hPeriod LLFieldFiber f)
        (differentialLLFluxDirectionPT period hPeriod df)))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def globalPTDifferentialLLKineticAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a : SmoothThroatField period hPeriod LLMetricFiber)
    (f : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptSymmetricDifferentialLLKineticDensity period hPeriod frame a f p ∂mu

theorem globalPTDifferentialLLKineticAction_simultaneous_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalPTDifferentialLLKineticAction period hPeriod frame
      (a + t • da) (f + t • df) mu)
      (∫ p, ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        frame a f da df p ∂mu) 0 := by
  have hi (d : Fin 5) := ptCoeff_integrable period hPeriod d frame a da f df mu
  have h1 : ptCoeff period hPeriod 1 frame a da f df =
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame a f da df := by
    funext p
    unfold ptCoeff rawCoeff ptSymmetricDifferentialLLKineticFirstVariation
      differentialLLKineticFirstVariation
    simp only
    ring
  rw [← h1]
  rw [show (fun t : Real => globalPTDifferentialLLKineticAction period hPeriod frame
      (a + t • da) (f + t • df) mu) = fun t : Real =>
      (∫ p, ptCoeff period hPeriod 0 frame a da f df p ∂mu) +
      t * (∫ p, ptCoeff period hPeriod 1 frame a da f df p ∂mu) +
      t^2 * (∫ p, ptCoeff period hPeriod 2 frame a da f df p ∂mu) +
      t^3 * (∫ p, ptCoeff period hPeriod 3 frame a da f df p ∂mu) +
      t^4 * (∫ p, ptCoeff period hPeriod 4 frame a da f df p ∂mu) by
    funext t
    unfold globalPTDifferentialLLKineticAction
    simp_rw [density_quartic period hPeriod frame a da f df t]
    exact integral_quartic mu _ _ _ _ _ (hi 0) (hi 1) (hi 2) (hi 3) (hi 4) t]
  exact integral_quartic_hasDerivAt_zero mu _ _ _ _ _

end
end P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D
end JanusFormal
