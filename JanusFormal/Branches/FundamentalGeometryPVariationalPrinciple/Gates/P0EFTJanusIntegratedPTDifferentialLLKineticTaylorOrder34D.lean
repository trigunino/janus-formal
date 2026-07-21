import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D

/-! Exact cubic and quartic Taylor coefficients of the integrated PT kinetic curve. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTDifferentialLLKineticTaylorOrder34D

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
open P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegrableQuarticPolynomial

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def rawTaylorCoeff (degree : Fin 5)
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

def ptTaylorCoeff (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * (rawTaylorCoeff period hPeriod degree frame a da f df p +
    rawTaylorCoeff period hPeriod degree frame
      (throatPTPullback period hPeriod LLMetricFiber a)
      (differentialLLAuxMetricDirectionPT period hPeriod da)
      (throatPTPullback period hPeriod LLFieldFiber f)
      (differentialLLFluxDirectionPT period hPeriod df) p)

abbrev C3 := ptTaylorCoeff period hPeriod (3 : Fin 5)
abbrev C4 := ptTaylorCoeff period hPeriod (4 : Fin 5)

theorem rawTaylorCoeff_continuous (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (rawTaylorCoeff period hPeriod degree frame a da f df) := by
  have A0 : Continuous (fun p => 1 + ‖a p‖ ^ 2) :=
    continuous_const.add (a.contMDiff_toFun.continuous.norm.pow 2)
  have A1 : Continuous (fun p => 2 * inner Real (a p) (da p)) :=
    continuous_const.mul (a.contMDiff_toFun.continuous.inner da.contMDiff_toFun.continuous)
  have A2 : Continuous (fun p => ‖da p‖ ^ 2) := da.contMDiff_toFun.continuous.norm.pow 2
  have E0 := throatDerivativeEnergy_continuous period hPeriod frame f
  have E1 : Continuous (fun p => 2 * throatDerivativePairing period hPeriod frame f df p) :=
    continuous_const.mul (throatDerivativePairing_continuous period hPeriod frame f df)
  have E2 := throatDerivativeEnergy_continuous period hPeriod frame df
  unfold rawTaylorCoeff
  fin_cases degree <;> simp only <;>
    first | exact continuous_const.mul (A0.mul E0)
          | exact continuous_const.mul ((A0.mul E1).add (A1.mul E0))
          | exact continuous_const.mul (((A0.mul E2).add (A1.mul E1)).add (A2.mul E0))
          | exact continuous_const.mul ((A1.mul E2).add (A2.mul E1))
          | exact continuous_const.mul (A2.mul E2)

theorem ptTaylorCoeff_continuous (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (ptTaylorCoeff period hPeriod degree frame a da f df) := by
  unfold ptTaylorCoeff
  exact continuous_const.mul
    ((rawTaylorCoeff_continuous period hPeriod degree frame a da f df).add
      (rawTaylorCoeff_continuous period hPeriod degree frame
        (throatPTPullback period hPeriod LLMetricFiber a)
        (differentialLLAuxMetricDirectionPT period hPeriod da)
        (throatPTPullback period hPeriod LLFieldFiber f)
        (differentialLLFluxDirectionPT period hPeriod df)))

theorem ptTaylorCoeff_integrable (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptTaylorCoeff period hPeriod degree frame a da f df) mu :=
  (ptTaylorCoeff_continuous period hPeriod degree frame a da f df).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem density_taylor_polynomial
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber) (t : Real)
    (p : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticDensity period hPeriod frame (a + t • da) (f + t • df) p =
      ptTaylorCoeff period hPeriod 0 frame a da f df p +
      t * ptTaylorCoeff period hPeriod 1 frame a da f df p +
      t^2 * ptTaylorCoeff period hPeriod 2 frame a da f df p +
      t^3 * C3 period hPeriod frame a da f df p +
      t^4 * C4 period hPeriod frame a da f df p := by
  simp only [C3, C4]
  rw [ptSymmetricDifferentialLLKineticDensity_simultaneous_polynomial]
  unfold ptTaylorCoeff rawTaylorCoeff
  simp only
  ring

theorem integrated_taylor_polynomial
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] (t : Real) :
    globalPTDifferentialLLKineticAction period hPeriod frame (a + t • da) (f + t • df) mu =
      (∫ p, ptTaylorCoeff period hPeriod 0 frame a da f df p ∂mu) +
      t * (∫ p, ptTaylorCoeff period hPeriod 1 frame a da f df p ∂mu) +
      t^2 * (∫ p, ptTaylorCoeff period hPeriod 2 frame a da f df p ∂mu) +
      t^3 * (∫ p, C3 period hPeriod frame a da f df p ∂mu) +
      t^4 * (∫ p, C4 period hPeriod frame a da f df p ∂mu) := by
  unfold globalPTDifferentialLLKineticAction
  simp_rw [density_taylor_polynomial period hPeriod frame a da f df t]
  exact integral_quartic mu _ _ _ _ _
    (ptTaylorCoeff_integrable period hPeriod 0 frame a da f df mu)
    (ptTaylorCoeff_integrable period hPeriod 1 frame a da f df mu)
    (ptTaylorCoeff_integrable period hPeriod 2 frame a da f df mu)
    (ptTaylorCoeff_integrable period hPeriod 3 frame a da f df mu)
    (ptTaylorCoeff_integrable period hPeriod 4 frame a da f df mu) t

theorem third_iteratedDeriv_integrated_curve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    iteratedDeriv 3 (fun t : Real => globalPTDifferentialLLKineticAction period hPeriod frame
      (a + t • da) (f + t • df) mu) 0 =
      6 * (∫ p, C3 period hPeriod frame a da f df p ∂mu) := by
  rw [show (fun t : Real => globalPTDifferentialLLKineticAction period hPeriod frame
      (a + t • da) (f + t • df) mu) = fun t =>
      (∫ p, ptTaylorCoeff period hPeriod 0 frame a da f df p ∂mu) +
      t * (∫ p, ptTaylorCoeff period hPeriod 1 frame a da f df p ∂mu) +
      t^2 * (∫ p, ptTaylorCoeff period hPeriod 2 frame a da f df p ∂mu) +
      t^3 * (∫ p, C3 period hPeriod frame a da f df p ∂mu) +
      t^4 * (∫ p, C4 period hPeriod frame a da f df p ∂mu) by
    funext t; exact integrated_taylor_polynomial period hPeriod frame a da f df mu t]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_mul,
    iteratedDeriv_const, iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  norm_num [Finset.sum_range_succ]

theorem fourth_iteratedDeriv_integrated_curve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da : SmoothThroatField period hPeriod LLMetricFiber)
    (f df : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    iteratedDeriv 4 (fun t : Real => globalPTDifferentialLLKineticAction period hPeriod frame
      (a + t • da) (f + t • df) mu) 0 =
      24 * (∫ p, C4 period hPeriod frame a da f df p ∂mu) := by
  rw [show (fun t : Real => globalPTDifferentialLLKineticAction period hPeriod frame
      (a + t • da) (f + t • df) mu) = fun t =>
      (∫ p, ptTaylorCoeff period hPeriod 0 frame a da f df p ∂mu) +
      t * (∫ p, ptTaylorCoeff period hPeriod 1 frame a da f df p ∂mu) +
      t^2 * (∫ p, ptTaylorCoeff period hPeriod 2 frame a da f df p ∂mu) +
      t^3 * (∫ p, C3 period hPeriod frame a da f df p ∂mu) +
      t^4 * (∫ p, C4 period hPeriod frame a da f df p ∂mu) by
    funext t; exact integrated_taylor_polynomial period hPeriod frame a da f df mu t]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_mul,
    iteratedDeriv_const, iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  norm_num [Finset.sum_range_succ]

end
end P0EFTJanusIntegratedPTDifferentialLLKineticTaylorOrder34D
end JanusFormal
