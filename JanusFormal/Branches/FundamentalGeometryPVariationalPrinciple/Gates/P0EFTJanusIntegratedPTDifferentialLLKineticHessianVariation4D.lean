import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegrableQuarticPolynomial

/-! The actual integrated kinetic mixed Hessian differentiates the actual
integrated first variation. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTDifferentialLLKineticHessianVariation4D

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
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
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

private def rawRemainder (degree : Fin 2)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da₁ da₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (f df₁ df₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) : Real :=
  match degree with
  | 0 =>
      2 * inner Real (a p) (da₂ p) *
          throatDerivativePairing period hPeriod frame df₂ df₁ p +
        ‖da₂ p‖ ^ 2 * throatDerivativePairing period hPeriod frame f df₁ p +
        2 * inner Real (da₂ p) (da₁ p) *
          throatDerivativePairing period hPeriod frame f df₂ p +
        inner Real (a p) (da₁ p) *
          throatDerivativeEnergy period hPeriod frame df₂ p
  | 1 =>
      ‖da₂ p‖ ^ 2 * throatDerivativePairing period hPeriod frame df₂ df₁ p +
        inner Real (da₂ p) (da₁ p) *
          throatDerivativeEnergy period hPeriod frame df₂ p

private def ptRemainder (degree : Fin 2)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da₁ da₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (f df₁ df₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    (rawRemainder period hPeriod degree frame a da₁ da₂ f df₁ df₂ p +
      rawRemainder period hPeriod degree frame
        (throatPTPullback period hPeriod LLMetricFiber a)
        (differentialLLAuxMetricDirectionPT period hPeriod da₁)
        (differentialLLAuxMetricDirectionPT period hPeriod da₂)
        (throatPTPullback period hPeriod LLFieldFiber f)
        (differentialLLFluxDirectionPT period hPeriod df₁)
        (differentialLLFluxDirectionPT period hPeriod df₂) p)

private theorem pairing_curve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (f g v : SmoothThroatField period hPeriod LLFieldFiber) (t : Real)
    (p : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame (f + t • g) v p =
      throatDerivativePairing period hPeriod frame f v p +
        t * throatDerivativePairing period hPeriod frame g v p := by
  unfold throatDerivativePairing
  rw [throatFrameDerivative_add, throatFrameDerivative_smul]
  simp only [Pi.add_apply, Pi.smul_apply, inner_add_left, real_inner_smul_left,
    Finset.sum_add_distrib, Finset.mul_sum]

private theorem pairing_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (f g : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame f g p =
      throatDerivativePairing period hPeriod frame g f p := by
  unfold throatDerivativePairing
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

private theorem energy_curve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (f g : SmoothThroatField period hPeriod LLFieldFiber) (t : Real)
    (p : EffectiveThroat period hPeriod) :
    throatDerivativeEnergy period hPeriod frame (f + t • g) p =
      throatDerivativeEnergy period hPeriod frame f p +
        2 * t * throatDerivativePairing period hPeriod frame f g p +
        t ^ 2 * throatDerivativeEnergy period hPeriod frame g p := by
  unfold throatDerivativeEnergy throatDerivativePairing
  rw [throatFrameDerivative_add, throatFrameDerivative_smul]
  simp only [Pi.add_apply, Pi.smul_apply, norm_add_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

private theorem firstVariation_expansion
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da₁ da₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (f df₁ df₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (t : Real) (p : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
        (a + t • da₂) (f + t • df₂) da₁ df₁ p =
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
          a f da₁ df₁ p +
        t * ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
          frame a f da₁ da₂ df₁ df₂ p +
        t ^ 2 * ptRemainder period hPeriod 0 frame a da₁ da₂ f df₁ df₂ p +
        t ^ 3 * ptRemainder period hPeriod 1 frame a da₁ da₂ f df₁ df₂ p := by
  unfold ptSymmetricDifferentialLLKineticFirstVariation
    differentialLLKineticFirstVariation
  rw [show throatPTPullback period hPeriod LLMetricFiber (a + t • da₂) =
      throatPTPullback period hPeriod LLMetricFiber a +
        t • differentialLLAuxMetricDirectionPT period hPeriod da₂ by
      apply SmoothThroatField.ext period hPeriod LLMetricFiber; intro q; rfl]
  rw [show throatPTPullback period hPeriod LLFieldFiber (f + t • df₂) =
      throatPTPullback period hPeriod LLFieldFiber f +
        t • differentialLLFluxDirectionPT period hPeriod df₂ by
      apply SmoothThroatField.ext period hPeriod LLFieldFiber; intro q; rfl]
  rw [show (a + t • da₂).toFun p = a p + t • da₂ p by rfl]
  rw [show (throatPTPullback period hPeriod LLMetricFiber a +
      t • differentialLLAuxMetricDirectionPT period hPeriod da₂).toFun p =
      throatPTPullback period hPeriod LLMetricFiber a p +
        t • differentialLLAuxMetricDirectionPT period hPeriod da₂ p by rfl]
  simp_rw [pairing_curve period hPeriod, energy_curve period hPeriod]
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
    differentialLLKineticMixedHessianDensity ptRemainder rawRemainder
  rw [pairing_symmetric period hPeriod frame df₂ df₁ p,
    pairing_symmetric period hPeriod frame
      (differentialLLFluxDirectionPT period hPeriod df₂)
      (differentialLLFluxDirectionPT period hPeriod df₁) p,
    real_inner_comm (da₂ p) (da₁ p),
    real_inner_comm (differentialLLAuxMetricDirectionPT period hPeriod da₂ p)
      (differentialLLAuxMetricDirectionPT period hPeriod da₁ p)]
  change _ = _
  simp only [Pi.add_apply, Pi.smul_apply, norm_add_sq_real, real_inner_smul_right,
    inner_add_left, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

private theorem ptRemainder_integrable (degree : Fin 2)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da₁ da₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (f df₁ df₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptRemainder period hPeriod degree frame a da₁ da₂ f df₁ df₂) mu := by
  have hraw (a' da₁' da₂' : SmoothThroatField period hPeriod LLMetricFiber)
      (f' df₁' df₂' : SmoothThroatField period hPeriod LLFieldFiber) :
      Continuous (rawRemainder period hPeriod degree frame
        a' da₁' da₂' f' df₁' df₂') := by
    have ha := a'.contMDiff_toFun.continuous
    have hda₁ := da₁'.contMDiff_toFun.continuous
    have hda₂ := da₂'.contMDiff_toFun.continuous
    have hfdf₁ := throatDerivativePairing_continuous period hPeriod frame f' df₁'
    have hfdf₂ := throatDerivativePairing_continuous period hPeriod frame f' df₂'
    have hdf₂df₁ := throatDerivativePairing_continuous period hPeriod frame df₂' df₁'
    have hedf₂ := throatDerivativeEnergy_continuous period hPeriod frame df₂'
    unfold rawRemainder
    fin_cases degree <;> simp only <;> fun_prop
  have h : Continuous (ptRemainder period hPeriod degree frame
      a da₁ da₂ f df₁ df₂) := by
    unfold ptRemainder
    fun_prop
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem globalPTDifferentialLLKineticFirstVariation_second_direction_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (a da₁ da₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (f df₁ df₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => ∫ p,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
        (a + t • da₂) (f + t • df₂) da₁ df₁ p ∂mu)
      (globalPTDifferentialLLKineticMixedHessian period hPeriod frame
        a f da₁ da₂ df₁ df₂ mu) 0 := by
  have h0 := ptSymmetricDifferentialLLKineticFirstVariation_integrable
    period hPeriod frame a f da₁ df₁ mu
  have h1 : Continuous (ptSymmetricDifferentialLLKineticMixedHessianDensity
      period hPeriod frame a f da₁ da₂ df₁ df₂) := by
    have ha := a.contMDiff_toFun.continuous
    have hda₁ := da₁.contMDiff_toFun.continuous
    have hda₂ := da₂.contMDiff_toFun.continuous
    have hp := throatDerivativePairing_continuous period hPeriod
    have he := throatDerivativeEnergy_continuous period hPeriod
    have hpta := (throatPTPullback period hPeriod LLMetricFiber a).contMDiff_toFun.continuous
    have hptf := (throatPTPullback period hPeriod LLFieldFiber f).contMDiff_toFun.continuous
    have hptda₁ := (differentialLLAuxMetricDirectionPT period hPeriod da₁).contMDiff_toFun.continuous
    have hptda₂ := (differentialLLAuxMetricDirectionPT period hPeriod da₂).contMDiff_toFun.continuous
    unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
      differentialLLKineticMixedHessianDensity
    fun_prop
  have h1i : Integrable (ptSymmetricDifferentialLLKineticMixedHessianDensity
      period hPeriod frame a f da₁ da₂ df₁ df₂) mu :=
    h1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 := ptRemainder_integrable period hPeriod 0 frame a da₁ da₂ f df₁ df₂ mu
  have h3 := ptRemainder_integrable period hPeriod 1 frame a da₁ da₂ f df₁ df₂ mu
  rw [show (fun t : Real => ∫ p,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod frame
        (a + t • da₂) (f + t • df₂) da₁ df₁ p ∂mu) =
      fun t : Real =>
        (∫ p, ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
          frame a f da₁ df₁ p ∂mu) +
        t * (∫ p, ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
          frame a f da₁ da₂ df₁ df₂ p ∂mu) +
        t ^ 2 * (∫ p, ptRemainder period hPeriod 0 frame a da₁ da₂ f df₁ df₂ p ∂mu) +
        t ^ 3 * (∫ p, ptRemainder period hPeriod 1 frame a da₁ da₂ f df₁ df₂ p ∂mu) +
        t ^ 4 * (∫ _p, (0 : Real) ∂mu) by
    funext t
    simp_rw [firstVariation_expansion period hPeriod frame a da₁ da₂ f df₁ df₂ t]
    simpa only [Pi.add_apply, mul_zero, add_zero] using integral_quartic mu _ _ _ _
      (fun _ : EffectiveThroat period hPeriod => (0 : Real))
      h0 h1i h2 h3 (integrable_zero _ _ mu) t]
  unfold globalPTDifferentialLLKineticMixedHessian
  exact integral_quartic_hasDerivAt_zero mu _ _ _ _ _

end
end P0EFTJanusIntegratedPTDifferentialLLKineticHessianVariation4D
end JanusFormal
