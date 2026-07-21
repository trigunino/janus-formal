import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D

namespace JanusFormal
namespace P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D

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
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem differentialLLKineticMixedHessianDensity_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (differentialLLKineticMixedHessianDensity period hPeriod frame
      aux field dAux₁ dAux₂ dField₁ dField₂) := by
  unfold differentialLLKineticMixedHessianDensity
  have hOne : Continuous (fun _ : EffectiveThroat period hPeriod => (1 : Real)) := continuous_const
  have hTwo : Continuous (fun _ : EffectiveThroat period hPeriod => (2 : Real)) := continuous_const
  have h0 := (hOne.add (aux.contMDiff_toFun.continuous.norm.pow 2)).mul
    (throatDerivativePairing_continuous period hPeriod frame dField₁ dField₂)
  have h1 := (hTwo.mul
    (aux.contMDiff_toFun.continuous.inner dAux₁.contMDiff_toFun.continuous)).mul
    (throatDerivativePairing_continuous period hPeriod frame field dField₂)
  have h2 := (hTwo.mul
    (aux.contMDiff_toFun.continuous.inner dAux₂.contMDiff_toFun.continuous)).mul
    (throatDerivativePairing_continuous period hPeriod frame field dField₁)
  have h3 := (dAux₁.contMDiff_toFun.continuous.inner
    dAux₂.contMDiff_toFun.continuous).mul
    (throatDerivativeEnergy_continuous period hPeriod frame field)
  exact ((h0.add h1).add h2).add h3

theorem differentialLLKineticMixedHessianDensity_integrable
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (differentialLLKineticMixedHessianDensity period hPeriod frame
      aux field dAux₁ dAux₂ dField₁ dField₂) mu :=
  (differentialLLKineticMixedHessianDensity_continuous period hPeriod frame aux
    field dAux₁ dAux₂ dField₁ dField₂).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end
end P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D
end JanusFormal
