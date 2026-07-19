import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D

/-! Mixed Hessian of the actual PT-averaged differential LL kinetic action. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D

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

/-- Polarization of the second coefficient of
`(1/2) * (1 + ‖aux‖²) * Energy field`. -/
def differentialLLKineticMixedHessianDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 + ‖aux point‖ ^ 2) *
      throatDerivativePairing period hPeriod frame dField₁ dField₂ point +
    2 * inner Real (aux point) (dAux₁ point) *
      throatDerivativePairing period hPeriod frame field dField₂ point +
    2 * inner Real (aux point) (dAux₂ point) *
      throatDerivativePairing period hPeriod frame field dField₁ point +
    inner Real (dAux₁ point) (dAux₂ point) *
      throatDerivativeEnergy period hPeriod frame field point

private theorem throatDerivativePairing_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame first second point =
      throatDerivativePairing period hPeriod frame second first point := by
  unfold throatDerivativePairing
  apply Finset.sum_congr rfl
  intro index _
  exact real_inner_comm _ _

private theorem throatDerivativePairing_add_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first first' second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame (first + first') second point =
      throatDerivativePairing period hPeriod frame first second point +
        throatDerivativePairing period hPeriod frame first' second point := by
  unfold throatDerivativePairing
  simp_rw [congrFun (congrFun
    (throatFrameDerivative_add period hPeriod LLFieldFiber frame first first') point)]
  simp only [Pi.add_apply, inner_add_left, Finset.sum_add_distrib]

private theorem throatDerivativePairing_smul_left
    (frame : SmoothThroatGeneratingFrame period hPeriod) (scalar : Real)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame (scalar • first) second point =
      scalar * throatDerivativePairing period hPeriod frame first second point := by
  unfold throatDerivativePairing
  simp_rw [congrFun (congrFun
    (throatFrameDerivative_smul period hPeriod LLFieldFiber frame scalar first) point)]
  simp only [Pi.smul_apply, real_inner_smul_left, Finset.mul_sum]

private theorem throatDerivativePairing_add_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second second' : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame first (second + second') point =
      throatDerivativePairing period hPeriod frame first second point +
        throatDerivativePairing period hPeriod frame first second' point := by
  rw [throatDerivativePairing_symmetric period hPeriod frame first,
    throatDerivativePairing_add_left,
    throatDerivativePairing_symmetric period hPeriod frame second,
    throatDerivativePairing_symmetric period hPeriod frame second']

private theorem throatDerivativePairing_smul_right
    (frame : SmoothThroatGeneratingFrame period hPeriod) (scalar : Real)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame first (scalar • second) point =
      scalar * throatDerivativePairing period hPeriod frame first second point := by
  rw [throatDerivativePairing_symmetric period hPeriod frame first,
    throatDerivativePairing_smul_left,
    throatDerivativePairing_symmetric period hPeriod frame second]

theorem differentialLLKineticMixedHessianDensity_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    differentialLLKineticMixedHessianDensity period hPeriod frame aux field
        dAux₁ dAux₂ dField₁ dField₂ point =
      differentialLLKineticMixedHessianDensity period hPeriod frame aux field
        dAux₂ dAux₁ dField₂ dField₁ point := by
  unfold differentialLLKineticMixedHessianDensity
  rw [throatDerivativePairing_symmetric period hPeriod frame dField₁ dField₂]
  rw [real_inner_comm (dAux₁ point) (dAux₂ point)]
  ring

theorem differentialLLKineticMixedHessianDensity_add_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₁' dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₁' dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    differentialLLKineticMixedHessianDensity period hPeriod frame aux field
        (dAux₁ + dAux₁') dAux₂ (dField₁ + dField₁') dField₂ point =
      differentialLLKineticMixedHessianDensity period hPeriod frame aux field
          dAux₁ dAux₂ dField₁ dField₂ point +
        differentialLLKineticMixedHessianDensity period hPeriod frame aux field
          dAux₁' dAux₂ dField₁' dField₂ point := by
  unfold differentialLLKineticMixedHessianDensity
  rw [throatDerivativePairing_add_left, throatDerivativePairing_add_right]
  rw [show (dAux₁ + dAux₁').toFun point = dAux₁ point + dAux₁' point by rfl]
  rw [inner_add_left, inner_add_right]
  ring

theorem differentialLLKineticMixedHessianDensity_smul_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (scalar : Real)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    differentialLLKineticMixedHessianDensity period hPeriod frame aux field
        (scalar • dAux₁) dAux₂ (scalar • dField₁) dField₂ point =
      scalar * differentialLLKineticMixedHessianDensity period hPeriod frame aux field
        dAux₁ dAux₂ dField₁ dField₂ point := by
  unfold differentialLLKineticMixedHessianDensity
  rw [throatDerivativePairing_smul_left, throatDerivativePairing_smul_right]
  rw [show (scalar • dAux₁).toFun point = scalar • dAux₁ point by rfl]
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

/-- PT average of the mixed Hessian density, with both directions transported
on the second orbit. -/
def ptSymmetricDifferentialLLKineticMixedHessianDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    (differentialLLKineticMixedHessianDensity period hPeriod frame aux field
        dAux₁ dAux₂ dField₁ dField₂ point +
      differentialLLKineticMixedHessianDensity period hPeriod frame
        (throatPTPullback period hPeriod LLMetricFiber aux)
        (throatPTPullback period hPeriod LLFieldFiber field)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux₁)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux₂)
        (differentialLLFluxDirectionPT period hPeriod dField₁)
        (differentialLLFluxDirectionPT period hPeriod dField₂) point)

theorem ptSymmetricDifferentialLLKineticMixedHessianDensity_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod frame aux field
        dAux₁ dAux₂ dField₁ dField₂ point =
      ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod frame aux field
        dAux₂ dAux₁ dField₂ dField₁ point := by
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
  congr 2
  · exact differentialLLKineticMixedHessianDensity_symmetric
      period hPeriod frame aux field dAux₁ dAux₂ dField₁ dField₂ point
  · exact differentialLLKineticMixedHessianDensity_symmetric period hPeriod frame
      (throatPTPullback period hPeriod LLMetricFiber aux)
      (throatPTPullback period hPeriod LLFieldFiber field)
      (differentialLLAuxMetricDirectionPT period hPeriod dAux₁)
      (differentialLLAuxMetricDirectionPT period hPeriod dAux₂)
      (differentialLLFluxDirectionPT period hPeriod dField₁)
      (differentialLLFluxDirectionPT period hPeriod dField₂) point

def globalPTDifferentialLLKineticMixedHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
    frame aux field dAux₁ dAux₂ dField₁ dField₂ point ∂mu

theorem globalPTDifferentialLLKineticMixedHessian_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTDifferentialLLKineticMixedHessian period hPeriod frame aux field
        dAux₁ dAux₂ dField₁ dField₂ mu =
      globalPTDifferentialLLKineticMixedHessian period hPeriod frame aux field
        dAux₂ dAux₁ dField₂ dField₁ mu := by
  unfold globalPTDifferentialLLKineticMixedHessian
  apply integral_congr_ae
  filter_upwards [] with point
  exact ptSymmetricDifferentialLLKineticMixedHessianDensity_symmetric
    period hPeriod frame aux field dAux₁ dAux₂ dField₁ dField₂ point

end
end P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
end JanusFormal
