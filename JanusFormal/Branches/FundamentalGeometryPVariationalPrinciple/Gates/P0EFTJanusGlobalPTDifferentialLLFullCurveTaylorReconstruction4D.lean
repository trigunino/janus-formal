import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLFullCurveTaylorDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLVariationalAPI4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegrableQuarticPolynomial
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D

/-! Exact global PT Taylor reconstruction along the genuine full LL curve. -/

namespace JanusFormal
namespace P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D

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
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusDifferentialLLFullCurveTaylorDensity4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusIntegrableQuarticPolynomial
open P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D

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

private def rawTaylorCoeff (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) : Real :=
  match degree with
  | 0 => differentialLLDensity period hPeriod frame fields p
  | 1 => differentialLLKineticFirstVariation period hPeriod frame
      fields.llAuxMetric fields.llField dAux variation.fieldDirection p +
      llFirstVariationDensity period hPeriod fields variation p
  | 2 => (1 / 2 : Real) * differentialLLKineticMixedHessianDensity period hPeriod
      frame fields.llAuxMetric fields.llField dAux dAux variation.fieldDirection
        variation.fieldDirection p +
      llSecondVariationCoefficient period hPeriod fields variation p
  | 3 => rawFullLLCubicDensity period hPeriod frame fields dAux variation p
  | 4 => rawFullLLQuarticDensity period hPeriod frame dAux variation.fieldDirection p

private def variationPT (variation : LLVariation period hPeriod) :
    LLVariation period hPeriod where
  measureDirection := throatPTPullback period hPeriod Real variation.measureDirection
  fieldDirection := differentialLLFluxDirectionPT period hPeriod variation.fieldDirection

def ptTaylorCoeff (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    (rawTaylorCoeff period hPeriod degree frame fields dAux variation p +
      rawTaylorCoeff period hPeriod degree frame (llPTPullback period hPeriod fields)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux)
        (variationPT period hPeriod variation) p)

private theorem llPTPullback_fullCurve
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) (t : Real) :
    llPTPullback period hPeriod
        (differentialLLFullCurve period hPeriod fields dAux
          variation.measureDirection variation.fieldDirection t) =
      differentialLLFullCurve period hPeriod (llPTPullback period hPeriod fields)
        (differentialLLAuxMetricDirectionPT period hPeriod dAux)
        (variationPT period hPeriod variation).measureDirection
        (variationPT period hPeriod variation).fieldDirection t := by
  cases fields
  apply IndependentFields.ext <;> rfl

private theorem ptDensity_polynomial
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) (t : Real)
    (p : EffectiveThroat period hPeriod) :
    (1 / 2 : Real) *
      (differentialLLDensity period hPeriod frame
          (differentialLLFullCurve period hPeriod fields dAux
            variation.measureDirection variation.fieldDirection t) p +
        differentialLLDensity period hPeriod frame
          (llPTPullback period hPeriod
            (differentialLLFullCurve period hPeriod fields dAux
              variation.measureDirection variation.fieldDirection t)) p) =
      ptTaylorCoeff period hPeriod 0 frame fields dAux variation p +
      t * ptTaylorCoeff period hPeriod 1 frame fields dAux variation p +
      t ^ 2 * ptTaylorCoeff period hPeriod 2 frame fields dAux variation p +
      t ^ 3 * ptTaylorCoeff period hPeriod 3 frame fields dAux variation p +
      t ^ 4 * ptTaylorCoeff period hPeriod 4 frame fields dAux variation p := by
  rw [llPTPullback_fullCurve period hPeriod]
  rw [differentialLLDensity_fullCurve_exact_taylor,
    differentialLLDensity_fullCurve_exact_taylor]
  unfold ptTaylorCoeff rawTaylorCoeff
  simp only [Function.comp_apply]
  ring

private theorem rawTaylorCoeff_continuous (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) :
    Continuous (rawTaylorCoeff period hPeriod degree frame fields dAux variation) := by
  have hDensity := differentialLLDensity_continuous period hPeriod frame fields
  have hp := throatDerivativePairing_continuous period hPeriod frame
  have he := throatDerivativeEnergy_continuous period hPeriod frame
  have ha := fields.llAuxMetric.contMDiff_toFun.continuous
  have hda := dAux.contMDiff_toFun.continuous
  have hm := variation.measureDirection.contMDiff_toFun.continuous
  have hf := fields.llField.contMDiff_toFun.continuous
  have hdf := variation.fieldDirection.contMDiff_toFun.continuous
  have hw1 := llFirstVariationDensity_continuous period hPeriod fields variation
  have hw2 := llSecondVariationCoefficient_continuous period hPeriod fields variation
  have hw3 := llThirdVariationCoefficient_continuous period hPeriod variation
  unfold rawTaylorCoeff rawFullLLCubicDensity rawFullLLQuarticDensity
    differentialLLKineticFirstVariation differentialLLKineticMixedHessianDensity
  fin_cases degree <;> simp only
  · exact hDensity
  all_goals fun_prop

theorem ptTaylorCoeff_integrable (degree : Fin 5)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptTaylorCoeff period hPeriod degree frame fields dAux variation) mu := by
  have h : Continuous (ptTaylorCoeff period hPeriod degree frame fields dAux variation) := by
    unfold ptTaylorCoeff
    exact continuous_const.mul
      ((rawTaylorCoeff_continuous period hPeriod degree frame fields dAux variation).add
        (rawTaylorCoeff_continuous period hPeriod degree frame
          (llPTPullback period hPeriod fields)
          (differentialLLAuxMetricDirectionPT period hPeriod dAux)
          (variationPT period hPeriod variation)))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem globalPTAction_fullCurve_quartic
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) (t : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields dAux
          variation.measureDirection variation.fieldDirection t) mu =
      (∫ p, ptTaylorCoeff period hPeriod 0 frame fields dAux variation p ∂mu) +
      t * (∫ p, ptTaylorCoeff period hPeriod 1 frame fields dAux variation p ∂mu) +
      t ^ 2 * (∫ p, ptTaylorCoeff period hPeriod 2 frame fields dAux variation p ∂mu) +
      t ^ 3 * (∫ p, ptTaylorCoeff period hPeriod 3 frame fields dAux variation p ∂mu) +
      t ^ 4 * (∫ p, ptTaylorCoeff period hPeriod 4 frame fields dAux variation p ∂mu) := by
  have hi (d : Fin 5) := ptTaylorCoeff_integrable period hPeriod d frame fields dAux variation mu
  let curve := differentialLLFullCurve period hPeriod fields dAux
    variation.measureDirection variation.fieldDirection t
  have hCurve := differentialLLDensity_integrable period hPeriod frame curve mu
  have hPTCurve := differentialLLDensity_integrable period hPeriod frame
    (llPTPullback period hPeriod curve) mu
  rw [show globalPTSymmetricDifferentialLLAction period hPeriod frame curve mu =
      ∫ p, (1 / 2 : Real) *
        (differentialLLDensity period hPeriod frame curve p +
          differentialLLDensity period hPeriod frame
            (llPTPullback period hPeriod curve) p) ∂mu by
    unfold globalPTSymmetricDifferentialLLAction globalDifferentialLLAction
    rw [integral_const_mul, integral_add hCurve hPTCurve]]
  dsimp [curve]
  simp_rw [ptDensity_polynomial period hPeriod frame fields dAux variation t]
  exact integral_quartic mu _ _ _ _ _ (hi 0) (hi 1) (hi 2) (hi 3) (hi 4) t

/-- The genuine linear coefficient of the exact global curve. -/
def globalPTFullLLTaylorEuler
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptTaylorCoeff period hPeriod 1 frame fields dAux variation p ∂mu

/-- Twice the quadratic coefficient. Pointwise this is exactly the sum of
the kinetic mixed Hessian on the diagonal and the worldvolume diagonal
second variation, not a reconstruction from Hessian data alone. -/
def globalPTFullLLTaylorHessianDiagonal
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  2 * (∫ p, ptTaylorCoeff period hPeriod 2 frame fields dAux variation p ∂mu)

def globalPTFullLLTaylorCubic
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptTaylorCoeff period hPeriod 3 frame fields dAux variation p ∂mu

def globalPTFullLLTaylorQuartic
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptTaylorCoeff period hPeriod 4 frame fields dAux variation p ∂mu

theorem ptTaylorCoeff_two_is_half_actual_diagonal_hessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) :
    2 * ptTaylorCoeff period hPeriod 2 frame fields dAux variation p =
      ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod frame
        fields.llAuxMetric fields.llField dAux dAux variation.fieldDirection
          variation.fieldDirection p +
      ptLLWorldvolumeHessianDensity period hPeriod fields variation variation p := by
  unfold ptTaylorCoeff rawTaylorCoeff
    ptSymmetricDifferentialLLKineticMixedHessianDensity
    ptLLWorldvolumeHessianDensity ptAverage llWorldvolumeHessianDensity
    variationPT llSecondVariationCoefficient llPTPullback
    differentialLLAuxMetricDirectionPT differentialLLFluxDirectionPT
    throatPTPullback
  simp only [Function.comp_apply]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

theorem globalPTFullLLTaylorHessianDiagonal_eq_actual
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTFullLLTaylorHessianDiagonal period hPeriod frame fields dAux variation mu =
      globalPTDifferentialLLKineticMixedHessian period hPeriod frame
        fields.llAuxMetric fields.llField dAux dAux variation.fieldDirection
          variation.fieldDirection mu +
      globalPTLLWorldvolumeHessian period hPeriod fields variation variation mu := by
  have hK : Integrable (ptSymmetricDifferentialLLKineticMixedHessianDensity
      period hPeriod frame fields.llAuxMetric fields.llField dAux dAux
        variation.fieldDirection variation.fieldDirection) mu := by
    have hRaw := differentialLLKineticMixedHessianDensity_continuous period hPeriod
      frame fields.llAuxMetric fields.llField dAux dAux variation.fieldDirection
        variation.fieldDirection
    have hPTRaw := differentialLLKineticMixedHessianDensity_continuous period hPeriod
      frame (throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric)
      (throatPTPullback period hPeriod LLFieldFiber fields.llField)
      (differentialLLAuxMetricDirectionPT period hPeriod dAux)
      (differentialLLAuxMetricDirectionPT period hPeriod dAux)
      (differentialLLFluxDirectionPT period hPeriod variation.fieldDirection)
      (differentialLLFluxDirectionPT period hPeriod variation.fieldDirection)
    exact (continuous_const.mul (hRaw.add hPTRaw)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hW := ptLLWorldvolumeHessianDensity_integrable period hPeriod fields
    variation variation mu
  unfold globalPTFullLLTaylorHessianDiagonal
    globalPTDifferentialLLKineticMixedHessian globalPTLLWorldvolumeHessian
  rw [← integral_add hK hW, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  exact ptTaylorCoeff_two_is_half_actual_diagonal_hessian period hPeriod frame
    fields dAux variation p

theorem globalPTFullLLTaylorEuler_eq_actual
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTFullLLTaylorEuler period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) mu =
      fullLLEuler period hPeriod frame fields direction mu := by
  let variation := fullDirectionLLVariation period hPeriod direction
  have hi (d : Fin 5) := ptTaylorCoeff_integrable period hPeriod d frame fields
    direction.llAuxMetric variation mu
  have hPolynomial : HasDerivAt
      (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
          variation.measureDirection variation.fieldDirection t) mu)
      (∫ p, ptTaylorCoeff period hPeriod 1 frame fields direction.llAuxMetric
        variation p ∂mu) 0 := by
    rw [show (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
          variation.measureDirection variation.fieldDirection t) mu) =
      fun t : Real =>
        (∫ p, ptTaylorCoeff period hPeriod 0 frame fields direction.llAuxMetric variation p ∂mu) +
        t * (∫ p, ptTaylorCoeff period hPeriod 1 frame fields direction.llAuxMetric variation p ∂mu) +
        t ^ 2 * (∫ p, ptTaylorCoeff period hPeriod 2 frame fields direction.llAuxMetric variation p ∂mu) +
        t ^ 3 * (∫ p, ptTaylorCoeff period hPeriod 3 frame fields direction.llAuxMetric variation p ∂mu) +
        t ^ 4 * (∫ p, ptTaylorCoeff period hPeriod 4 frame fields direction.llAuxMetric variation p ∂mu) by
      funext t
      exact globalPTAction_fullCurve_quartic period hPeriod frame fields
        direction.llAuxMetric variation t mu]
    exact integral_quartic_hasDerivAt_zero mu _ _ _ _ _
  have hActual := truePTAction_fullCurve_hasDerivAt_fullLLEuler period hPeriod
    frame fields direction mu
  unfold globalPTFullLLTaylorEuler fullLLEuler
  exact hPolynomial.unique hActual

/-- Exact global Taylor reconstruction through degree four. The cubic and
quartic terms are retained explicitly. -/
theorem globalPTAction_fullCurve_exact_taylor
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) (t : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields dAux
          variation.measureDirection variation.fieldDirection t) mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu +
      t * globalPTFullLLTaylorEuler period hPeriod frame fields dAux variation mu +
      (t ^ 2 / 2) * globalPTFullLLTaylorHessianDiagonal period hPeriod frame
        fields dAux variation mu +
      t ^ 3 * globalPTFullLLTaylorCubic period hPeriod frame fields dAux variation mu +
      t ^ 4 * globalPTFullLLTaylorQuartic period hPeriod frame fields dAux variation mu := by
  have h := globalPTAction_fullCurve_quartic period hPeriod frame fields dAux
    variation t mu
  have h0 := globalPTAction_fullCurve_quartic period hPeriod frame fields dAux
    variation 0 mu
  have hBase : globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu =
      ∫ p, ptTaylorCoeff period hPeriod 0 frame fields dAux variation p ∂mu := by
    simpa [differentialLLFullCurve] using h0
  rw [hBase]
  unfold globalPTFullLLTaylorEuler globalPTFullLLTaylorHessianDiagonal
    globalPTFullLLTaylorCubic globalPTFullLLTaylorQuartic
  convert h using 1 <;> ring

/-- Final named form: value, actual Euler, half the actual diagonal full LL
Hessian, and the explicit integrated cubic and quartic coefficients. -/
theorem globalPTAction_fullDirection_exact_taylor
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) (t : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
          direction.llMeasure direction.common.ll t) mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu +
      t * fullLLEuler period hPeriod frame fields direction mu +
      (t ^ 2 / 2) * globalPTFullLLHessianForm period hPeriod frame fields
        direction direction mu +
      t ^ 3 * globalPTFullLLTaylorCubic period hPeriod frame fields
        direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction) mu +
      t ^ 4 * globalPTFullLLTaylorQuartic period hPeriod frame fields
        direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction) mu := by
  have h := globalPTAction_fullCurve_exact_taylor period hPeriod frame fields
    direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction) t mu
  rw [globalPTFullLLTaylorEuler_eq_actual period hPeriod frame fields direction mu] at h
  rw [globalPTFullLLTaylorHessianDiagonal_eq_actual period hPeriod frame fields
    direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction) mu] at h
  simpa only [fullDirectionLLVariation, globalPTFullLLHessianForm] using h

end
end P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
end JanusFormal
