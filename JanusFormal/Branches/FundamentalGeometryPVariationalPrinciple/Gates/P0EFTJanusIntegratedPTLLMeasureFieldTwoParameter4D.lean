import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLLMeasureFieldTwoParameterRawAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegrableQuarticPolynomial

/-! PT-averaged raw integration of the algebraic LL two-parameter density. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
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

def ptAverage (f : EffectiveThroat period hPeriod → Real)
    (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * (f p + f (fixedThroatPT period hPeriod p))

private def rawCoeff (degree : Fin 6)
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) : Real :=
  match degree with
  | 0 => llWorldvolumeDensity period hPeriod fields p
  | 1 => variation.measureDirection p * ‖fields.llField p‖ ^ 2
  | 2 => 2 * fields.llMeasure p *
      inner Real (fields.llField p) (variation.fieldDirection p)
  | 3 => fields.llMeasure p * ‖variation.fieldDirection p‖ ^ 2
  | 4 => 2 * variation.measureDirection p *
      inner Real (fields.llField p) (variation.fieldDirection p)
  | 5 => variation.measureDirection p * ‖variation.fieldDirection p‖ ^ 2

def ptCoeff (degree : Fin 6)
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod) :
    EffectiveThroat period hPeriod → Real :=
  ptAverage period hPeriod (rawCoeff period hPeriod degree fields variation)

private theorem rawCoeff_continuous (degree : Fin 6)
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod) :
    Continuous (rawCoeff period hPeriod degree fields variation) := by
  unfold rawCoeff
  fin_cases degree <;> simp only
  · exact llWorldvolumeDensity_continuous period hPeriod fields
  · exact variation.measureDirection.contMDiff_toFun.continuous.mul
      (fields.llField.contMDiff_toFun.continuous.norm.pow 2)
  · exact (continuous_const.mul fields.llMeasure.contMDiff_toFun.continuous).mul
      (fields.llField.contMDiff_toFun.continuous.inner
        variation.fieldDirection.contMDiff_toFun.continuous)
  · exact fields.llMeasure.contMDiff_toFun.continuous.mul
      (variation.fieldDirection.contMDiff_toFun.continuous.norm.pow 2)
  · exact (continuous_const.mul variation.measureDirection.contMDiff_toFun.continuous).mul
      (fields.llField.contMDiff_toFun.continuous.inner
        variation.fieldDirection.contMDiff_toFun.continuous)
  · exact variation.measureDirection.contMDiff_toFun.continuous.mul
      (variation.fieldDirection.contMDiff_toFun.continuous.norm.pow 2)

theorem ptCoeff_integrable (degree : Fin 6)
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptCoeff period hPeriod degree fields variation) mu := by
  have hraw := rawCoeff_continuous period hPeriod degree fields variation
  have h : Continuous (ptCoeff period hPeriod degree fields variation) := by
    unfold ptCoeff ptAverage
    exact continuous_const.mul (hraw.add
      (hraw.comp (continuous_fixedThroatPT period hPeriod)))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def globalPTLLAction (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptAverage period hPeriod
    (llWorldvolumeDensity period hPeriod fields) p ∂mu

private theorem ptDensity_twoParameter
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod) (s t : Real)
    (p : EffectiveThroat period hPeriod) :
    ptAverage period hPeriod (llWorldvolumeDensity period hPeriod
      (llMeasureFieldCurve period hPeriod fields variation s t)) p =
      ptCoeff period hPeriod 0 fields variation p +
      s * ptCoeff period hPeriod 1 fields variation p +
      t * ptCoeff period hPeriod 2 fields variation p +
      t ^ 2 * ptCoeff period hPeriod 3 fields variation p +
      s * t * ptCoeff period hPeriod 4 fields variation p +
      s * t ^ 2 * ptCoeff period hPeriod 5 fields variation p := by
  unfold ptAverage ptCoeff rawCoeff
  simp only [ptAverage]
  rw [llWorldvolumeDensity_twoParameter period hPeriod fields variation s t p,
    llWorldvolumeDensity_twoParameter period hPeriod fields variation s t
      (fixedThroatPT period hPeriod p)]
  ring

theorem globalPTLLAction_twoParameter
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod) (s t : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTLLAction period hPeriod
      (llMeasureFieldCurve period hPeriod fields variation s t) mu =
      ∫ p, ptCoeff period hPeriod 0 fields variation p +
        s * ptCoeff period hPeriod 1 fields variation p +
        t * ptCoeff period hPeriod 2 fields variation p +
        t ^ 2 * ptCoeff period hPeriod 3 fields variation p +
        s * t * ptCoeff period hPeriod 4 fields variation p +
        s * t ^ 2 * ptCoeff period hPeriod 5 fields variation p ∂mu := by
  unfold globalPTLLAction
  congr 1
  funext p
  exact ptDensity_twoParameter period hPeriod fields variation s t p

theorem globalPTLLAction_diagonal_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalPTLLAction period hPeriod
      (llMeasureFieldCurve period hPeriod fields variation t t) mu)
      (∫ p, ptCoeff period hPeriod 1 fields variation p +
        ptCoeff period hPeriod 2 fields variation p ∂mu) 0 := by
  have hi (d : Fin 6) := ptCoeff_integrable period hPeriod d fields variation mu
  rw [show (fun t : Real => globalPTLLAction period hPeriod
      (llMeasureFieldCurve period hPeriod fields variation t t) mu) =
      fun t : Real =>
        (∫ p, ptCoeff period hPeriod 0 fields variation p ∂mu) +
        t * (∫ p, (ptCoeff period hPeriod 1 fields variation p +
          ptCoeff period hPeriod 2 fields variation p) ∂mu) +
        t ^ 2 * (∫ p, (ptCoeff period hPeriod 3 fields variation p +
          ptCoeff period hPeriod 4 fields variation p) ∂mu) +
        t ^ 3 * (∫ p, ptCoeff period hPeriod 5 fields variation p ∂mu) +
        t ^ 4 * (∫ _p, (0 : Real) ∂mu) by
    funext t
    rw [globalPTLLAction_twoParameter period hPeriod fields variation t t mu]
    have hIntegrand :
        (fun p => ptCoeff period hPeriod 0 fields variation p +
          t * ptCoeff period hPeriod 1 fields variation p +
          t * ptCoeff period hPeriod 2 fields variation p +
          t ^ 2 * ptCoeff period hPeriod 3 fields variation p +
          t * t * ptCoeff period hPeriod 4 fields variation p +
          t * t ^ 2 * ptCoeff period hPeriod 5 fields variation p) =
        (fun p => ptCoeff period hPeriod 0 fields variation p +
          t * (ptCoeff period hPeriod 1 fields variation p +
            ptCoeff period hPeriod 2 fields variation p) +
          t ^ 2 * (ptCoeff period hPeriod 3 fields variation p +
            ptCoeff period hPeriod 4 fields variation p) +
          t ^ 3 * ptCoeff period hPeriod 5 fields variation p + t ^ 4 * 0) := by
      funext p
      ring
    rw [hIntegrand]
    exact (by
      simpa only [Pi.add_apply] using integral_quartic mu _ _ _ _
        (fun _ : EffectiveThroat period hPeriod => (0 : Real))
        (hi 0) ((hi 1).add (hi 2)) ((hi 3).add (hi 4)) (hi 5)
        (integrable_zero _ _ mu) t)]
  simpa only [integral_add (hi 1) (hi 2)] using
    integral_quartic_hasDerivAt_zero mu
      (ptCoeff period hPeriod 0 fields variation)
      (fun p => ptCoeff period hPeriod 1 fields variation p +
        ptCoeff period hPeriod 2 fields variation p)
      (fun p => ptCoeff period hPeriod 3 fields variation p +
        ptCoeff period hPeriod 4 fields variation p)
      (ptCoeff period hPeriod 5 fields variation) (fun _ => 0)

end
end P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
end JanusFormal
