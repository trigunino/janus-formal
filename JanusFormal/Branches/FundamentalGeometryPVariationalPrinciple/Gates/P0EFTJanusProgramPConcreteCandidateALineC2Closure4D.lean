import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteFullActionFrechetC2Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompactParametricIntegralC2
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Concrete Candidate-A linewise C² closure

This gate closes the Candidate-A slot of
`FullMetricLineMissingC2Slots` on the genuine exponential metric line and a
finite measure over the compact mapping torus.  No other full-action slot is
claimed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConcreteCandidateALineC2Closure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff Matrix.Norms.Frobenius BigOperators Topology
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusCoDiagonalLorentzRootFirstDerivative
open P0EFTJanusCoDiagonalInteractionDensityFrechet
open P0EFTJanusGlobalDiagonalInteractionDensity4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothDiagonalInteraction4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusCompactParametricIntegralC2
open P0EFTJanusProgramPConcreteFullActionFrechetBridge4D
open P0EFTJanusProgramPConcreteFullActionFrechetC2Closure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance localRealNormedAddCommGroup : NormedAddCommGroup Real :=
  inferInstance

local instance localRealNormedSpace : NormedSpace Real Real :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup Real :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module Real Real :=
  localRealNormedSpace.toModule

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev CandidateScalePair :=
  P0EFTJanusGlobalDiagonalInteractionDensity4D.ScalePair

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Smooth outer Candidate-A density -/

private theorem globalDiagonalTwoSectorDensity_contDiffOn
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real ∞
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      ambientPositiveScalePairDomain := by
  have hDirect :=
    coDiagonalInteractionDensity_contDiffOn interactionScale coefficients
  have hExchanged : ContDiffOn Real ∞
      (exchangedDiagonalInteractionDensity interactionScale coefficients)
      ambientPositiveScalePairDomain := by
    rw [ambientPositiveScalePairDomain_isOpen.contDiffOn_iff]
    intro point hPoint
    unfold exchangedDiagonalInteractionDensity
    exact
      (hDirect.contDiffAt
        (ambientPositiveScalePairDomain_isOpen.mem_nhds
          ((scalePairExchange_mem_domain_iff point).2 hPoint))).comp point
        scalePairExchange.contDiff.contDiffAt
  exact hDirect.add hExchanged

private theorem globalDiagonalTwoSectorDensity_contDiffOn_two
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      ambientPositiveScalePairDomain :=
  (globalDiagonalTwoSectorDensity_contDiffOn interactionScale coefficients).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-! ## Exact parameter curve, velocity and acceleration -/

private theorem positiveScaleCurve_uncurry_continuous
    (baseScale direction :
      SmoothQuotientField period hPeriod (Fin 4 → Real)) :
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        positiveScaleCurve period hPeriod baseScale direction
          input.1 input.2) := by
  apply continuous_pi
  intro index
  have hBase :
      Continuous (fun point => baseScale point index) :=
    ((contMDiff_pi_space.mp baseScale.contMDiff_toFun) index).continuous
  have hDirection :
      Continuous (fun point => direction point index) :=
    ((contMDiff_pi_space.mp direction.contMDiff_toFun) index).continuous
  exact (hBase.comp continuous_snd).mul
    (Real.continuous_exp.comp
      (continuous_fst.mul (hDirection.comp continuous_snd)))

private def candidateAScaleCurve
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (input : Real × EffectiveQuotient period hPeriod) :
    CandidateScalePair :=
  (positiveScaleCurve period hPeriod
      (plusScaleField period hPeriod metrics) variation.plusLogDirection
      input.1 input.2,
    positiveScaleCurve period hPeriod
      (minusScaleField period hPeriod metrics) variation.minusLogDirection
      input.1 input.2)

private theorem candidateAScaleCurve_continuous
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    Continuous (candidateAScaleCurve period hPeriod metrics variation) :=
  (positiveScaleCurve_uncurry_continuous period hPeriod
      (plusScaleField period hPeriod metrics) variation.plusLogDirection).prodMk
    (positiveScaleCurve_uncurry_continuous period hPeriod
      (minusScaleField period hPeriod metrics) variation.minusLogDirection)

private theorem candidateAScaleCurve_mem_domain
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (input : Real × EffectiveQuotient period hPeriod) :
    candidateAScaleCurve period hPeriod metrics variation input ∈
      ambientPositiveScalePairDomain :=
  ⟨positiveScaleCurve_pos period hPeriod _ _
      (plusScaleField_pos period hPeriod metrics) input.1 input.2,
    positiveScaleCurve_pos period hPeriod _ _
      (minusScaleField_pos period hPeriod metrics) input.1 input.2⟩

private theorem candidateAScaleCurve_eq
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    candidateAScaleCurve period hPeriod metrics variation (parameter, point) =
      scalePairField period hPeriod
        (metricCurve period hPeriod metrics variation parameter) point :=
  (scalePairField_metricCurve period hPeriod metrics variation parameter point).symm

private def candidateAScaleVelocity
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (input : Real × EffectiveQuotient period hPeriod) :
    CandidateScalePair :=
  (fun index =>
      (candidateAScaleCurve period hPeriod metrics variation input).1 index *
        variation.plusLogDirection input.2 index,
    fun index =>
      (candidateAScaleCurve period hPeriod metrics variation input).2 index *
        variation.minusLogDirection input.2 index)

private def candidateAScaleAcceleration
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (input : Real × EffectiveQuotient period hPeriod) :
    CandidateScalePair :=
  (fun index =>
      (candidateAScaleCurve period hPeriod metrics variation input).1 index *
        variation.plusLogDirection input.2 index ^ 2,
    fun index =>
      (candidateAScaleCurve period hPeriod metrics variation input).2 index *
        variation.minusLogDirection input.2 index ^ 2)

private theorem candidateAScaleVelocity_continuous
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    Continuous (candidateAScaleVelocity period hPeriod metrics variation) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro index
    exact
      ((continuous_apply index).comp
        (candidateAScaleCurve_continuous period hPeriod metrics variation).fst).mul
        (((contMDiff_pi_space.mp
          variation.plusLogDirection.contMDiff_toFun) index).continuous.comp
            continuous_snd)
  · apply continuous_pi
    intro index
    exact
      ((continuous_apply index).comp
        (candidateAScaleCurve_continuous period hPeriod metrics variation).snd).mul
        (((contMDiff_pi_space.mp
          variation.minusLogDirection.contMDiff_toFun) index).continuous.comp
            continuous_snd)

private theorem candidateAScaleAcceleration_continuous
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    Continuous (candidateAScaleAcceleration period hPeriod metrics variation) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro index
    exact
      ((continuous_apply index).comp
        (candidateAScaleCurve_continuous period hPeriod metrics variation).fst).mul
        ((((contMDiff_pi_space.mp
          variation.plusLogDirection.contMDiff_toFun) index).continuous.comp
            continuous_snd).pow 2)
  · apply continuous_pi
    intro index
    exact
      ((continuous_apply index).comp
        (candidateAScaleCurve_continuous period hPeriod metrics variation).snd).mul
        ((((contMDiff_pi_space.mp
          variation.minusLogDirection.contMDiff_toFun) index).continuous.comp
            continuous_snd).pow 2)

private theorem candidateAScaleCurve_hasDerivAt
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        candidateAScaleCurve period hPeriod metrics variation (varied, point))
      (candidateAScaleVelocity period hPeriod metrics variation
        (parameter, point)) parameter := by
  simpa [candidateAScaleCurve, candidateAScaleVelocity] using
    (positiveScaleCurve_hasDerivAt period hPeriod
      (plusScaleField period hPeriod metrics) variation.plusLogDirection
      parameter point).prodMk
      (positiveScaleCurve_hasDerivAt period hPeriod
        (minusScaleField period hPeriod metrics) variation.minusLogDirection
        parameter point)

private theorem candidateAScaleVelocity_hasDerivAt
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        candidateAScaleVelocity period hPeriod metrics variation
          (varied, point))
      (candidateAScaleAcceleration period hPeriod metrics variation
        (parameter, point)) parameter := by
  apply HasDerivAt.prodMk
  · rw [hasDerivAt_pi]
    intro index
    simpa [candidateAScaleVelocity, candidateAScaleAcceleration,
      candidateAScaleCurve, pow_two, mul_assoc] using
      ((positiveScaleCurve_hasDerivAt period hPeriod
        (plusScaleField period hPeriod metrics) variation.plusLogDirection
        parameter point |> hasDerivAt_pi.mp) index).mul_const
          (variation.plusLogDirection point index)
  · rw [hasDerivAt_pi]
    intro index
    simpa [candidateAScaleVelocity, candidateAScaleAcceleration,
      candidateAScaleCurve, pow_two, mul_assoc] using
      ((positiveScaleCurve_hasDerivAt period hPeriod
        (minusScaleField period hPeriod metrics) variation.minusLogDirection
        parameter point |> hasDerivAt_pi.mp) index).mul_const
          (variation.minusLogDirection point index)

/-! ## Exact density derivative chain -/

private def candidateADensityJoint
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  globalDiagonalTwoSectorDensity interactionScale coefficients
    (candidateAScaleCurve period hPeriod metrics variation input)

private def candidateAFirstDerivativeJoint
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  fderiv Real
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      (candidateAScaleCurve period hPeriod metrics variation input)
    (candidateAScaleVelocity period hPeriod metrics variation input)

private def candidateASecondDerivativeJoint
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  fderiv Real
      (fderiv Real
        (globalDiagonalTwoSectorDensity interactionScale coefficients))
      (candidateAScaleCurve period hPeriod metrics variation input)
      (candidateAScaleVelocity period hPeriod metrics variation input)
      (candidateAScaleVelocity period hPeriod metrics variation input) +
    fderiv Real
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      (candidateAScaleCurve period hPeriod metrics variation input)
      (candidateAScaleAcceleration period hPeriod metrics variation input)

private theorem candidateADensityJoint_continuous
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    Continuous
      (candidateADensityJoint period hPeriod interactionScale coefficients
        metrics variation) := by
  exact
    (globalDiagonalTwoSectorDensity_contDiffOn_two interactionScale coefficients)
      |>.continuousOn.comp_continuous
        (candidateAScaleCurve_continuous period hPeriod metrics variation)
        (candidateAScaleCurve_mem_domain period hPeriod metrics variation)

private theorem candidateAFirstDerivativeJoint_continuous
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    Continuous
      (candidateAFirstDerivativeJoint period hPeriod interactionScale
        coefficients metrics variation) := by
  have hOuterFirst : ContDiffOn Real 1
      (fderiv Real
        (globalDiagonalTwoSectorDensity interactionScale coefficients))
      ambientPositiveScalePairDomain :=
    (globalDiagonalTwoSectorDensity_contDiffOn_two interactionScale coefficients)
      |>.fderiv_of_isOpen ambientPositiveScalePairDomain_isOpen (by norm_num)
  have hFirstComposite : Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        fderiv Real
          (globalDiagonalTwoSectorDensity interactionScale coefficients)
          (candidateAScaleCurve period hPeriod metrics variation input)) :=
    hOuterFirst.continuousOn.comp_continuous
      (candidateAScaleCurve_continuous period hPeriod metrics variation)
      (candidateAScaleCurve_mem_domain period hPeriod metrics variation)
  exact hFirstComposite.clm_apply
    (candidateAScaleVelocity_continuous period hPeriod metrics variation)

private theorem candidateASecondDerivativeJoint_continuous
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    Continuous
      (candidateASecondDerivativeJoint period hPeriod interactionScale
        coefficients metrics variation) := by
  have hOuterFirst : ContDiffOn Real 1
      (fderiv Real
        (globalDiagonalTwoSectorDensity interactionScale coefficients))
      ambientPositiveScalePairDomain :=
    (globalDiagonalTwoSectorDensity_contDiffOn_two interactionScale coefficients)
      |>.fderiv_of_isOpen ambientPositiveScalePairDomain_isOpen (by norm_num)
  have hOuterSecond : ContDiffOn Real 0
      (fderiv Real
        (fderiv Real
          (globalDiagonalTwoSectorDensity interactionScale coefficients)))
      ambientPositiveScalePairDomain :=
    hOuterFirst.fderiv_of_isOpen ambientPositiveScalePairDomain_isOpen
      (by norm_num)
  have hFirstComposite : Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        fderiv Real
          (globalDiagonalTwoSectorDensity interactionScale coefficients)
          (candidateAScaleCurve period hPeriod metrics variation input)) :=
    hOuterFirst.continuousOn.comp_continuous
      (candidateAScaleCurve_continuous period hPeriod metrics variation)
      (candidateAScaleCurve_mem_domain period hPeriod metrics variation)
  have hSecondComposite : Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        fderiv Real
          (fderiv Real
            (globalDiagonalTwoSectorDensity interactionScale coefficients))
          (candidateAScaleCurve period hPeriod metrics variation input)) :=
    hOuterSecond.continuousOn.comp_continuous
      (candidateAScaleCurve_continuous period hPeriod metrics variation)
      (candidateAScaleCurve_mem_domain period hPeriod metrics variation)
  exact
    ((hSecondComposite.clm_apply
      (candidateAScaleVelocity_continuous period hPeriod metrics variation))
      |>.clm_apply
        (candidateAScaleVelocity_continuous period hPeriod metrics variation)).add
      (hFirstComposite.clm_apply
        (candidateAScaleAcceleration_continuous period hPeriod metrics variation))

private theorem candidateADensityJoint_hasDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        candidateADensityJoint period hPeriod interactionScale coefficients
          metrics variation (varied, point))
      (candidateAFirstDerivativeJoint period hPeriod interactionScale
        coefficients metrics variation (parameter, point)) parameter := by
  have hOuterAt : ContDiffAt Real 2
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      (candidateAScaleCurve period hPeriod metrics variation
        (parameter, point)) :=
    (globalDiagonalTwoSectorDensity_contDiffOn_two interactionScale coefficients)
      |>.contDiffAt
        (ambientPositiveScalePairDomain_isOpen.mem_nhds
          (candidateAScaleCurve_mem_domain period hPeriod metrics variation
            (parameter, point)))
  have hOuterDerivative : HasFDerivAt
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      (fderiv Real
        (globalDiagonalTwoSectorDensity interactionScale coefficients)
        (candidateAScaleCurve period hPeriod metrics variation
          (parameter, point)))
      (candidateAScaleCurve period hPeriod metrics variation
        (parameter, point)) :=
    (hOuterAt.differentiableAt (by norm_num)).hasFDerivAt
  change HasDerivAt
    (globalDiagonalTwoSectorDensity interactionScale coefficients ∘
      fun varied =>
        candidateAScaleCurve period hPeriod metrics variation (varied, point))
    ((fderiv Real
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      (candidateAScaleCurve period hPeriod metrics variation
        (parameter, point)))
      (candidateAScaleVelocity period hPeriod metrics variation
        (parameter, point))) parameter
  exact hOuterDerivative.comp_hasDerivAt parameter
    (candidateAScaleCurve_hasDerivAt period hPeriod metrics variation
      parameter point)

private theorem candidateAFirstDerivativeJoint_hasDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        candidateAFirstDerivativeJoint period hPeriod interactionScale
          coefficients metrics variation (varied, point))
      (candidateASecondDerivativeJoint period hPeriod interactionScale
        coefficients metrics variation (parameter, point)) parameter := by
  have hOuterAt : ContDiffAt Real 2
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      (candidateAScaleCurve period hPeriod metrics variation
        (parameter, point)) :=
    (globalDiagonalTwoSectorDensity_contDiffOn_two interactionScale coefficients)
      |>.contDiffAt
        (ambientPositiveScalePairDomain_isOpen.mem_nhds
          (candidateAScaleCurve_mem_domain period hPeriod metrics variation
            (parameter, point)))
  have hGradientC1 : ContDiffAt Real 1
      (fderiv Real
        (globalDiagonalTwoSectorDensity interactionScale coefficients))
      (candidateAScaleCurve period hPeriod metrics variation
        (parameter, point)) :=
    hOuterAt.fderiv_right (by norm_num)
  have hGradient : HasFDerivAt
      (fderiv Real
        (globalDiagonalTwoSectorDensity interactionScale coefficients))
      (fderiv Real
        (fderiv Real
          (globalDiagonalTwoSectorDensity interactionScale coefficients))
        (candidateAScaleCurve period hPeriod metrics variation
          (parameter, point)))
      (candidateAScaleCurve period hPeriod metrics variation
        (parameter, point)) :=
    (hGradientC1.differentiableAt (by norm_num)).hasFDerivAt
  have hComposite := hGradient.comp_hasDerivAt parameter
    (candidateAScaleCurve_hasDerivAt period hPeriod metrics variation
      parameter point)
  have hApplied := hComposite.clm_apply
    (candidateAScaleVelocity_hasDerivAt period hPeriod metrics variation
      parameter point)
  simpa [candidateAFirstDerivativeJoint,
    candidateASecondDerivativeJoint] using hApplied

/-- The genuine integrated Candidate-A action on its existing exponential
metric line is globally `C²` for every finite measure on the compact quotient. -/
theorem candidateAActionCurve_contDiff_two
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    ContDiff Real 2
      (candidateAActionCurve period hPeriod measure interactionScale
        coefficients metrics variation) := by
  have hIntegrated := integral_contDiff_two_of_jointContinuous_compact
    (measure := measure)
    (density := fun parameter point =>
      candidateADensityJoint period hPeriod interactionScale coefficients
        metrics variation (parameter, point))
    (firstDerivative := fun parameter point =>
      candidateAFirstDerivativeJoint period hPeriod interactionScale
        coefficients metrics variation (parameter, point))
    (secondDerivative := fun parameter point =>
      candidateASecondDerivativeJoint period hPeriod interactionScale
        coefficients metrics variation (parameter, point))
    (candidateADensityJoint_continuous period hPeriod interactionScale
      coefficients metrics variation)
    (candidateAFirstDerivativeJoint_continuous period hPeriod interactionScale
      coefficients metrics variation)
    (candidateASecondDerivativeJoint_continuous period hPeriod interactionScale
      coefficients metrics variation)
    (fun parameter point =>
      candidateADensityJoint_hasDerivAt period hPeriod interactionScale
        coefficients metrics variation parameter point)
    (fun parameter point =>
      candidateAFirstDerivativeJoint_hasDerivAt period hPeriod interactionScale
        coefficients metrics variation parameter point)
  change ContDiff Real 2 (fun parameter =>
    ∫ point, globalDiagonalTwoSectorDensity interactionScale coefficients
      (scalePairField period hPeriod
        (metricCurve period hPeriod metrics variation parameter) point) ∂measure)
  simpa only [candidateADensityJoint, candidateAScaleCurve_eq] using hIntegrated

end

end P0EFTJanusProgramPConcreteCandidateALineC2Closure4D
end JanusFormal
