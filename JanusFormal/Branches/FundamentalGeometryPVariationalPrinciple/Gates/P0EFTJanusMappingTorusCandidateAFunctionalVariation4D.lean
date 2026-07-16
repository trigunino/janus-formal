import Mathlib.Analysis.Calculus.ParametricIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiagonalInteraction4D

/-!
# Functional variation of Candidate A on the smooth D8 quotient

This gate varies the same smooth positive diagonal Lorentz fields consumed by
the global Candidate-A density.  Arbitrary smooth logarithmic scale directions
generate exponential curves which remain in the positive cone for every real
parameter.  The exact finite-dimensional Frechet derivative therefore gives
the pointwise field variation without an independently supplied root or metric.

Under an explicit measurability and domination contract, the same pointwise
variation differentiates the integrated Candidate-A action.  The result is
restricted to the fixed-frame simultaneously diagonal sector.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateAFunctionalVariation4D

set_option autoImplicit false

noncomputable section

open Filter
open scoped Manifold ContDiff Matrix.Norms.Frobenius Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothDiagonalInteraction4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalInteractionDensity4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Two arbitrary smooth logarithmic scale directions for the two independent
metric sectors. -/
structure SmoothDiagonalMetricVariation where
  plusLogDirection : SmoothQuotientField period hPeriod Coefficients4
  minusLogDirection : SmoothQuotientField period hPeriod Coefficients4

/-- Exponential variation of one already-positive smooth scale field. -/
def positiveScaleCurve
    (baseScale direction : SmoothQuotientField period hPeriod Coefficients4)
    (parameter : Real) : SmoothQuotientField period hPeriod Coefficients4 where
  toFun := fun point i =>
    baseScale point i * Real.exp (parameter * direction point i)
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro i
    have hBase := (contMDiff_pi_space.mp baseScale.contMDiff_toFun) i
    have hDirection := (contMDiff_pi_space.mp direction.contMDiff_toFun) i
    exact hBase.mul
      (Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hDirection))

theorem positiveScaleCurve_pos
    (baseScale direction : SmoothQuotientField period hPeriod Coefficients4)
    (hBase : ∀ point i, 0 < baseScale point i)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) (i : Fin 4) :
    0 < positiveScaleCurve period hPeriod baseScale direction parameter point i :=
  mul_pos (hBase point i) (Real.exp_pos _)

/-- The metric magnitude induced by a scale is its square. -/
def squaredMagnitudeField
    (scale : SmoothQuotientField period hPeriod Coefficients4) :
    SmoothQuotientField period hPeriod Coefficients4 where
  toFun := fun point i => (scale point i) ^ 2
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro i
    exact ((contMDiff_pi_space.mp scale.contMDiff_toFun) i).pow 2

/-- Global exponential metric curve through the supplied positive diagonal
pair.  Positivity is automatic for every real parameter. -/
def metricCurve
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) : SmoothPositiveDiagonalMetricPair period hPeriod where
  plusMagnitude := squaredMagnitudeField period hPeriod
    (positiveScaleCurve period hPeriod
      (plusScaleField period hPeriod metrics) variation.plusLogDirection
      parameter)
  minusMagnitude := squaredMagnitudeField period hPeriod
    (positiveScaleCurve period hPeriod
      (minusScaleField period hPeriod metrics) variation.minusLogDirection
      parameter)
  plus_pos := fun point i => pow_pos
    (positiveScaleCurve_pos period hPeriod _ _
      (plusScaleField_pos period hPeriod metrics) parameter point i) 2
  minus_pos := fun point i => pow_pos
    (positiveScaleCurve_pos period hPeriod _ _
      (minusScaleField_pos period hPeriod metrics) parameter point i) 2

/-- The scale field recovered by Candidate A from the varied metric is exactly
the exponential scale curve used to define it. -/
theorem scalePairField_metricCurve
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    scalePairField period hPeriod
        (metricCurve period hPeriod metrics variation parameter) point =
      (positiveScaleCurve period hPeriod
          (plusScaleField period hPeriod metrics) variation.plusLogDirection
          parameter point,
        positiveScaleCurve period hPeriod
          (minusScaleField period hPeriod metrics) variation.minusLogDirection
          parameter point) := by
  apply Prod.ext
  · funext i
    change Real.sqrt
        ((positiveScaleCurve period hPeriod
          (plusScaleField period hPeriod metrics) variation.plusLogDirection
          parameter point i) ^ 2) = _
    rw [Real.sqrt_sq_eq_abs, abs_of_pos]
    exact positiveScaleCurve_pos period hPeriod _ _
      (plusScaleField_pos period hPeriod metrics) parameter point i
  · funext i
    change Real.sqrt
        ((positiveScaleCurve period hPeriod
          (minusScaleField period hPeriod metrics) variation.minusLogDirection
          parameter point i) ^ 2) = _
    rw [Real.sqrt_sq_eq_abs, abs_of_pos]
    exact positiveScaleCurve_pos period hPeriod _ _
      (minusScaleField_pos period hPeriod metrics) parameter point i

@[simp]
theorem metricCurve_zero
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    metricCurve period hPeriod metrics variation 0 = metrics := by
  apply SmoothPositiveDiagonalMetricPair.ext
  · apply SmoothQuotientField.ext period hPeriod Coefficients4
    intro point
    funext i
    change
      (Real.sqrt (metrics.plusMagnitude point i) *
        Real.exp (0 * variation.plusLogDirection point i)) ^ 2 =
          metrics.plusMagnitude point i
    simpa using Real.sq_sqrt (le_of_lt (metrics.plus_pos point i))
  · apply SmoothQuotientField.ext period hPeriod Coefficients4
    intro point
    funext i
    change
      (Real.sqrt (metrics.minusMagnitude point i) *
        Real.exp (0 * variation.minusLogDirection point i)) ^ 2 =
          metrics.minusMagnitude point i
    simpa using Real.sq_sqrt (le_of_lt (metrics.minus_pos point i))

/-- Exact velocity of the two scale fields at an arbitrary parameter. -/
def scaleVelocityAt
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : ScalePair :=
  (fun i =>
      positiveScaleCurve period hPeriod
          (plusScaleField period hPeriod metrics) variation.plusLogDirection
          parameter point i * variation.plusLogDirection point i,
    fun i =>
      positiveScaleCurve period hPeriod
          (minusScaleField period hPeriod metrics) variation.minusLogDirection
          parameter point i * variation.minusLogDirection point i)

theorem positiveScaleCurve_hasDerivAt
    (baseScale direction : SmoothQuotientField period hPeriod Coefficients4)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied => positiveScaleCurve period hPeriod baseScale direction
        varied point)
      (fun i => positiveScaleCurve period hPeriod baseScale direction
        parameter point i * direction point i) parameter := by
  rw [hasDerivAt_pi]
  intro i
  have hExponential :=
    ((hasDerivAt_id (x := parameter)).mul_const (direction point i)).exp
  simpa [positiveScaleCurve, mul_assoc] using
    hExponential.const_mul (baseScale point i)

/-- The varied scale pair has exactly the displayed velocity. -/
theorem scalePairCurve_hasDerivAt
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied => scalePairField period hPeriod
        (metricCurve period hPeriod metrics variation varied) point)
      (scaleVelocityAt period hPeriod metrics variation parameter point)
      parameter := by
  have hPlus := positiveScaleCurve_hasDerivAt period hPeriod
    (plusScaleField period hPeriod metrics) variation.plusLogDirection
    parameter point
  have hMinus := positiveScaleCurve_hasDerivAt period hPeriod
    (minusScaleField period hPeriod metrics) variation.minusLogDirection
    parameter point
  rw [show
    (fun varied => scalePairField period hPeriod
      (metricCurve period hPeriod metrics variation varied) point) =
      (fun varied =>
        (positiveScaleCurve period hPeriod
            (plusScaleField period hPeriod metrics)
            variation.plusLogDirection varied point,
          positiveScaleCurve period hPeriod
            (minusScaleField period hPeriod metrics)
            variation.minusLogDirection varied point)) from
      funext fun varied =>
        scalePairField_metricCurve period hPeriod metrics variation varied point]
  simpa [scaleVelocityAt] using hPlus.prodMk hMinus

/-- Exact Candidate-A first-variation density at an arbitrary point of the
metric curve. -/
def pointwiseCandidateAFirstVariationAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  globalDiagonalTwoSectorDensityDerivative interactionScale coefficients
    (scalePairField period hPeriod
      (metricCurve period hPeriod metrics variation parameter) point)
    (scaleVelocityAt period hPeriod metrics variation parameter point)

/-- Exact first-variation density at the original global metric pair. -/
def pointwiseCandidateAFirstVariation
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  pointwiseCandidateAFirstVariationAt period hPeriod interactionScale
    coefficients metrics variation 0 point

/-- Candidate-A density evaluated on the genuine global metric curve. -/
def candidateADensityCurve
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  candidateADensity period hPeriod interactionScale coefficients
    (metricCurve period hPeriod metrics variation parameter) point

@[simp]
theorem candidateADensityCurve_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    candidateADensityCurve period hPeriod interactionScale coefficients metrics
        variation 0 point =
      candidateADensity period hPeriod interactionScale coefficients metrics
        point := by
  simp [candidateADensityCurve]

/-- Exact pointwise functional derivative at every parameter; the outer
Frechet derivative and inner scale velocity refer to the same metric curve. -/
theorem candidateADensityCurve_hasDerivAt_at
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied => candidateADensityCurve period hPeriod interactionScale
        coefficients metrics variation varied point)
      (pointwiseCandidateAFirstVariationAt period hPeriod interactionScale
        coefficients metrics variation parameter point) parameter := by
  have hOuter := globalDiagonalTwoSectorDensity_hasFDerivAt interactionScale
    coefficients (scalePairField_mem_domain period hPeriod
      (metricCurve period hPeriod metrics variation parameter) point)
  have hComposite := hOuter.comp_hasDerivAt parameter
    (scalePairCurve_hasDerivAt period hPeriod metrics variation parameter point)
  simpa [candidateADensityCurve, candidateADensity, Function.comp_def,
    pointwiseCandidateAFirstVariationAt] using hComposite

/-- Exact pointwise functional derivative at the original pair. -/
theorem candidateADensityCurve_hasDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied => candidateADensityCurve period hPeriod interactionScale
        coefficients metrics variation varied point)
      (pointwiseCandidateAFirstVariation period hPeriod interactionScale
        coefficients metrics variation point) 0 := by
  exact candidateADensityCurve_hasDerivAt_at period hPeriod interactionScale
    coefficients metrics variation 0 point

section IntegratedVariation

open MeasureTheory

variable [MeasurableSpace (EffectiveQuotient period hPeriod)]

/-- The integrated Candidate-A action along the same global metric curve. -/
def candidateAActionCurve
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) : Real :=
  candidateAAction period hPeriod interactionScale coefficients
    (metricCurve period hPeriod metrics variation parameter) measure

/-- Integral of the exact pointwise Candidate-A first variation. -/
def integratedCandidateAFirstVariation
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) : Real :=
  ∫ point, pointwiseCandidateAFirstVariation period hPeriod interactionScale
    coefficients metrics variation point ∂measure

@[simp]
theorem candidateAActionCurve_zero
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) :
    candidateAActionCurve period hPeriod measure interactionScale coefficients
        metrics variation 0 =
      candidateAAction period hPeriod interactionScale coefficients metrics
        measure := by
  simp [candidateAActionCurve]

/-- Explicit analytic contract for differentiating the genuine global action.
The metric curve itself needs no domain hypothesis because it stays positive
for every parameter. -/
structure DominatedCandidateAVariationContract
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod) where
  parameterDomain : Set Real
  parameterDomain_mem_nhds : parameterDomain ∈ 𝓝 (0 : Real)
  density_aeStronglyMeasurable : ∀ᶠ parameter in 𝓝 (0 : Real),
    AEStronglyMeasurable
      (candidateADensityCurve period hPeriod interactionScale coefficients
        metrics variation parameter) measure
  density_integrable_at_zero : Integrable
    (candidateADensityCurve period hPeriod interactionScale coefficients
      metrics variation 0) measure
  derivative_aeStronglyMeasurable : AEStronglyMeasurable
    (pointwiseCandidateAFirstVariationAt period hPeriod interactionScale
      coefficients metrics variation 0) measure
  bound : EffectiveQuotient period hPeriod → Real
  derivative_norm_le : ∀ᵐ point ∂measure, ∀ parameter ∈ parameterDomain,
    ‖pointwiseCandidateAFirstVariationAt period hPeriod interactionScale
      coefficients metrics variation parameter point‖ ≤ bound point
  bound_integrable : Integrable bound measure

/-- Under the displayed contract, the exact pointwise variation is integrable
and is the derivative of the integrated Candidate-A action. -/
theorem candidateAActionCurve_integrable_and_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (contract : DominatedCandidateAVariationContract period hPeriod measure
      interactionScale coefficients metrics variation) :
    Integrable
        (pointwiseCandidateAFirstVariation period hPeriod interactionScale
          coefficients metrics variation) measure ∧
      HasDerivAt
        (candidateAActionCurve period hPeriod measure interactionScale
          coefficients metrics variation)
        (integratedCandidateAFirstVariation period hPeriod measure
          interactionScale coefficients metrics variation) 0 := by
  have hPointwise : ∀ᵐ point ∂measure,
      ∀ parameter ∈ contract.parameterDomain,
        HasDerivAt
          (fun varied => candidateADensityCurve period hPeriod interactionScale
            coefficients metrics variation varied point)
          (pointwiseCandidateAFirstVariationAt period hPeriod interactionScale
            coefficients metrics variation parameter point) parameter :=
    Filter.Eventually.of_forall fun point parameter _ =>
      candidateADensityCurve_hasDerivAt_at period hPeriod interactionScale
        coefficients metrics variation parameter point
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun parameter point => candidateADensityCurve period hPeriod
      interactionScale coefficients metrics variation parameter point)
    (F' := fun parameter point => pointwiseCandidateAFirstVariationAt period
      hPeriod interactionScale coefficients metrics variation parameter point)
    (bound := contract.bound) contract.parameterDomain_mem_nhds
    contract.density_aeStronglyMeasurable
    contract.density_integrable_at_zero
    contract.derivative_aeStronglyMeasurable contract.derivative_norm_le
    contract.bound_integrable hPointwise
  constructor
  · exact hIntegral.1
  · unfold candidateAActionCurve candidateAAction
      integratedCandidateAFirstVariation pointwiseCandidateAFirstVariation
    exact hIntegral.2

/-- Derivative-under-the-integral projection of the stronger result. -/
theorem candidateAActionCurve_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (contract : DominatedCandidateAVariationContract period hPeriod measure
      interactionScale coefficients metrics variation) :
    HasDerivAt
      (candidateAActionCurve period hPeriod measure interactionScale
        coefficients metrics variation)
      (integratedCandidateAFirstVariation period hPeriod measure interactionScale
        coefficients metrics variation) 0 :=
  (candidateAActionCurve_integrable_and_hasDerivAt period hPeriod measure
    interactionScale coefficients metrics variation contract).2

end IntegratedVariation

end

end P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
end JanusFormal
