import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalInteractionDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D

/-!
# Spatially differentiable Candidate-A density on the smooth D8 quotient

The global fixed-frame diagonal density is evaluated on the two independent
smooth Lorentz magnitude fields living on the actual D8 quotient.  The result
is differentiable in spacetime, its manifold derivative obeys the exact chain
rule through the full two-metric Frechet derivative, and it transforms
covariantly under the analytic PT/exchange involution.

This remains the simultaneously diagonal Lorentz sector and does not assert
full diffeomorphism covariance for arbitrary metric fields.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothDiagonalInteraction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalInteractionDensity4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The two smooth scale fields assembled into the same product input used by
the finite-dimensional Candidate-A density. -/
def scalePairField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    EffectiveQuotient period hPeriod → ScalePair :=
  fun point =>
    (plusScaleField period hPeriod metrics point,
      minusScaleField period hPeriod metrics point)

theorem scalePairField_contMDiff
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(ℝ, ScalePair) ω
      (scalePairField period hPeriod metrics) := by
  exact (plusScaleField period hPeriod metrics).contMDiff_toFun.prodMk_space
    (minusScaleField period hPeriod metrics).contMDiff_toFun

theorem scalePairField_mem_domain
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    scalePairField period hPeriod metrics point ∈
      P0EFTJanusCoDiagonalLorentzRootFirstDerivative.ambientPositiveScalePairDomain := by
  exact ⟨plusScaleField_pos period hPeriod metrics point,
    minusScaleField_pos period hPeriod metrics point⟩

/-- Squaring the co-diagonal scale field recovers exactly the plus Lorentz
metric field already installed on the quotient. -/
theorem ambientPlusMetric_scalePairField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    P0EFTJanusCoDiagonalInteractionDensityFrechet.ambientPlusMetric
        (scalePairField period hPeriod metrics point) =
      plusLorentzMetricField period hPeriod metrics point := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [P0EFTJanusCoDiagonalInteractionDensityFrechet.ambientPlusMetric,
      P0EFTJanusCoDiagonalLorentzRootFirstDerivative.ambientLorentzMetric,
      scalePairField, plusScaleField, positiveSquareRootField,
      plusLorentzMetricField_apply,
      P0EFTJanusGlobalDiagonalLorentzRoot4D.lorentzMetric,
      P0EFTJanusGlobalDiagonalLorentzRoot4D.signature,
      P0EFTJanusCoDiagonalLorentzRootChart.lorentzSign,
      Real.sq_sqrt (le_of_lt (metrics.plus_pos point i))]
  · simp [P0EFTJanusCoDiagonalInteractionDensityFrechet.ambientPlusMetric,
      P0EFTJanusCoDiagonalLorentzRootFirstDerivative.ambientLorentzMetric,
      scalePairField, plusScaleField, positiveSquareRootField,
      plusLorentzMetricField_apply,
      P0EFTJanusGlobalDiagonalLorentzRoot4D.lorentzMetric, hij]

/-- The root used by the interaction density is exactly the smooth principal
root field of the two Lorentz metrics, rather than an independent auxiliary
field. -/
theorem ambientRootMatrix_scalePairField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    P0EFTJanusCoDiagonalLorentzRootFirstDerivative.ambientRootMatrix
        (scalePairField period hPeriod metrics point) =
      principalRootField period hPeriod metrics point := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [P0EFTJanusCoDiagonalLorentzRootFirstDerivative.ambientRootMatrix,
      P0EFTJanusCoDiagonalLorentzRootFirstDerivative.ambientRootRatio,
      scalePairField, plusScaleField, minusScaleField,
      positiveSquareRootField, principalRootField_apply,
      P0EFTJanusGlobalDiagonalLorentzRoot4D.principalRoot,
      P0EFTJanusGlobalDiagonalLorentzRoot4D.principalRootSpectrum,
      P0EFTJanusGlobalDiagonalLorentzRoot4D.relativeRatio,
      coefficientPairAt,
      Real.sqrt_div (le_of_lt (metrics.minus_pos point i))]
  · simp [P0EFTJanusCoDiagonalLorentzRootFirstDerivative.ambientRootMatrix,
      scalePairField, principalRootField_apply,
      P0EFTJanusGlobalDiagonalLorentzRoot4D.principalRoot, hij]

/-- Candidate-A two-sector density on the actual quotient, built from the
same smooth pair at every point. -/
def candidateADensity
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    EffectiveQuotient period hPeriod → ℝ :=
  globalDiagonalTwoSectorDensity interactionScale coefficients ∘
    scalePairField period hPeriod metrics

/-- Spatial differentiability follows from the full two-metric Frechet
derivative on the global positive diagonal domain. -/
theorem candidateADensity_mdifferentiable
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    MDifferentiable coverModelWithCorners 𝓘(ℝ, ℝ)
      (candidateADensity period hPeriod interactionScale coefficients
        metrics) := by
  intro point
  exact
    (globalDiagonalTwoSectorDensity_differentiableAt interactionScale
      coefficients (scalePairField_mem_domain period hPeriod metrics point)).comp_mdifferentiableAt
        ((scalePairField_contMDiff period hPeriod metrics).mdifferentiableAt
          (by simp))

/-- Exact spacetime chain rule: the manifold derivative is the proven full
two-metric density derivative composed with the derivative of the same smooth
metric-pair field. -/
theorem candidateAOuter_fderiv
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    fderiv ℝ (globalDiagonalTwoSectorDensity interactionScale coefficients)
        (scalePairField period hPeriod metrics point) =
      globalDiagonalTwoSectorDensityDerivative interactionScale coefficients
        (scalePairField period hPeriod metrics point) :=
  (globalDiagonalTwoSectorDensity_hasFDerivAt interactionScale coefficients
    (scalePairField_mem_domain period hPeriod metrics point)).fderiv

theorem candidateADensity_mfderiv
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    mfderiv coverModelWithCorners 𝓘(ℝ, ℝ)
        (candidateADensity period hPeriod interactionScale coefficients
          metrics) point =
      (mfderiv 𝓘(ℝ, ScalePair) 𝓘(ℝ, ℝ)
        (globalDiagonalTwoSectorDensity interactionScale coefficients)
        (scalePairField period hPeriod metrics point)).comp
        (mfderiv coverModelWithCorners 𝓘(ℝ, ScalePair)
          (scalePairField period hPeriod metrics) point) := by
  have hOuter := globalDiagonalTwoSectorDensity_hasFDerivAt interactionScale
    coefficients (scalePairField_mem_domain period hPeriod metrics point)
  have hInner := (scalePairField_contMDiff period hPeriod metrics).mdifferentiableAt
    (x := point) (by simp)
  unfold candidateADensity
  exact mfderiv_comp point hOuter.differentiableAt.mdifferentiableAt hInner

/-- Evaluating the PT/exchanged smooth pair equals exchanging the original
pair after evaluating it at the PT-related spacetime point. -/
theorem scalePairField_ptExchange
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    scalePairField period hPeriod (ptExchange period hPeriod metrics) point =
      scalePairExchange
        (scalePairField period hPeriod metrics
          (reflectedSpherePT period hPeriod point)) :=
  rfl

/-- Exact PT covariance of the spatial Candidate-A density. -/
theorem candidateADensity_ptExchange
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    candidateADensity period hPeriod interactionScale coefficients
        (ptExchange period hPeriod metrics) point =
      candidateADensity period hPeriod interactionScale coefficients metrics
        (reflectedSpherePT period hPeriod point) := by
  rw [candidateADensity, Function.comp_apply, scalePairField_ptExchange,
    globalDiagonalTwoSectorDensity_exchange]
  rfl

/-- A PT-fixed smooth metric pair gives a pointwise PT-invariant density. -/
theorem candidateADensity_pt_invariant_of_fixed
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (hFixed : ptExchange period hPeriod metrics = metrics)
    (point : EffectiveQuotient period hPeriod) :
    candidateADensity period hPeriod interactionScale coefficients metrics
        (reflectedSpherePT period hPeriod point) =
      candidateADensity period hPeriod interactionScale coefficients metrics
        point := by
  rw [← candidateADensity_ptExchange period hPeriod interactionScale
    coefficients metrics point, hFixed]

section IntegratedDensity

open MeasureTheory

variable [MeasurableSpace (EffectiveQuotient period hPeriod)]
  [BorelSpace (EffectiveQuotient period hPeriod)]

/-- Analytic PT viewed as a measurable equivalence for the Borel structure of
the same smooth quotient. -/
def ptMeasurableEquiv :
    EffectiveQuotient period hPeriod ≃ᵐ
      EffectiveQuotient period hPeriod :=
  (reflectedSpherePTDiffeomorph period hPeriod).toHomeomorph.toMeasurableEquiv

@[simp]
theorem ptMeasurableEquiv_apply
    (point : EffectiveQuotient period hPeriod) :
    ptMeasurableEquiv period hPeriod point =
      reflectedSpherePT period hPeriod point :=
  rfl

/-- Integrated smooth diagonal Candidate-A density for any supplied Borel
measure on the effective quotient. -/
def candidateAAction
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : ℝ :=
  ∫ point, candidateADensity period hPeriod interactionScale coefficients
    metrics point ∂measure

/-- A PT-invariant measure makes the genuine smooth-field action exactly
invariant under sector exchange. -/
theorem candidateAAction_ptExchange
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hPT : MeasurePreserving (ptMeasurableEquiv period hPeriod)
      measure measure) :
    candidateAAction period hPeriod interactionScale coefficients
        (ptExchange period hPeriod metrics) measure =
      candidateAAction period hPeriod interactionScale coefficients
        metrics measure := by
  rw [candidateAAction, candidateAAction]
  calc
    (∫ point, candidateADensity period hPeriod interactionScale coefficients
        (ptExchange period hPeriod metrics) point ∂measure) =
        ∫ point, candidateADensity period hPeriod interactionScale coefficients
          metrics (ptMeasurableEquiv period hPeriod point) ∂measure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point =>
        candidateADensity_ptExchange period hPeriod interactionScale
          coefficients metrics point
    _ = ∫ point, candidateADensity period hPeriod interactionScale coefficients
          metrics point ∂measure :=
      hPT.integral_comp'
        (candidateADensity period hPeriod interactionScale coefficients metrics)

end IntegratedDensity

end

end P0EFTJanusMappingTorusSmoothDiagonalInteraction4D
end JanusFormal
