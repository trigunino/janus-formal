import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateAFunctionalVariation4D

/-!
# Integrated Candidate-A metric-scale Hessian

This gate differentiates the first variation of the same global Candidate-A
density in a second fixed-frame diagonal metric-scale direction.  The full
eight-component positive scale domain and the second-variation domination
hypotheses are explicit.  No Einstein--Hilbert, Maxwell, ghost, or boundary
term is included.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateAIntegratedMetricHessian4D

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothDiagonalInteraction4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusGlobalDiagonalInteractionDensity4D
open P0EFTJanusCoDiagonalLorentzRootFirstDerivative
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

/-- The genuine scale-chart tangent induced by a logarithmic metric
variation at the base metric. -/
def candidateAMetricScaleDirection
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    P0EFTJanusGlobalDiagonalInteractionDensity4D.ScalePair :=
  scaleVelocityAt period hPeriod metrics variation 0 point

/-- Affine curve in the full eight-component metric-scale chart. -/
def candidateAMetricScaleCurve
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    P0EFTJanusGlobalDiagonalInteractionDensity4D.ScalePair :=
  scalePairField period hPeriod metrics point +
    parameter • candidateAMetricScaleDirection period hPeriod metrics variation point

@[simp]
theorem candidateAMetricScaleCurve_zero
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    candidateAMetricScaleCurve period hPeriod metrics variation 0 point =
      scalePairField period hPeriod metrics point := by
  simp [candidateAMetricScaleCurve]

theorem candidateAMetricScaleCurve_hasDerivAt
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied => candidateAMetricScaleCurve period hPeriod metrics variation
        varied point)
      (candidateAMetricScaleDirection period hPeriod metrics variation point)
      parameter := by
  simpa [candidateAMetricScaleCurve, add_comm] using
    ((hasDerivAt_id (x := parameter)).smul_const
      (candidateAMetricScaleDirection period hPeriod metrics variation point)).add_const
        (scalePairField period hPeriod metrics point)

/-- Visible analytic hypothesis: the same global Candidate-A density is C2 on
the explicit open positive scale domain. -/
structure CandidateAGlobalDensityC2Contract
    (interactionScale : Real) (coefficients : PotentialCoefficients) : Prop where
  density_contDiffOn : ContDiffOn Real 2
    (globalDiagonalTwoSectorDensity interactionScale coefficients)
    ambientPositiveScalePairDomain

/-- The actual second Frechet derivative of the same eight-component density,
evaluated on two metric-scale directions. -/
def candidateAMetricHessianDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  fderiv Real
      (fderiv Real (globalDiagonalTwoSectorDensity interactionScale coefficients))
      (scalePairField period hPeriod metrics point)
      (candidateAMetricScaleDirection period hPeriod metrics second point)
      (candidateAMetricScaleDirection period hPeriod metrics first point)

/-- Symmetry follows from C2 regularity of the same density. -/
theorem candidateAMetricHessianDensity_symmetric
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (contract : CandidateAGlobalDensityC2Contract interactionScale coefficients)
    (point : EffectiveQuotient period hPeriod) :
    candidateAMetricHessianDensity period hPeriod interactionScale coefficients
        metrics first second point =
      candidateAMetricHessianDensity period hPeriod interactionScale coefficients
        metrics second first point := by
  have hPoint := scalePairField_mem_domain period hPeriod metrics point
  have hC2 := contract.density_contDiffOn.contDiffAt
    (ambientPositiveScalePairDomain_isOpen.mem_nhds hPoint)
  exact (hC2.isSymmSndFDerivAt (by simp)).eq
    (candidateAMetricScaleDirection period hPeriod metrics second point)
    (candidateAMetricScaleDirection period hPeriod metrics first point)

/-- First variation in the first direction, evaluated along the affine scale
curve generated by the second direction. -/
def candidateAFirstVariationAlongSecond
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  fderiv Real (globalDiagonalTwoSectorDensity interactionScale coefficients)
      (candidateAMetricScaleCurve period hPeriod metrics second parameter point)
    (candidateAMetricScaleDirection period hPeriod metrics first point)

theorem candidateAFirstVariationAlongSecond_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    candidateAFirstVariationAlongSecond period hPeriod interactionScale coefficients
        metrics first second 0 point =
      pointwiseCandidateAFirstVariation period hPeriod interactionScale
        coefficients metrics first point := by
  rw [candidateAFirstVariationAlongSecond, candidateAMetricScaleCurve_zero]
  rw [(globalDiagonalTwoSectorDensity_hasFDerivAt interactionScale coefficients
    (scalePairField_mem_domain period hPeriod metrics point)).fderiv]
  simp [pointwiseCandidateAFirstVariation,
    pointwiseCandidateAFirstVariationAt, candidateAMetricScaleDirection]

/-- Pointwise second derivative of the first variation, with no derivative
identity included in the assumptions. -/
theorem candidateAFirstVariationAlongSecond_hasDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (contract : CandidateAGlobalDensityC2Contract interactionScale coefficients)
    (parameter : Real) (point : EffectiveQuotient period hPeriod)
    (hCurve : candidateAMetricScaleCurve period hPeriod metrics second parameter
      point ∈ ambientPositiveScalePairDomain) :
    HasDerivAt
      (fun varied => candidateAFirstVariationAlongSecond period hPeriod
        interactionScale coefficients metrics first second varied point)
      (fderiv Real
          (fderiv Real
            (globalDiagonalTwoSectorDensity interactionScale coefficients))
          (candidateAMetricScaleCurve period hPeriod metrics second parameter point)
          (candidateAMetricScaleDirection period hPeriod metrics second point)
          (candidateAMetricScaleDirection period hPeriod metrics first point))
      parameter := by
  have hC2 := contract.density_contDiffOn.contDiffAt
    (ambientPositiveScalePairDomain_isOpen.mem_nhds hCurve)
  have hGradientC1 : ContDiffAt Real 1
      (fderiv Real
        (globalDiagonalTwoSectorDensity interactionScale coefficients))
      (candidateAMetricScaleCurve period hPeriod metrics second parameter point) :=
    hC2.fderiv_right (by norm_num)
  have hGradient : HasFDerivAt
      (fderiv Real
        (globalDiagonalTwoSectorDensity interactionScale coefficients))
      (fderiv Real
        (fderiv Real
          (globalDiagonalTwoSectorDensity interactionScale coefficients))
        (candidateAMetricScaleCurve period hPeriod metrics second parameter point))
      (candidateAMetricScaleCurve period hPeriod metrics second parameter point) :=
    (hGradientC1.differentiableAt (by norm_num)).hasFDerivAt
  have hComposite := hGradient.comp_hasDerivAt parameter
    (candidateAMetricScaleCurve_hasDerivAt period hPeriod metrics second parameter point)
  have hApplied := hComposite.clm_apply
    (hasDerivAt_const (x := parameter)
      (candidateAMetricScaleDirection period hPeriod metrics first point))
  simpa [candidateAFirstVariationAlongSecond] using hApplied

section Integrated

variable [MeasurableSpace (EffectiveQuotient period hPeriod)]

/-- Integral of the actual Candidate-A metric Hessian density. -/
def integratedCandidateAMetricHessian
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod) : Real :=
  ∫ point, candidateAMetricHessianDensity period hPeriod interactionScale
    coefficients metrics first second point ∂measure

/-- Explicit open-domain and domination contract for differentiating the
integrated first variation a second time. -/
structure DominatedCandidateASecondVariationContract
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod) extends
    CandidateAGlobalDensityC2Contract interactionScale coefficients where
  parameterDomain : Set Real
  parameterDomain_mem_nhds : parameterDomain ∈ 𝓝 (0 : Real)
  curve_mem_domain : ∀ point parameter, parameter ∈ parameterDomain →
    candidateAMetricScaleCurve period hPeriod metrics second parameter point ∈
      ambientPositiveScalePairDomain
  firstVariation_aeStronglyMeasurable : ∀ᶠ parameter in 𝓝 (0 : Real),
    AEStronglyMeasurable
      (candidateAFirstVariationAlongSecond period hPeriod interactionScale
        coefficients metrics first second parameter) measure
  firstVariation_integrable_at_zero : Integrable
    (candidateAFirstVariationAlongSecond period hPeriod interactionScale
      coefficients metrics first second 0) measure
  hessian_aeStronglyMeasurable : AEStronglyMeasurable
    (candidateAMetricHessianDensity period hPeriod interactionScale coefficients
      metrics first second) measure
  bound : EffectiveQuotient period hPeriod → Real
  hessian_norm_le : ∀ᵐ point ∂measure, ∀ parameter ∈ parameterDomain,
    ‖fderiv Real
        (fderiv Real
          (globalDiagonalTwoSectorDensity interactionScale coefficients))
        (candidateAMetricScaleCurve period hPeriod metrics second parameter point)
        (candidateAMetricScaleDirection period hPeriod metrics second point)
        (candidateAMetricScaleDirection period hPeriod metrics first point)‖ ≤
      bound point
  bound_integrable : Integrable bound measure

/-- Integrated curve of first variations in the fixed first direction. -/
def integratedCandidateAFirstVariationAlongSecond
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) : Real :=
  ∫ point, candidateAFirstVariationAlongSecond period hPeriod interactionScale
    coefficients metrics first second parameter point ∂measure

@[simp]
theorem integratedCandidateAFirstVariationAlongSecond_zero
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod) :
    integratedCandidateAFirstVariationAlongSecond period hPeriod measure
        interactionScale coefficients metrics first second 0 =
      integratedCandidateAFirstVariation period hPeriod measure interactionScale
        coefficients metrics first := by
  unfold integratedCandidateAFirstVariationAlongSecond
    integratedCandidateAFirstVariation
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    candidateAFirstVariationAlongSecond_zero period hPeriod interactionScale
      coefficients metrics first second point

/-- The integrated first variation differentiates to the actual Hessian of
the same Candidate-A interaction. -/
theorem integratedCandidateAFirstVariationAlongSecond_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (contract : DominatedCandidateASecondVariationContract period hPeriod measure
      interactionScale coefficients metrics first second) :
    HasDerivAt
      (integratedCandidateAFirstVariationAlongSecond period hPeriod measure
        interactionScale coefficients metrics first second)
      (integratedCandidateAMetricHessian period hPeriod measure interactionScale
        coefficients metrics first second) 0 := by
  have hPointwise : ∀ᵐ point ∂measure, ∀ parameter ∈ contract.parameterDomain,
      HasDerivAt
        (fun varied => candidateAFirstVariationAlongSecond period hPeriod
          interactionScale coefficients metrics first second varied point)
        (fderiv Real
          (fderiv Real
            (globalDiagonalTwoSectorDensity interactionScale coefficients))
          (candidateAMetricScaleCurve period hPeriod metrics second parameter point)
          (candidateAMetricScaleDirection period hPeriod metrics second point)
          (candidateAMetricScaleDirection period hPeriod metrics first point))
        parameter :=
    Filter.Eventually.of_forall fun point parameter hParameter =>
      candidateAFirstVariationAlongSecond_hasDerivAt period hPeriod
        interactionScale coefficients metrics first second contract.toCandidateAGlobalDensityC2Contract
        parameter point (contract.curve_mem_domain point parameter hParameter)
  have hHessianMeasurable := contract.hessian_aeStronglyMeasurable
  change AEStronglyMeasurable
    (fun point =>
      fderiv Real
        (fderiv Real
          (globalDiagonalTwoSectorDensity interactionScale coefficients))
        (scalePairField period hPeriod metrics point)
        (candidateAMetricScaleDirection period hPeriod metrics second point)
        (candidateAMetricScaleDirection period hPeriod metrics first point)) measure at hHessianMeasurable
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := candidateAFirstVariationAlongSecond period hPeriod interactionScale
      coefficients metrics first second)
    (F' := fun parameter point =>
      fderiv Real
        (fderiv Real
          (globalDiagonalTwoSectorDensity interactionScale coefficients))
        (candidateAMetricScaleCurve period hPeriod metrics second parameter point)
        (candidateAMetricScaleDirection period hPeriod metrics second point)
        (candidateAMetricScaleDirection period hPeriod metrics first point))
    (bound := contract.bound) contract.parameterDomain_mem_nhds
    contract.firstVariation_aeStronglyMeasurable
    contract.firstVariation_integrable_at_zero
    (by simpa only [candidateAMetricScaleCurve_zero] using hHessianMeasurable)
    contract.hessian_norm_le
    contract.bound_integrable hPointwise
  unfold integratedCandidateAFirstVariationAlongSecond
    integratedCandidateAMetricHessian candidateAMetricHessianDensity
  simpa [candidateAMetricScaleCurve_zero] using hIntegral.2

/-- The integrated Hessian is symmetric under the displayed C2 and
integrability hypotheses. -/
theorem integratedCandidateAMetricHessian_symmetric
    (measure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (contract : CandidateAGlobalDensityC2Contract interactionScale coefficients) :
    integratedCandidateAMetricHessian period hPeriod measure interactionScale
        coefficients metrics first second =
      integratedCandidateAMetricHessian period hPeriod measure interactionScale
        coefficients metrics second first := by
  unfold integratedCandidateAMetricHessian
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    candidateAMetricHessianDensity_symmetric period hPeriod interactionScale
      coefficients metrics first second contract point

end Integrated

end

end P0EFTJanusMappingTorusCandidateAIntegratedMetricHessian4D
end JanusFormal
