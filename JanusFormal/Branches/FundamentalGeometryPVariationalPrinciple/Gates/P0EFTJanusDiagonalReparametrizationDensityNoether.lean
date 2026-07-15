import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoDiagonalInteractionDensityFrechet

/-!
# One-dimensional diagonal reparametrization of the Candidate-A density

The co-diagonal Candidate-A interaction density is pulled back along an actual
differentiable curve in the positive scale-pair chart.  For a differentiable
common generator `xi`, its one-dimensional density variation is derived by
the product rule:

`delta rho = xi * rho' + xi' * rho = (xi * rho)'`.

An oriented endpoint ledger then cancels the corresponding primitive
difference exactly.  This is a real one-dimensional curve calculation.  It
does not construct a spacetime diffeomorphism, a four-dimensional integral,
or a covariant Bianchi identity.
-/

namespace JanusFormal
namespace P0EFTJanusDiagonalReparametrizationDensityNoether

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusCoDiagonalLorentzRootFirstDerivative
open P0EFTJanusCoDiagonalInteractionDensityFrechet

abbrev ScalePair :=
  P0EFTJanusCoDiagonalInteractionDensityFrechet.ScalePair

/-- Candidate-A data along one differentiable real curve in the positive
co-diagonal scale-pair chart. -/
structure CandidateDensityCurve where
  interactionScale : ℝ
  coefficients : PotentialCoefficients
  scaleCurve : ℝ → ScalePair
  scaleVelocity : ℝ → ScalePair
  scaleCurve_mem : ∀ parameter,
    scaleCurve parameter ∈ ambientPositiveScalePairDomain
  scaleCurve_hasDerivAt : ∀ parameter,
    HasDerivAt scaleCurve (scaleVelocity parameter) parameter

/-- The committed co-diagonal Candidate-A density pulled back to the real
parameter curve. -/
def candidateDensity
    (data : CandidateDensityCurve) (parameter : ℝ) : ℝ :=
  coDiagonalInteractionDensity data.interactionScale data.coefficients
    (data.scaleCurve parameter)

/-- The actual chart covector applied to the actual curve velocity. -/
def candidateDensityDerivative
    (data : CandidateDensityCurve) (parameter : ℝ) : ℝ :=
  coDiagonalInteractionDensityDerivative data.interactionScale
    data.coefficients (data.scaleCurve parameter)
      (data.scaleVelocity parameter)

/-- Pulling the proved Frechet derivative back along the supplied genuine
curve gives the displayed real derivative; no density derivative is supplied
as an independent hypothesis. -/
theorem candidateDensity_hasDerivAt
    (data : CandidateDensityCurve) (parameter : ℝ) :
    HasDerivAt (candidateDensity data)
      (candidateDensityDerivative data parameter) parameter := by
  exact
    (coDiagonalInteractionDensity_hasFDerivAt data.interactionScale
      data.coefficients (data.scaleCurve parameter)
      (data.scaleCurve_mem parameter)).comp_hasDerivAt parameter
        (data.scaleCurve_hasDerivAt parameter)

/-- A differentiable common one-dimensional reparametrization generator. -/
structure DiagonalReparametrization where
  generator : ℝ → ℝ
  generatorDerivative : ℝ → ℝ
  generator_hasDerivAt : ∀ parameter,
    HasDerivAt generator (generatorDerivative parameter) parameter

/-- Infinitesimal transformation law for a weight-one density:
`delta rho = xi rho' + xi' rho`. -/
def diagonalDensityVariation
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (parameter : ℝ) : ℝ :=
  reparametrization.generator parameter *
      candidateDensityDerivative data parameter +
    reparametrization.generatorDerivative parameter *
      candidateDensity data parameter

/-- Actual affine first jet of the common parameter pullback
`phi_epsilon(parameter)`. -/
def affineParameterPullback
    (reparametrization : DiagonalReparametrization)
    (parameter epsilon : ℝ) : ℝ :=
  parameter + epsilon * reparametrization.generator parameter

/-- Actual affine first jet of the corresponding weight-one Jacobian. -/
def affineJacobianPullback
    (reparametrization : DiagonalReparametrization)
    (parameter epsilon : ℝ) : ℝ :=
  1 + epsilon * reparametrization.generatorDerivative parameter

/-- The displayed Jacobian is the actual parameter derivative of the affine
pullback, not an independent weight curve. -/
theorem affineParameterPullback_parameter_hasDerivAt
    (reparametrization : DiagonalReparametrization)
    (parameter epsilon : ℝ) :
    HasDerivAt
      (fun variedParameter =>
        affineParameterPullback reparametrization variedParameter epsilon)
      (affineJacobianPullback reparametrization parameter epsilon) parameter := by
  have hRaw :=
    (hasDerivAt_id parameter).add
      ((reparametrization.generator_hasDerivAt parameter).const_mul epsilon)
  change HasDerivAt
    (fun variedParameter : ℝ =>
      variedParameter + epsilon * reparametrization.generator variedParameter)
    (1 + epsilon * reparametrization.generatorDerivative parameter) parameter
  exact hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Weight-one density pulled back along the displayed affine
reparametrization first jet. -/
def candidateDensityPullbackCurve
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (parameter epsilon : ℝ) : ℝ :=
  affineJacobianPullback reparametrization parameter epsilon *
    candidateDensity data
      (affineParameterPullback reparametrization parameter epsilon)

theorem affineParameterPullback_hasDerivAt
    (reparametrization : DiagonalReparametrization) (parameter : ℝ) :
    HasDerivAt (affineParameterPullback reparametrization parameter)
      (reparametrization.generator parameter) 0 := by
  have hRaw :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := parameter)).add
      ((hasDerivAt_id (0 : ℝ)).const_mul
        (reparametrization.generator parameter))
  refine (hRaw.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · simp
  · intro epsilon
    simp [affineParameterPullback]
    ring

theorem affineJacobianPullback_hasDerivAt
    (reparametrization : DiagonalReparametrization) (parameter : ℝ) :
    HasDerivAt (affineJacobianPullback reparametrization parameter)
      (reparametrization.generatorDerivative parameter) 0 := by
  have hRaw :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
      ((hasDerivAt_id (0 : ℝ)).const_mul
        (reparametrization.generatorDerivative parameter))
  refine (hRaw.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · simp
  · intro epsilon
    simp [affineJacobianPullback]
    ring

/-- The infinitesimal density law is now derived from an actual pullback
first jet, rather than postulated independently. -/
theorem candidateDensityPullbackCurve_hasDerivAt
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (parameter : ℝ) :
    HasDerivAt
      (candidateDensityPullbackCurve data reparametrization parameter)
      (diagonalDensityVariation data reparametrization parameter) 0 := by
  have hParameter :=
    affineParameterPullback_hasDerivAt reparametrization parameter
  have hDensityAt :
      HasDerivAt (candidateDensity data)
        (candidateDensityDerivative data parameter)
        (affineParameterPullback reparametrization parameter 0) := by
    simpa [affineParameterPullback] using
      candidateDensity_hasDerivAt data parameter
  have hDensity :=
    hDensityAt.comp 0 hParameter
  have hJacobian :=
    affineJacobianPullback_hasDerivAt reparametrization parameter
  have hProduct := hJacobian.mul hDensity
  refine (hProduct.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · simp [diagonalDensityVariation, affineParameterPullback,
      affineJacobianPullback]
    ring
  · intro epsilon
    rfl

/-- Primitive whose derivative is the diagonal density variation. -/
def densityNoetherPrimitive
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (parameter : ℝ) : ℝ :=
  reparametrization.generator parameter * candidateDensity data parameter

/-- The density transformation is an actual total derivative, obtained from
the two genuine derivatives and the product rule. -/
theorem densityNoetherPrimitive_hasDerivAt
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (parameter : ℝ) :
    HasDerivAt (densityNoetherPrimitive data reparametrization)
      (diagonalDensityVariation data reparametrization parameter) parameter := by
  have hProduct :=
    (reparametrization.generator_hasDerivAt parameter).mul
      (candidateDensity_hasDerivAt data parameter)
  refine hProduct.congr_deriv ?_
  simp [diagonalDensityVariation]
  ring

/-- Pointwise Noether/transgression identity in expanded form. -/
theorem diagonalDensityVariation_eq_totalDerivativeCoefficient
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (parameter : ℝ) :
    diagonalDensityVariation data reparametrization parameter =
      reparametrization.generatorDerivative parameter *
          candidateDensity data parameter +
        reparametrization.generator parameter *
          candidateDensityDerivative data parameter := by
  simp [diagonalDensityVariation]
  ring

/-- Oriented real interval used only to type the endpoint ledger. -/
structure OrientedParameterInterval where
  initialParameter : ℝ
  finalParameter : ℝ

/-- Face/endpoints ledger for the one-dimensional transgression. -/
structure DensityEndpointLedger where
  faceTransgression : ℝ
  initialEndpointShift : ℝ
  finalEndpointShift : ℝ

def DensityEndpointLedger.totalShift
    (ledger : DensityEndpointLedger) : ℝ :=
  ledger.faceTransgression + ledger.initialEndpointShift +
    ledger.finalEndpointShift

/-- Exact endpoint representative of the total derivative.  No integration
or fundamental theorem of calculus is asserted here. -/
def exactDensityEndpointLedger
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (interval : OrientedParameterInterval) : DensityEndpointLedger :=
  { faceTransgression :=
      densityNoetherPrimitive data reparametrization interval.finalParameter -
        densityNoetherPrimitive data reparametrization interval.initialParameter
    initialEndpointShift :=
      densityNoetherPrimitive data reparametrization interval.initialParameter
    finalEndpointShift :=
      -densityNoetherPrimitive data reparametrization interval.finalParameter }

@[simp]
theorem exactDensityEndpointLedger_faceTransgression
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (interval : OrientedParameterInterval) :
    (exactDensityEndpointLedger data reparametrization interval).faceTransgression =
      densityNoetherPrimitive data reparametrization interval.finalParameter -
        densityNoetherPrimitive data reparametrization
          interval.initialParameter := by
  rfl

/-- The face primitive difference and its two oriented endpoint shifts cancel
exactly. -/
theorem exactDensityEndpointLedger_totalShift_zero
    (data : CandidateDensityCurve)
    (reparametrization : DiagonalReparametrization)
    (interval : OrientedParameterInterval) :
    (exactDensityEndpointLedger data reparametrization interval).totalShift = 0 := by
  simp [DensityEndpointLedger.totalShift, exactDensityEndpointLedger]

end

end P0EFTJanusDiagonalReparametrizationDensityNoether
end JanusFormal
