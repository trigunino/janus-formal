import Mathlib.Analysis.Calculus.ParametricIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInducedScalarStressVariation4D

/-!
# Integrated four-dimensional scalar stress variation

This gate lifts the exact pointwise metric variation to an arbitrary measured
base.  The metric, its inverse and its determinant measure still come from the
same field at every point.  Differentiation under the integral is justified by
an explicit common-neighbourhood Lipschitz majorant; no finite-site replacement
or unproved interchange of limits is used.

The gate does not yet identify the supplied covector field with `d phi`, prove
the scalar Euler equation, or establish stress conservation.
-/

namespace JanusFormal
namespace P0EFTJanusIntegratedScalarStressVariation4D

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D

variable {X : Type*} [MeasurableSpace X]

/-- One global scalar sector over a common measured base. -/
structure ScalarMetricSector4 (X : Type*) where
  metric : X -> FixedSignMetric4
  variation : X -> SymmetricMetricVariation4
  jet : X -> ScalarMatterJet
  massSquared : Real
  source : Real

/-- The exact integrated density along the covariant metric curve. -/
def integratedScalarAction
    (mu : Measure X) (sector : ScalarMetricSector4 X) (t : Real) : Real :=
  integral mu (fun x =>
    metricInducedScalarDensityCurve
      (sector.metric x) (sector.variation x)
      sector.massSquared sector.source (sector.jet x) t)

/-- Pointwise stress pairing which is the actual metric derivative. -/
def pointwiseScalarStressVariation
    (sector : ScalarMetricSector4 X) (x : X) : Real :=
  -(Real.sqrt |Matrix.det (sector.metric x).metric| / 2) *
    tensorMetricPairing
      (pointwiseScalarStressTensor (sector.metric x)
        sector.massSquared sector.source (sector.jet x))
      (sector.variation x).tensor

/-- The integrated stress pairing on the same measured base. -/
def integratedScalarStressVariation
    (mu : Measure X) (sector : ScalarMetricSector4 X) : Real :=
  integral mu (pointwiseScalarStressVariation sector)

omit [MeasurableSpace X] in
theorem pointwiseScalarDensity_stress_hasDerivAt
    (sector : ScalarMetricSector4 X) (x : X) :
    HasDerivAt
      (fun t => metricInducedScalarDensityCurve
        (sector.metric x) (sector.variation x)
        sector.massSquared sector.source (sector.jet x) t)
      (pointwiseScalarStressVariation sector x) 0 := by
  have h := metricInducedScalarDensityCurve_stress_hasDerivAt
    (sector.metric x) (sector.variation x)
    sector.massSquared sector.source (sector.jet x)
  unfold FrobeniusScalarHasDerivAt at h
  exact h.hasDerivAt.congr_deriv (by
    simp [pointwiseScalarStressVariation])

/-- Rebase the same affine metric curve at an arbitrary admissible parameter. -/
def shiftedFixedSignMetric4
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (t : Real)
    (hDomain : metricCurve data variation t ∈
      fixedDeterminantSignDomain data.orientation) : FixedSignMetric4 where
  metric := metricCurve data variation t
  orientation := data.orientation
  orientation_ne_zero := data.orientation_ne_zero
  metric_symmetric := by
    simp [metricCurve, Matrix.transpose_add, Matrix.transpose_smul,
      data.metric_symmetric, variation.tensor_symmetric]
  metric_mem_domain := hDomain

theorem shifted_metricCurve
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (t s : Real)
    (hDomain : metricCurve data variation t ∈
      fixedDeterminantSignDomain data.orientation) :
    metricCurve (shiftedFixedSignMetric4 data variation t hDomain)
        variation s =
      metricCurve data variation (t + s) := by
  ext first second
  simp [shiftedFixedSignMetric4, metricCurve, add_smul]
  ring

theorem shifted_metricInducedScalarDensityCurve
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (massSquared source : Real) (jet : ScalarMatterJet)
    (t s : Real)
    (hDomain : metricCurve data variation t ∈
      fixedDeterminantSignDomain data.orientation) :
    metricInducedScalarDensityCurve
        (shiftedFixedSignMetric4 data variation t hDomain) variation
        massSquared source jet s =
      metricInducedScalarDensityCurve data variation
        massSquared source jet (t + s) := by
  simp only [metricInducedScalarDensityCurve, exactInverseMetricCurve]
  rw [shifted_metricCurve data variation t s hDomain]

/-- Actual pointwise derivative at every parameter where the affine metric
curve remains in its fixed-sign component. -/
theorem metricInducedScalarDensityCurve_stress_hasDerivAt_at
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (massSquared source : Real) (jet : ScalarMatterJet)
    (t : Real)
    (hDomain : metricCurve data variation t ∈
      fixedDeterminantSignDomain data.orientation) :
    HasDerivAt
      (metricInducedScalarDensityCurve data variation massSquared source jet)
      (-(Real.sqrt
          |Matrix.det (metricCurve data variation t)| / 2) *
        tensorMetricPairing
          (pointwiseScalarStressTensor
            (shiftedFixedSignMetric4 data variation t hDomain)
            massSquared source jet)
          variation.tensor) t := by
  let shifted := shiftedFixedSignMetric4 data variation t hDomain
  have hZero := metricInducedScalarDensityCurve_stress_hasDerivAt
    shifted variation massSquared source jet
  unfold FrobeniusScalarHasDerivAt at hZero
  let shift : Real -> Real := fun r => r - t
  have hShift : HasDerivAt shift 1 t := by
    simpa [shift] using (hasDerivAt_id t).sub_const t
  have hOuter : HasDerivAt
      (metricInducedScalarDensityCurve shifted variation massSquared source jet)
      ((ContinuousLinearMap.toSpanSingleton Real
        (-(Real.sqrt |Matrix.det shifted.metric| / 2) *
          tensorMetricPairing
            (pointwiseScalarStressTensor shifted massSquared source jet)
            variation.tensor)) 1)
      (shift t) := by
    simpa [shift] using hZero.hasDerivAt
  have hComposed := hOuter.comp t hShift
  have hMetric : shifted.metric = metricCurve data variation t := rfl
  have hFunction :
      metricInducedScalarDensityCurve shifted variation
          massSquared source jet ∘ shift =
      metricInducedScalarDensityCurve data variation massSquared source jet := by
    funext r
    change metricInducedScalarDensityCurve shifted variation
      massSquared source jet (shift r) = _
    rw [show shifted = shiftedFixedSignMetric4 data variation t hDomain from rfl,
      shifted_metricInducedScalarDensityCurve]
    congr 1
    simp [shift]
  rw [hFunction] at hComposed
  simpa [shifted, hMetric] using hComposed

/-- Total derivative field, set to zero outside the determinant-sign domain. -/
noncomputable def pointwiseScalarStressVariationAt
    (sector : ScalarMetricSector4 X) (t : Real) (x : X) : Real :=
  by
    classical
    exact if hDomain : metricCurve (sector.metric x) (sector.variation x) t ∈
        fixedDeterminantSignDomain (sector.metric x).orientation then
      -(Real.sqrt
          |Matrix.det (metricCurve (sector.metric x) (sector.variation x) t)| / 2) *
        tensorMetricPairing
          (pointwiseScalarStressTensor
            (shiftedFixedSignMetric4 (sector.metric x) (sector.variation x)
              t hDomain)
            sector.massSquared sector.source (sector.jet x))
          (sector.variation x).tensor
    else 0

omit [MeasurableSpace X] in
@[simp]
theorem pointwiseScalarStressVariationAt_zero
    (sector : ScalarMetricSector4 X) (x : X) :
    pointwiseScalarStressVariationAt sector 0 x =
      pointwiseScalarStressVariation sector x := by
  classical
  simp [pointwiseScalarStressVariationAt, pointwiseScalarStressVariation,
    shiftedFixedSignMetric4, (sector.metric x).metric_mem_domain]

omit [MeasurableSpace X] in
theorem pointwiseScalarDensity_stress_hasDerivAt_at
    (sector : ScalarMetricSector4 X) (t : Real) (x : X)
    (hDomain : metricCurve (sector.metric x) (sector.variation x) t ∈
      fixedDeterminantSignDomain (sector.metric x).orientation) :
    HasDerivAt
      (fun r => metricInducedScalarDensityCurve
        (sector.metric x) (sector.variation x)
        sector.massSquared sector.source (sector.jet x) r)
      (pointwiseScalarStressVariationAt sector t x) t := by
  classical
  rw [pointwiseScalarStressVariationAt, dif_pos hDomain]
  exact metricInducedScalarDensityCurve_stress_hasDerivAt_at
    (sector.metric x) (sector.variation x)
    sector.massSquared sector.source (sector.jet x) t hDomain

/--
Derivative of the genuine spacetime integral.  The hypotheses are precisely
the standard dominated-differentiation contract: measurability and
integrability at the base point, a common parameter neighbourhood, and an
integrable Lipschitz majorant.
-/
theorem integratedScalarAction_stress_hasDerivAt
    (mu : Measure X) (sector : ScalarMetricSector4 X)
    (parameterDomain : Set Real)
    (hDomain : parameterDomain ∈ nhds (0 : Real))
    (hDensityMeasurable :
      Filter.Eventually (fun t => AEStronglyMeasurable
        (fun x => metricInducedScalarDensityCurve
          (sector.metric x) (sector.variation x)
          sector.massSquared sector.source (sector.jet x) t) mu)
        (nhds (0 : Real)))
    (hDensityIntegrable : Integrable
      (fun x => metricInducedScalarDensityCurve
        (sector.metric x) (sector.variation x)
        sector.massSquared sector.source (sector.jet x) 0) mu)
    (hStressMeasurable :
      AEStronglyMeasurable (pointwiseScalarStressVariation sector) mu)
    (bound : X -> Real)
    (hLipschitz : ∀ᵐ x ∂mu,
      LipschitzOnWith (Real.nnabs (bound x))
        (fun t => metricInducedScalarDensityCurve
          (sector.metric x) (sector.variation x)
          sector.massSquared sector.source (sector.jet x) t)
        parameterDomain)
    (hBoundIntegrable : Integrable bound mu) :
    HasDerivAt (integratedScalarAction mu sector)
      (integratedScalarStressVariation mu sector) 0 := by
  have hDerivative : ∀ᵐ x ∂mu,
      HasDerivAt
        (fun t => metricInducedScalarDensityCurve
          (sector.metric x) (sector.variation x)
          sector.massSquared sector.source (sector.jet x) t)
        (pointwiseScalarStressVariation sector x) 0 :=
    Filter.Eventually.of_forall
      (pointwiseScalarDensity_stress_hasDerivAt sector)
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_lip
    hDomain hDensityMeasurable hDensityIntegrable hStressMeasurable
    hLipschitz hBoundIntegrable hDerivative
  exact hIntegral.2

/-- Dominated differentiation stated with an actual derivative bound on every
admissible parameter.  Rebasing the affine curve supplies the derivative at
`t`; the only remaining analytic inputs are a common determinant-sign domain,
measurability and an integrable uniform majorant. -/
theorem integratedScalarAction_stress_hasDerivAt_of_deriv_le
    (mu : Measure X) (sector : ScalarMetricSector4 X)
    (parameterDomain : Set Real)
    (hParameterDomain : parameterDomain ∈ nhds (0 : Real))
    (hMetricDomain : ∀ᵐ x ∂mu, ∀ t ∈ parameterDomain,
      metricCurve (sector.metric x) (sector.variation x) t ∈
        fixedDeterminantSignDomain (sector.metric x).orientation)
    (hDensityMeasurable :
      Filter.Eventually (fun t => AEStronglyMeasurable
        (fun x => metricInducedScalarDensityCurve
          (sector.metric x) (sector.variation x)
          sector.massSquared sector.source (sector.jet x) t) mu)
        (nhds (0 : Real)))
    (hDensityIntegrable : Integrable
      (fun x => metricInducedScalarDensityCurve
        (sector.metric x) (sector.variation x)
        sector.massSquared sector.source (sector.jet x) 0) mu)
    (hDerivativeMeasurable : AEStronglyMeasurable
      (pointwiseScalarStressVariationAt sector 0) mu)
    (bound : X -> Real)
    (hDerivativeBound : ∀ᵐ x ∂mu, ∀ t ∈ parameterDomain,
      ‖pointwiseScalarStressVariationAt sector t x‖ <= bound x)
    (hBoundIntegrable : Integrable bound mu) :
    HasDerivAt (integratedScalarAction mu sector)
      (integratedScalarStressVariation mu sector) 0 := by
  have hPointwiseDerivative : ∀ᵐ x ∂mu, ∀ t ∈ parameterDomain,
      HasDerivAt
        (fun r => metricInducedScalarDensityCurve
          (sector.metric x) (sector.variation x)
          sector.massSquared sector.source (sector.jet x) r)
        (pointwiseScalarStressVariationAt sector t x) t :=
    hMetricDomain.mono fun x hx t ht =>
      pointwiseScalarDensity_stress_hasDerivAt_at sector t x (hx t ht)
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hParameterDomain hDensityMeasurable hDensityIntegrable
    hDerivativeMeasurable hDerivativeBound hBoundIntegrable
    hPointwiseDerivative
  have hStressIntegral :
      integral mu (pointwiseScalarStressVariationAt sector 0) =
        integratedScalarStressVariation mu sector := by
    unfold integratedScalarStressVariation
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (pointwiseScalarStressVariationAt_zero sector)
  have hResult := hIntegral.2
  rw [hStressIntegral] at hResult
  exact hResult

/-- Two PT-labelled sectors share one base and one measure. -/
structure TwoScalarMetricSectors4 (X : Type*) where
  plus : ScalarMetricSector4 X
  minus : ScalarMetricSector4 X

/-- Sector exchange underlying the PT-labelled doublet. -/
def exchangeTwoScalarMetricSectors4
    (sectors : TwoScalarMetricSectors4 X) : TwoScalarMetricSectors4 X where
  plus := sectors.minus
  minus := sectors.plus

omit [MeasurableSpace X] in
@[simp]
theorem exchangeTwoScalarMetricSectors4_involutive
    (sectors : TwoScalarMetricSectors4 X) :
    exchangeTwoScalarMetricSectors4
        (exchangeTwoScalarMetricSectors4 sectors) = sectors := by
  cases sectors
  rfl

def integratedTwoSectorScalarAction
    (mu : Measure X) (sectors : TwoScalarMetricSectors4 X) (t : Real) : Real :=
  integratedScalarAction mu sectors.plus t +
    integratedScalarAction mu sectors.minus t

def integratedTwoSectorScalarStressVariation
    (mu : Measure X) (sectors : TwoScalarMetricSectors4 X) : Real :=
  integratedScalarStressVariation mu sectors.plus +
    integratedScalarStressVariation mu sectors.minus

theorem integratedTwoSectorScalarAction_exchange
    (mu : Measure X) (sectors : TwoScalarMetricSectors4 X) :
    integratedTwoSectorScalarAction mu
        (exchangeTwoScalarMetricSectors4 sectors) =
      integratedTwoSectorScalarAction mu sectors := by
  funext t
  simp [integratedTwoSectorScalarAction,
    exchangeTwoScalarMetricSectors4, add_comm]

theorem integratedTwoSectorScalarStressVariation_exchange
    (mu : Measure X) (sectors : TwoScalarMetricSectors4 X) :
    integratedTwoSectorScalarStressVariation mu
        (exchangeTwoScalarMetricSectors4 sectors) =
      integratedTwoSectorScalarStressVariation mu sectors := by
  simp [integratedTwoSectorScalarStressVariation,
    exchangeTwoScalarMetricSectors4, add_comm]

theorem integratedTwoSectorScalarAction_stress_hasDerivAt
    (mu : Measure X) (sectors : TwoScalarMetricSectors4 X)
    (hPlus : HasDerivAt (integratedScalarAction mu sectors.plus)
      (integratedScalarStressVariation mu sectors.plus) 0)
    (hMinus : HasDerivAt (integratedScalarAction mu sectors.minus)
      (integratedScalarStressVariation mu sectors.minus) 0) :
    HasDerivAt (integratedTwoSectorScalarAction mu sectors)
      (integratedTwoSectorScalarStressVariation mu sectors) 0 := by
  change HasDerivAt
    (fun t => integratedScalarAction mu sectors.plus t +
      integratedScalarAction mu sectors.minus t)
    (integratedScalarStressVariation mu sectors.plus +
      integratedScalarStressVariation mu sectors.minus) 0
  exact hPlus.add hMinus

end

end P0EFTJanusIntegratedScalarStressVariation4D
end JanusFormal
