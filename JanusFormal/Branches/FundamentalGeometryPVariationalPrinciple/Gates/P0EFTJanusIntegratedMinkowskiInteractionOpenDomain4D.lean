import Mathlib.Analysis.Calculus.ParametricIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMinkowskiInteractionDensityOpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalFieldBridge4D

/-!
# Integrated Candidate-A interaction on the PT-safe root domain

The pointwise two-sector Candidate-A density is lifted to fields on an
arbitrary measured base.  Fields take values in the explicit PT-safe open
root domain.  An admissible affine variation stays in that domain on one
parameter neighbourhood common to every base point.

Differentiation under the integral uses an explicit measurable, integrable
domination contract for the actual pointwise open-domain derivative.  No
boundary hypothesis occurs: the interaction density contains no spatial
derivative and this gate performs no integration by parts.  The construction
also specializes to the effective D8 mapping-torus spacetime.
-/

namespace JanusFormal
namespace P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D

set_option autoImplicit false
set_option maxRecDepth 2048

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMinkowskiRelativeRootBranch4D
open P0EFTJanusMinkowskiInteractionDensityVariation4D
open P0EFTJanusMinkowskiInteractionDensityOpenDomain4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusGlobalFieldBridge4D
open P0EFTJanusMappingTorusPTInvolution

abbrev Matrix4 := P0EFTJanusMinkowskiRelativeRootBranch4D.Matrix4
abbrev MetricPair := P0EFTJanusMinkowskiRelativeRootBranch4D.MetricPair

attribute [local instance]
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4AddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4TopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4Module
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairTopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairModule

/-- Scalar derivative using exactly the real normed structure selected by the
pointwise Frechet gate. -/
abbrev OpenScalarHasDerivAt
    (function : Real → Real) (derivative point : Real) : Prop :=
  @HasDerivAt Real _ Real
    Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace Real Real).toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    _ function derivative point

/-- Metric fields whose value at every base point lies in the explicit
PT-safe two-ordering root domain. -/
abbrev PTMetricField (X : Type*) := X → ptPairedRootOpenDomain

/-- Unconstrained tangent field for an affine variation of both metrics. -/
abbrev MetricPairFieldVariation (X : Type*) := X → MetricPair

/-- The genuine affine metric-field curve. -/
def metricFieldCurve {X : Type*}
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (t : Real) (x : X) : MetricPair :=
  letI : AddCommGroup MetricPair :=
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup.toAddCommGroup
  letI : Module Real MetricPair :=
    P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace.toModule
  t • variation x + (field x : MetricPair)

@[simp] theorem metricFieldCurve_zero {X : Type*}
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (x : X) :
    metricFieldCurve field variation 0 x = (field x : MetricPair) := by
  simp [metricFieldCurve]

theorem metricFieldCurve_hasDerivAt {X : Type*}
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (x : X) (t : Real) :
    PairHasDerivAt (fun r ↦ metricFieldCurve field variation r x)
      (variation x) t := by
  unfold PairHasDerivAt metricFieldCurve
  simpa only [Function.id_def, one_smul] using
    (HasDerivAt.add_const (field x : MetricPair)
      ((hasDerivAt_id (x := t)).smul_const (variation x)))

/-- A uniform open-domain contract for a metric-field variation.  Its
parameter neighbourhood is common to all points of the measured base. -/
structure OpenDomainMetricFieldVariation {X : Type*}
    (field : PTMetricField X) (variation : MetricPairFieldVariation X) where
  parameterDomain : Set Real
  parameterDomain_mem_nhds : parameterDomain ∈ 𝓝 (0 : Real)
  curve_mem_domain : ∀ x t, t ∈ parameterDomain →
    metricFieldCurve field variation t x ∈ ptPairedRootOpenDomain

/-- The two-sector Candidate-A functional on a measured field base. -/
def integratedCandidateAFunctional {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X) : Real :=
  ∫ x, ptPairedCandidateAInteractionDensity interactionScale coefficients
    (field x : MetricPair) ∂mu

/-- The functional evaluated on the affine metric-field curve. -/
def integratedCandidateAActionCurve {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X)
    (variation : MetricPairFieldVariation X) (t : Real) : Real :=
  ∫ x, ptPairedCandidateAInteractionDensity interactionScale coefficients
    (metricFieldCurve field variation t x) ∂mu

@[simp] theorem integratedCandidateAActionCurve_zero
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X)
    (variation : MetricPairFieldVariation X) :
    integratedCandidateAActionCurve mu interactionScale coefficients field
        variation 0 =
      integratedCandidateAFunctional mu interactionScale coefficients field := by
  simp [integratedCandidateAActionCurve, integratedCandidateAFunctional]

/-- Exact pointwise first variation at the original field. -/
def pointwiseCandidateAFirstVariation {X : Type*}
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (x : X) : Real :=
  ptPairedCandidateADerivative interactionScale coefficients
    (field x : MetricPair) (field x).property (variation x)

/-- Integrated exact pointwise first variation. -/
def integratedCandidateAFirstVariation {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X)
    (variation : MetricPairFieldVariation X) : Real :=
  ∫ x, pointwiseCandidateAFirstVariation interactionScale coefficients
    field variation x ∂mu

/-- Total pointwise derivative field.  Outside the selected parameter domain
it is set to zero; on the domain it is exactly the open-domain derivative. -/
def pointwiseCandidateAFirstVariationAt {X : Type*}
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (t : Real) (x : X) : Real := by
  classical
  exact if h : metricFieldCurve field variation t x ∈
      ptPairedRootOpenDomain then
    ptPairedCandidateADerivative interactionScale coefficients
      (metricFieldCurve field variation t x) h (variation x)
  else 0

theorem pointwiseCandidateAFirstVariationAt_of_mem {X : Type*}
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (t : Real) (x : X)
    (h : metricFieldCurve field variation t x ∈ ptPairedRootOpenDomain) :
    pointwiseCandidateAFirstVariationAt interactionScale coefficients field
        variation t x =
      ptPairedCandidateADerivative interactionScale coefficients
        (metricFieldCurve field variation t x) h (variation x) := by
  simp only [pointwiseCandidateAFirstVariationAt, dif_pos h]

@[simp] theorem pointwiseCandidateAFirstVariationAt_zero {X : Type*}
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (x : X) :
    pointwiseCandidateAFirstVariationAt interactionScale coefficients field
        variation 0 x =
      pointwiseCandidateAFirstVariation interactionScale coefficients field
        variation x := by
  simp [pointwiseCandidateAFirstVariationAt,
    pointwiseCandidateAFirstVariation]

/-- The exact pointwise open-domain Frechet theorem composed with the affine
field curve at an arbitrary admissible parameter. -/
theorem pointwiseCandidateADensityCurve_hasDerivAt_at {X : Type*}
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (x : X) (t : Real)
    (hPoint : metricFieldCurve field variation t x ∈
      ptPairedRootOpenDomain) :
    OpenScalarHasDerivAt
      (fun r ↦ ptPairedCandidateAInteractionDensity interactionScale
        coefficients (metricFieldCurve field variation r x))
      (pointwiseCandidateAFirstVariationAt interactionScale coefficients
        field variation t x) t := by
  have hDensity :=
    ptPairedCandidateAInteractionDensity_hasFDerivAt interactionScale
      coefficients hPoint
  unfold OpenPairScalarHasFDerivAt at hDensity
  have hComposite := hDensity.comp_hasDerivAt_of_eq t
    (metricFieldCurve_hasDerivAt field variation x t) rfl
  have hFunctions :
      (fun r ↦ ptPairedCandidateAInteractionDensity interactionScale
        coefficients (metricFieldCurve field variation r x)) =ᶠ[𝓝 t]
      (ptPairedCandidateAInteractionDensity interactionScale coefficients ∘
        fun r ↦ metricFieldCurve field variation r x) :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  have hLambda := hComposite.congr_of_eventuallyEq hFunctions
  unfold OpenScalarHasDerivAt
  simpa only [pointwiseCandidateAFirstVariationAt_of_mem
    interactionScale coefficients field variation t x hPoint] using hLambda

/-- Pointwise derivative at the original field, with no derivative supplied
as an assumption. -/
theorem pointwiseCandidateADensityCurve_hasDerivAt {X : Type*}
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (x : X) :
    OpenScalarHasDerivAt
      (fun r ↦ ptPairedCandidateAInteractionDensity interactionScale
        coefficients (metricFieldCurve field variation r x))
      (pointwiseCandidateAFirstVariation interactionScale coefficients field
        variation x) 0 := by
  simpa using pointwiseCandidateADensityCurve_hasDerivAt_at interactionScale
    coefficients field variation x 0 (by
      rw [metricFieldCurve_zero]
      exact (field x).property)

/-- Explicit analytic hypotheses for differentiation under the integral.
The open-domain condition is carried separately by `admissible`; this
structure contains only measurability, integrability and domination. -/
structure DominatedInteractionIntegralContract {X : Type*}
    [MeasurableSpace X] (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X)
    (variation : MetricPairFieldVariation X)
    (admissible : OpenDomainMetricFieldVariation field variation) where
  density_aeStronglyMeasurable : ∀ᶠ t in 𝓝 (0 : Real),
    AEStronglyMeasurable
      (fun x ↦ ptPairedCandidateAInteractionDensity interactionScale
        coefficients (metricFieldCurve field variation t x)) mu
  density_integrable_at_zero : Integrable
    (fun x ↦ ptPairedCandidateAInteractionDensity interactionScale
      coefficients (metricFieldCurve field variation 0 x)) mu
  derivative_aeStronglyMeasurable : AEStronglyMeasurable
    (pointwiseCandidateAFirstVariationAt interactionScale coefficients field
      variation 0) mu
  bound : X → Real
  derivative_norm_le : ∀ᵐ x ∂mu, ∀ t ∈ admissible.parameterDomain,
    ‖pointwiseCandidateAFirstVariationAt interactionScale coefficients field
      variation t x‖ ≤ bound x
  bound_integrable : Integrable bound mu

/-- Integrability of the exact first-variation density and derivative of the
genuine field functional.  The proof uses the open-domain derivative at every
admissible parameter and the displayed integrable majorant.  No boundary term
or boundary condition is involved. -/
theorem integratedCandidateAActionCurve_integrable_and_hasDerivAt
    {X : Type*}
    [MeasurableSpace X] (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X)
    (variation : MetricPairFieldVariation X)
    (admissible : OpenDomainMetricFieldVariation field variation)
    (contract : DominatedInteractionIntegralContract mu interactionScale
      coefficients field variation admissible) :
    Integrable
        (pointwiseCandidateAFirstVariation interactionScale coefficients field
          variation) mu ∧
      OpenScalarHasDerivAt
        (integratedCandidateAActionCurve mu interactionScale coefficients field
          variation)
        (integratedCandidateAFirstVariation mu interactionScale coefficients
          field variation) 0 := by
  have hPointwise : ∀ᵐ x ∂mu, ∀ t ∈ admissible.parameterDomain,
      OpenScalarHasDerivAt
        (fun r ↦ ptPairedCandidateAInteractionDensity interactionScale
          coefficients (metricFieldCurve field variation r x))
        (pointwiseCandidateAFirstVariationAt interactionScale coefficients
          field variation t x) t :=
    Filter.Eventually.of_forall fun x t ht ↦
      pointwiseCandidateADensityCurve_hasDerivAt_at interactionScale
        coefficients field variation x t
        (admissible.curve_mem_domain x t ht)
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x ↦ ptPairedCandidateAInteractionDensity interactionScale
      coefficients (metricFieldCurve field variation t x))
    (F' := pointwiseCandidateAFirstVariationAt interactionScale coefficients
      field variation)
    (bound := contract.bound) admissible.parameterDomain_mem_nhds
    contract.density_aeStronglyMeasurable
    contract.density_integrable_at_zero
    contract.derivative_aeStronglyMeasurable contract.derivative_norm_le
    contract.bound_integrable hPointwise
  constructor
  · exact hIntegral.1.congr (Filter.Eventually.of_forall fun x ↦
      pointwiseCandidateAFirstVariationAt_zero interactionScale coefficients
        field variation x)
  · unfold OpenScalarHasDerivAt integratedCandidateAActionCurve
      integratedCandidateAFirstVariation
    simpa only [pointwiseCandidateAFirstVariationAt_zero] using hIntegral.2

/-- Derivative-under-the-integral projection of the stronger integrability
statement. -/
theorem integratedCandidateAActionCurve_hasDerivAt {X : Type*}
    [MeasurableSpace X] (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X)
    (variation : MetricPairFieldVariation X)
    (admissible : OpenDomainMetricFieldVariation field variation)
    (contract : DominatedInteractionIntegralContract mu interactionScale
      coefficients field variation admissible) :
    OpenScalarHasDerivAt
      (integratedCandidateAActionCurve mu interactionScale coefficients field
        variation)
      (integratedCandidateAFirstVariation mu interactionScale coefficients
        field variation) 0 :=
  (integratedCandidateAActionCurve_integrable_and_hasDerivAt mu
    interactionScale coefficients field variation admissible contract).2

/-- Pointwise exchange of the two metric sectors preserves the PT-safe field
space. -/
def exchangePTMetricField {X : Type*} (field : PTMetricField X) :
    PTMetricField X := fun x ↦
  ⟨metricPairExchange (field x : MetricPair),
    (ptPairedRootOpenDomain_exchange_iff (field x : MetricPair)).2
      (field x).property⟩

/-- Pointwise exchange of a metric tangent field. -/
def exchangeMetricPairFieldVariation {X : Type*}
    (variation : MetricPairFieldVariation X) : MetricPairFieldVariation X :=
  fun x ↦ metricPairExchange (variation x)

@[simp] theorem exchangePTMetricField_value {X : Type*}
    (field : PTMetricField X) (x : X) :
    (exchangePTMetricField field x : MetricPair) =
      metricPairExchange (field x : MetricPair) :=
  rfl

@[simp] theorem metricFieldCurve_exchange {X : Type*}
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (t : Real) (x : X) :
    metricFieldCurve (exchangePTMetricField field)
        (exchangeMetricPairFieldVariation variation) t x =
      metricPairExchange (metricFieldCurve field variation t x) := by
  simp [metricFieldCurve, exchangeMetricPairFieldVariation,
    map_add, map_smul]

/-- Exchange preserves a common admissible parameter domain. -/
def OpenDomainMetricFieldVariation.exchange {X : Type*}
    {field : PTMetricField X} {variation : MetricPairFieldVariation X}
    (admissible : OpenDomainMetricFieldVariation field variation) :
    OpenDomainMetricFieldVariation (exchangePTMetricField field)
      (exchangeMetricPairFieldVariation variation) where
  parameterDomain := admissible.parameterDomain
  parameterDomain_mem_nhds := admissible.parameterDomain_mem_nhds
  curve_mem_domain := by
    intro x t ht
    rw [metricFieldCurve_exchange]
    exact (ptPairedRootOpenDomain_exchange_iff _).2
      (admissible.curve_mem_domain x t ht)

/-- Exact exchange invariance of the integrated field functional. -/
theorem integratedCandidateAFunctional_exchange {X : Type*}
    [MeasurableSpace X] (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X) :
    integratedCandidateAFunctional mu interactionScale coefficients
        (exchangePTMetricField field) =
      integratedCandidateAFunctional mu interactionScale coefficients field := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    ptPairedCandidateAInteractionDensity_exchange interactionScale
      coefficients (field x : MetricPair)

/-- Exact exchange invariance of the complete action curve. -/
theorem integratedCandidateAActionCurve_exchange {X : Type*}
    [MeasurableSpace X] (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X)
    (variation : MetricPairFieldVariation X) (t : Real) :
    integratedCandidateAActionCurve mu interactionScale coefficients
        (exchangePTMetricField field)
        (exchangeMetricPairFieldVariation variation) t =
      integratedCandidateAActionCurve mu interactionScale coefficients field
        variation t := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change ptPairedCandidateAInteractionDensity interactionScale coefficients
      (metricFieldCurve (exchangePTMetricField field)
        (exchangeMetricPairFieldVariation variation) t x) =
      ptPairedCandidateAInteractionDensity interactionScale coefficients
        (metricFieldCurve field variation t x)
    rw [metricFieldCurve_exchange]
    exact ptPairedCandidateAInteractionDensity_exchange interactionScale
      coefficients (metricFieldCurve field variation t x)

/-- Exchange covariance of the exact pointwise first variation, obtained by
uniqueness of the derivatives of the exchange-identical action curves. -/
theorem pointwiseCandidateAFirstVariation_exchange {X : Type*}
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (x : X) :
    pointwiseCandidateAFirstVariation interactionScale coefficients
        (exchangePTMetricField field)
        (exchangeMetricPairFieldVariation variation) x =
      pointwiseCandidateAFirstVariation interactionScale coefficients field
        variation x := by
  have hExchanged := pointwiseCandidateADensityCurve_hasDerivAt
    interactionScale coefficients (exchangePTMetricField field)
      (exchangeMetricPairFieldVariation variation) x
  have hOriginal := pointwiseCandidateADensityCurve_hasDerivAt
    interactionScale coefficients field variation x
  have hCurves :
      (fun r ↦ ptPairedCandidateAInteractionDensity interactionScale
        coefficients
        (metricFieldCurve (exchangePTMetricField field)
          (exchangeMetricPairFieldVariation variation) r x)) =
      (fun r ↦ ptPairedCandidateAInteractionDensity interactionScale
        coefficients (metricFieldCurve field variation r x)) := by
    funext r
    rw [metricFieldCurve_exchange]
    exact ptPairedCandidateAInteractionDensity_exchange interactionScale
      coefficients (metricFieldCurve field variation r x)
  rw [hCurves] at hExchanged
  exact hExchanged.unique hOriginal

/-- Exchange invariance of the integrated first variation. -/
theorem integratedCandidateAFirstVariation_exchange {X : Type*}
    [MeasurableSpace X] (mu : Measure X) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : PTMetricField X)
    (variation : MetricPairFieldVariation X) :
    integratedCandidateAFirstVariation mu interactionScale coefficients
        (exchangePTMetricField field)
        (exchangeMetricPairFieldVariation variation) =
      integratedCandidateAFirstVariation mu interactionScale coefficients
        field variation := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    pointwiseCandidateAFirstVariation_exchange interactionScale coefficients
      field variation x

/-- A measured base with a measurable, measure-preserving PT involution.  The
measure-preservation hypothesis is exactly what is needed to reindex the
spacetime integral. -/
structure MeasuredPTBase (X : Type*) [MeasurableSpace X] where
  measure : Measure X
  pt : X ≃ᵐ X
  pt_involutive : Function.Involutive pt
  pt_measurePreserving : MeasurePreserving pt measure measure

/-- Reindex a domain-valued metric field along a base map. -/
def reindexPTMetricField {X : Type*} (reindex : X → X)
    (field : PTMetricField X) : PTMetricField X :=
  fun x ↦ field (reindex x)

/-- Reindex a metric tangent field along a base map. -/
def reindexMetricPairFieldVariation {X : Type*} (reindex : X → X)
    (variation : MetricPairFieldVariation X) : MetricPairFieldVariation X :=
  fun x ↦ variation (reindex x)

/-- Full PT action: pull back along the base involution and exchange the two
metric sectors in the fibre. -/
def measuredPTMetricFieldExchange {X : Type*} [MeasurableSpace X]
    (base : MeasuredPTBase X) (field : PTMetricField X) : PTMetricField X :=
  exchangePTMetricField (reindexPTMetricField base.pt field)

/-- Full PT action on tangent fields. -/
def measuredPTMetricVariationExchange {X : Type*} [MeasurableSpace X]
    (base : MeasuredPTBase X) (variation : MetricPairFieldVariation X) :
    MetricPairFieldVariation X :=
  exchangeMetricPairFieldVariation
    (reindexMetricPairFieldVariation base.pt variation)

@[simp] theorem metricFieldCurve_measuredPTExchange
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (t : Real) (x : X) :
    metricFieldCurve (measuredPTMetricFieldExchange base field)
        (measuredPTMetricVariationExchange base variation) t x =
      metricPairExchange
        (metricFieldCurve field variation t (base.pt x)) := by
  unfold measuredPTMetricFieldExchange measuredPTMetricVariationExchange
  rw [metricFieldCurve_exchange]
  rfl

/-- A uniform admissible domain is preserved by the full measured PT action. -/
def OpenDomainMetricFieldVariation.measuredPTExchange
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    {field : PTMetricField X} {variation : MetricPairFieldVariation X}
    (admissible : OpenDomainMetricFieldVariation field variation) :
    OpenDomainMetricFieldVariation
      (measuredPTMetricFieldExchange base field)
      (measuredPTMetricVariationExchange base variation) where
  parameterDomain := admissible.parameterDomain
  parameterDomain_mem_nhds := admissible.parameterDomain_mem_nhds
  curve_mem_domain := by
    intro x t ht
    rw [metricFieldCurve_measuredPTExchange]
    exact (ptPairedRootOpenDomain_exchange_iff _).2
      (admissible.curve_mem_domain (base.pt x) t ht)

/-- Full PT invariance of the field functional: fibre exchange uses the
pointwise identity, while base reindexing uses measure preservation. -/
theorem integratedCandidateAFunctional_measuredPTExchange
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) :
    integratedCandidateAFunctional base.measure interactionScale coefficients
        (measuredPTMetricFieldExchange base field) =
      integratedCandidateAFunctional base.measure interactionScale
        coefficients field := by
  unfold integratedCandidateAFunctional
  calc
    (∫ x, ptPairedCandidateAInteractionDensity interactionScale coefficients
        (measuredPTMetricFieldExchange base field x : MetricPair)
        ∂base.measure) =
        ∫ x, ptPairedCandidateAInteractionDensity interactionScale coefficients
          (field (base.pt x) : MetricPair) ∂base.measure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        ptPairedCandidateAInteractionDensity_exchange interactionScale
          coefficients (field (base.pt x) : MetricPair)
    _ = ∫ x, ptPairedCandidateAInteractionDensity interactionScale coefficients
          (field x : MetricPair) ∂base.measure :=
      base.pt_measurePreserving.integral_comp'
        (fun x : X ↦ ptPairedCandidateAInteractionDensity interactionScale
          coefficients (field x : MetricPair))

/-- Full PT invariance of the complete affine action curve. -/
theorem integratedCandidateAActionCurve_measuredPTExchange
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (t : Real) :
    integratedCandidateAActionCurve base.measure interactionScale coefficients
        (measuredPTMetricFieldExchange base field)
        (measuredPTMetricVariationExchange base variation) t =
      integratedCandidateAActionCurve base.measure interactionScale
        coefficients field variation t := by
  unfold integratedCandidateAActionCurve
  calc
    (∫ x, ptPairedCandidateAInteractionDensity interactionScale coefficients
        (metricFieldCurve (measuredPTMetricFieldExchange base field)
          (measuredPTMetricVariationExchange base variation) t x)
        ∂base.measure) =
        ∫ x, ptPairedCandidateAInteractionDensity interactionScale coefficients
          (metricFieldCurve field variation t (base.pt x)) ∂base.measure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change ptPairedCandidateAInteractionDensity interactionScale
            coefficients
            (metricFieldCurve (measuredPTMetricFieldExchange base field)
              (measuredPTMetricVariationExchange base variation) t x) =
          ptPairedCandidateAInteractionDensity interactionScale coefficients
            (metricFieldCurve field variation t (base.pt x))
        rw [metricFieldCurve_measuredPTExchange]
        exact ptPairedCandidateAInteractionDensity_exchange interactionScale
          coefficients (metricFieldCurve field variation t (base.pt x))
    _ = ∫ x, ptPairedCandidateAInteractionDensity interactionScale coefficients
          (metricFieldCurve field variation t x) ∂base.measure :=
      base.pt_measurePreserving.integral_comp'
        (fun x : X ↦ ptPairedCandidateAInteractionDensity interactionScale
          coefficients (metricFieldCurve field variation t x))

theorem pointwiseCandidateAFirstVariation_measuredPTExchange
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (x : X) :
    pointwiseCandidateAFirstVariation interactionScale coefficients
        (measuredPTMetricFieldExchange base field)
        (measuredPTMetricVariationExchange base variation) x =
      pointwiseCandidateAFirstVariation interactionScale coefficients field
        variation (base.pt x) := by
  simpa [measuredPTMetricFieldExchange,
    measuredPTMetricVariationExchange, reindexPTMetricField,
    reindexMetricPairFieldVariation, pointwiseCandidateAFirstVariation] using
    pointwiseCandidateAFirstVariation_exchange interactionScale coefficients
      (reindexPTMetricField base.pt field)
      (reindexMetricPairFieldVariation base.pt variation) x

/-- Full PT invariance of the integrated exact first variation. -/
theorem integratedCandidateAFirstVariation_measuredPTExchange
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X) :
    integratedCandidateAFirstVariation base.measure interactionScale
        coefficients (measuredPTMetricFieldExchange base field)
        (measuredPTMetricVariationExchange base variation) =
      integratedCandidateAFirstVariation base.measure interactionScale
        coefficients field variation := by
  unfold integratedCandidateAFirstVariation
  calc
    (∫ x, pointwiseCandidateAFirstVariation interactionScale coefficients
        (measuredPTMetricFieldExchange base field)
        (measuredPTMetricVariationExchange base variation) x ∂base.measure) =
        ∫ x, pointwiseCandidateAFirstVariation interactionScale coefficients
          field variation (base.pt x) ∂base.measure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        pointwiseCandidateAFirstVariation_measuredPTExchange base
          interactionScale coefficients field variation x
    _ = ∫ x, pointwiseCandidateAFirstVariation interactionScale coefficients
          field variation x ∂base.measure :=
      base.pt_measurePreserving.integral_comp'
        (fun x : X ↦ pointwiseCandidateAFirstVariation interactionScale
          coefficients field variation x)

/-- The same dominated contract differentiates the fully PT-transformed
curve, because that complete curve is exactly equal to the original one and
its integrated first variation is PT invariant. -/
theorem integratedCandidateAActionCurve_measuredPT_hasDerivAt
    {X : Type*} [MeasurableSpace X] (base : MeasuredPTBase X)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : PTMetricField X) (variation : MetricPairFieldVariation X)
    (admissible : OpenDomainMetricFieldVariation field variation)
    (contract : DominatedInteractionIntegralContract base.measure
      interactionScale coefficients field variation admissible) :
    OpenScalarHasDerivAt
      (integratedCandidateAActionCurve base.measure interactionScale
        coefficients (measuredPTMetricFieldExchange base field)
        (measuredPTMetricVariationExchange base variation))
      (integratedCandidateAFirstVariation base.measure interactionScale
        coefficients (measuredPTMetricFieldExchange base field)
        (measuredPTMetricVariationExchange base variation)) 0 := by
  have hOriginal := integratedCandidateAActionCurve_hasDerivAt base.measure
    interactionScale coefficients field variation admissible contract
  have hCurves :
      integratedCandidateAActionCurve base.measure interactionScale
          coefficients (measuredPTMetricFieldExchange base field)
          (measuredPTMetricVariationExchange base variation) =ᶠ[𝓝 (0 : Real)]
        integratedCandidateAActionCurve base.measure interactionScale
          coefficients field variation :=
    Filter.Eventually.of_forall fun t ↦
      integratedCandidateAActionCurve_measuredPTExchange base
        interactionScale coefficients field variation t
  have hTransformed := hOriginal.congr_of_eventuallyEq hCurves
  exact hTransformed.congr_deriv
    (integratedCandidateAFirstVariation_measuredPTExchange base
      interactionScale coefficients field variation).symm

/-- The actual D8 reflected-mapping-torus PT involution as a homeomorphism. -/
def effectiveD8SpacetimePTHomeomorph
    (period : Real) (hPeriod : period ≠ 0) :
    EffectiveJanusSpacetime period hPeriod ≃ₜ
      EffectiveJanusSpacetime period hPeriod where
  toFun := reflectedSpherePT period hPeriod
  invFun := reflectedSpherePT period hPeriod
  left_inv := reflectedSpherePT_involutive period hPeriod
  right_inv := reflectedSpherePT_involutive period hPeriod
  continuous_toFun := continuous_reflectedSpherePT period hPeriod
  continuous_invFun := continuous_reflectedSpherePT period hPeriod

/-- The effective D8 spacetime with its actual PT map and any explicitly
PT-invariant Borel measure.  No canonical volume measure is assumed here. -/
def effectiveD8MeasuredPTBase
    (period : Real) (hPeriod : period ≠ 0)
    [MeasurableSpace (EffectiveJanusSpacetime period hPeriod)]
    [BorelSpace (EffectiveJanusSpacetime period hPeriod)]
    (mu : Measure (EffectiveJanusSpacetime period hPeriod))
    (hMu : MeasurePreserving
      (effectiveD8SpacetimePTHomeomorph period hPeriod).toMeasurableEquiv
      mu mu) :
    MeasuredPTBase (EffectiveJanusSpacetime period hPeriod) where
  measure := mu
  pt := (effectiveD8SpacetimePTHomeomorph period hPeriod).toMeasurableEquiv
  pt_involutive := reflectedSpherePT_involutive period hPeriod
  pt_measurePreserving := hMu

/-- The metric-field space on the same effective D8 mapping-torus spacetime
used by the global field bridge. -/
abbrev EffectiveD8PTMetricField
    (period : Real) (hPeriod : period ≠ 0) :=
  PTMetricField (EffectiveJanusSpacetime period hPeriod)

/-- Tangent fields on the effective D8 mapping-torus spacetime. -/
abbrev EffectiveD8MetricPairFieldVariation
    (period : Real) (hPeriod : period ≠ 0) :=
  MetricPairFieldVariation (EffectiveJanusSpacetime period hPeriod)

end

end P0EFTJanusIntegratedMinkowskiInteractionOpenDomain4D
end JanusFormal
