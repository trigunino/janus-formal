import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

/-!
# Integrated ultralocal BV master Hamiltonian for general Lorentz metrics

The bulk pointwise metric BV Hamiltonian and its represented odd bracket are
integrated against the canonical finite Lorentz-volume measure.  The exact
`L¹` obligations and a sufficient global continuity contract are explicit.
Affine polarization gives the true derivative of this ultralocal functional,
and preservation of the canonical measure gives PT/exchange covariance.
No derivative-dependent term or general functional CME is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators Topology
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Exact regularity boundary -/

/-- Exact `L¹` obligation for one background-raised two-sector pairing. -/
abbrev GeneralMetricTensorPairPairingL1
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) : Prop :=
  Integrable
    (fun point : EffectiveQuotient period hPeriod =>
      generalMetricTensorPairPairingAt period hPeriod metrics
        first second point)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Sufficient global regularity contract for the fibrewise inverse-metric
pairing attached to fixed genuine background metrics. -/
abbrev GeneralMetricInversePairingContinuityContract
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) : Prop :=
  ∀ first second : SmoothGeneralMetricTensorPair period hPeriod,
    Continuous
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricTensorPairPairingAt period hPeriod metrics
          first second point)

theorem generalMetricTensorPairPairingL1_of_continuous
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod)
    (hContinuous : Continuous
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricTensorPairPairingAt period hPeriod metrics
          first second point)) :
    GeneralMetricTensorPairPairingL1 period hPeriod metrics first second := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricTensorPairPairingAt period hPeriod metrics
          first second point))

theorem generalMetricTensorPairPairingL1_of_continuityContract
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (hRegularity : GeneralMetricInversePairingContinuityContract
      period hPeriod metrics)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) :
    GeneralMetricTensorPairPairingL1
      period hPeriod metrics first second :=
  generalMetricTensorPairPairingL1_of_continuous period hPeriod metrics
    first second (hRegularity first second)

theorem generalLorentzMetricBVUltralocalMasterActionDensity_integrable
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (hPairing : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      phase.2 phase.2) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        generalLorentzMetricBVUltralocalMasterActionAt
          period hPeriod metrics phase point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  simpa only [generalLorentzMetricBVUltralocalMasterActionAt] using
    hPairing.const_mul (1 / 2 : Real)

theorem generalLorentzMetricBVUltralocalMasterActionDensity_integrable_of_contract
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (hRegularity : GeneralMetricInversePairingContinuityContract
      period hPeriod metrics)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        generalLorentzMetricBVUltralocalMasterActionAt
          period hPeriod metrics phase point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  generalLorentzMetricBVUltralocalMasterActionDensity_integrable
    period hPeriod metrics phase
      (generalMetricTensorPairPairingL1_of_continuityContract
        period hPeriod metrics hRegularity _ _)

theorem generalMetricBVOddAntibracketDensity_integrable
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (hForward : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      (first.fieldGradient phase) (second.antifieldGradient phase))
    (hBackward : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      (second.fieldGradient phase) (first.antifieldGradient phase)) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricBVOddAntibracketAt period hPeriod metrics
          first second phase point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  refine (hForward.sub
    (hBackward.const_mul
      (finiteBVOddKoszulSign first.parity second.parity))).congr ?_
  filter_upwards [] with point
  rfl

theorem generalMetricBVOddAntibracketDensity_integrable_of_contract
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (hRegularity : GeneralMetricInversePairingContinuityContract
      period hPeriod metrics)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricBVOddAntibracketAt period hPeriod metrics
          first second phase point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  generalMetricBVOddAntibracketDensity_integrable period hPeriod metrics
    first second phase
    (generalMetricTensorPairPairingL1_of_continuityContract
      period hPeriod metrics hRegularity _ _)
    (generalMetricTensorPairPairingL1_of_continuityContract
      period hPeriod metrics hRegularity _ _)

/-! ## Integrated action, first variation, and represented bracket -/

def canonicalGeneralMetricTensorPairPairing
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) : Real :=
  ∫ point, generalMetricTensorPairPairingAt period hPeriod metrics
      first second point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

def canonicalGeneralLorentzMetricBVUltralocalMasterAction
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) : Real :=
  ∫ point, generalLorentzMetricBVUltralocalMasterActionAt
      period hPeriod metrics phase point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Integrated pairing selected by the declared antifield gradient. -/
def canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod) : Real :=
  canonicalGeneralMetricTensorPairPairing period hPeriod metrics
    phase.2 variation.2

/-- Integrated action along the actual affine line in the full linear BV
phase space. -/
def canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (parameter : Real) : Real :=
  canonicalGeneralLorentzMetricBVUltralocalMasterAction period hPeriod metrics
    (smoothGeneralMetricBVAffineLine
      period hPeriod phase variation parameter)

/-- Integral of the represented pointwise odd bracket.  This is not a
general functional BV antibracket. -/
def canonicalGeneralMetricBVOddAntibracket
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) : Real :=
  ∫ point, generalMetricBVOddAntibracketAt period hPeriod metrics
      first second phase point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Exact integrated quadratic formula under precisely the base, crossed,
and quadratic-remainder `L¹` hypotheses. -/
theorem canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_expansion
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (parameter : Real)
    (hBase : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      phase.2 phase.2)
    (hCross : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      phase.2 variation.2)
    (hVariation : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      variation.2 variation.2) :
    canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine
        period hPeriod metrics phase variation parameter =
      canonicalGeneralLorentzMetricBVUltralocalMasterAction
          period hPeriod metrics phase +
        parameter *
          canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation
            period hPeriod metrics phase variation +
        parameter ^ 2 / 2 *
          canonicalGeneralMetricTensorPairPairing period hPeriod metrics
            variation.2 variation.2 := by
  have hBaseAction :=
    generalLorentzMetricBVUltralocalMasterActionDensity_integrable
      period hPeriod metrics phase hBase
  unfold canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine
    canonicalGeneralLorentzMetricBVUltralocalMasterAction
    canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation
    canonicalGeneralMetricTensorPairPairing
  simp_rw [generalLorentzMetricBVUltralocalMasterActionAt_affine_expansion
    period hPeriod metrics phase variation]
  calc
    _ =
      (∫ point,
          generalLorentzMetricBVUltralocalMasterActionAt
              period hPeriod metrics phase point +
            parameter * generalMetricTensorPairPairingAt
              period hPeriod metrics phase.2 variation.2 point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
        ∫ point, parameter ^ 2 / 2 *
            generalMetricTensorPairPairingAt period hPeriod metrics
              variation.2 variation.2 point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
            apply integral_add
            · exact hBaseAction.add (hCross.const_mul parameter)
            · exact hVariation.const_mul (parameter ^ 2 / 2)
    _ =
      ((∫ point,
          generalLorentzMetricBVUltralocalMasterActionAt
            period hPeriod metrics phase point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
        ∫ point, parameter * generalMetricTensorPairPairingAt
            period hPeriod metrics phase.2 variation.2 point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
        ∫ point, parameter ^ 2 / 2 *
            generalMetricTensorPairPairingAt period hPeriod metrics
              variation.2 variation.2 point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
            congr 1
            exact integral_add hBaseAction (hCross.const_mul parameter)
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

/-- The integrated affine polynomial gives the actual derivative of the
ultralocal bulk functional. -/
theorem canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_hasDerivAt
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (hBase : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      phase.2 phase.2)
    (hCross : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      phase.2 variation.2)
    (hVariation : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      variation.2 variation.2) :
    HasDerivAt
      (canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine
        period hPeriod metrics phase variation)
      (canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation
        period hPeriod metrics phase variation)
      0 := by
  let firstVariation :=
    canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation
      period hPeriod metrics phase variation
  let quadraticRemainder :=
    canonicalGeneralMetricTensorPairPairing period hPeriod metrics
      variation.2 variation.2
  have hLinear : HasDerivAt
      (fun parameter : Real => parameter * firstVariation) firstVariation 0 := by
    simpa using
      (hasDerivAt_id (x := (0 : Real))).mul_const firstVariation
  have hQuadratic : HasDerivAt
      (fun parameter : Real =>
        parameter ^ 2 / 2 * quadraticRemainder) 0 0 := by
    simpa [id] using
      (((hasDerivAt_id (x := (0 : Real))).pow 2).div_const 2).mul_const
        quadraticRemainder
  have hPolynomial : HasDerivAt
      (fun parameter : Real =>
        canonicalGeneralLorentzMetricBVUltralocalMasterAction
            period hPeriod metrics phase +
          parameter * firstVariation +
          parameter ^ 2 / 2 * quadraticRemainder)
      firstVariation 0 := by
    have hRaw :=
      (hLinear.const_add
        (canonicalGeneralLorentzMetricBVUltralocalMasterAction
          period hPeriod metrics phase)).add hQuadratic
    refine (hRaw.congr_deriv (by simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    intro parameter
    rfl
  refine hPolynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  intro parameter
  simpa [firstVariation, quadraticRemainder] using
    (canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_expansion
      period hPeriod metrics phase variation parameter
      hBase hCross hVariation)

theorem canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation_eq_gradient
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod) :
    canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation
        period hPeriod metrics phase variation =
      canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        ((generalLorentzMetricBVUltralocalMasterObservable
          period hPeriod metrics).antifieldGradient phase)
        variation.2 :=
  rfl

/-- Derivative stated directly against the declared BV antifield gradient. -/
theorem canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_hasDerivAt_gradient
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (hBase : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      phase.2 phase.2)
    (hCross : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      phase.2 variation.2)
    (hVariation : GeneralMetricTensorPairPairingL1 period hPeriod metrics
      variation.2 variation.2) :
    HasDerivAt
      (canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine
        period hPeriod metrics phase variation)
      (canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        ((generalLorentzMetricBVUltralocalMasterObservable
          period hPeriod metrics).antifieldGradient phase)
        variation.2)
      0 := by
  exact canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_hasDerivAt
    period hPeriod metrics phase variation hBase hCross hVariation

/-! ## PT/exchange covariance and integrated CME -/

theorem canonicalGeneralLorentzMetricBVUltralocalMasterAction_ptExchange
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    canonicalGeneralLorentzMetricBVUltralocalMasterAction period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (smoothGeneralMetricBVPTExchange period hPeriod phase) =
      canonicalGeneralLorentzMetricBVUltralocalMasterAction
        period hPeriod metrics phase := by
  unfold canonicalGeneralLorentzMetricBVUltralocalMasterAction
  calc
    (∫ point, generalLorentzMetricBVUltralocalMasterActionAt period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, generalLorentzMetricBVUltralocalMasterActionAt
          period hPeriod metrics phase
          (reflectedSpherePT period hPeriod point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (generalLorentzMetricBVUltralocalMasterActionAt_ptExchange
              period hPeriod metrics phase)
    _ = _ :=
      intrinsicCanonicalLorentzVolumeMeasure_integral_pt period hPeriod
        (generalLorentzMetricBVUltralocalMasterActionAt
          period hPeriod metrics phase)

theorem canonicalGeneralMetricBVOddAntibracket_ptExchange
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    canonicalGeneralMetricBVOddAntibracket period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (generalMetricBVPointObservablePTExchange period hPeriod first)
        (generalMetricBVPointObservablePTExchange period hPeriod second)
        (smoothGeneralMetricBVPTExchange period hPeriod phase) =
      canonicalGeneralMetricBVOddAntibracket period hPeriod metrics
        first second phase := by
  unfold canonicalGeneralMetricBVOddAntibracket
  calc
    (∫ point, generalMetricBVOddAntibracketAt period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (generalMetricBVPointObservablePTExchange period hPeriod first)
        (generalMetricBVPointObservablePTExchange period hPeriod second)
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, generalMetricBVOddAntibracketAt period hPeriod metrics
          first second phase (reflectedSpherePT period hPeriod point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (generalMetricBVOddAntibracketAt_ptExchange
              period hPeriod metrics first second phase)
    _ = _ :=
      intrinsicCanonicalLorentzVolumeMeasure_integral_pt period hPeriod
        (fun point => generalMetricBVOddAntibracketAt period hPeriod metrics
          first second phase point)

/-- Integrated CME for the represented ultralocal bulk master observable. -/
theorem canonicalGeneralLorentzMetricBVUltralocalMaster_integrated_CME
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    canonicalGeneralMetricBVOddAntibracket period hPeriod metrics
        (generalLorentzMetricBVUltralocalMasterObservable period hPeriod metrics)
        (generalLorentzMetricBVUltralocalMasterObservable period hPeriod metrics)
        phase = 0 := by
  unfold canonicalGeneralMetricBVOddAntibracket
  simp only [generalLorentzMetricBVUltralocalMaster_classical_master_equation,
    integral_zero]

theorem canonicalGeneralLorentzMetricBVUltralocalMaster_integrated_CME_ptExchange
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    canonicalGeneralMetricBVOddAntibracket period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (generalMetricBVPointObservablePTExchange period hPeriod
          (generalLorentzMetricBVUltralocalMasterObservable
            period hPeriod metrics))
        (generalMetricBVPointObservablePTExchange period hPeriod
          (generalLorentzMetricBVUltralocalMasterObservable
            period hPeriod metrics))
        (smoothGeneralMetricBVPTExchange period hPeriod phase) = 0 := by
  rw [canonicalGeneralMetricBVOddAntibracket_ptExchange]
  exact canonicalGeneralLorentzMetricBVUltralocalMaster_integrated_CME
    period hPeriod metrics phase

end

end P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
end JanusFormal
