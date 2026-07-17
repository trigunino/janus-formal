import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D

/-!
# Integrated intrinsic BV pairing on the physical throat

The inverse-metric pairing and odd bracket from the pointwise intrinsic throat
gate are integrated against the canonical finite throat measure.  Since the
pointwise inverse was constructed fibrewise and has not yet been promoted to a
smooth inverse bundle field, its exact minimal `L¹` obligation is isolated as
`IntrinsicThroatTensorPairPairingL1`.  A single global continuity contract is
also recorded as a sufficient geometric route to every required `L¹` fact.

The canonical ultralocal action and represented odd bracket are PT/exchange
covariant, and the contractible master observable satisfies the integrated CME.
The exact pointwise polarization gives an integrated quadratic line formula
under three explicit `L¹` hypotheses and hence the true `HasDerivAt` of this
ultralocal action, identified with its integrated antifield-gradient pairing.
No derivative-dependent term, general functional antibracket, or general
functional CME is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVPTCovariance4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-! ## Exact regularity boundary -/

/-- Exact density-level obligation needed to integrate one inverse-metric
pairing.  `Integrable` packages both a.e. strong measurability and `L¹` control. -/
abbrev IntrinsicThroatTensorPairPairingL1
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) : Prop :=
  Integrable
    (fun point : EffectiveThroat period hPeriod =>
      intrinsicThroatTensorPairPairingAt period hPeriod first second point)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Sufficient global regularity contract: the fibrewise inverse pairing varies
continuously for every pair of genuine smooth throat tensors.  This is exactly
the missing smooth inverse-field interface, not a hidden action assumption. -/
abbrev IntrinsicThroatInversePairingContinuityContract : Prop :=
  ∀ first second : SmoothThroatGeneralMetricTensorPair period hPeriod,
    Continuous
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatTensorPairPairingAt period hPeriod first second point)

theorem intrinsicThroatTensorPairPairingL1_of_continuous
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hContinuous : Continuous
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatTensorPairPairingAt period hPeriod first second point)) :
    IntrinsicThroatTensorPairPairingL1 period hPeriod first second := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatTensorPairPairingAt period hPeriod first second point))

theorem intrinsicThroatTensorPairPairingL1_of_continuityContract
    (hRegularity : IntrinsicThroatInversePairingContinuityContract
      period hPeriod)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    IntrinsicThroatTensorPairPairingL1 period hPeriod first second :=
  intrinsicThroatTensorPairPairingL1_of_continuous period hPeriod first second
    (hRegularity first second)

theorem intrinsicThroatContractibleAntifieldActionDensity_integrable
    (antifield : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hPairing : IntrinsicThroatTensorPairPairingL1 period hPeriod
      antifield antifield) :
    Integrable
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatContractibleAntifieldActionAt period hPeriod
          antifield point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  simpa only [intrinsicThroatContractibleAntifieldActionAt] using
    hPairing.const_mul (1 / 2 : Real)

theorem intrinsicThroatContractibleMasterActionDensity_integrable
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (hPairing : IntrinsicThroatTensorPairPairingL1 period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)) :
    Integrable
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatContractibleMasterActionAt period hPeriod phase point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  simpa only [intrinsicThroatContractibleMasterActionAt] using
    intrinsicThroatContractibleAntifieldActionDensity_integrable
      period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      hPairing

theorem intrinsicThroatContractibleMasterActionDensity_integrable_of_contract
    (hRegularity : IntrinsicThroatInversePairingContinuityContract
      period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    Integrable
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatContractibleMasterActionAt period hPeriod phase point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicThroatContractibleMasterActionDensity_integrable period hPeriod phase
    (intrinsicThroatTensorPairPairingL1_of_continuityContract period hPeriod
      hRegularity _ _)

theorem intrinsicThroatBVOddAntibracketDensity_integrable
    (first second : IntrinsicThroatBVTraceObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (hForward : IntrinsicThroatTensorPairPairingL1 period hPeriod
      (first.fieldGradient phase) (second.antifieldGradient phase))
    (hBackward : IntrinsicThroatTensorPairPairingL1 period hPeriod
      (second.fieldGradient phase) (first.antifieldGradient phase)) :
    Integrable
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatBVOddAntibracketAt period hPeriod
          first second phase point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  refine (hForward.sub
    (hBackward.const_mul
      (finiteBVOddKoszulSign first.parity second.parity))).congr ?_
  filter_upwards [] with point
  rfl

theorem intrinsicThroatBVOddAntibracketDensity_integrable_of_contract
    (hRegularity : IntrinsicThroatInversePairingContinuityContract
      period hPeriod)
    (first second : IntrinsicThroatBVTraceObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    Integrable
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatBVOddAntibracketAt period hPeriod
          first second phase point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicThroatBVOddAntibracketDensity_integrable period hPeriod
    first second phase
    (intrinsicThroatTensorPairPairingL1_of_continuityContract period hPeriod
      hRegularity _ _)
    (intrinsicThroatTensorPairPairingL1_of_continuityContract period hPeriod
      hRegularity _ _)

/-! ## Canonical integrated ultralocal action and odd bracket -/

/-- Canonical integrated inverse-metric pairing of two genuine smooth throat
tensor pairs. -/
def canonicalIntrinsicThroatTensorPairPairing
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) : Real :=
  ∫ point, intrinsicThroatTensorPairPairingAt period hPeriod first second point
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Canonical action as a function of its genuine smooth throat-antifield
argument. -/
def canonicalIntrinsicThroatContractibleAntifieldAction
    (antifield : SmoothThroatGeneralMetricTensorPair period hPeriod) : Real :=
  ∫ point, intrinsicThroatContractibleAntifieldActionAt period hPeriod
      antifield point
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Integrated first variation selected by the declared antifield gradient. -/
def canonicalIntrinsicThroatContractibleMasterFirstVariation
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod) : Real :=
  canonicalIntrinsicThroatTensorPairPairing period hPeriod
    (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2) variation

/-- The integrated master action evaluated on an affine variation of its
genuine smooth throat-antifield argument. -/
def canonicalIntrinsicThroatContractibleMasterAntifieldLine
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (parameter : Real) : Real :=
  canonicalIntrinsicThroatContractibleAntifieldAction period hPeriod
    (smoothThroatGeneralMetricTensorPairAffineLine period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      variation parameter)

/-- Canonical integral of the intrinsic ultralocal contractible action. -/
def canonicalIntrinsicThroatContractibleMasterAction
    (phase : SmoothGeneralMetricBVField period hPeriod) : Real :=
  ∫ point, intrinsicThroatContractibleMasterActionAt period hPeriod phase point
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Integral of the represented pointwise intrinsic odd bracket.  This is an
ultralocal represented bracket, not a general functional BV antibracket. -/
def canonicalIntrinsicThroatBVOddAntibracket
    (first second : IntrinsicThroatBVTraceObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) : Real :=
  ∫ point, intrinsicThroatBVOddAntibracketAt period hPeriod
      first second phase point
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Exact integrated quadratic formula.  The three hypotheses are precisely
the `L¹` obligations for the base, crossed, and quadratic-remainder pairings. -/
theorem canonicalIntrinsicThroatContractibleAntifieldAction_affine_expansion
    (base variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (parameter : Real)
    (hBase : IntrinsicThroatTensorPairPairingL1 period hPeriod base base)
    (hCross : IntrinsicThroatTensorPairPairingL1 period hPeriod base variation)
    (hVariation : IntrinsicThroatTensorPairPairingL1
      period hPeriod variation variation) :
    canonicalIntrinsicThroatContractibleAntifieldAction period hPeriod
        (smoothThroatGeneralMetricTensorPairAffineLine
          period hPeriod base variation parameter) =
      canonicalIntrinsicThroatContractibleAntifieldAction
          period hPeriod base +
        parameter * canonicalIntrinsicThroatTensorPairPairing
          period hPeriod base variation +
        parameter ^ 2 / 2 * canonicalIntrinsicThroatTensorPairPairing
          period hPeriod variation variation := by
  have hBaseAction :=
    intrinsicThroatContractibleAntifieldActionDensity_integrable
      period hPeriod base hBase
  unfold canonicalIntrinsicThroatContractibleAntifieldAction
    canonicalIntrinsicThroatTensorPairPairing
  simp_rw [intrinsicThroatContractibleAntifieldActionAt_affine_expansion
    period hPeriod base variation]
  calc
    _ =
      (∫ point,
          intrinsicThroatContractibleAntifieldActionAt period hPeriod
              base point +
            parameter * intrinsicThroatTensorPairPairingAt
              period hPeriod base variation point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        ∫ point, parameter ^ 2 / 2 *
            intrinsicThroatTensorPairPairingAt
              period hPeriod variation variation point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
            apply integral_add
            · exact hBaseAction.add (hCross.const_mul parameter)
            · exact hVariation.const_mul (parameter ^ 2 / 2)
    _ =
      ((∫ point,
          intrinsicThroatContractibleAntifieldActionAt period hPeriod
            base point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        ∫ point, parameter * intrinsicThroatTensorPairPairingAt
            period hPeriod base variation point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        ∫ point, parameter ^ 2 / 2 *
            intrinsicThroatTensorPairPairingAt
              period hPeriod variation variation point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
            congr 1
            exact integral_add hBaseAction (hCross.const_mul parameter)
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

/-- The integrated affine polynomial gives the actual derivative of the
ultralocal action functional. -/
theorem canonicalIntrinsicThroatContractibleAntifieldAction_affine_hasDerivAt
    (base variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hBase : IntrinsicThroatTensorPairPairingL1 period hPeriod base base)
    (hCross : IntrinsicThroatTensorPairPairingL1 period hPeriod base variation)
    (hVariation : IntrinsicThroatTensorPairPairingL1
      period hPeriod variation variation) :
    HasDerivAt
      (fun parameter : Real =>
        canonicalIntrinsicThroatContractibleAntifieldAction period hPeriod
          (smoothThroatGeneralMetricTensorPairAffineLine
            period hPeriod base variation parameter))
      (canonicalIntrinsicThroatTensorPairPairing
        period hPeriod base variation)
      0 := by
  let firstVariation := canonicalIntrinsicThroatTensorPairPairing
    period hPeriod base variation
  let quadraticRemainder := canonicalIntrinsicThroatTensorPairPairing
    period hPeriod variation variation
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
        canonicalIntrinsicThroatContractibleAntifieldAction
            period hPeriod base +
          parameter * firstVariation +
          parameter ^ 2 / 2 * quadraticRemainder)
      firstVariation 0 := by
    have hRaw :=
      (hLinear.const_add
        (canonicalIntrinsicThroatContractibleAntifieldAction
          period hPeriod base)).add hQuadratic
    refine (hRaw.congr_deriv (by simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    intro parameter
    rfl
  refine hPolynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  intro parameter
  simpa [firstVariation, quadraticRemainder] using
    (canonicalIntrinsicThroatContractibleAntifieldAction_affine_expansion
      period hPeriod base variation parameter hBase hCross hVariation)

theorem canonicalIntrinsicThroatContractibleMasterAntifieldLine_zero
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatContractibleMasterAntifieldLine period hPeriod
        phase variation 0 =
      canonicalIntrinsicThroatContractibleMasterAction period hPeriod phase := by
  unfold canonicalIntrinsicThroatContractibleMasterAntifieldLine
    canonicalIntrinsicThroatContractibleAntifieldAction
    canonicalIntrinsicThroatContractibleMasterAction
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (intrinsicThroatContractibleMasterActionAt_affine_zero
      period hPeriod phase variation)

theorem canonicalIntrinsicThroatContractibleMasterFirstVariation_eq_gradient
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatContractibleMasterFirstVariation period hPeriod
        phase variation =
      canonicalIntrinsicThroatTensorPairPairing period hPeriod
        ((intrinsicThroatContractibleMasterObservable
          period hPeriod).antifieldGradient phase) variation :=
  rfl

/-- Integrated polynomial formula along the actual master-antifield line. -/
theorem canonicalIntrinsicThroatContractibleMasterAntifieldLine_expansion
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (parameter : Real)
    (hBase : IntrinsicThroatTensorPairPairingL1 period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2))
    (hCross : IntrinsicThroatTensorPairPairingL1 period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      variation)
    (hVariation : IntrinsicThroatTensorPairPairingL1
      period hPeriod variation variation) :
    canonicalIntrinsicThroatContractibleMasterAntifieldLine period hPeriod
        phase variation parameter =
      canonicalIntrinsicThroatContractibleMasterAction period hPeriod phase +
        parameter *
          canonicalIntrinsicThroatContractibleMasterFirstVariation
            period hPeriod phase variation +
        parameter ^ 2 / 2 * canonicalIntrinsicThroatTensorPairPairing
          period hPeriod variation variation := by
  simpa [canonicalIntrinsicThroatContractibleMasterAntifieldLine,
    canonicalIntrinsicThroatContractibleMasterFirstVariation,
    canonicalIntrinsicThroatContractibleMasterAction,
    canonicalIntrinsicThroatContractibleAntifieldAction,
    intrinsicThroatContractibleMasterActionAt] using
    (canonicalIntrinsicThroatContractibleAntifieldAction_affine_expansion
      period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      variation parameter hBase hCross hVariation)

/-- True first variation of the integrated master action, identified with the
integrated pairing against its declared antifield gradient. -/
theorem canonicalIntrinsicThroatContractibleMasterAntifieldLine_hasDerivAt
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hBase : IntrinsicThroatTensorPairPairingL1 period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2))
    (hCross : IntrinsicThroatTensorPairPairingL1 period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      variation)
    (hVariation : IntrinsicThroatTensorPairPairingL1
      period hPeriod variation variation) :
    HasDerivAt
      (canonicalIntrinsicThroatContractibleMasterAntifieldLine
        period hPeriod phase variation)
      (canonicalIntrinsicThroatTensorPairPairing period hPeriod
        ((intrinsicThroatContractibleMasterObservable
          period hPeriod).antifieldGradient phase) variation)
      0 := by
  change HasDerivAt
    (fun parameter : Real =>
      canonicalIntrinsicThroatContractibleAntifieldAction period hPeriod
        (smoothThroatGeneralMetricTensorPairAffineLine period hPeriod
          (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
          variation parameter))
    (canonicalIntrinsicThroatTensorPairPairing period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      variation) 0
  exact
    (canonicalIntrinsicThroatContractibleAntifieldAction_affine_hasDerivAt
      period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
      variation hBase hCross hVariation)

theorem canonicalIntrinsicThroatContractibleMasterAction_ptExchange
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    canonicalIntrinsicThroatContractibleMasterAction period hPeriod
        (smoothGeneralMetricBVPTExchange period hPeriod phase) =
      canonicalIntrinsicThroatContractibleMasterAction period hPeriod phase := by
  unfold canonicalIntrinsicThroatContractibleMasterAction
  calc
    (∫ point, intrinsicThroatContractibleMasterActionAt period hPeriod
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, intrinsicThroatContractibleMasterActionAt period hPeriod phase
          (fixedThroatPT period hPeriod point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (intrinsicThroatContractibleMasterActionAt_ptExchange
              period hPeriod phase)
    _ = _ :=
      (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
        period hPeriod).integral_comp'
        (intrinsicThroatContractibleMasterActionAt period hPeriod phase)

/-- Integrated PT/exchange covariance for the odd bracket of genuine bulk
observables after restriction of both Darboux gradients to the throat. -/
theorem canonicalIntrinsicThroatBVOddAntibracket_ptExchange
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    canonicalIntrinsicThroatBVOddAntibracket period hPeriod
        (generalMetricBVPointObservableThroatTrace period hPeriod
          (generalMetricBVPointObservablePTExchange period hPeriod first))
        (generalMetricBVPointObservableThroatTrace period hPeriod
          (generalMetricBVPointObservablePTExchange period hPeriod second))
        (smoothGeneralMetricBVPTExchange period hPeriod phase) =
      canonicalIntrinsicThroatBVOddAntibracket period hPeriod
        (generalMetricBVPointObservableThroatTrace period hPeriod first)
        (generalMetricBVPointObservableThroatTrace period hPeriod second)
        phase := by
  unfold canonicalIntrinsicThroatBVOddAntibracket
  calc
    (∫ point, intrinsicThroatBVOddAntibracketAt period hPeriod
        (generalMetricBVPointObservableThroatTrace period hPeriod
          (generalMetricBVPointObservablePTExchange period hPeriod first))
        (generalMetricBVPointObservableThroatTrace period hPeriod
          (generalMetricBVPointObservablePTExchange period hPeriod second))
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, intrinsicThroatBVOddAntibracketAt period hPeriod
          (generalMetricBVPointObservableThroatTrace period hPeriod first)
          (generalMetricBVPointObservableThroatTrace period hPeriod second)
          phase (fixedThroatPT period hPeriod point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (intrinsicThroatBVOddAntibracketAt_ptExchange
              period hPeriod first second phase)
    _ = _ :=
      (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
        period hPeriod).integral_comp'
        (fun point => intrinsicThroatBVOddAntibracketAt period hPeriod
          (generalMetricBVPointObservableThroatTrace period hPeriod first)
          (generalMetricBVPointObservableThroatTrace period hPeriod second)
          phase point)

/-- Integrated classical master equation for the intrinsic ultralocal
contractible boundary doublet. -/
theorem canonicalIntrinsicThroatContractibleMaster_integrated_CME
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    canonicalIntrinsicThroatBVOddAntibracket period hPeriod
        (intrinsicThroatContractibleMasterObservable period hPeriod)
        (intrinsicThroatContractibleMasterObservable period hPeriod)
        phase = 0 := by
  unfold canonicalIntrinsicThroatBVOddAntibracket
  simp only [intrinsicThroatContractibleMaster_classical_master_equation,
    integral_zero]

theorem canonicalIntrinsicThroatContractibleMaster_integrated_CME_ptExchange
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    canonicalIntrinsicThroatBVOddAntibracket period hPeriod
        (intrinsicThroatContractibleMasterObservable period hPeriod)
        (intrinsicThroatContractibleMasterObservable period hPeriod)
        (smoothGeneralMetricBVPTExchange period hPeriod phase) = 0 :=
  canonicalIntrinsicThroatContractibleMaster_integrated_CME period hPeriod _

end

end P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D
end JanusFormal
