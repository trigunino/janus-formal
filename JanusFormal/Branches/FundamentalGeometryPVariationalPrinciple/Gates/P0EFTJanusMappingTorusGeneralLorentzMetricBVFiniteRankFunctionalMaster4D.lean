import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D

/-!
# A genuine finite-rank nonlocal BV functional for general metric tensors

The canonical integrated tensor pairing defines a global moment of the
antifield.  Squaring one such moment gives a genuinely nonlocal functional:
its value depends on an integral over the whole spacetime.  This gate proves
its exact affine derivative, packages its actual functional gradients,
constructs the generated square-zero Hamiltonian vector field and proves the
functional classical master equation.

This is a rank-one nonlocal model.  Derivative-dependent kernels and completed
spaces of arbitrary functionals remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricBVFiniteRankFunctionalMaster4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators Topology
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-! ## The integrated pairing is an honest bilinear form -/

theorem canonicalGeneralMetricTensorPairPairing_symmetric
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) :
    canonicalGeneralMetricTensorPairPairing period hPeriod metrics first second =
      canonicalGeneralMetricTensorPairPairing period hPeriod metrics second first := by
  unfold canonicalGeneralMetricTensorPairPairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    generalMetricTensorPairPairingAt_symmetric
      period hPeriod metrics first second point

theorem canonicalGeneralMetricTensorPairPairing_add_left
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothGeneralMetricTensorPair period hPeriod) :
    canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        (smoothGeneralMetricTensorPairAdd period hPeriod first second) third =
      canonicalGeneralMetricTensorPairPairing period hPeriod metrics first third +
        canonicalGeneralMetricTensorPairPairing period hPeriod metrics second third := by
  unfold canonicalGeneralMetricTensorPairPairing
  simp_rw [generalMetricTensorPairPairingAt_add_left]
  exact integral_add
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics first third)
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics second third)

theorem canonicalGeneralMetricTensorPairPairing_add_right
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothGeneralMetricTensorPair period hPeriod) :
    canonicalGeneralMetricTensorPairPairing period hPeriod metrics first
        (smoothGeneralMetricTensorPairAdd period hPeriod second third) =
      canonicalGeneralMetricTensorPairPairing period hPeriod metrics first second +
        canonicalGeneralMetricTensorPairPairing period hPeriod metrics first third := by
  rw [canonicalGeneralMetricTensorPairPairing_symmetric
      period hPeriod metrics first,
    canonicalGeneralMetricTensorPairPairing_add_left,
    canonicalGeneralMetricTensorPairPairing_symmetric
      period hPeriod metrics second,
    canonicalGeneralMetricTensorPairPairing_symmetric
      period hPeriod metrics third]

theorem canonicalGeneralMetricTensorPairPairing_smul_left
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) :
    canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        (smoothGeneralMetricTensorPairSMul period hPeriod scalar first) second =
      scalar * canonicalGeneralMetricTensorPairPairing
        period hPeriod metrics first second := by
  unfold canonicalGeneralMetricTensorPairPairing
  simp_rw [generalMetricTensorPairPairingAt_smul_left]
  rw [integral_const_mul]

theorem canonicalGeneralMetricTensorPairPairing_smul_right
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) :
    canonicalGeneralMetricTensorPairPairing period hPeriod metrics first
        (smoothGeneralMetricTensorPairSMul period hPeriod scalar second) =
      scalar * canonicalGeneralMetricTensorPairPairing
        period hPeriod metrics first second := by
  rw [canonicalGeneralMetricTensorPairPairing_symmetric
      period hPeriod metrics first,
    canonicalGeneralMetricTensorPairPairing_smul_left,
    canonicalGeneralMetricTensorPairPairing_symmetric
      period hPeriod metrics second]

@[simp]
theorem canonicalGeneralMetricTensorPairPairing_zero_left
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (second : SmoothGeneralMetricTensorPair period hPeriod) :
    canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        (smoothGeneralMetricTensorPairZero period hPeriod) second = 0 := by
  unfold canonicalGeneralMetricTensorPairPairing
  simp

@[simp]
theorem canonicalGeneralMetricTensorPairPairing_zero_right
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first : SmoothGeneralMetricTensorPair period hPeriod) :
    canonicalGeneralMetricTensorPairPairing period hPeriod metrics first
        (smoothGeneralMetricTensorPairZero period hPeriod) = 0 := by
  rw [canonicalGeneralMetricTensorPairPairing_symmetric]
  exact canonicalGeneralMetricTensorPairPairing_zero_left
    period hPeriod metrics first

/-! ## Certified functional observables -/

/-- A functional observable whose displayed gradients are certified by its
directional derivative along every smooth affine BV line. -/
structure GeneralMetricBVFunctionalObservable
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) where
  parity : FiniteBVParity
  value : SmoothGeneralMetricBVField period hPeriod → Real
  fieldGradient : SmoothGeneralMetricBVField period hPeriod →
    SmoothGeneralMetricTensorPair period hPeriod
  antifieldGradient : SmoothGeneralMetricBVField period hPeriod →
    SmoothGeneralMetricTensorPair period hPeriod
  hasDerivAt : ∀ phase variation,
    HasDerivAt
      (fun parameter : Real => value
        (smoothGeneralMetricBVAffineLine
          period hPeriod phase variation parameter))
      (canonicalGeneralMetricTensorPairPairing period hPeriod metrics
          (fieldGradient phase) variation.1 +
        canonicalGeneralMetricTensorPairPairing period hPeriod metrics
          (antifieldGradient phase) variation.2)
      0

/-- Odd antibracket defined from certified functional gradients, rather than
by integrating an independently declared pointwise bracket. -/
def generalMetricBVFunctionalOddAntibracket
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVFunctionalObservable
      period hPeriod metrics)
    (phase : SmoothGeneralMetricBVField period hPeriod) : Real :=
  canonicalGeneralMetricTensorPairPairing period hPeriod metrics
      (first.fieldGradient phase) (second.antifieldGradient phase) -
    finiteBVOddKoszulSign first.parity second.parity *
      canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        (second.fieldGradient phase) (first.antifieldGradient phase)

theorem generalMetricBVFunctionalOddAntibracket_graded_skew
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVFunctionalObservable
      period hPeriod metrics)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    generalMetricBVFunctionalOddAntibracket period hPeriod metrics
        first second phase =
      -finiteBVOddKoszulSign first.parity second.parity *
        generalMetricBVFunctionalOddAntibracket period hPeriod metrics
          second first phase := by
  rcases first with ⟨firstParity, firstValue, firstField, firstAntifield, firstDeriv⟩
  rcases second with
    ⟨secondParity, secondValue, secondField, secondAntifield, secondDeriv⟩
  have hFirst := canonicalGeneralMetricTensorPairPairing_symmetric
    period hPeriod metrics (firstField phase) (secondAntifield phase)
  have hSecond := canonicalGeneralMetricTensorPairPairing_symmetric
    period hPeriod metrics (secondField phase) (firstAntifield phase)
  cases firstParity <;> cases secondParity <;>
    simp only [generalMetricBVFunctionalOddAntibracket,
      finiteBVOddKoszulSign] at * <;> linarith

/-! ## Certified integrated ultralocal functional -/

/-- The existing integrated ultralocal master action, now packaged with its
globally certified affine derivative and actual functional gradients. -/
def canonicalGeneralLorentzMetricBVUltralocalMasterFunctionalObservable
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    GeneralMetricBVFunctionalObservable period hPeriod metrics where
  parity := .even
  value := canonicalGeneralLorentzMetricBVUltralocalMasterAction
    period hPeriod metrics
  fieldGradient := fun _ =>
    smoothGeneralMetricTensorPairZero period hPeriod
  antifieldGradient := fun phase => phase.2
  hasDerivAt := by
    intro phase variation
    have hDerivative :=
      canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_hasDerivAt_unconditional
        period hPeriod metrics phase variation
    convert hDerivative using 1
    · ext parameter
      rfl
    · rw [canonicalGeneralMetricTensorPairPairing_zero_left, zero_add]
      rfl

/-- Functional CME certified from the global gradients of the integrated
ultralocal action. -/
theorem canonicalGeneralLorentzMetricBVUltralocalMaster_functional_CME
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    generalMetricBVFunctionalOddAntibracket period hPeriod metrics
        (canonicalGeneralLorentzMetricBVUltralocalMasterFunctionalObservable
          period hPeriod metrics)
        (canonicalGeneralLorentzMetricBVUltralocalMasterFunctionalObservable
          period hPeriod metrics)
        phase = 0 := by
  simp [generalMetricBVFunctionalOddAntibracket,
    canonicalGeneralLorentzMetricBVUltralocalMasterFunctionalObservable]

/-! ## A rank-one nonlocal master functional -/

/-- Global antifield moment selected by a fixed smooth tensor kernel. -/
def generalMetricBVFiniteRankMoment
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) : Real :=
  canonicalGeneralMetricTensorPairPairing period hPeriod metrics kernel phase.2

/-- Rank-one nonlocal master action `1/2 (∫⟨K,h⁺⟩)²`. -/
def generalMetricBVFiniteRankFunctionalMasterAction
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) : Real :=
  (1 / 2 : Real) *
    generalMetricBVFiniteRankMoment period hPeriod metrics kernel phase ^ 2

theorem generalMetricBVFiniteRankMoment_affine
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (parameter : Real) :
    generalMetricBVFiniteRankMoment period hPeriod metrics kernel
        (smoothGeneralMetricBVAffineLine
          period hPeriod phase variation parameter) =
      generalMetricBVFiniteRankMoment period hPeriod metrics kernel phase +
        parameter * canonicalGeneralMetricTensorPairPairing
          period hPeriod metrics kernel variation.2 := by
  change canonicalGeneralMetricTensorPairPairing period hPeriod metrics kernel
      (smoothGeneralMetricTensorPairAffineLine
        period hPeriod phase.2 variation.2 parameter) = _
  unfold smoothGeneralMetricTensorPairAffineLine
  rw [canonicalGeneralMetricTensorPairPairing_add_right,
    canonicalGeneralMetricTensorPairPairing_smul_right]
  rfl

theorem generalMetricBVFiniteRankFunctionalMasterAction_affine_expansion
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (parameter : Real) :
    generalMetricBVFiniteRankFunctionalMasterAction period hPeriod metrics kernel
        (smoothGeneralMetricBVAffineLine
          period hPeriod phase variation parameter) =
      generalMetricBVFiniteRankFunctionalMasterAction
          period hPeriod metrics kernel phase +
        parameter *
          (generalMetricBVFiniteRankMoment period hPeriod metrics kernel phase *
            canonicalGeneralMetricTensorPairPairing
              period hPeriod metrics kernel variation.2) +
        parameter ^ 2 / 2 *
          canonicalGeneralMetricTensorPairPairing
            period hPeriod metrics kernel variation.2 ^ 2 := by
  unfold generalMetricBVFiniteRankFunctionalMasterAction
  rw [generalMetricBVFiniteRankMoment_affine]
  ring

theorem generalMetricBVFiniteRankFunctionalMasterAction_affine_hasDerivAt
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod) :
    HasDerivAt
      (fun parameter : Real =>
        generalMetricBVFiniteRankFunctionalMasterAction
          period hPeriod metrics kernel
          (smoothGeneralMetricBVAffineLine
            period hPeriod phase variation parameter))
      (generalMetricBVFiniteRankMoment period hPeriod metrics kernel phase *
        canonicalGeneralMetricTensorPairPairing
          period hPeriod metrics kernel variation.2)
      0 := by
  let firstVariation :=
    generalMetricBVFiniteRankMoment period hPeriod metrics kernel phase *
      canonicalGeneralMetricTensorPairPairing
        period hPeriod metrics kernel variation.2
  let quadraticRemainder :=
    canonicalGeneralMetricTensorPairPairing
      period hPeriod metrics kernel variation.2 ^ 2
  have hLinear : HasDerivAt
      (fun parameter : Real => parameter * firstVariation) firstVariation 0 := by
    simpa using (hasDerivAt_id (x := (0 : Real))).mul_const firstVariation
  have hQuadratic : HasDerivAt
      (fun parameter : Real =>
        parameter ^ 2 / 2 * quadraticRemainder) 0 0 := by
    simpa [id] using
      (((hasDerivAt_id (x := (0 : Real))).pow 2).div_const 2).mul_const
        quadraticRemainder
  have hPolynomial : HasDerivAt
      (fun parameter : Real =>
        generalMetricBVFiniteRankFunctionalMasterAction
            period hPeriod metrics kernel phase +
          parameter * firstVariation +
          parameter ^ 2 / 2 * quadraticRemainder)
      firstVariation 0 := by
    exact ((hLinear.const_add
      (generalMetricBVFiniteRankFunctionalMasterAction
        period hPeriod metrics kernel phase)).add hQuadratic).congr_deriv (by simp)
  refine hPolynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  intro parameter
  simpa [firstVariation, quadraticRemainder] using
    (generalMetricBVFiniteRankFunctionalMasterAction_affine_expansion
      period hPeriod metrics kernel phase variation parameter)

/-- The rank-one action with its actual global functional gradients. -/
def generalMetricBVFiniteRankFunctionalMasterObservable
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod) :
    GeneralMetricBVFunctionalObservable period hPeriod metrics where
  parity := .even
  value := generalMetricBVFiniteRankFunctionalMasterAction
    period hPeriod metrics kernel
  fieldGradient := fun _ =>
    smoothGeneralMetricTensorPairZero period hPeriod
  antifieldGradient := fun phase =>
    smoothGeneralMetricTensorPairSMul period hPeriod
      (generalMetricBVFiniteRankMoment period hPeriod metrics kernel phase) kernel
  hasDerivAt := by
    intro phase variation
    have hDerivative :=
      generalMetricBVFiniteRankFunctionalMasterAction_affine_hasDerivAt
        period hPeriod metrics kernel phase variation
    convert hDerivative using 1
    rw [canonicalGeneralMetricTensorPairPairing_zero_left, zero_add,
      canonicalGeneralMetricTensorPairPairing_smul_left]

/-- Functional CME: the certified field gradient is zero, so the genuine
functional antibracket of the nonlocal master action with itself vanishes. -/
theorem generalMetricBVFiniteRankFunctionalMaster_CME
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    generalMetricBVFunctionalOddAntibracket period hPeriod metrics
        (generalMetricBVFiniteRankFunctionalMasterObservable
          period hPeriod metrics kernel)
        (generalMetricBVFiniteRankFunctionalMasterObservable
          period hPeriod metrics kernel)
        phase = 0 := by
  simp [generalMetricBVFunctionalOddAntibracket,
    generalMetricBVFiniteRankFunctionalMasterObservable]

/-- Hamiltonian vector generated by the rank-one functional. -/
def generalMetricBVFiniteRankFunctionalBRST
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    SmoothGeneralMetricBVField period hPeriod :=
  (smoothGeneralMetricTensorPairSMul period hPeriod
      (generalMetricBVFiniteRankMoment period hPeriod metrics kernel phase) kernel,
    smoothGeneralMetricTensorPairZero period hPeriod)

theorem generalMetricBVFiniteRankFunctionalMaster_generates_BRST
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    ((generalMetricBVFiniteRankFunctionalMasterObservable
        period hPeriod metrics kernel).antifieldGradient phase,
      (generalMetricBVFiniteRankFunctionalMasterObservable
        period hPeriod metrics kernel).fieldGradient phase) =
      generalMetricBVFiniteRankFunctionalBRST
        period hPeriod metrics kernel phase :=
  rfl

/-- The generated rank-one Hamiltonian vector field is explicitly
square-zero: after one application its antifield component vanishes. -/
theorem generalMetricBVFiniteRankFunctionalBRST_square_zero
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (kernel : SmoothGeneralMetricTensorPair period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    generalMetricBVFiniteRankFunctionalBRST period hPeriod metrics kernel
        (generalMetricBVFiniteRankFunctionalBRST
          period hPeriod metrics kernel phase) =
      (smoothGeneralMetricTensorPairZero period hPeriod,
        smoothGeneralMetricTensorPairZero period hPeriod) := by
  rw [generalMetricBVFiniteRankFunctionalBRST]
  have hMoment :
      generalMetricBVFiniteRankMoment period hPeriod metrics kernel
          (generalMetricBVFiniteRankFunctionalBRST
            period hPeriod metrics kernel phase) = 0 := by
    simp [generalMetricBVFiniteRankMoment,
      generalMetricBVFiniteRankFunctionalBRST]
  rw [hMoment]
  apply Prod.ext
  · apply Prod.ext
    · apply SmoothSymmetricCovariantTwoTensor.ext
      apply ContMDiffSection.ext
      intro point
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      change (0 : Real) * kernel.1.tensor point first second = 0
      norm_num
    · apply SmoothSymmetricCovariantTwoTensor.ext
      apply ContMDiffSection.ext
      intro point
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      change (0 : Real) * kernel.2.tensor point first second = 0
      norm_num
  · rfl

/-! ## Explicit intrinsic nonzero witness -/

@[simp]
theorem intrinsicGeneralMetricTensorPairWitness_pairingAt_eq_eight
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod
        (intrinsicGeneralLorentzMetricPair period hPeriod)
        (intrinsicGeneralMetricTensorPairWitness period hPeriod)
        (intrinsicGeneralMetricTensorPairWitness period hPeriod) point = 8 := by
  unfold generalMetricTensorPairPairingAt
    intrinsicGeneralLorentzMetricPair
    intrinsicGeneralMetricTensorPairWitness
  rw [generalMetricTensorPairingAt_metric_self]
  norm_num

theorem generalMetricBVFiniteRankMoment_intrinsic_witness :
    generalMetricBVFiniteRankMoment period hPeriod
        (intrinsicGeneralLorentzMetricPair period hPeriod)
        (intrinsicGeneralMetricTensorPairWitness period hPeriod)
        (intrinsicGeneralMetricBVPhaseWitness period hPeriod) =
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod Set.univ).toReal * 8 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  unfold generalMetricBVFiniteRankMoment
    intrinsicGeneralMetricBVPhaseWitness
    canonicalGeneralMetricTensorPairPairing
  calc
    ∫ point, generalMetricTensorPairPairingAt period hPeriod
          (intrinsicGeneralLorentzMetricPair period hPeriod)
          (intrinsicGeneralMetricTensorPairWitness period hPeriod)
          (intrinsicGeneralMetricTensorPairWitness period hPeriod) point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
        ∫ _point, (8 : Real)
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
            apply integral_congr_ae
            filter_upwards [] with point
            exact intrinsicGeneralMetricTensorPairWitness_pairingAt_eq_eight
              period hPeriod point
    _ = _ := by simp [measureReal_def]

theorem generalMetricBVFiniteRankMoment_intrinsic_witness_ne_zero :
    generalMetricBVFiniteRankMoment period hPeriod
        (intrinsicGeneralLorentzMetricPair period hPeriod)
        (intrinsicGeneralMetricTensorPairWitness period hPeriod)
        (intrinsicGeneralMetricBVPhaseWitness period hPeriod) ≠ 0 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  rw [generalMetricBVFiniteRankMoment_intrinsic_witness]
  exact mul_ne_zero
    (ENNReal.toReal_ne_zero.2
      ⟨(Measure.measure_univ_ne_zero).2
        (intrinsicCanonicalLorentzVolumeMeasure_ne_zero period hPeriod),
        measure_ne_top _ _⟩)
    (by norm_num)

theorem generalMetricBVFiniteRankFunctionalMasterAction_intrinsic_witness_ne_zero :
    generalMetricBVFiniteRankFunctionalMasterAction period hPeriod
        (intrinsicGeneralLorentzMetricPair period hPeriod)
        (intrinsicGeneralMetricTensorPairWitness period hPeriod)
        (intrinsicGeneralMetricBVPhaseWitness period hPeriod) ≠ 0 := by
  unfold generalMetricBVFiniteRankFunctionalMasterAction
  exact mul_ne_zero (by norm_num)
    (pow_ne_zero 2
      (generalMetricBVFiniteRankMoment_intrinsic_witness_ne_zero
        period hPeriod))

end

end P0EFTJanusMappingTorusGeneralLorentzMetricBVFiniteRankFunctionalMaster4D
end JanusFormal
