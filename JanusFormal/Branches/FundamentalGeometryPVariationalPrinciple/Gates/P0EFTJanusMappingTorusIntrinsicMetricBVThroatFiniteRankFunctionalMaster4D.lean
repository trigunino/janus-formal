import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricBVThroatPairingRegularity4D

/-!
# A genuine finite-rank BV functional on the intrinsic metric throat

The canonical integrated inverse-metric pairing on the physical throat
defines a global antifield moment.  Squaring one fixed-kernel moment gives a
rank-one nonlocal functional on the genuine smooth throat BV phase space.
This gate proves its affine derivative, certified functional gradients,
functional odd bracket and CME, generated square-zero BRST field, and a
nonzero intrinsic witness.

No completed space of arbitrary functionals or higher-rank kernel expansion
is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicMetricBVThroatFiniteRankFunctionalMaster4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators Topology
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatPairingRegularity4D

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

/-! ## Integrated pairing and affine throat BV space -/

theorem canonicalIntrinsicThroatTensorPairPairing_symmetric
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatTensorPairPairing period hPeriod first second =
      canonicalIntrinsicThroatTensorPairPairing period hPeriod second first := by
  unfold canonicalIntrinsicThroatTensorPairPairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    intrinsicThroatTensorPairPairingAt_symmetric
      period hPeriod first second point

theorem canonicalIntrinsicThroatTensorPairPairing_add_left
    (first second third : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (smoothThroatGeneralMetricTensorPairAdd period hPeriod first second)
        third =
      canonicalIntrinsicThroatTensorPairPairing period hPeriod first third +
        canonicalIntrinsicThroatTensorPairPairing period hPeriod second third := by
  unfold canonicalIntrinsicThroatTensorPairPairing
  simp_rw [intrinsicThroatTensorPairPairingAt_add_left]
  exact integral_add
    (intrinsicThroatTensorPairPairingL1_unconditional
      period hPeriod first third)
    (intrinsicThroatTensorPairPairingL1_unconditional
      period hPeriod second third)

theorem canonicalIntrinsicThroatTensorPairPairing_add_right
    (first second third : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatTensorPairPairing period hPeriod first
        (smoothThroatGeneralMetricTensorPairAdd period hPeriod second third) =
      canonicalIntrinsicThroatTensorPairPairing period hPeriod first second +
        canonicalIntrinsicThroatTensorPairPairing period hPeriod first third := by
  rw [canonicalIntrinsicThroatTensorPairPairing_symmetric
      period hPeriod first,
    canonicalIntrinsicThroatTensorPairPairing_add_left,
    canonicalIntrinsicThroatTensorPairPairing_symmetric
      period hPeriod second,
    canonicalIntrinsicThroatTensorPairPairing_symmetric
      period hPeriod third]

theorem canonicalIntrinsicThroatTensorPairPairing_smul_left
    (scalar : Real)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (smoothThroatGeneralMetricTensorPairSMul
          period hPeriod scalar first) second =
      scalar * canonicalIntrinsicThroatTensorPairPairing
        period hPeriod first second := by
  unfold canonicalIntrinsicThroatTensorPairPairing
  simp_rw [intrinsicThroatTensorPairPairingAt_smul_left]
  rw [integral_const_mul]

theorem canonicalIntrinsicThroatTensorPairPairing_smul_right
    (scalar : Real)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatTensorPairPairing period hPeriod first
        (smoothThroatGeneralMetricTensorPairSMul
          period hPeriod scalar second) =
      scalar * canonicalIntrinsicThroatTensorPairPairing
        period hPeriod first second := by
  rw [canonicalIntrinsicThroatTensorPairPairing_symmetric
      period hPeriod first,
    canonicalIntrinsicThroatTensorPairPairing_smul_left,
    canonicalIntrinsicThroatTensorPairPairing_symmetric
      period hPeriod second]

@[simp]
theorem canonicalIntrinsicThroatTensorPairPairing_zero_left
    (second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (smoothThroatGeneralMetricTensorPairZero period hPeriod) second = 0 := by
  unfold canonicalIntrinsicThroatTensorPairPairing
  simp

@[simp]
theorem canonicalIntrinsicThroatTensorPairPairing_zero_right
    (first : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    canonicalIntrinsicThroatTensorPairPairing period hPeriod first
        (smoothThroatGeneralMetricTensorPairZero period hPeriod) = 0 := by
  rw [canonicalIntrinsicThroatTensorPairPairing_symmetric]
  exact canonicalIntrinsicThroatTensorPairPairing_zero_left
    period hPeriod first

@[simp]
theorem smoothThroatGeneralMetricTensorPairSMul_zero_scalar
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    smoothThroatGeneralMetricTensorPairSMul period hPeriod 0 tensor =
      smoothThroatGeneralMetricTensorPairZero period hPeriod := by
  apply Prod.ext
  · apply SmoothSymmetricThroatCovariantTwoTensor.ext
    apply ContMDiffSection.ext
    intro point
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    change (0 : Real) * tensor.1.tensor point first second = 0
    norm_num
  · apply SmoothSymmetricThroatCovariantTwoTensor.ext
    apply ContMDiffSection.ext
    intro point
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    change (0 : Real) * tensor.2.tensor point first second = 0
    norm_num

/-- Affine line in both entries of the genuine smooth throat BV phase space. -/
def smoothThroatGeneralMetricBVAffineLine
    (base variation : SmoothThroatGeneralMetricBVField period hPeriod)
    (parameter : Real) : SmoothThroatGeneralMetricBVField period hPeriod :=
  (smoothThroatGeneralMetricTensorPairAffineLine period hPeriod
      base.1 variation.1 parameter,
    smoothThroatGeneralMetricTensorPairAffineLine period hPeriod
      base.2 variation.2 parameter)

/-! ## Certified throat functional observables -/

/-- A throat functional whose displayed gradients are certified along every
smooth affine BV line. -/
structure IntrinsicMetricBVThroatFunctionalObservable where
  parity : FiniteBVParity
  value : SmoothThroatGeneralMetricBVField period hPeriod → Real
  fieldGradient : SmoothThroatGeneralMetricBVField period hPeriod →
    SmoothThroatGeneralMetricTensorPair period hPeriod
  antifieldGradient : SmoothThroatGeneralMetricBVField period hPeriod →
    SmoothThroatGeneralMetricTensorPair period hPeriod
  hasDerivAt : ∀ phase variation,
    HasDerivAt
      (fun parameter : Real => value
        (smoothThroatGeneralMetricBVAffineLine
          period hPeriod phase variation parameter))
      (canonicalIntrinsicThroatTensorPairPairing period hPeriod
          (fieldGradient phase) variation.1 +
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
          (antifieldGradient phase) variation.2)
      0

/-- Odd antibracket of certified global throat functional gradients. -/
def intrinsicMetricBVThroatFunctionalOddAntibracket
    (first second : IntrinsicMetricBVThroatFunctionalObservable
      period hPeriod)
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) : Real :=
  canonicalIntrinsicThroatTensorPairPairing period hPeriod
      (first.fieldGradient phase) (second.antifieldGradient phase) -
    finiteBVOddKoszulSign first.parity second.parity *
      canonicalIntrinsicThroatTensorPairPairing period hPeriod
        (second.fieldGradient phase) (first.antifieldGradient phase)

theorem intrinsicMetricBVThroatFunctionalOddAntibracket_graded_skew
    (first second : IntrinsicMetricBVThroatFunctionalObservable
      period hPeriod)
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) :
    intrinsicMetricBVThroatFunctionalOddAntibracket period hPeriod
        first second phase =
      -finiteBVOddKoszulSign first.parity second.parity *
        intrinsicMetricBVThroatFunctionalOddAntibracket period hPeriod
          second first phase := by
  rcases first with
    ⟨firstParity, firstValue, firstField, firstAntifield, firstDeriv⟩
  rcases second with
    ⟨secondParity, secondValue, secondField, secondAntifield, secondDeriv⟩
  have hFirst := canonicalIntrinsicThroatTensorPairPairing_symmetric
    period hPeriod (firstField phase) (secondAntifield phase)
  have hSecond := canonicalIntrinsicThroatTensorPairPairing_symmetric
    period hPeriod (secondField phase) (firstAntifield phase)
  cases firstParity <;> cases secondParity <;>
    simp only [intrinsicMetricBVThroatFunctionalOddAntibracket,
      finiteBVOddKoszulSign] at * <;> linarith

/-! ## Rank-one nonlocal master functional -/

/-- Global throat antifield moment selected by one fixed smooth kernel. -/
def intrinsicMetricBVThroatFiniteRankMoment
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) : Real :=
  canonicalIntrinsicThroatTensorPairPairing
    period hPeriod kernel phase.2

/-- Rank-one nonlocal throat action `1/2 (∫⟨K,h⁺⟩)²`. -/
def intrinsicMetricBVThroatFiniteRankFunctionalMasterAction
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) : Real :=
  (1 / 2 : Real) *
    intrinsicMetricBVThroatFiniteRankMoment
      period hPeriod kernel phase ^ 2

theorem intrinsicMetricBVThroatFiniteRankMoment_affine
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase variation : SmoothThroatGeneralMetricBVField period hPeriod)
    (parameter : Real) :
    intrinsicMetricBVThroatFiniteRankMoment period hPeriod kernel
        (smoothThroatGeneralMetricBVAffineLine
          period hPeriod phase variation parameter) =
      intrinsicMetricBVThroatFiniteRankMoment
          period hPeriod kernel phase +
        parameter * canonicalIntrinsicThroatTensorPairPairing
          period hPeriod kernel variation.2 := by
  change canonicalIntrinsicThroatTensorPairPairing period hPeriod kernel
      (smoothThroatGeneralMetricTensorPairAffineLine
        period hPeriod phase.2 variation.2 parameter) = _
  unfold smoothThroatGeneralMetricTensorPairAffineLine
  rw [canonicalIntrinsicThroatTensorPairPairing_add_right,
    canonicalIntrinsicThroatTensorPairPairing_smul_right]
  rfl

theorem intrinsicMetricBVThroatFiniteRankFunctionalMasterAction_affine_expansion
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase variation : SmoothThroatGeneralMetricBVField period hPeriod)
    (parameter : Real) :
    intrinsicMetricBVThroatFiniteRankFunctionalMasterAction period hPeriod
        kernel (smoothThroatGeneralMetricBVAffineLine
          period hPeriod phase variation parameter) =
      intrinsicMetricBVThroatFiniteRankFunctionalMasterAction
          period hPeriod kernel phase +
        parameter *
          (intrinsicMetricBVThroatFiniteRankMoment
              period hPeriod kernel phase *
            canonicalIntrinsicThroatTensorPairPairing
              period hPeriod kernel variation.2) +
        parameter ^ 2 / 2 *
          canonicalIntrinsicThroatTensorPairPairing
            period hPeriod kernel variation.2 ^ 2 := by
  unfold intrinsicMetricBVThroatFiniteRankFunctionalMasterAction
  rw [intrinsicMetricBVThroatFiniteRankMoment_affine]
  ring

theorem intrinsicMetricBVThroatFiniteRankFunctionalMasterAction_affine_hasDerivAt
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase variation : SmoothThroatGeneralMetricBVField period hPeriod) :
    HasDerivAt
      (fun parameter : Real =>
        intrinsicMetricBVThroatFiniteRankFunctionalMasterAction
          period hPeriod kernel
          (smoothThroatGeneralMetricBVAffineLine
            period hPeriod phase variation parameter))
      (intrinsicMetricBVThroatFiniteRankMoment period hPeriod kernel phase *
        canonicalIntrinsicThroatTensorPairPairing
          period hPeriod kernel variation.2)
      0 := by
  let firstVariation :=
    intrinsicMetricBVThroatFiniteRankMoment period hPeriod kernel phase *
      canonicalIntrinsicThroatTensorPairPairing
        period hPeriod kernel variation.2
  let quadraticRemainder :=
    canonicalIntrinsicThroatTensorPairPairing
      period hPeriod kernel variation.2 ^ 2
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
        intrinsicMetricBVThroatFiniteRankFunctionalMasterAction
            period hPeriod kernel phase +
          parameter * firstVariation +
          parameter ^ 2 / 2 * quadraticRemainder)
      firstVariation 0 := by
    exact ((hLinear.const_add
      (intrinsicMetricBVThroatFiniteRankFunctionalMasterAction
        period hPeriod kernel phase)).add hQuadratic).congr_deriv (by simp)
  refine hPolynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  intro parameter
  simpa [firstVariation, quadraticRemainder] using
    (intrinsicMetricBVThroatFiniteRankFunctionalMasterAction_affine_expansion
      period hPeriod kernel phase variation parameter)

/-- The rank-one throat action with its actual global functional gradients. -/
def intrinsicMetricBVThroatFiniteRankFunctionalMasterObservable
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    IntrinsicMetricBVThroatFunctionalObservable period hPeriod where
  parity := .even
  value := intrinsicMetricBVThroatFiniteRankFunctionalMasterAction
    period hPeriod kernel
  fieldGradient := fun _ =>
    smoothThroatGeneralMetricTensorPairZero period hPeriod
  antifieldGradient := fun phase =>
    smoothThroatGeneralMetricTensorPairSMul period hPeriod
      (intrinsicMetricBVThroatFiniteRankMoment
        period hPeriod kernel phase) kernel
  hasDerivAt := by
    intro phase variation
    have hDerivative :=
      intrinsicMetricBVThroatFiniteRankFunctionalMasterAction_affine_hasDerivAt
        period hPeriod kernel phase variation
    convert hDerivative using 1
    rw [canonicalIntrinsicThroatTensorPairPairing_zero_left, zero_add,
      canonicalIntrinsicThroatTensorPairPairing_smul_left]

theorem intrinsicMetricBVThroatFiniteRankFunctionalMaster_CME
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) :
    intrinsicMetricBVThroatFunctionalOddAntibracket period hPeriod
        (intrinsicMetricBVThroatFiniteRankFunctionalMasterObservable
          period hPeriod kernel)
        (intrinsicMetricBVThroatFiniteRankFunctionalMasterObservable
          period hPeriod kernel)
        phase = 0 := by
  simp [intrinsicMetricBVThroatFunctionalOddAntibracket,
    intrinsicMetricBVThroatFiniteRankFunctionalMasterObservable]

/-- Hamiltonian vector generated by the rank-one throat functional. -/
def intrinsicMetricBVThroatFiniteRankFunctionalBRST
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) :
    SmoothThroatGeneralMetricBVField period hPeriod :=
  (smoothThroatGeneralMetricTensorPairSMul period hPeriod
      (intrinsicMetricBVThroatFiniteRankMoment
        period hPeriod kernel phase) kernel,
    smoothThroatGeneralMetricTensorPairZero period hPeriod)

theorem intrinsicMetricBVThroatFiniteRankFunctionalMaster_generates_BRST
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) :
    ((intrinsicMetricBVThroatFiniteRankFunctionalMasterObservable
        period hPeriod kernel).antifieldGradient phase,
      (intrinsicMetricBVThroatFiniteRankFunctionalMasterObservable
        period hPeriod kernel).fieldGradient phase) =
      intrinsicMetricBVThroatFiniteRankFunctionalBRST
        period hPeriod kernel phase :=
  rfl

theorem intrinsicMetricBVThroatFiniteRankFunctionalBRST_square_zero
    (kernel : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) :
    intrinsicMetricBVThroatFiniteRankFunctionalBRST period hPeriod kernel
        (intrinsicMetricBVThroatFiniteRankFunctionalBRST
          period hPeriod kernel phase) =
      smoothThroatGeneralMetricBVZero period hPeriod := by
  rw [intrinsicMetricBVThroatFiniteRankFunctionalBRST]
  have hMoment :
      intrinsicMetricBVThroatFiniteRankMoment period hPeriod kernel
          (intrinsicMetricBVThroatFiniteRankFunctionalBRST
            period hPeriod kernel phase) = 0 := by
    simp [intrinsicMetricBVThroatFiniteRankMoment,
      intrinsicMetricBVThroatFiniteRankFunctionalBRST]
  rw [hMoment, smoothThroatGeneralMetricTensorPairSMul_zero_scalar]
  rfl

/-! ## Explicit intrinsic nonzero witness -/

def intrinsicMetricBVThroatFiniteRankPhaseWitness :
    SmoothThroatGeneralMetricBVField period hPeriod :=
  (smoothThroatGeneralMetricTensorPairZero period hPeriod,
    intrinsicThroatContractibleAntifieldWitness period hPeriod)

@[simp]
theorem intrinsicThroatContractibleAntifieldWitness_pairingAt_eq_six
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod
        (intrinsicThroatContractibleAntifieldWitness period hPeriod)
        (intrinsicThroatContractibleAntifieldWitness period hPeriod) point = 6 := by
  unfold intrinsicThroatTensorPairPairingAt
    intrinsicThroatContractibleAntifieldWitness
  rw [intrinsicThroatTensorPairingAt_intrinsicMetric_self]
  norm_num

theorem intrinsicMetricBVThroatFiniteRankMoment_intrinsic_witness :
    intrinsicMetricBVThroatFiniteRankMoment period hPeriod
        (intrinsicThroatContractibleAntifieldWitness period hPeriod)
        (intrinsicMetricBVThroatFiniteRankPhaseWitness period hPeriod) =
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod Set.univ).toReal * 6 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  unfold intrinsicMetricBVThroatFiniteRankMoment
    intrinsicMetricBVThroatFiniteRankPhaseWitness
    canonicalIntrinsicThroatTensorPairPairing
  calc
    ∫ point, intrinsicThroatTensorPairPairingAt period hPeriod
          (intrinsicThroatContractibleAntifieldWitness period hPeriod)
          (intrinsicThroatContractibleAntifieldWitness period hPeriod) point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
        ∫ _point, (6 : Real)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
            apply integral_congr_ae
            filter_upwards [] with point
            exact intrinsicThroatContractibleAntifieldWitness_pairingAt_eq_six
              period hPeriod point
    _ = _ := by simp [measureReal_def]

theorem intrinsicMetricBVThroatFiniteRankMoment_intrinsic_witness_ne_zero :
    intrinsicMetricBVThroatFiniteRankMoment period hPeriod
        (intrinsicThroatContractibleAntifieldWitness period hPeriod)
        (intrinsicMetricBVThroatFiniteRankPhaseWitness period hPeriod) ≠ 0 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  rw [intrinsicMetricBVThroatFiniteRankMoment_intrinsic_witness]
  exact mul_ne_zero
    (ENNReal.toReal_ne_zero.2
      ⟨(Measure.measure_univ_ne_zero).2
        (intrinsicCanonicalThroatVolumeMeasure_ne_zero period hPeriod),
        measure_ne_top _ _⟩)
    (by norm_num)

theorem intrinsicMetricBVThroatFiniteRankFunctionalMasterAction_intrinsic_witness_ne_zero :
    intrinsicMetricBVThroatFiniteRankFunctionalMasterAction period hPeriod
        (intrinsicThroatContractibleAntifieldWitness period hPeriod)
        (intrinsicMetricBVThroatFiniteRankPhaseWitness period hPeriod) ≠ 0 := by
  unfold intrinsicMetricBVThroatFiniteRankFunctionalMasterAction
  exact mul_ne_zero (by norm_num)
    (pow_ne_zero 2
      (intrinsicMetricBVThroatFiniteRankMoment_intrinsic_witness_ne_zero
        period hPeriod))

end

end P0EFTJanusMappingTorusIntrinsicMetricBVThroatFiniteRankFunctionalMaster4D
end JanusFormal
