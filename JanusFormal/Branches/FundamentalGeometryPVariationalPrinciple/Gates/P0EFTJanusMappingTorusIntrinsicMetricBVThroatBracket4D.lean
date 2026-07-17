import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D

/-!
# Intrinsic inverse metric and pointwise BV bracket on the throat

The nondegenerate intrinsic throat trace is promoted pointwise to a genuine
musical equivalence.  It raises the traced metric variations and antifields,
giving a canonical pointwise pairing and odd bracket.  These are pointwise
finite-dimensional constructions; no smooth inverse field, functional
antibracket or derivative-dependent functional CME is asserted.  The final
CME is only the pointwise ultralocal identity of the contractible doublet.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTNaturality4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTRadical4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatTangentFiniteDimensional
    (point : EffectiveThroat period hPeriod) :
    FiniteDimensional Real (ThroatTangentFiber period hPeriod point) := by
  change FiniteDimensional Real ThroatCoverCoordinates
  infer_instance

private theorem throatTangent_finrank_eq_cotangent
    (point : EffectiveThroat period hPeriod) :
    Module.finrank Real (ThroatTangentFiber period hPeriod point) =
      Module.finrank Real (ThroatCotangentFiber period hPeriod point) := by
  calc
    Module.finrank Real (ThroatTangentFiber period hPeriod point) =
        Module.finrank Real
          (Module.Dual Real (ThroatTangentFiber period hPeriod point)) :=
      (Subspace.dual_finrank_eq (K := Real)
        (V := ThroatTangentFiber period hPeriod point)).symm
    _ = Module.finrank Real
        (ThroatCotangentFiber period hPeriod point) :=
      (LinearMap.toContinuousLinearMap
        (𝕜 := Real)
        (E := ThroatTangentFiber period hPeriod point)
        (F' := Real)).finrank_eq

/-- Pointwise musical equivalence supplied by the nondegenerate intrinsic
throat metric. -/
def intrinsicThroatMusical
    (point : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod point ≃L[Real]
      ThroatCotangentFiber period hPeriod point :=
  ((intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor point).toLinearMap
    |>.linearEquivOfInjective
      ((intrinsicSmoothNondegenerateThroatMetric period hPeriod).2 point)
      (throatTangent_finrank_eq_cotangent period hPeriod point)
    |>.toContinuousLinearEquiv

@[simp]
theorem intrinsicThroatMusical_apply
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    intrinsicThroatMusical period hPeriod point vector =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        point vector := by
  simp [intrinsicThroatMusical,
    LinearMap.linearEquivOfInjective_apply]

/-- Pointwise inverse metric, as the inverse of the genuine throat musical
equivalence. -/
def intrinsicThroatInverseMusical
    (point : EffectiveThroat period hPeriod) :
    ThroatCotangentFiber period hPeriod point ≃L[Real]
      ThroatTangentFiber period hPeriod point :=
  (intrinsicThroatMusical period hPeriod point).symm

@[simp]
theorem intrinsicThroatMusical_inverse_apply
    (point : EffectiveThroat period hPeriod)
    (covector : ThroatCotangentFiber period hPeriod point) :
    intrinsicThroatMusical period hPeriod point
        (intrinsicThroatInverseMusical period hPeriod point covector) =
      covector :=
  (intrinsicThroatMusical period hPeriod point).apply_symm_apply covector

@[simp]
theorem intrinsicThroatInverseMusical_apply_musical
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    intrinsicThroatInverseMusical period hPeriod point
        (intrinsicThroatMusical period hPeriod point vector) = vector :=
  (intrinsicThroatMusical period hPeriod point).symm_apply_apply vector

/-- The intrinsic throat metric is pointwise invariant under the true throat
PT differential. -/
theorem intrinsicThroatMetric_pt_natural
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        point first second =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        (fixedThroatPT period hPeriod point)
        (throatPTDerivativeEquiv period hPeriod point first)
        (throatPTDerivativeEquiv period hPeriod point second) := by
  have hNatural := generalLorentzMetricThroatTrace_pt_natural period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) point first second
  rw [intrinsicSmoothGeneralLorentzMetric_pt_fixed] at hNatural
  simpa [intrinsicSmoothNondegenerateThroatMetric,
    generalLorentzMetricNondegenerateThroatTrace,
    throatPTTensorPullbackValue_apply,
    throatPTDerivativeEquiv_apply] using hNatural

theorem smoothSymmetricTensorThroatTrace_pt_natural_equiv
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    (smoothSymmetricTensorThroatTrace period hPeriod
        (smoothPTTensorPullback period hPeriod tensor)).tensor
        point first second =
      (smoothSymmetricTensorThroatTrace period hPeriod tensor).tensor
        (fixedThroatPT period hPeriod point)
        (throatPTDerivativeEquiv period hPeriod point first)
        (throatPTDerivativeEquiv period hPeriod point second) := by
  simpa [throatPTTensorPullbackValue_apply,
    throatPTDerivativeEquiv_apply] using
      smoothSymmetricTensorThroatTrace_pt_natural
        period hPeriod tensor point first second

/-- Raise one index of a genuine symmetric throat tensor with the intrinsic
inverse metric. -/
def raisedIntrinsicThroatTensorAt
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod point →L[Real]
      ThroatTangentFiber period hPeriod point :=
  (intrinsicThroatInverseMusical period hPeriod point).toContinuousLinearMap.comp
    (tensor.tensor point)

/-- Addition of genuine smooth symmetric throat tensors. -/
def smoothSymmetricThroatTensorAdd
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod where
  tensor := first.tensor + second.tensor
  symmetric := by
    intro point left right
    change first.tensor point left right + second.tensor point left right =
      first.tensor point right left + second.tensor point right left
    rw [first.symmetric, second.symmetric]

/-- Real scalar multiplication of genuine smooth symmetric throat tensors. -/
def smoothSymmetricThroatTensorSMul
    (scalar : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod where
  tensor := scalar • tensor.tensor
  symmetric := by
    intro point left right
    change scalar * tensor.tensor point left right =
      scalar * tensor.tensor point right left
    rw [tensor.symmetric]

theorem raisedIntrinsicThroatTensorAt_add
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    raisedIntrinsicThroatTensorAt period hPeriod
        (smoothSymmetricThroatTensorAdd period hPeriod first second) point =
      raisedIntrinsicThroatTensorAt period hPeriod first point +
        raisedIntrinsicThroatTensorAt period hPeriod second point := by
  apply ContinuousLinearMap.ext
  intro vector
  simp [raisedIntrinsicThroatTensorAt, smoothSymmetricThroatTensorAdd]

theorem raisedIntrinsicThroatTensorAt_smul
    (scalar : Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    raisedIntrinsicThroatTensorAt period hPeriod
        (smoothSymmetricThroatTensorSMul period hPeriod scalar tensor) point =
      scalar • raisedIntrinsicThroatTensorAt period hPeriod tensor point := by
  apply ContinuousLinearMap.ext
  intro vector
  simp [raisedIntrinsicThroatTensorAt, smoothSymmetricThroatTensorSMul]

/-- Raising a traced PT-pulled tensor is conjugation by the inverse throat PT
differential. -/
theorem raisedIntrinsicThroatTensorAt_pt
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (raisedIntrinsicThroatTensorAt period hPeriod
        (smoothSymmetricTensorThroatTrace period hPeriod
          (smoothPTTensorPullback period hPeriod tensor)) point).toLinearMap =
      (throatPTDerivativeEquiv period hPeriod point).symm.toLinearEquiv.conj
        (raisedIntrinsicThroatTensorAt period hPeriod
          (smoothSymmetricTensorThroatTrace period hPeriod tensor)
          (fixedThroatPT period hPeriod point)).toLinearMap := by
  apply LinearMap.ext
  intro vector
  change intrinsicThroatInverseMusical period hPeriod point
        ((smoothSymmetricTensorThroatTrace period hPeriod
          (smoothPTTensorPullback period hPeriod tensor)).tensor
            point vector) =
      (throatPTDerivativeEquiv period hPeriod point).symm
        (intrinsicThroatInverseMusical period hPeriod
          (fixedThroatPT period hPeriod point)
          ((smoothSymmetricTensorThroatTrace period hPeriod tensor).tensor
            (fixedThroatPT period hPeriod point)
            (throatPTDerivativeEquiv period hPeriod point vector)))
  apply (throatPTDerivativeEquiv period hPeriod point).injective
  rw [(throatPTDerivativeEquiv period hPeriod point).apply_symm_apply]
  apply (intrinsicThroatMusical period hPeriod
    (fixedThroatPT period hPeriod point)).injective
  apply ContinuousLinearMap.ext
  intro second
  rw [intrinsicThroatMusical_apply, intrinsicThroatMusical_apply]
  change
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        (fixedThroatPT period hPeriod point)
        (throatPTDerivativeEquiv period hPeriod point
          (intrinsicThroatInverseMusical period hPeriod point
            ((smoothSymmetricTensorThroatTrace period hPeriod
              (smoothPTTensorPullback period hPeriod tensor)).tensor
                point vector))) second =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        (fixedThroatPT period hPeriod point)
        (intrinsicThroatInverseMusical period hPeriod
          (fixedThroatPT period hPeriod point)
          ((smoothSymmetricTensorThroatTrace period hPeriod tensor).tensor
            (fixedThroatPT period hPeriod point)
            (throatPTDerivativeEquiv period hPeriod point vector))) second
  rw [← (throatPTDerivativeEquiv period hPeriod point).apply_symm_apply second,
    ← intrinsicThroatMetric_pt_natural period hPeriod point]
  rw [← intrinsicThroatMusical_apply period hPeriod point,
    intrinsicThroatMusical_inverse_apply period hPeriod point,
    ← intrinsicThroatMusical_apply period hPeriod
      (fixedThroatPT period hPeriod point),
    intrinsicThroatMusical_inverse_apply period hPeriod
      (fixedThroatPT period hPeriod point)]
  rw [smoothSymmetricTensorThroatTrace_pt_natural_equiv
    period hPeriod tensor point vector
      ((throatPTDerivativeEquiv period hPeriod point).symm second)]

/-- Intrinsic pointwise throat pairing `tr(g⁻¹h g⁻¹k)`. -/
def intrinsicThroatTensorPairingAt
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  LinearMap.trace Real (ThroatTangentFiber period hPeriod point)
    ((raisedIntrinsicThroatTensorAt period hPeriod first point).toLinearMap *
      (raisedIntrinsicThroatTensorAt period hPeriod second point).toLinearMap)

theorem intrinsicThroatTensorPairingAt_symmetric
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod first second point =
      intrinsicThroatTensorPairingAt period hPeriod second first point := by
  exact LinearMap.trace_mul_comm Real _ _

theorem intrinsicThroatTensorPairingAt_add_left
    (first second third : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod
        (smoothSymmetricThroatTensorAdd period hPeriod first second) third point =
      intrinsicThroatTensorPairingAt period hPeriod first third point +
        intrinsicThroatTensorPairingAt period hPeriod second third point := by
  unfold intrinsicThroatTensorPairingAt
  rw [raisedIntrinsicThroatTensorAt_add]
  simp [add_mul]

theorem intrinsicThroatTensorPairingAt_add_right
    (first second third : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod first
        (smoothSymmetricThroatTensorAdd period hPeriod second third) point =
      intrinsicThroatTensorPairingAt period hPeriod first second point +
        intrinsicThroatTensorPairingAt period hPeriod first third point := by
  rw [intrinsicThroatTensorPairingAt_symmetric period hPeriod first,
    intrinsicThroatTensorPairingAt_add_left,
    intrinsicThroatTensorPairingAt_symmetric period hPeriod second,
    intrinsicThroatTensorPairingAt_symmetric period hPeriod third]

theorem intrinsicThroatTensorPairingAt_smul_left
    (scalar : Real)
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod
        (smoothSymmetricThroatTensorSMul period hPeriod scalar first) second point =
      scalar * intrinsicThroatTensorPairingAt period hPeriod first second point := by
  unfold intrinsicThroatTensorPairingAt
  rw [raisedIntrinsicThroatTensorAt_smul]
  simp

theorem intrinsicThroatTensorPairingAt_smul_right
    (scalar : Real)
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod first
        (smoothSymmetricThroatTensorSMul period hPeriod scalar second) point =
      scalar * intrinsicThroatTensorPairingAt period hPeriod first second point := by
  rw [intrinsicThroatTensorPairingAt_symmetric period hPeriod first,
    intrinsicThroatTensorPairingAt_smul_left,
    intrinsicThroatTensorPairingAt_symmetric period hPeriod second]

/-- The intrinsic pairing of two traced bulk tensors is a scalar under the
true throat PT map. -/
theorem intrinsicThroatTensorPairingAt_pt
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod
        (smoothSymmetricTensorThroatTrace period hPeriod
          (smoothPTTensorPullback period hPeriod first))
        (smoothSymmetricTensorThroatTrace period hPeriod
          (smoothPTTensorPullback period hPeriod second)) point =
      intrinsicThroatTensorPairingAt period hPeriod
        (smoothSymmetricTensorThroatTrace period hPeriod first)
        (smoothSymmetricTensorThroatTrace period hPeriod second)
        (fixedThroatPT period hPeriod point) := by
  unfold intrinsicThroatTensorPairingAt
  rw [raisedIntrinsicThroatTensorAt_pt period hPeriod first point,
    raisedIntrinsicThroatTensorAt_pt period hPeriod second point]
  let equivalence :=
    (throatPTDerivativeEquiv period hPeriod point).symm.toLinearEquiv
  let firstEnd :=
    (raisedIntrinsicThroatTensorAt period hPeriod
      (smoothSymmetricTensorThroatTrace period hPeriod first)
      (fixedThroatPT period hPeriod point)).toLinearMap
  let secondEnd :=
    (raisedIntrinsicThroatTensorAt period hPeriod
      (smoothSymmetricTensorThroatTrace period hPeriod second)
      (fixedThroatPT period hPeriod point)).toLinearMap
  have hTrace := LinearMap.trace_conj' (firstEnd * secondEnd) equivalence
  rw [← hTrace]
  congr 1
  apply LinearMap.ext
  intro vector
  simp [equivalence, firstEnd, secondEnd]

/-- Componentwise addition on the two-sector throat tensor space. -/
def smoothThroatGeneralMetricTensorPairAdd
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    SmoothThroatGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricThroatTensorAdd period hPeriod first.1 second.1,
    smoothSymmetricThroatTensorAdd period hPeriod first.2 second.2)

/-- Componentwise scalar multiplication on the two-sector throat tensor
space. -/
def smoothThroatGeneralMetricTensorPairSMul
    (scalar : Real)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    SmoothThroatGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricThroatTensorSMul period hPeriod scalar tensor.1,
    smoothSymmetricThroatTensorSMul period hPeriod scalar tensor.2)

/-- Affine line in the genuine smooth throat-antifield space. -/
def smoothThroatGeneralMetricTensorPairAffineLine
    (base variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (parameter : Real) : SmoothThroatGeneralMetricTensorPair period hPeriod :=
  smoothThroatGeneralMetricTensorPairAdd period hPeriod base
    (smoothThroatGeneralMetricTensorPairSMul period hPeriod parameter variation)

def intrinsicThroatTensorPairPairingAt
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  intrinsicThroatTensorPairingAt period hPeriod first.1 second.1 point +
    intrinsicThroatTensorPairingAt period hPeriod first.2 second.2 point

theorem intrinsicThroatTensorPairPairingAt_symmetric
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod first second point =
      intrinsicThroatTensorPairPairingAt period hPeriod second first point := by
  rw [intrinsicThroatTensorPairPairingAt,
    intrinsicThroatTensorPairPairingAt,
    intrinsicThroatTensorPairingAt_symmetric period hPeriod first.1 second.1,
    intrinsicThroatTensorPairingAt_symmetric period hPeriod first.2 second.2]

theorem intrinsicThroatTensorPairPairingAt_add_left
    (first second third : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod
        (smoothThroatGeneralMetricTensorPairAdd period hPeriod first second)
        third point =
      intrinsicThroatTensorPairPairingAt period hPeriod first third point +
        intrinsicThroatTensorPairPairingAt period hPeriod second third point := by
  unfold intrinsicThroatTensorPairPairingAt
    smoothThroatGeneralMetricTensorPairAdd
  rw [intrinsicThroatTensorPairingAt_add_left,
    intrinsicThroatTensorPairingAt_add_left]
  ring

theorem intrinsicThroatTensorPairPairingAt_add_right
    (first second third : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod first
        (smoothThroatGeneralMetricTensorPairAdd period hPeriod second third)
        point =
      intrinsicThroatTensorPairPairingAt period hPeriod first second point +
        intrinsicThroatTensorPairPairingAt period hPeriod first third point := by
  rw [intrinsicThroatTensorPairPairingAt_symmetric period hPeriod first,
    intrinsicThroatTensorPairPairingAt_add_left,
    intrinsicThroatTensorPairPairingAt_symmetric period hPeriod second,
    intrinsicThroatTensorPairPairingAt_symmetric period hPeriod third]

theorem intrinsicThroatTensorPairPairingAt_smul_left
    (scalar : Real)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod
        (smoothThroatGeneralMetricTensorPairSMul period hPeriod scalar first)
        second point =
      scalar * intrinsicThroatTensorPairPairingAt period hPeriod first second point := by
  unfold intrinsicThroatTensorPairPairingAt
    smoothThroatGeneralMetricTensorPairSMul
  rw [intrinsicThroatTensorPairingAt_smul_left,
    intrinsicThroatTensorPairingAt_smul_left]
  ring

theorem intrinsicThroatTensorPairPairingAt_smul_right
    (scalar : Real)
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod first
        (smoothThroatGeneralMetricTensorPairSMul period hPeriod scalar second)
        point =
      scalar * intrinsicThroatTensorPairPairingAt period hPeriod first second point := by
  rw [intrinsicThroatTensorPairPairingAt_symmetric period hPeriod first,
    intrinsicThroatTensorPairPairingAt_smul_left,
    intrinsicThroatTensorPairPairingAt_symmetric period hPeriod second]

@[simp]
theorem intrinsicThroatTensorPairPairingAt_zero_left
    (second : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod
        (smoothThroatGeneralMetricTensorPairZero period hPeriod)
        second point = 0 := by
  simp [intrinsicThroatTensorPairPairingAt,
    smoothThroatGeneralMetricTensorPairZero,
    intrinsicThroatTensorPairingAt,
    raisedIntrinsicThroatTensorAt]

/-- The traced two-sector pairing is covariant under simultaneous PT and
exchange of the two bulk sectors. -/
theorem intrinsicThroatTensorPairPairingAt_ptExchange
    (first second : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod
        (smoothGeneralMetricTensorPairThroatTrace period hPeriod
          (smoothGeneralMetricTensorPairPTExchange period hPeriod first))
        (smoothGeneralMetricTensorPairThroatTrace period hPeriod
          (smoothGeneralMetricTensorPairPTExchange period hPeriod second))
        point =
      intrinsicThroatTensorPairPairingAt period hPeriod
        (smoothGeneralMetricTensorPairThroatTrace period hPeriod first)
        (smoothGeneralMetricTensorPairThroatTrace period hPeriod second)
        (fixedThroatPT period hPeriod point) := by
  simp only [intrinsicThroatTensorPairPairingAt,
    smoothGeneralMetricTensorPairThroatTrace,
    smoothGeneralMetricTensorPairPTExchange]
  rw [intrinsicThroatTensorPairingAt_pt period hPeriod first.2 second.2,
    intrinsicThroatTensorPairingAt_pt period hPeriod first.1 second.1]
  exact add_comm _ _

/-- A point observable restricted along a bulk BV phase. Its Darboux gradients
are genuine smooth throat traces of the bulk gradients. -/
structure IntrinsicThroatBVTraceObservable where
  parity : FiniteBVParity
  value : SmoothGeneralMetricBVField period hPeriod →
    EffectiveThroat period hPeriod → Real
  fieldGradient : SmoothGeneralMetricBVField period hPeriod →
    SmoothThroatGeneralMetricTensorPair period hPeriod
  antifieldGradient : SmoothGeneralMetricBVField period hPeriod →
    SmoothThroatGeneralMetricTensorPair period hPeriod

/-- Canonical restriction of a bulk point observable to the actual throat. -/
def generalMetricBVPointObservableThroatTrace
    (observable : GeneralMetricBVPointObservable period hPeriod) :
    IntrinsicThroatBVTraceObservable period hPeriod where
  parity := observable.parity
  value := fun phase point => observable.value phase
    (fixedThroatQuotientInclusion period hPeriod point)
  fieldGradient := fun phase =>
    smoothGeneralMetricTensorPairThroatTrace period hPeriod
      (observable.fieldGradient phase)
  antifieldGradient := fun phase =>
    smoothGeneralMetricTensorPairThroatTrace period hPeriod
      (observable.antifieldGradient phase)

/-- Pointwise odd bracket of traced variation/antifield gradients. -/
def intrinsicThroatBVOddAntibracketAt
    (first second : IntrinsicThroatBVTraceObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  intrinsicThroatTensorPairPairingAt period hPeriod
      (first.fieldGradient phase) (second.antifieldGradient phase) point -
    finiteBVOddKoszulSign first.parity second.parity *
      intrinsicThroatTensorPairPairingAt period hPeriod
        (second.fieldGradient phase) (first.antifieldGradient phase) point

/-- The quadratic ultralocal action as a function of its genuine smooth
throat-antifield argument. -/
def intrinsicThroatContractibleAntifieldActionAt
    (antifield : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    intrinsicThroatTensorPairPairingAt period hPeriod antifield antifield point

/-- Pointwise ultralocal Hamiltonian `S∂ = 1/2 ⟨h⁺,h⁺⟩` for the contractible
boundary doublet.  This is not an integrated functional. -/
def intrinsicThroatContractibleMasterActionAt
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  intrinsicThroatContractibleAntifieldActionAt period hPeriod
    (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2) point

theorem intrinsicThroatContractibleMasterActionAt_ptExchange
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatContractibleMasterActionAt period hPeriod
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point =
      intrinsicThroatContractibleMasterActionAt period hPeriod phase
        (fixedThroatPT period hPeriod point) := by
  simp only [intrinsicThroatContractibleMasterActionAt,
    intrinsicThroatContractibleAntifieldActionAt,
    smoothGeneralMetricBVPTExchange]
  rw [intrinsicThroatTensorPairPairingAt_ptExchange period hPeriod]

/-- Exact polarization of the ultralocal quadratic action along every affine
smooth throat-antifield line. -/
theorem intrinsicThroatContractibleAntifieldActionAt_affine_expansion
    (base variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) (parameter : Real) :
    intrinsicThroatContractibleAntifieldActionAt period hPeriod
        (smoothThroatGeneralMetricTensorPairAffineLine
          period hPeriod base variation parameter) point =
      intrinsicThroatContractibleAntifieldActionAt period hPeriod base point +
        parameter * intrinsicThroatTensorPairPairingAt
          period hPeriod base variation point +
        parameter ^ 2 / 2 * intrinsicThroatTensorPairPairingAt
          period hPeriod variation variation point := by
  unfold intrinsicThroatContractibleAntifieldActionAt
    smoothThroatGeneralMetricTensorPairAffineLine
  rw [intrinsicThroatTensorPairPairingAt_add_left,
    intrinsicThroatTensorPairPairingAt_add_right,
    intrinsicThroatTensorPairPairingAt_add_right,
    intrinsicThroatTensorPairPairingAt_smul_right,
    intrinsicThroatTensorPairPairingAt_smul_left,
    intrinsicThroatTensorPairPairingAt_smul_left,
    intrinsicThroatTensorPairPairingAt_smul_right,
    intrinsicThroatTensorPairPairingAt_symmetric period hPeriod variation base]
  ring

/-- The actual master action is the zero-parameter value of the corresponding
affine throat-antifield variation. -/
theorem intrinsicThroatContractibleMasterActionAt_affine_zero
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatContractibleAntifieldActionAt period hPeriod
        (smoothThroatGeneralMetricTensorPairAffineLine period hPeriod
          (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
          variation 0) point =
      intrinsicThroatContractibleMasterActionAt period hPeriod phase point := by
  rw [intrinsicThroatContractibleAntifieldActionAt_affine_expansion]
  simp [intrinsicThroatContractibleMasterActionAt]

@[simp]
theorem raisedIntrinsicThroatTensorAt_intrinsicMetric
    (point : EffectiveThroat period hPeriod) :
    raisedIntrinsicThroatTensorAt period hPeriod
        (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 point =
      ContinuousLinearMap.id Real
        (ThroatTangentFiber period hPeriod point) := by
  apply ContinuousLinearMap.ext
  intro vector
  change intrinsicThroatInverseMusical period hPeriod point
      ((intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        point vector) = vector
  rw [← intrinsicThroatMusical_apply period hPeriod point,
    intrinsicThroatInverseMusical_apply_musical]

theorem intrinsicThroatTensorPairingAt_intrinsicMetric_self
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod
        (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1
        (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 point = 3 := by
  have hDimension :
      Module.finrank Real (ThroatTangentFiber period hPeriod point) = 3 := by
    change Module.finrank Real ThroatCoverCoordinates = 3
    simp [ThroatCoverCoordinates]
  unfold intrinsicThroatTensorPairingAt
  rw [raisedIntrinsicThroatTensorAt_intrinsicMetric]
  have hIdentityProduct :
      (ContinuousLinearMap.id Real
          (ThroatTangentFiber period hPeriod point)).toLinearMap *
          (ContinuousLinearMap.id Real
            (ThroatTangentFiber period hPeriod point)).toLinearMap =
        LinearMap.id := by
    ext vector
    rfl
  rw [hIdentityProduct, LinearMap.trace_id, hDimension]
  norm_num

/-- Explicit nonzero smooth throat-antifield direction: the intrinsic metric
in both sectors. -/
def intrinsicThroatContractibleAntifieldWitness :
    SmoothThroatGeneralMetricTensorPair period hPeriod :=
  ((intrinsicSmoothNondegenerateThroatMetric period hPeriod).1,
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1)

theorem intrinsicThroatContractibleAntifieldActionAt_witness_eq_three
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatContractibleAntifieldActionAt period hPeriod
        (intrinsicThroatContractibleAntifieldWitness period hPeriod) point = 3 := by
  unfold intrinsicThroatContractibleAntifieldActionAt
    intrinsicThroatContractibleAntifieldWitness
    intrinsicThroatTensorPairPairingAt
  rw [intrinsicThroatTensorPairingAt_intrinsicMetric_self]
  norm_num

theorem intrinsicThroatContractibleAntifieldActionAt_witness_ne_zero
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatContractibleAntifieldActionAt period hPeriod
        (intrinsicThroatContractibleAntifieldWitness period hPeriod) point ≠ 0 := by
  rw [intrinsicThroatContractibleAntifieldActionAt_witness_eq_three]
  norm_num

/-- Canonical pointwise first-gradient data for the ultralocal boundary
Hamiltonian. -/
def intrinsicThroatContractibleMasterObservable :
    IntrinsicThroatBVTraceObservable period hPeriod where
  parity := .even
  value := intrinsicThroatContractibleMasterActionAt period hPeriod
  fieldGradient := fun _ =>
    smoothThroatGeneralMetricTensorPairZero period hPeriod
  antifieldGradient := fun phase =>
    smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2

/-- The declared antifield gradient is the actual directional derivative of
the ultralocal action along every affine smooth throat-antifield variation. -/
theorem intrinsicThroatContractibleMasterActionAt_hasDerivAt_antifield
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    HasDerivAt
      (fun parameter : Real =>
        intrinsicThroatContractibleAntifieldActionAt period hPeriod
          (smoothThroatGeneralMetricTensorPairAffineLine period hPeriod
            (smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2)
            variation parameter) point)
      (intrinsicThroatTensorPairPairingAt period hPeriod
        ((intrinsicThroatContractibleMasterObservable
          period hPeriod).antifieldGradient phase) variation point)
      0 := by
  let base :=
    smoothGeneralMetricTensorPairThroatTrace period hPeriod phase.2
  let firstVariation :=
    intrinsicThroatTensorPairPairingAt period hPeriod base variation point
  let quadraticRemainder :=
    intrinsicThroatTensorPairPairingAt period hPeriod variation variation point
  have hLinear : HasDerivAt
      (fun parameter : Real => parameter * firstVariation) firstVariation 0 := by
    simpa using
      (hasDerivAt_id (x := (0 : Real))).mul_const firstVariation
  have hQuadratic : HasDerivAt
      (fun parameter : Real => parameter ^ 2 / 2 * quadraticRemainder) 0 0 := by
    simpa [id] using
      (((hasDerivAt_id (x := (0 : Real))).pow 2).div_const 2).mul_const
        quadraticRemainder
  have hPolynomial : HasDerivAt
      (fun parameter : Real =>
        intrinsicThroatContractibleAntifieldActionAt
            period hPeriod base point +
          parameter * firstVariation +
          parameter ^ 2 / 2 * quadraticRemainder)
      firstVariation 0 := by
    have hRaw :=
      (hLinear.const_add
        (intrinsicThroatContractibleAntifieldActionAt
          period hPeriod base point)).add hQuadratic
    refine (hRaw.congr_deriv (by simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    intro parameter
    rfl
  refine hPolynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  intro parameter
  simpa [base, firstVariation, quadraticRemainder,
    intrinsicThroatContractibleMasterObservable] using
    (intrinsicThroatContractibleAntifieldActionAt_affine_expansion
      period hPeriod base variation point parameter)

/-- The Hamiltonian gradient is exactly the traced contractible boundary
BRST vector `(h⁺, 0)`. -/
theorem intrinsicThroatContractibleMaster_generates_BRST
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    ((intrinsicThroatContractibleMasterObservable period hPeriod).antifieldGradient
        phase,
      (intrinsicThroatContractibleMasterObservable period hPeriod).fieldGradient
        phase) =
      smoothThroatGeneralMetricBVBRST period hPeriod
        (smoothGeneralMetricBVThroatTrace period hPeriod phase) :=
  rfl

/-- Pointwise classical master equation for the ultralocal contractible
boundary doublet. -/
theorem intrinsicThroatContractibleMaster_classical_master_equation
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatBVOddAntibracketAt period hPeriod
        (intrinsicThroatContractibleMasterObservable period hPeriod)
        (intrinsicThroatContractibleMasterObservable period hPeriod)
        phase point = 0 := by
  simp [intrinsicThroatBVOddAntibracketAt,
    intrinsicThroatContractibleMasterObservable,
    finiteBVOddKoszulSign]

theorem intrinsicThroatBVOddAntibracketAt_graded_skew
    (first second : IntrinsicThroatBVTraceObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatBVOddAntibracketAt period hPeriod first second phase point =
      -finiteBVOddKoszulSign first.parity second.parity *
        intrinsicThroatBVOddAntibracketAt period hPeriod
          second first phase point := by
  rcases first with ⟨firstParity, firstValue, firstField, firstAntifield⟩
  rcases second with ⟨secondParity, secondValue, secondField, secondAntifield⟩
  have hFirst := intrinsicThroatTensorPairPairingAt_symmetric period hPeriod
    (firstField phase) (secondAntifield phase) point
  have hSecond := intrinsicThroatTensorPairPairingAt_symmetric period hPeriod
    (secondField phase) (firstAntifield phase) point
  cases firstParity <;> cases secondParity <;>
    simp only [intrinsicThroatBVOddAntibracketAt,
      finiteBVOddKoszulSign] at * <;> linarith

/-- Exact compatibility with restriction of the two bulk Darboux gradients.
This does not identify the boundary pairing with the unrestricted ambient
pairing, which also sees normal components. -/
theorem intrinsicThroatBVOddAntibracketAt_bulkTrace
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatBVOddAntibracketAt period hPeriod
        (generalMetricBVPointObservableThroatTrace period hPeriod first)
        (generalMetricBVPointObservableThroatTrace period hPeriod second)
        phase point =
      intrinsicThroatTensorPairPairingAt period hPeriod
          (smoothGeneralMetricTensorPairThroatTrace period hPeriod
            (first.fieldGradient phase))
          (smoothGeneralMetricTensorPairThroatTrace period hPeriod
            (second.antifieldGradient phase)) point -
        finiteBVOddKoszulSign first.parity second.parity *
          intrinsicThroatTensorPairPairingAt period hPeriod
            (smoothGeneralMetricTensorPairThroatTrace period hPeriod
              (second.fieldGradient phase))
            (smoothGeneralMetricTensorPairThroatTrace period hPeriod
              (first.antifieldGradient phase)) point :=
  rfl

/-- The intrinsic odd bracket of bulk traces is a scalar under coherent
PT/exchange of both observables and the BV phase. -/
theorem intrinsicThroatBVOddAntibracketAt_ptExchange
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatBVOddAntibracketAt period hPeriod
        (generalMetricBVPointObservableThroatTrace period hPeriod
          (generalMetricBVPointObservablePTExchange period hPeriod first))
        (generalMetricBVPointObservableThroatTrace period hPeriod
          (generalMetricBVPointObservablePTExchange period hPeriod second))
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point =
      intrinsicThroatBVOddAntibracketAt period hPeriod
        (generalMetricBVPointObservableThroatTrace period hPeriod first)
        (generalMetricBVPointObservableThroatTrace period hPeriod second)
        phase (fixedThroatPT period hPeriod point) := by
  simp only [intrinsicThroatBVOddAntibracketAt,
    generalMetricBVPointObservableThroatTrace,
    generalMetricBVPointObservablePTExchange,
    smoothGeneralMetricBVPTExchange_involutive]
  rw [intrinsicThroatTensorPairPairingAt_ptExchange period hPeriod,
    intrinsicThroatTensorPairPairingAt_ptExchange period hPeriod]

end

end P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
end JanusFormal
