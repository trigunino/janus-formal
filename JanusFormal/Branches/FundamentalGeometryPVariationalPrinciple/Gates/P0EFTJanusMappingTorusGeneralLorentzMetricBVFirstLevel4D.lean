import Mathlib.LinearAlgebra.Trace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D

/-!
# First BV level for general Lorentz-metric tensors

This gate installs the linear BV layer that is safe before constructing a
functional metric CME.  Even fields are arbitrary smooth symmetric covariant
two-tensor variations and antifields are parity-shifted copies.  A nontrivial
odd square-zero doublet, the background-metric trace pairing and its
pointwise Darboux antibracket are explicit.

The construction is a formal tangent extension of the general Lorentz field
packet.  It does not assert that affine tensor variations remain Lorentzian,
and it does not claim a derivative-dependent functional master equation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

abbrev GeneralMetricTangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-! ## Linear operations on smooth symmetric tensor variations -/

def smoothSymmetricTensorNeg
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor := -tensor.tensor
  symmetric := by
    intro point first second
    change -tensor.tensor point first second =
      -tensor.tensor point second first
    rw [tensor.symmetric]

def smoothSymmetricTensorAdd
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor := first.tensor + second.tensor
  symmetric := by
    intro point firstVector secondVector
    change first.tensor point firstVector secondVector +
        second.tensor point firstVector secondVector =
      first.tensor point secondVector firstVector +
        second.tensor point secondVector firstVector
    rw [first.symmetric, second.symmetric]

def smoothSymmetricTensorSMul
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor := scalar • tensor.tensor
  symmetric := by
    intro point first second
    change scalar * tensor.tensor point first second =
      scalar * tensor.tensor point second first
    rw [tensor.symmetric]

@[simp]
theorem smoothSymmetricTensorNeg_involutive
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothSymmetricTensorNeg period hPeriod
        (smoothSymmetricTensorNeg period hPeriod tensor) = tensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  exact neg_neg tensor.tensor

@[simp]
theorem smoothSymmetricTensorNeg_zero :
    smoothSymmetricTensorNeg period hPeriod
      (zeroSymmetricTensor period hPeriod) =
        zeroSymmetricTensor period hPeriod := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change -(0 : Real) = 0
  norm_num

/-- Two-sector smooth symmetric tensor variations. -/
abbrev SmoothGeneralMetricTensorPair :=
  SmoothSymmetricCovariantTwoTensor period hPeriod ×
    SmoothSymmetricCovariantTwoTensor period hPeriod

def smoothGeneralMetricTensorPairZero :
    SmoothGeneralMetricTensorPair period hPeriod :=
  (zeroSymmetricTensor period hPeriod, zeroSymmetricTensor period hPeriod)

def smoothGeneralMetricTensorPairNeg
    (tensors : SmoothGeneralMetricTensorPair period hPeriod) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricTensorNeg period hPeriod tensors.1,
    smoothSymmetricTensorNeg period hPeriod tensors.2)

@[simp]
theorem smoothGeneralMetricTensorPairNeg_involutive
    (tensors : SmoothGeneralMetricTensorPair period hPeriod) :
    smoothGeneralMetricTensorPairNeg period hPeriod
        (smoothGeneralMetricTensorPairNeg period hPeriod tensors) = tensors := by
  apply Prod.ext <;> simp [smoothGeneralMetricTensorPairNeg]

@[simp]
theorem smoothGeneralMetricTensorPairNeg_zero :
    smoothGeneralMetricTensorPairNeg period hPeriod
        (smoothGeneralMetricTensorPairZero period hPeriod) =
      smoothGeneralMetricTensorPairZero period hPeriod := by
  apply Prod.ext <;>
    exact smoothSymmetricTensorNeg_zero period hPeriod

/-! ## Shifted cotangent doublet -/

/-- Smooth even metric variations paired with parity-shifted tensor
antifields.  Both entries are genuine smooth tensor sections. -/
abbrev SmoothGeneralMetricBVField :=
  SmoothGeneralMetricTensorPair period hPeriod ×
    SmoothGeneralMetricTensorPair period hPeriod

def smoothGeneralMetricBVZero :
    SmoothGeneralMetricBVField period hPeriod :=
  (smoothGeneralMetricTensorPairZero period hPeriod,
    smoothGeneralMetricTensorPairZero period hPeriod)

def smoothGeneralMetricBVNeg
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    SmoothGeneralMetricBVField period hPeriod :=
  (smoothGeneralMetricTensorPairNeg period hPeriod phase.1,
    smoothGeneralMetricTensorPairNeg period hPeriod phase.2)

/-- Grading involution: tensor variations are even and antifields odd. -/
def smoothGeneralMetricBVParity
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    SmoothGeneralMetricBVField period hPeriod :=
  (phase.1, smoothGeneralMetricTensorPairNeg period hPeriod phase.2)

@[simp]
theorem smoothGeneralMetricBVParity_involutive
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    smoothGeneralMetricBVParity period hPeriod
        (smoothGeneralMetricBVParity period hPeriod phase) = phase := by
  apply Prod.ext
  · rfl
  · exact smoothGeneralMetricTensorPairNeg_involutive
      period hPeriod phase.2

/-- Nontrivial contractible odd doublet `Q(h,h⁺) = (h⁺,0)`. -/
def smoothGeneralMetricBVBRST
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    SmoothGeneralMetricBVField period hPeriod :=
  (phase.2, smoothGeneralMetricTensorPairZero period hPeriod)

@[simp]
theorem smoothGeneralMetricBVBRST_square_zero
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    smoothGeneralMetricBVBRST period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod phase) =
      smoothGeneralMetricBVZero period hPeriod :=
  rfl

theorem smoothGeneralMetricBVBRST_parity_odd
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    smoothGeneralMetricBVParity period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod phase) =
      smoothGeneralMetricBVNeg period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod
          (smoothGeneralMetricBVParity period hPeriod phase)) := by
  apply Prod.ext
  · exact (smoothGeneralMetricTensorPairNeg_involutive
      period hPeriod phase.2).symm
  · rfl

/-! ## Background-raised canonical pointwise pairing and odd bracket -/

/-- Raise one index of a tensor variation with the genuine background
general Lorentz metric. -/
def raisedGeneralMetricTensorAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    GeneralMetricTangentFiber period hPeriod point →L[Real]
      GeneralMetricTangentFiber period hPeriod point :=
  (metric.musical point).symm.toContinuousLinearMap.comp
    (tensor.tensor point)

/-- Invariant pointwise pairing `tr(g⁻¹h g⁻¹k)` supplied by the
background Lorentz metric. -/
def generalMetricTensorPairingAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  LinearMap.trace Real (GeneralMetricTangentFiber period hPeriod point)
    ((raisedGeneralMetricTensorAt period hPeriod metric first point).toLinearMap *
      (raisedGeneralMetricTensorAt period hPeriod metric second point).toLinearMap)

theorem generalMetricTensorPairingAt_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric first second point =
      generalMetricTensorPairingAt period hPeriod metric second first point := by
  exact LinearMap.trace_mul_comm Real _ _

/-- Sum of the canonical pointwise pairings in both metric sectors. -/
def generalMetricTensorPairPairingAt
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  generalMetricTensorPairingAt period hPeriod metrics.1
      first.1 second.1 point +
    generalMetricTensorPairingAt period hPeriod metrics.2
      first.2 second.2 point

theorem generalMetricTensorPairPairingAt_symmetric
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod metrics first second point =
      generalMetricTensorPairPairingAt period hPeriod metrics second first point := by
  rw [generalMetricTensorPairPairingAt, generalMetricTensorPairPairingAt,
    generalMetricTensorPairingAt_symmetric period hPeriod metrics.1 first.1 second.1,
    generalMetricTensorPairingAt_symmetric period hPeriod metrics.2 first.2 second.2]

/-- Pointwise observable data with the two Darboux gradients.  No functional
smoothness or variational-derivative claim is attached. -/
structure GeneralMetricBVPointObservable where
  parity : FiniteBVParity
  value : SmoothGeneralMetricBVField period hPeriod →
    EffectiveQuotient period hPeriod → Real
  fieldGradient : SmoothGeneralMetricBVField period hPeriod →
    SmoothGeneralMetricTensorPair period hPeriod
  antifieldGradient : SmoothGeneralMetricBVField period hPeriod →
    SmoothGeneralMetricTensorPair period hPeriod

/-- Canonical pointwise odd antibracket in the background-raised Darboux
coordinates of the two general metric sectors. -/
def generalMetricBVOddAntibracketAt
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  generalMetricTensorPairPairingAt period hPeriod metrics
      (first.fieldGradient phase) (second.antifieldGradient phase) point -
    finiteBVOddKoszulSign first.parity second.parity *
      generalMetricTensorPairPairingAt period hPeriod metrics
        (second.fieldGradient phase) (first.antifieldGradient phase) point

theorem generalMetricBVOddAntibracketAt_graded_skew
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricBVOddAntibracketAt period hPeriod metrics
        first second phase point =
      -finiteBVOddKoszulSign first.parity second.parity *
        generalMetricBVOddAntibracketAt period hPeriod metrics
          second first phase point := by
  rcases first with ⟨firstParity, firstValue, firstField, firstAntifield⟩
  rcases second with ⟨secondParity, secondValue, secondField, secondAntifield⟩
  have hFirst := generalMetricTensorPairPairingAt_symmetric period hPeriod
    metrics (firstField phase) (secondAntifield phase) point
  have hSecond := generalMetricTensorPairPairingAt_symmetric period hPeriod
    metrics (secondField phase) (firstAntifield phase) point
  cases firstParity <;> cases secondParity <;>
    simp only [generalMetricBVOddAntibracketAt, finiteBVOddKoszulSign] at * <;>
    linarith

/-! ## Connection to the independent general-Lorentz packet -/

/-- The existing independent fields together with their first-level metric
BV tangent/antifield sector. -/
@[ext]
structure GeneralLorentzIndependentFieldsWithMetricBV where
  independent : GeneralLorentzIndependentFields period hPeriod
  metricBV : SmoothGeneralMetricBVField period hPeriod

/-- Canonical zero-BV extension of every existing independent packet. -/
def attachZeroGeneralMetricBV
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    GeneralLorentzIndependentFieldsWithMetricBV period hPeriod where
  independent := fields
  metricBV := smoothGeneralMetricBVZero period hPeriod

@[simp]
theorem attachZeroGeneralMetricBV_independent
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (attachZeroGeneralMetricBV period hPeriod fields).independent = fields :=
  rfl

/-- Formal affine tensor pair underlying a metric BV variation.  Its codomain
is deliberately the unrestricted symmetric tensor space, not the Lorentz
metric domain. -/
def generalLorentzMetricFormalAffineTensors
    (fields : GeneralLorentzIndependentFields period hPeriod)
    (variation : SmoothGeneralMetricTensorPair period hPeriod)
    (epsilon : Real) : SmoothGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricTensorAdd period hPeriod fields.metrics.1.tensor
      (smoothSymmetricTensorSMul period hPeriod epsilon variation.1),
    smoothSymmetricTensorAdd period hPeriod fields.metrics.2.tensor
      (smoothSymmetricTensorSMul period hPeriod epsilon variation.2))

/-- Packet-level pointwise odd bracket, using its actual two background
general Lorentz metrics. -/
def generalLorentzPacketMetricBVOddAntibracketAt
    (packet : GeneralLorentzIndependentFieldsWithMetricBV period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  generalMetricBVOddAntibracketAt period hPeriod
    packet.independent.metrics first second packet.metricBV point

end

end P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
end JanusFormal
