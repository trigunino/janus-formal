import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationModuleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

/-!
# Positive smooth dualizer for the bulk metric pairing

The existing finite smooth tangent generators and each background metric
assemble a smooth covariant dualizer. Its background-raised pairing with a
tensor is the sum of squares of all finite-frame readings. Full support of the
canonical bulk volume then makes the integrated geometric dual faithful.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricPositiveDualizer4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Bundle MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev MetricPair :=
  SmoothGeneralMetricTensorPair period hPeriod

private abbrev effectiveBackground : EffectiveD8Background where
  period := period
  period_ne_zero := hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev SmoothBulkCovector :=
  EffectiveD8SmoothCovectorField (effectiveBackground period hPeriod)

/-! ## Separating finite-frame energy -/

/-- Sum of squares of all readings of one bulk symmetric tensor. -/
def generalMetricFrameEnergy
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ i, ∑ j,
    (tensor.tensor point (frame.vectorAt point i)
      (frame.vectorAt point j)) ^ 2

theorem generalMetricFrameEnergy_nonnegative
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ generalMetricFrameEnergy period hPeriod frame tensor point := by
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem generalMetricFrameEnergy_zero_reading
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hEnergy : generalMetricFrameEnergy
      period hPeriod frame tensor point = 0)
    (i j : Fin frame.count) :
    tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j) = 0 := by
  have hOuter :
      ∀ i ∈ Finset.univ,
        (∑ j,
          (tensor.tensor point (frame.vectorAt point i)
            (frame.vectorAt point j)) ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hEnergy
  have hSquare :
      (tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j)) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => sq_nonneg _)).mp
      (hOuter i (Finset.mem_univ i)) j (Finset.mem_univ j)
  exact sq_eq_zero_iff.mp hSquare

/-- Vanishing frame energy at one point forces the tensor value to vanish. -/
theorem generalMetricFrameEnergy_eq_zero_value
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hEnergy : generalMetricFrameEnergy
      period hPeriod frame tensor point = 0) :
    tensor.tensor point = 0 := by
  have hOuter : (tensor.tensor point).toLinearMap = 0 := by
    apply LinearMap.ext_on_range (frame.spansAt point)
    intro i
    apply ContinuousLinearMap.ext
    intro y
    have hInner :
        (tensor.tensor point (frame.vectorAt point i)).toLinearMap = 0 := by
      apply LinearMap.ext_on_range (frame.spansAt point)
      intro j
      exact generalMetricFrameEnergy_zero_reading
        period hPeriod frame tensor point hEnergy i j
    exact LinearMap.congr_fun hInner y
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun hOuter x

/-- Pointwise vanishing of the finite-frame energy detects the zero tensor. -/
theorem generalMetricFrameEnergy_pointwiseSeparates
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hEnergy :
      ∀ point,
        generalMetricFrameEnergy period hPeriod frame tensor point = 0) :
    tensor = 0 := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  exact generalMetricFrameEnergy_eq_zero_value
    period hPeriod frame tensor point (hEnergy point)

/-- Two-sector finite-frame energy. -/
def generalMetricPairFrameEnergy
    (frame : SmoothD8Frame period hPeriod)
    (tensor : MetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  generalMetricFrameEnergy period hPeriod frame tensor.1 point +
    generalMetricFrameEnergy period hPeriod frame tensor.2 point

theorem generalMetricPairFrameEnergy_nonnegative
    (frame : SmoothD8Frame period hPeriod)
    (tensor : MetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ generalMetricPairFrameEnergy
      period hPeriod frame tensor point :=
  add_nonneg
    (generalMetricFrameEnergy_nonnegative
      period hPeriod frame tensor.1 point)
    (generalMetricFrameEnergy_nonnegative
      period hPeriod frame tensor.2 point)

theorem generalMetricPairFrameEnergy_pointwiseSeparates
    (frame : SmoothD8Frame period hPeriod)
    (tensor : MetricPair period hPeriod)
    (hEnergy :
      ∀ point,
        generalMetricPairFrameEnergy
          period hPeriod frame tensor point = 0) :
    tensor = 0 := by
  have hFirst :
      ∀ point,
        generalMetricFrameEnergy
          period hPeriod frame tensor.1 point = 0 := by
    intro point
    have hFirstNonnegative :=
      generalMetricFrameEnergy_nonnegative
        period hPeriod frame tensor.1 point
    have hSecondNonnegative :=
      generalMetricFrameEnergy_nonnegative
        period hPeriod frame tensor.2 point
    have hSum := hEnergy point
    unfold generalMetricPairFrameEnergy at hSum
    linarith
  have hSecond :
      ∀ point,
        generalMetricFrameEnergy
          period hPeriod frame tensor.2 point = 0 := by
    intro point
    have hFirstNonnegative :=
      generalMetricFrameEnergy_nonnegative
        period hPeriod frame tensor.1 point
    have hSecondNonnegative :=
      generalMetricFrameEnergy_nonnegative
        period hPeriod frame tensor.2 point
    have hSum := hEnergy point
    unfold generalMetricPairFrameEnergy at hSum
    linarith
  apply Prod.ext
  · exact generalMetricFrameEnergy_pointwiseSeparates
      period hPeriod frame tensor.1 hFirst
  · exact generalMetricFrameEnergy_pointwiseSeparates
      period hPeriod frame tensor.2 hSecond

/-! ## Smooth finite-frame dualizer -/

/-- One frame reading as a genuine smooth scalar field. -/
def generalMetricFrameCoefficient
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (i j : Fin frame.count) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j)
  contMDiff_toFun := by
    have hApplied := tensor.tensor.contMDiff.clm_bundle_apply₂
      (frame.contMDiff_vector i) (frame.contMDiff_vector j)
    intro point
    have hAppliedAt := hApplied point
    rw [contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp]
theorem generalMetricFrameCoefficient_apply
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (i j : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricFrameCoefficient
        period hPeriod frame tensor i j point =
      tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j) :=
  rfl

/-- The finite-frame energy is smooth, hence continuous. -/
theorem generalMetricFrameEnergy_continuous
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Continuous
      (generalMetricFrameEnergy period hPeriod frame tensor) := by
  have hSmooth :
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (generalMetricFrameEnergy period hPeriod frame tensor) := by
    unfold generalMetricFrameEnergy
    apply ContMDiff.sum
    intro i _
    apply ContMDiff.sum
    intro j _
    exact
      (generalMetricFrameCoefficient
        period hPeriod frame tensor i j).contMDiff_toFun.pow 2
  exact hSmooth.continuous

theorem generalMetricPairFrameEnergy_continuous
    (frame : SmoothD8Frame period hPeriod)
    (tensor : MetricPair period hPeriod) :
    Continuous
      (generalMetricPairFrameEnergy period hPeriod frame tensor) :=
  (generalMetricFrameEnergy_continuous
      period hPeriod frame tensor.1).add
    (generalMetricFrameEnergy_continuous
      period hPeriod frame tensor.2)

private abbrev ModelTangent := CoverCoordinates
private abbrev ModelCovector := ModelTangent →L[Real] Real

private def bulkCovectorCoordinates
    (covector : SmoothBulkCovector period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) : ModelCovector :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (GeneralMetricTangentFiber period hPeriod)
    Real (fun _ : EffectiveQuotient period hPeriod => Real)
    anchor current anchor current (covector current)

private theorem bulkCovectorCoordinates_contMDiffAt
    (covector : SmoothBulkCovector period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, ModelCovector) ∞
      (bulkCovectorCoordinates period hPeriod covector anchor) anchor := by
  have hSmooth := covector.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2

private theorem bulkCovectorCoordinates_apply
    (covector : SmoothBulkCovector period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ModelTangent
        (GeneralMetricTangentFiber period hPeriod) anchor).baseSet)
    (vector : ModelTangent) :
    bulkCovectorCoordinates period hPeriod covector anchor current vector =
      covector current
        ((trivializationAt ModelTangent
          (GeneralMetricTangentFiber period hPeriod) anchor).symm
            current vector) := by
  unfold bulkCovectorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent (by simp)]
  simp

/-- The outer product of two smooth bulk covectors is a smooth tensor. -/
def smoothBulkCovectorOuterProduct
    (first second : SmoothBulkCovector period hPeriod) :
    SmoothCovariantTwoTensor period hPeriod where
  toFun := fun point => (first point).smulRight (second point)
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hFirst := bulkCovectorCoordinates_contMDiffAt
      period hPeriod first anchor
    have hSecond := bulkCovectorCoordinates_contMDiffAt
      period hPeriod second anchor
    have hOuter :
        ContMDiffAt coverModelWithCorners
          𝓘(Real, ModelTangent →L[Real] ModelCovector) ∞
          (fun current =>
            (bulkCovectorCoordinates
              period hPeriod first anchor current).smulRight
              (bulkCovectorCoordinates
                period hPeriod second anchor current)) anchor :=
      (contDiff_fst.smulRight contDiff_snd).comp_contMDiffAt
        (hFirst.prodMk_space hSecond)
    apply hOuter.congr_of_eventuallyEq
    have hCurrent : ∀ᶠ current in 𝓝 anchor,
        current ∈
          (trivializationAt ModelTangent
            (GeneralMetricTangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelTangent
        (GeneralMetricTangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelTangent
            (GeneralMetricTangentFiber period hPeriod) anchor)
    filter_upwards [hCurrent] with current hCurrent'
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    rw [inCoordinates_apply_eq₂ hCurrent' hCurrent' (Set.mem_univ _)]
    simp only [ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul]
    rw [bulkCovectorCoordinates_apply
      period hPeriod first anchor current hCurrent' firstVector]
    rw [bulkCovectorCoordinates_apply
      period hPeriod second anchor current hCurrent' secondVector]
    simp

@[simp]
theorem smoothBulkCovectorOuterProduct_apply
    (first second : SmoothBulkCovector period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (left right : GeneralMetricTangentFiber period hPeriod point) :
    smoothBulkCovectorOuterProduct
        period hPeriod first second point left right =
      first point left * second point right :=
  rfl

/-- Symmetrized outer product of smooth bulk covectors. -/
def smoothBulkCovectorSymmetricProduct
    (first second : SmoothBulkCovector period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor :=
    (1 / 2 : Real) •
        smoothBulkCovectorOuterProduct period hPeriod first second +
      (1 / 2 : Real) •
        smoothBulkCovectorOuterProduct period hPeriod second first
  symmetric := by
    intro point left right
    change
      (1 / 2 : Real) * (first point left * second point right) +
          (1 / 2 : Real) * (second point left * first point right) =
        (1 / 2 : Real) * (first point right * second point left) +
          (1 / 2 : Real) * (second point right * first point left)
    ring

@[simp]
theorem smoothBulkCovectorSymmetricProduct_apply
    (first second : SmoothBulkCovector period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (left right : GeneralMetricTangentFiber period hPeriod point) :
    (smoothBulkCovectorSymmetricProduct
      period hPeriod first second).tensor point left right =
      (1 / 2 : Real) * (first point left * second point right) +
        (1 / 2 : Real) * (second point left * first point right) :=
  rfl

/-- Smooth scalar multiplication before imposing tensor symmetry. -/
def smoothBulkScalarSMulCovariantTensor
    (scalar : SmoothQuotientField period hPeriod Real)
    (tensor : SmoothCovariantTwoTensor period hPeriod) :
    SmoothCovariantTwoTensor period hPeriod where
  toFun := fun point => scalar point • tensor point
  contMDiff_toFun :=
    scalar.contMDiff_toFun.smul_section tensor.contMDiff

/-- Smooth pointwise scalar multiplication of a symmetric tensor. -/
def smoothBulkScalarSMulTensor
    (scalar : SmoothQuotientField period hPeriod Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor :=
    smoothBulkScalarSMulCovariantTensor
      period hPeriod scalar tensor.tensor
  symmetric := by
    intro point first second
    change scalar point * tensor.tensor point first second =
      scalar point * tensor.tensor point second first
    rw [tensor.symmetric]

@[simp]
theorem smoothBulkScalarSMulTensor_apply
    (scalar : SmoothQuotientField period hPeriod Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : GeneralMetricTangentFiber period hPeriod point) :
    (smoothBulkScalarSMulTensor
      period hPeriod scalar tensor).tensor point first second =
      scalar point * tensor.tensor point first second :=
  rfl

/-- Contract a smooth tensor with one smooth finite-frame vector. -/
def generalMetricFrameCovector
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (index : Fin frame.count) :
    SmoothBulkCovector period hPeriod where
  toFun := fun point =>
    tensor.tensor point (frame.vectorAt point index)
  contMDiff_toFun :=
    tensor.tensor.contMDiff.clm_bundle_apply
      (frame.contMDiff_vector index)

@[simp]
theorem generalMetricFrameCovector_apply
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (index : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricFrameCovector
        period hPeriod frame tensor index point =
      tensor.tensor point (frame.vectorAt point index) :=
  rfl

/-- Smooth finite-frame dualizer built from a background metric. -/
def generalMetricSmoothFrameDualizer
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  ∑ i, ∑ j,
    smoothBulkScalarSMulTensor period hPeriod
      (generalMetricFrameCoefficient period hPeriod frame tensor i j)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (generalMetricFrameCovector
          period hPeriod frame metric.tensor i)
        (generalMetricFrameCovector
          period hPeriod frame metric.tensor j))

/-- Componentwise smooth dualizer for the two bulk metric sectors. -/
def generalMetricPairSmoothFrameDualizer
    (frame : SmoothD8Frame period hPeriod)
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (tensor : MetricPair period hPeriod) :
    MetricPair period hPeriod :=
  (generalMetricSmoothFrameDualizer
      period hPeriod frame metrics.1 tensor.1,
    generalMetricSmoothFrameDualizer
      period hPeriod frame metrics.2 tensor.2)

theorem generalMetricSymmetricFrameProduct_pairing
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (i j : Fin frame.count) :
    generalMetricTensorPairingAt period hPeriod metric tensor
        (smoothBulkCovectorSymmetricProduct period hPeriod
          (generalMetricFrameCovector
            period hPeriod frame metric.tensor i)
          (generalMetricFrameCovector
            period hPeriod frame metric.tensor j))
        point =
      tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j) := by
  apply generalMetricTensorPairingAt_symmetricMetricRankOne
  intro left right
  rfl

/-- The bulk smooth dualizer realizes the finite-frame sum of squares. -/
theorem generalMetricSmoothFrameDualizer_pairing_eq_energy
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric tensor
        (generalMetricSmoothFrameDualizer
          period hPeriod frame metric tensor) point =
      generalMetricFrameEnergy period hPeriod frame tensor point := by
  let pairing :
      SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real := {
    toFun := fun second =>
      generalMetricTensorPairingAt
        period hPeriod metric tensor second point
    map_add' := by
      intro first second
      exact generalMetricTensorPairingAt_add_right
        period hPeriod metric tensor first second point
    map_smul' := by
      intro scalar second
      exact generalMetricTensorPairingAt_smul_right
        period hPeriod metric scalar tensor second point
    }
  change pairing
      (generalMetricSmoothFrameDualizer
        period hPeriod frame metric tensor) = _
  unfold generalMetricSmoothFrameDualizer generalMetricFrameEnergy
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  let rankOne :=
    smoothBulkCovectorSymmetricProduct period hPeriod
      (generalMetricFrameCovector
        period hPeriod frame metric.tensor i)
      (generalMetricFrameCovector
        period hPeriod frame metric.tensor j)
  have hCongr :
      pairing
          (smoothBulkScalarSMulTensor period hPeriod
            (generalMetricFrameCoefficient
              period hPeriod frame tensor i j) rankOne) =
        pairing
          ((generalMetricFrameCoefficient
            period hPeriod frame tensor i j point) • rankOne) := by
    apply generalMetricTensorPairingAt_congr_right_at
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    rfl
  rw [hCongr, map_smul]
  change
    tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j) *
        generalMetricTensorPairingAt
          period hPeriod metric tensor rankOne point =
      (tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j)) ^ 2
  rw [show generalMetricTensorPairingAt
      period hPeriod metric tensor rankOne point =
        tensor.tensor point (frame.vectorAt point i)
          (frame.vectorAt point j) by
    exact generalMetricSymmetricFrameProduct_pairing
      period hPeriod frame metric tensor point i j]
  ring

theorem generalMetricPairSmoothFrameDualizer_pairing_eq_energy
    (frame : SmoothD8Frame period hPeriod)
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (tensor : MetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod metrics tensor
        (generalMetricPairSmoothFrameDualizer
          period hPeriod frame metrics tensor) point =
      generalMetricPairFrameEnergy
        period hPeriod frame tensor point := by
  unfold generalMetricTensorPairPairingAt
    generalMetricPairSmoothFrameDualizer
    generalMetricPairFrameEnergy
  rw [generalMetricSmoothFrameDualizer_pairing_eq_energy,
    generalMetricSmoothFrameDualizer_pairing_eq_energy]

/-! ## Integrated separation and injectivity -/

/-- The canonical integrated bulk metric pairing separates its first slot. -/
theorem canonicalGeneralMetricTensorPairPairing_separates
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    ∀ antifield : MetricPair period hPeriod,
      (∀ field,
        canonicalGeneralMetricTensorPairPairing
          period hPeriod metrics antifield field = 0) →
      antifield = 0 := by
  intro antifield hZero
  let frame := finiteSmoothTangentFrame period hPeriod
  let dualizer :=
    generalMetricPairSmoothFrameDualizer
      period hPeriod frame metrics antifield
  let μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  letI : IsFiniteMeasure μ :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  letI : Measure.IsOpenPosMeasure μ :=
    intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod
  have hIntegral := hZero dualizer
  change (∫ point,
    generalMetricTensorPairPairingAt period hPeriod metrics
      antifield dualizer point ∂μ) = 0 at hIntegral
  have hPairing :
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricTensorPairPairingAt period hPeriod metrics
          antifield dualizer point) =
        generalMetricPairFrameEnergy
          period hPeriod frame antifield := by
    funext point
    exact generalMetricPairSmoothFrameDualizer_pairing_eq_energy
      period hPeriod frame metrics antifield point
  have hContinuous :
      Continuous
        (fun point : EffectiveQuotient period hPeriod =>
          generalMetricTensorPairPairingAt period hPeriod metrics
            antifield dualizer point) := by
    rw [hPairing]
    exact generalMetricPairFrameEnergy_continuous
      period hPeriod frame antifield
  have hIntegrable :
      Integrable
        (fun point : EffectiveQuotient period hPeriod =>
          generalMetricTensorPairPairingAt period hPeriod metrics
            antifield dualizer point) μ :=
    hContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hNonnegative :
      ∀ point : EffectiveQuotient period hPeriod,
        0 ≤ generalMetricTensorPairPairingAt period hPeriod metrics
          antifield dualizer point := by
    intro point
    rw [congrFun hPairing point]
    exact generalMetricPairFrameEnergy_nonnegative
      period hPeriod frame antifield point
  have hAE :
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricTensorPairPairingAt period hPeriod metrics
          antifield dualizer point) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg
      hNonnegative hIntegrable).mp hIntegral
  have hEverywhere :
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricTensorPairPairingAt period hPeriod metrics
          antifield dualizer point) =
        (fun _ => 0) :=
    (Continuous.ae_eq_iff_eq μ hContinuous continuous_const).mp hAE
  apply generalMetricPairFrameEnergy_pointwiseSeparates
    period hPeriod frame antifield
  intro point
  rw [← generalMetricPairSmoothFrameDualizer_pairing_eq_energy
    period hPeriod frame metrics antifield point]
  exact congrFun hEverywhere point

/-- The bulk geometric metric antifield realization is faithful. -/
theorem generalMetricGeometricAntifieldToAlgebraicDual_injective
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (generalMetricGeometricAntifieldToAlgebraicDual
        period hPeriod metrics) := by
  intro first second hEqual
  have hMapped :
      generalMetricGeometricAntifieldToAlgebraicDual
          period hPeriod metrics (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hDifference :
      first - second = 0 :=
    canonicalGeneralMetricTensorPairPairing_separates
      period hPeriod metrics (first - second)
      (fun field => LinearMap.congr_fun hMapped field)
  exact sub_eq_zero.mp hDifference

end
end P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
end JanusFormal
