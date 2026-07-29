import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricFrameEnergySmooth4D

/-!
# Smooth finite-frame throat metric dualizer

Bundlewise application turns a smooth covariant tensor and every smooth
finite-frame vector into a genuine smooth covector section.  Smooth scalar
coefficients multiply symmetrized covector outer products, producing the
genuine smooth positive dualizer used by the BRST throat metric sector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricFrameCovectorSmooth4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusProgramPThroatMetricTensorModule4D
open P0EFTJanusProgramPThroatMetricGeneratingFrameSeparation4D
open P0EFTJanusProgramPThroatMetricFrameEnergySmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev SmoothThroatCovector :=
  ContMDiffSection throatCoverModelWithCorners
    (ThroatCoverCoordinates →L[Real] Real) ∞
    (ThroatCotangentFiber period hPeriod)

private abbrev ModelTangent := ThroatCoverCoordinates

private abbrev ModelCovector := ModelTangent →L[Real] Real

private def throatCovectorCoordinates
    (covector : SmoothThroatCovector period hPeriod)
    (anchor current : EffectiveThroat period hPeriod) : ModelCovector :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (ThroatTangentFiber period hPeriod)
    Real (fun _ : EffectiveThroat period hPeriod => Real)
    anchor current anchor current (covector current)

private theorem throatCovectorCoordinates_contMDiffAt
    (covector : SmoothThroatCovector period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners 𝓘(Real, ModelCovector) ∞
      (throatCovectorCoordinates period hPeriod covector anchor) anchor := by
  have hSmooth := covector.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2

private theorem throatCovectorCoordinates_apply
    (covector : SmoothThroatCovector period hPeriod)
    (anchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ModelTangent
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (vector : ModelTangent) :
    throatCovectorCoordinates period hPeriod covector anchor current vector =
      covector current
        ((trivializationAt ModelTangent
          (ThroatTangentFiber period hPeriod) anchor).symm current vector) := by
  unfold throatCovectorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent (by simp)]
  simp

/-- The fiberwise outer product of two genuine smooth throat covectors is a
genuine smooth covariant two-tensor section. -/
def smoothThroatCovectorOuterProduct
    (first second : SmoothThroatCovector period hPeriod) :
    SmoothThroatCovariantTwoTensor period hPeriod where
  toFun := fun point => (first point).smulRight (second point)
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hFirst := throatCovectorCoordinates_contMDiffAt
      period hPeriod first anchor
    have hSecond := throatCovectorCoordinates_contMDiffAt
      period hPeriod second anchor
    have hOuter :
        ContMDiffAt throatCoverModelWithCorners
          𝓘(Real, ModelTangent →L[Real] ModelCovector) ∞
          (fun current =>
            (throatCovectorCoordinates
              period hPeriod first anchor current).smulRight
              (throatCovectorCoordinates
                period hPeriod second anchor current)) anchor :=
      (contDiff_fst.smulRight contDiff_snd).comp_contMDiffAt
        (hFirst.prodMk_space hSecond)
    apply hOuter.congr_of_eventuallyEq
    have hCurrent : ∀ᶠ current in 𝓝 anchor,
        current ∈
          (trivializationAt ModelTangent
            (ThroatTangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelTangent
        (ThroatTangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelTangent
            (ThroatTangentFiber period hPeriod) anchor)
    filter_upwards [hCurrent] with current hCurrent'
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    rw [inCoordinates_apply_eq₂ hCurrent' hCurrent' (Set.mem_univ _)]
    simp only [ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul]
    rw [throatCovectorCoordinates_apply
      period hPeriod first anchor current hCurrent' firstVector]
    rw [throatCovectorCoordinates_apply
      period hPeriod second anchor current hCurrent' secondVector]
    simp

@[simp]
theorem smoothThroatCovectorOuterProduct_apply
    (first second : SmoothThroatCovector period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (left right : ThroatTangentFiber period hPeriod point) :
    smoothThroatCovectorOuterProduct
        period hPeriod first second point left right =
      first point left * second point right :=
  rfl

/-- Symmetrized outer product of two smooth throat covectors. -/
def smoothThroatCovectorSymmetricProduct
    (first second : SmoothThroatCovector period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod where
  tensor :=
    (1 / 2 : Real) •
        smoothThroatCovectorOuterProduct period hPeriod first second +
      (1 / 2 : Real) •
        smoothThroatCovectorOuterProduct period hPeriod second first
  symmetric := by
    intro point left right
    change
      (1 / 2 : Real) * (first point left * second point right) +
          (1 / 2 : Real) * (second point left * first point right) =
        (1 / 2 : Real) * (first point right * second point left) +
          (1 / 2 : Real) * (second point right * first point left)
    ring

@[simp]
theorem smoothThroatCovectorSymmetricProduct_apply
    (first second : SmoothThroatCovector period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (left right : ThroatTangentFiber period hPeriod point) :
    (smoothThroatCovectorSymmetricProduct
      period hPeriod first second).tensor point left right =
      (1 / 2 : Real) * (first point left * second point right) +
        (1 / 2 : Real) * (second point left * first point right) :=
  rfl

/-- Smooth scalar multiplication before imposing tensor symmetry. -/
def smoothThroatScalarSMulCovariantTensor
    (scalar : SmoothThroatField period hPeriod Real)
    (tensor : SmoothThroatCovariantTwoTensor period hPeriod) :
    SmoothThroatCovariantTwoTensor period hPeriod where
  toFun := fun point => scalar point • tensor point
  contMDiff_toFun :=
    scalar.contMDiff_toFun.smul_section tensor.contMDiff

@[simp]
theorem smoothThroatScalarSMulCovariantTensor_apply
    (scalar : SmoothThroatField period hPeriod Real)
    (tensor : SmoothThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    smoothThroatScalarSMulCovariantTensor
        period hPeriod scalar tensor point first second =
      scalar point * tensor point first second :=
  rfl

/-- Contraction of a smooth throat tensor with a smooth frame vector is a
genuine smooth covector section. -/
def throatMetricFrameCovector
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : Fin frame.count) :
    SmoothThroatCovector period hPeriod where
  toFun := fun point =>
    tensor.tensor point (frame.vectorAt point index)
  contMDiff_toFun :=
    tensor.tensor.contMDiff.clm_bundle_apply
      (frame.contMDiff_vector index)

@[simp]
theorem throatMetricFrameCovector_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : Fin frame.count)
    (point : EffectiveThroat period hPeriod) :
    throatMetricFrameCovector period hPeriod frame tensor index point =
      tensor.tensor point (frame.vectorAt point index) :=
  rfl

/-- Pointwise multiplication by a smooth scalar preserves genuine smooth
symmetric throat tensors. -/
def smoothThroatScalarSMulTensor
    (scalar : SmoothThroatField period hPeriod Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod where
  tensor :=
    smoothThroatScalarSMulCovariantTensor
      period hPeriod scalar tensor.tensor
  symmetric := by
    intro point first second
    change scalar point * tensor.tensor point first second =
      scalar point * tensor.tensor point second first
    rw [tensor.symmetric]

@[simp]
theorem smoothThroatScalarSMulTensor_apply
    (scalar : SmoothThroatField period hPeriod Real)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    (smoothThroatScalarSMulTensor
      period hPeriod scalar tensor).tensor point first second =
      scalar point * tensor.tensor point first second :=
  rfl

/-- Finite weighted smooth dualizer assembled without choosing a global
basis. The metric tensor is an explicit parameter, avoiding any coercion
between the existing nondegenerate-metric wrappers. -/
def throatMetricSmoothFrameDualizer
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (metric tensor :
      SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod :=
  ∑ i, ∑ j,
    smoothThroatScalarSMulTensor period hPeriod
      (throatMetricFrameCoefficient period hPeriod frame tensor i j)
      (smoothThroatCovectorSymmetricProduct period hPeriod
        (throatMetricFrameCovector period hPeriod frame metric i)
        (throatMetricFrameCovector period hPeriod frame metric j))

/-- Specialization of the smooth finite-frame dualizer to the certified
intrinsic nondegenerate throat metric. -/
def intrinsicThroatMetricSmoothFrameDualizer
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod :=
  throatMetricSmoothFrameDualizer period hPeriod frame
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 tensor

/-- Componentwise intrinsic smooth dualizer on the two-sector throat metric
pair used by the geometric antifield bridge. -/
def intrinsicThroatMetricPairSmoothFrameDualizer
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    SmoothThroatGeneralMetricTensorPair period hPeriod :=
  (intrinsicThroatMetricSmoothFrameDualizer
      period hPeriod frame tensor.1,
    intrinsicThroatMetricSmoothFrameDualizer
      period hPeriod frame tensor.2)

theorem intrinsicThroatMetricSymmetricFrameProduct_pairing
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (i j : Fin frame.count) :
    intrinsicThroatTensorPairingAt period hPeriod tensor
        (smoothThroatCovectorSymmetricProduct period hPeriod
          (throatMetricFrameCovector period hPeriod frame
            (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 i)
          (throatMetricFrameCovector period hPeriod frame
            (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 j))
        point =
      tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j) := by
  apply intrinsicThroatTensorPairingAt_symmetricMetricRankOne
  intro left right
  rfl

/-- The assembled intrinsic smooth dualizer realizes the separating
finite-frame energy pointwise. -/
theorem intrinsicThroatMetricSmoothFrameDualizer_pairing_eq_energy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairingAt period hPeriod tensor
        (intrinsicThroatMetricSmoothFrameDualizer
          period hPeriod frame tensor) point =
      throatMetricFrameEnergy period hPeriod frame tensor point := by
  let pairing :
      SmoothSymmetricThroatCovariantTwoTensor period hPeriod →ₗ[Real] Real :=
    {
      toFun := fun second =>
        intrinsicThroatTensorPairingAt period hPeriod tensor second point
      map_add' := by
        intro first second
        exact intrinsicThroatTensorPairingAt_add_right
          period hPeriod tensor first second point
      map_smul' := by
        intro scalar second
        exact intrinsicThroatTensorPairingAt_smul_right
          period hPeriod scalar tensor second point
    }
  change pairing
      (throatMetricSmoothFrameDualizer period hPeriod frame
        (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 tensor) =
    _
  unfold throatMetricSmoothFrameDualizer throatMetricFrameEnergy
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  let rankOne :=
    smoothThroatCovectorSymmetricProduct period hPeriod
      (throatMetricFrameCovector period hPeriod frame
        (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 i)
      (throatMetricFrameCovector period hPeriod frame
        (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 j)
  have hCongr :
      pairing
          (smoothThroatScalarSMulTensor period hPeriod
            (throatMetricFrameCoefficient
              period hPeriod frame tensor i j) rankOne) =
        pairing
          ((throatMetricFrameCoefficient
            period hPeriod frame tensor i j point) • rankOne) := by
    apply intrinsicThroatTensorPairingAt_congr_right_at
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    rfl
  rw [hCongr, map_smul]
  change
    tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j) *
        intrinsicThroatTensorPairingAt period hPeriod tensor rankOne point =
      (tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j)) ^ 2
  rw [show intrinsicThroatTensorPairingAt
      period hPeriod tensor rankOne point =
        tensor.tensor point (frame.vectorAt point i)
          (frame.vectorAt point j) by
    exact intrinsicThroatMetricSymmetricFrameProduct_pairing
      period hPeriod frame tensor point i j]
  ring

theorem intrinsicThroatMetricPairSmoothFrameDualizer_pairing_eq_energy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicThroatTensorPairPairingAt period hPeriod tensor
        (intrinsicThroatMetricPairSmoothFrameDualizer
          period hPeriod frame tensor) point =
      throatMetricPairFrameEnergy period hPeriod frame tensor point := by
  unfold intrinsicThroatTensorPairPairingAt
    intrinsicThroatMetricPairSmoothFrameDualizer
    throatMetricPairFrameEnergy
  rw [intrinsicThroatMetricSmoothFrameDualizer_pairing_eq_energy,
    intrinsicThroatMetricSmoothFrameDualizer_pairing_eq_energy]

end
end P0EFTJanusProgramPThroatMetricFrameCovectorSmooth4D
end JanusFormal
