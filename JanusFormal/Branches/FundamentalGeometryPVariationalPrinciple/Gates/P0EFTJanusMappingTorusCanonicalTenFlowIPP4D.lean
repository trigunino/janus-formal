import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumePreservingFlowIPP4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusJointAnalyticTimeAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D

/-! # The ten canonical volume-preserving flow directions -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowIPP4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusJointAnalyticTimeAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationQuotient4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationMeasure4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationSmooth4D
open P0EFTJanusMappingTorusCanonicalSpatialRotationQuotient4D
open P0EFTJanusMappingTorusCanonicalSpatialRotationMeasure4D
open P0EFTJanusMappingTorusCanonicalVolumePreservingFlowIPP4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The genuine complete quotient time action as invariant-flow data. -/
def canonicalTimeVolumePreservingFlow :
    CanonicalVolumePreservingFlow period hPeriod where
  flow := effectiveTimeFlow period hPeriod
  joint_contMDiff := by
    change ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞ (effectiveJointTimeFlow period hPeriod)
    convert (effectiveJointTimeFlow_contMDiff period hPeriod).of_le (by simp)
      using 1
  flow_zero := effectiveTimeFlow_zero period hPeriod
  flow_add := effectiveTimeFlow_add period hPeriod
  flow_embedding parameter :=
    (effectiveTimeFlowDiffeomorph period hPeriod parameter).toHomeomorph
      |>.measurableEmbedding
  measurePreserving :=
    intrinsicCanonicalLorentzVolumeMeasure_timeTranslation_measurePreserving
      period hPeriod

/-- One of the three genuine spatial rotation actions. -/
def canonicalSpatialVolumePreservingFlow (axis : Fin 3) :
    CanonicalVolumePreservingFlow period hPeriod where
  flow := spatialRotationFlow period hPeriod axis
  joint_contMDiff := by
    change ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      (jointSpatialRotationFlow period hPeriod axis)
    convert jointSpatialRotationFlow_contMDiff period hPeriod axis using 1
  flow_zero := spatialRotationFlow_zero period hPeriod axis
  flow_add := spatialRotationFlow_add period hPeriod axis
  flow_embedding := spatialRotationFlow_measurableEmbedding period hPeriod axis
  measurePreserving :=
    intrinsicCanonicalLorentzVolumeMeasure_spatialRotation_measurePreserving
      period hPeriod axis

/-- One of the six genuine phased normal rotation actions. -/
def canonicalPhasedNormalVolumePreservingFlow
    (axis : Fin 3) (phase : Fin 2) :
    CanonicalVolumePreservingFlow period hPeriod where
  flow := phasedNormalRotationFlow period hPeriod axis phase
  joint_contMDiff := by
    change ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      (jointPhasedNormalRotationFlow period hPeriod axis phase)
    convert jointPhasedNormalRotationFlow_contMDiff period hPeriod axis phase
      using 1
  flow_zero := phasedNormalRotationFlow_zero period hPeriod axis phase
  flow_add := phasedNormalRotationFlow_add period hPeriod axis phase
  flow_embedding :=
    phasedNormalRotationFlow_measurableEmbedding period hPeriod axis phase
  measurePreserving :=
    intrinsicCanonicalLorentzVolumeMeasure_phasedNormalRotation_measurePreserving
      period hPeriod axis phase

/-- One time, three spatial and six phased-normal directions. -/
inductive CanonicalFlowIndex
  | time
  | spatial (axis : Fin 3)
  | phasedNormal (axis : Fin 3) (phase : Fin 2)
  deriving DecidableEq, Fintype

theorem canonicalFlowIndex_card : Fintype.card CanonicalFlowIndex = 10 := by
  native_decide

/-- Uniform access to all ten canonical invariant flows. -/
def canonicalVolumePreservingFlow (index : CanonicalFlowIndex) :
    CanonicalVolumePreservingFlow period hPeriod :=
  match index with
  | .time => canonicalTimeVolumePreservingFlow period hPeriod
  | .spatial axis => canonicalSpatialVolumePreservingFlow period hPeriod axis
  | .phasedNormal axis phase =>
      canonicalPhasedNormalVolumePreservingFlow period hPeriod axis phase

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Directional derivative along one member of the canonical ten-flow family. -/
def canonicalFlowDirectionalDerivative
    (index : CanonicalFlowIndex)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) : Fiber :=
  canonicalFlowDerivative period hPeriod Fiber
    (canonicalVolumePreservingFlow period hPeriod index) field point

theorem canonicalFlowDirectionalDerivative_contMDiff
    (index : CanonicalFlowIndex)
    (field : SmoothQuotientField period hPeriod Fiber) :
    ContMDiff coverModelWithCorners 𝓘(Real, Fiber) ∞
      (canonicalFlowDirectionalDerivative period hPeriod Fiber index field) :=
  canonicalFlowDerivative_contMDiff period hPeriod Fiber
    (canonicalVolumePreservingFlow period hPeriod index) field

/-- Global boundaryless IPP for every one of the ten canonical directions. -/
theorem canonicalTenFlow_integral_inner_derivative_eq_neg
    {InnerFiber : Type*} [NormedAddCommGroup InnerFiber]
    [InnerProductSpace Real InnerFiber]
    (index : CanonicalFlowIndex)
    (first second : SmoothQuotientField period hPeriod InnerFiber) :
    (∫ point, inner Real (first point)
        (canonicalFlowDirectionalDerivative period hPeriod InnerFiber
          index second point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      -∫ point, inner Real
        (canonicalFlowDirectionalDerivative period hPeriod InnerFiber
          index first point)
        (second point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  canonicalVolumePreservingFlow_integral_inner_derivative_eq_neg
    period hPeriod (canonicalVolumePreservingFlow period hPeriod index)
      first second

/-- Gate marker: all ten global directions satisfy exact canonical-volume IPP. -/
theorem canonical_ten_flow_ipp_gate :
    ∀ (index : CanonicalFlowIndex)
      (first second : SmoothQuotientField period hPeriod Real),
      (∫ point, inner Real (first point)
          (canonicalFlowDirectionalDerivative period hPeriod Real
            index second point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
        -∫ point, inner Real
          (canonicalFlowDirectionalDerivative period hPeriod Real
            index first point)
          (second point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  canonicalTenFlow_integral_inner_derivative_eq_neg period hPeriod

end
end P0EFTJanusMappingTorusCanonicalTenFlowIPP4D
end JanusFormal
