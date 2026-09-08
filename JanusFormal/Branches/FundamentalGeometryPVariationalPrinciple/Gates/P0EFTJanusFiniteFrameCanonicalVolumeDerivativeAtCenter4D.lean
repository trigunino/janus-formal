import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2InteractionFrozenVolumeDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D

/-! # Derivative of the finite-frame canonical volume at the chart center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameCanonicalVolumeDerivativeAtCenter4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
open P0EFTJanusVariableMetricCanonicalVolumeRatio4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

private theorem continuousScalarAbs_hasFDerivAt_one :
    HasFDerivAt (continuousScalarAbs : C0Scalar period hPeriod → C0Scalar period hPeriod)
      (ContinuousLinearMap.id Real (C0Scalar period hPeriod)) 1 := by
  have hPositiveOpen : IsOpen
      {value : C0Scalar period hPeriod | ∀ point, 0 < value point} := by
    simpa only [range_subset_iff, mem_Ioi] using
      (ContinuousMap.isOpen_setOf_range_subset
        (X := EffectiveQuotient period hPeriod) (isOpen_Ioi : IsOpen (Ioi (0 : Real))))
  have hNeighborhood :
      {value : C0Scalar period hPeriod | ∀ point, 0 < value point} ∈
        𝓝 (1 : C0Scalar period hPeriod) :=
    hPositiveOpen.mem_nhds (fun _ => by norm_num)
  have hEqual :
      (continuousScalarAbs : C0Scalar period hPeriod → C0Scalar period hPeriod) =ᶠ[𝓝
        (1 : C0Scalar period hPeriod)] fun value => value := by
    filter_upwards [hNeighborhood] with value hValue
    apply ContinuousMap.ext
    intro point
    exact abs_of_pos (hValue point)
  exact (ContinuousLinearMap.id Real (C0Scalar period hPeriod)).hasFDerivAt.congr_of_eventuallyEq
    hEqual

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
private abbrev Model := GeneralMetricRelativeC2Core period hPeriod frame baseMetric

/-- Half-trace derivative of the canonical C⁰ volume coefficient. -/
def finiteFrameCanonicalVolumeC0DerivativeAtZero :
    Model period hPeriod frame baseMetric →L[Real] C0Scalar period hPeriod :=
  ((ContinuousLinearMap.mul Real (C0Scalar period hPeriod))
      (smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothMetricVolumeRatio period hPeriod baseMetric))).comp
    ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
      (generalMetricRelativeC2VolumeRatioDerivativeAtZero period hPeriod frame baseMetric))

theorem finiteFrameCanonicalVolumeC0_hasFDerivAt_zero :
    HasFDerivAt (finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric)
      (finiteFrameCanonicalVolumeC0DerivativeAtZero period hPeriod frame baseMetric) 0 := by
  have hRoot := generalMetricRelativeC2VolumeRatio_hasFDerivAt_zero period hPeriod frame baseMetric
  have hReadout :=
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).hasFDerivAt.comp 0 hRoot
  have hRootZero :
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (generalMetricRelativeC2VolumeRatio period hPeriod frame baseMetric 0) =
        (1 : C0Scalar period hPeriod) := by
    rw [generalMetricRelativeC2VolumeRatio_zero]
    rfl
  have hAbsAt : HasFDerivAt
      (continuousScalarAbs : C0Scalar period hPeriod → C0Scalar period hPeriod)
      (ContinuousLinearMap.id Real (C0Scalar period hPeriod))
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (generalMetricRelativeC2VolumeRatio period hPeriod frame baseMetric 0)) := by
    rw [hRootZero]
    exact continuousScalarAbs_hasFDerivAt_one period hPeriod
  have hAbs := hAbsAt.comp 0 hReadout
  let baseVolume : C0Scalar period hPeriod :=
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (globalSmoothMetricVolumeRatio period hPeriod baseMetric)
  have hMultiply :=
    ((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)) baseVolume).hasFDerivAt.comp 0 hAbs
  exact hMultiply.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

@[simp]
theorem finiteFrameCanonicalVolumeC0DerivativeAtZero_apply
    (direction : Model period hPeriod frame baseMetric) :
    finiteFrameCanonicalVolumeC0DerivativeAtZero period hPeriod frame baseMetric direction =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (globalSmoothMetricVolumeRatio period hPeriod baseMetric) *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          ((1 / 2 : Real) •
            c2FiniteMatrixTrace period hPeriod frame.count direction.1) := by
  rfl

end
end P0EFTJanusFiniteFrameCanonicalVolumeDerivativeAtCenter4D
end JanusFormal
