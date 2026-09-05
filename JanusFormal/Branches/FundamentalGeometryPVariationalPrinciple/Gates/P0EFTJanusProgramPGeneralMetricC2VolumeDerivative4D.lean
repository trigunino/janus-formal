import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

/-! # Exact first derivative of the general-metric C² volume density -/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRootDerivative4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Linear part of the affine relative matrix `I + g⁻¹h`. -/
def generalMetricRelativeC2ExtendedMatrixDerivative
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    GeneralMetricRelativeC2Core period hPeriod frame baseMetric →L[Real]
      C2FiniteMatrix period hPeriod frame.count :=
  generalMetricRelativeC2CoreToMatrix period hPeriod frame baseMetric

theorem generalMetricRelativeC2ExtendedMatrix_hasFDerivAt_zero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    HasFDerivAt
      (generalMetricRelativeC2ExtendedMatrix period hPeriod frame baseMetric)
      (generalMetricRelativeC2ExtendedMatrixDerivative
        period hPeriod frame baseMetric) 0 := by
  let identity := c2FiniteMatrixIdentity period hPeriod frame.count
  let inclusion := generalMetricRelativeC2CoreToMatrix
    period hPeriod frame baseMetric
  have hAffine :=
    (hasFDerivAt_const
      (x := (0 : GeneralMetricRelativeC2Core
        period hPeriod frame baseMetric)) (c := identity)).add
      inclusion.hasFDerivAt
  apply (hAffine.congr_fderiv (zero_add inclusion)).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro variation
  rfl

/-- Trace pulled back through the authentic completed relative-metric core. -/
def generalMetricRelativeC2DeterminantDerivativeAtZero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    GeneralMetricRelativeC2Core period hPeriod frame baseMetric →L[Real]
      C2Scalar period hPeriod :=
  (c2FiniteMatrixTrace period hPeriod frame.count).comp
    (generalMetricRelativeC2ExtendedMatrixDerivative
      period hPeriod frame baseMetric)

theorem generalMetricRelativeC2Determinant_hasFDerivAt_zero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    HasFDerivAt
      (generalMetricRelativeC2Determinant period hPeriod frame baseMetric)
      (generalMetricRelativeC2DeterminantDerivativeAtZero
        period hPeriod frame baseMetric) 0 := by
  have hInner := generalMetricRelativeC2ExtendedMatrix_hasFDerivAt_zero
    period hPeriod frame baseMetric
  have hOuter :
      HasFDerivAt
        (c2FiniteMatrixDeterminant period hPeriod frame.count)
        (c2FiniteMatrixTrace period hPeriod frame.count)
        (generalMetricRelativeC2ExtendedMatrix
          period hPeriod frame baseMetric 0) := by
    simpa [generalMetricRelativeC2ExtendedMatrix] using
      c2FiniteMatrixDeterminant_hasFDerivAt_identity
        period hPeriod frame.count
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Half-trace derivative of the selected positive relative volume ratio. -/
def generalMetricRelativeC2VolumeRatioDerivativeAtZero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    GeneralMetricRelativeC2Core period hPeriod frame baseMetric →L[Real]
      C2Scalar period hPeriod :=
  (c2ScalarHalfIdentity period hPeriod).comp
    (generalMetricRelativeC2DeterminantDerivativeAtZero
      period hPeriod frame baseMetric)

theorem generalMetricRelativeC2VolumeRatio_hasFDerivAt_zero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    HasFDerivAt
      (generalMetricRelativeC2VolumeRatio period hPeriod frame baseMetric)
      (generalMetricRelativeC2VolumeRatioDerivativeAtZero
        period hPeriod frame baseMetric) 0 := by
  have hInner := generalMetricRelativeC2Determinant_hasFDerivAt_zero
    period hPeriod frame baseMetric
  have hOuter :
      HasFDerivAt (c2ScalarLocalRootBranch period hPeriod)
        (c2ScalarHalfIdentity period hPeriod)
        (generalMetricRelativeC2Determinant
          period hPeriod frame baseMetric 0) := by
    simpa only [generalMetricRelativeC2Determinant_zero] using
      c2ScalarLocalRootBranch_hasFDerivAt_one period hPeriod
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Exact volume-density derivative at the base metric. -/
def generalMetricC2VolumeDensityDerivativeAtZero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (baseVolume : SmoothQuotientField period hPeriod Real) :
    GeneralMetricRelativeC2Core period hPeriod frame baseMetric →L[Real]
      C2Scalar period hPeriod :=
  (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod baseVolume)).comp
    (generalMetricRelativeC2VolumeRatioDerivativeAtZero
      period hPeriod frame baseMetric)

theorem generalMetricC2VolumeDensity_hasFDerivAt_zero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (baseVolume : SmoothQuotientField period hPeriod Real) :
    HasFDerivAt
      (generalMetricC2VolumeDensity
        period hPeriod frame baseMetric baseVolume)
      (generalMetricC2VolumeDensityDerivativeAtZero
        period hPeriod frame baseMetric baseVolume) 0 := by
  have hInner := generalMetricRelativeC2VolumeRatio_hasFDerivAt_zero
    period hPeriod frame baseMetric
  have hOuter : HasFDerivAt
      (fun field => canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore
          period hPeriod baseVolume) field)
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore
          period hPeriod baseVolume))
      (generalMetricRelativeC2VolumeRatio
        period hPeriod frame baseMetric 0) :=
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore
        period hPeriod baseVolume)).hasFDerivAt
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

@[simp]
theorem generalMetricC2VolumeDensityDerivativeAtZero_apply
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (baseVolume : SmoothQuotientField period hPeriod Real)
    (direction : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :
    generalMetricC2VolumeDensityDerivativeAtZero
        period hPeriod frame baseMetric baseVolume direction =
      (1 / 2 : Real) •
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (smoothToCanonicalPhysicalScalarC2JetCore
            period hPeriod baseVolume)
          (c2FiniteMatrixTrace period hPeriod frame.count direction.1) := by
  change canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod baseVolume)
      ((1 / 2 : Real) •
        c2FiniteMatrixTrace period hPeriod frame.count direction.1) = _
  exact (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
    (smoothToCanonicalPhysicalScalarC2JetCore
      period hPeriod baseVolume)).map_smul _ _

/-- The derivative specialized to the genuine regular metric chart. -/
def regularGeneralMetricC2VolumeDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C2Scalar period hPeriod :=
  generalMetricC2VolumeDensityDerivativeAtZero period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric metric.volume

theorem regularGeneralMetricC2Volume_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    HasFDerivAt (regularGeneralMetricC2Volume period hPeriod metric)
      (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric) 0 :=
  generalMetricC2VolumeDensity_hasFDerivAt_zero period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric metric.volume

/-- Gate marker for the exact half-trace variation of physical C² volume. -/
theorem general_metric_c2_volume_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    HasFDerivAt (regularGeneralMetricC2Volume period hPeriod metric)
        (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric) 0 ∧
      ∀ direction,
        regularGeneralMetricC2VolumeDerivativeAtZero
            period hPeriod metric direction =
          (1 / 2 : Real) •
            canonicalPhysicalScalarC2JetCoreProduct period hPeriod
              (smoothToCanonicalPhysicalScalarC2JetCore
                period hPeriod metric.volume)
              (c2FiniteMatrixTrace period hPeriod 4 direction.1) :=
  ⟨regularGeneralMetricC2Volume_hasFDerivAt_zero
      period hPeriod metric,
    generalMetricC2VolumeDensityDerivativeAtZero_apply period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric metric.volume⟩

end
end P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
end JanusFormal
