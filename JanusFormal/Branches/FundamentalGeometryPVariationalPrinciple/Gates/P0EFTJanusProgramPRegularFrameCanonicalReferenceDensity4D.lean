import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMetricVolumeDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D

/-!
# Canonical reference density in the regular frame

The regular-to-holonomic change matrix acts by congruence on the Gram matrix
of every smooth Lorentz metric, not only on the stored physical metric.  The
global relative-volume identity therefore extends from holonomic frames to
the genuine regular frame.  In canonical-volume gauge, the intrinsic
reference density evaluated on that frame is exactly one.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalReferenceDensity4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusMatrixInteractionDensityCovariance
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Matrix4 := Matrix Index4 Index4 Real
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Gram matrix of an arbitrary smooth Lorentz metric, evaluated in the
stored regular frame of another metric. -/
def regularFrameMetricMatrixFor
    (frameMetric : RegularGeneralLorentzMetric period hPeriod)
    (evaluatedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  metricGramMatrix period hPeriod evaluatedMetric point
    (fun index => frameMetric.frame index point)

/-- The already constructed regular-frame change matrix acts by congruence
on the Gram matrix of every smooth Lorentz metric. -/
theorem regularFrameMetricMatrixFor_congruence
    (frameMetric : RegularGeneralLorentzMetric period hPeriod)
    (evaluatedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularFrameMetricMatrixFor period hPeriod frameMetric evaluatedMetric
        (patch.coordinateMap coordinate) =
      (regularFrameChangeMatrix period hPeriod frameMetric patch coordinate).transpose *
        localMetricMatrix period hPeriod evaluatedMetric patch coordinate *
        regularFrameChangeMatrix period hPeriod frameMetric patch coordinate := by
  let basis := pulledRegularFrameBasis period hPeriod frameMetric patch coordinate
  let form := localMetricCoordinateForm period hPeriod evaluatedMetric patch coordinate
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (b := Pi.basisFun Real Index4) basis form
  have hLocal :
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4) form =
        localMetricMatrix period hPeriod evaluatedMetric patch coordinate := by
    change LinearMap.BilinForm.toMatrix'
        (Matrix.toBilin'
          (localMetricMatrix period hPeriod evaluatedMetric patch coordinate)) = _
    exact LinearMap.BilinForm.toMatrix'_toBilin'
      (localMetricMatrix period hPeriod evaluatedMetric patch coordinate)
  have hMatrix :
      LinearMap.BilinForm.toMatrix basis form =
        regularFrameMetricMatrixFor period hPeriod frameMetric evaluatedMetric
          (patch.coordinateMap coordinate) := by
    ext first second
    rw [LinearMap.BilinForm.toMatrix_apply]
    rw [show basis first =
        pulledRegularFrameVector period hPeriod frameMetric patch first coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod frameMetric patch coordinate
        first]
    rw [show basis second =
        pulledRegularFrameVector period hPeriod frameMetric patch second coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod frameMetric patch coordinate
        second]
    rw [localMetricCoordinateForm_apply,
      coordinateMap_mfderiv_pulledRegularFrameVector,
      coordinateMap_mfderiv_pulledRegularFrameVector]
    rfl
  rw [hLocal, hMatrix] at hCongruence
  change regularFrameMetricMatrixFor period hPeriod frameMetric evaluatedMetric
      (patch.coordinateMap coordinate) =
    ((Pi.basisFun Real Index4).toMatrix basis).transpose *
      localMetricMatrix period hPeriod evaluatedMetric patch coordinate *
      (Pi.basisFun Real Index4).toMatrix basis
  exact hCongruence.symm

/-- Every smooth metric volume evaluated in the regular frame is its
holonomic density multiplied by the same positive frame Jacobian. -/
theorem metricVolumeDensity_regularFrame_eq_jacobian_mul_local
    (frameMetric : RegularGeneralLorentzMetric period hPeriod)
    (evaluatedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    metricVolumeDensity period hPeriod evaluatedMetric
        (patch.coordinateMap coordinate)
        (fun index => frameMetric.frame index (patch.coordinateMap coordinate)) =
      regularFrameHolonomicJacobianWeight period hPeriod frameMetric patch coordinate *
        localMetricVolumeFactor period hPeriod evaluatedMetric patch coordinate := by
  change
    Real.sqrt |Matrix.det
        (regularFrameMetricMatrixFor period hPeriod frameMetric evaluatedMetric
          (patch.coordinateMap coordinate))| =
      |Matrix.det
          (regularFrameChangeMatrix period hPeriod frameMetric patch coordinate)| *
        Real.sqrt |Matrix.det
          (localMetricMatrix period hPeriod evaluatedMetric patch coordinate)|
  rw [regularFrameMetricMatrixFor_congruence period hPeriod]
  simpa [metricCongruence] using
    metricVolume_diagonal_weight
      (regularFrameChangeMatrix period hPeriod frameMetric patch coordinate)
      (localMetricMatrix period hPeriod evaluatedMetric patch coordinate)

/-- The frame-free relative-volume identity is valid on the genuine regular
frame, not only on holonomic coordinate frames. -/
theorem globalMetricVolumeRatio_mul_regularFrameIntrinsicDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod metric.metric point *
        metricVolumeDensity period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
          (fun index => metric.frame index point) =
      metricVolumeDensity period hPeriod metric.metric point
        (fun index => metric.frame index point) := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  rw [metricVolumeDensity_regularFrame_eq_jacobian_mul_local period hPeriod
      metric (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate,
    metricVolumeDensity_regularFrame_eq_jacobian_mul_local period hPeriod
      metric metric.metric patch coordinate]
  calc
    globalMetricVolumeRatio period hPeriod metric.metric
          (patch.coordinateMap coordinate) *
          (regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
            localMetricVolumeFactor period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate) =
        regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
          (globalMetricVolumeRatio period hPeriod metric.metric
              (patch.coordinateMap coordinate) *
            localMetricVolumeFactor period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate) := by
      ring
    _ = regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
          localMetricVolumeFactor period hPeriod metric.metric patch coordinate := by
      rw [localMetricVolumeFactor_eq_metricVolumeDensity period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate,
        localMetricVolumeFactor_eq_metricVolumeDensity period hPeriod
          metric.metric patch coordinate,
        globalMetricVolumeRatio_mul_intrinsic_density period hPeriod]

/-- Canonical-volume gauge means precisely that the canonical reference
volume has unit density on the stored regular frame. -/
theorem regularFrameIntrinsicReferenceDensity_eq_one_of_canonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    metricVolumeDensity period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
        (fun index => metric.frame index point) = 1 := by
  have hBridge :=
    globalMetricVolumeRatio_mul_regularFrameIntrinsicDensity period hPeriod
      metric point
  have hGaugePoint := congrArg
    (fun field : SmoothScalarField period hPeriod => field point) hGauge
  change metric.volume point =
    globalMetricVolumeRatio period hPeriod metric.metric point at hGaugePoint
  rw [← metric.volume_eq point, hGaugePoint] at hBridge
  apply mul_left_cancel₀
    (ne_of_gt (globalMetricVolumeRatio_pos period hPeriod metric.metric point))
  simpa using hBridge

/-- Gate marker: relative metric volume is now frame-independent at the
regular frame, and canonical-volume gauge normalizes its reference density. -/
theorem regular_frame_canonical_reference_density_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (∀ point : EffectiveQuotient period hPeriod,
      globalMetricVolumeRatio period hPeriod metric.metric point *
          metricVolumeDensity period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
            (fun index => metric.frame index point) =
        metricVolumeDensity period hPeriod metric.metric point
          (fun index => metric.frame index point)) ∧
      (∀ _hGauge : RegularGeneralMetricInCanonicalVolumeGauge
          period hPeriod metric,
        ∀ point : EffectiveQuotient period hPeriod,
          metricVolumeDensity period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
              (fun index => metric.frame index point) = 1) := by
  exact ⟨globalMetricVolumeRatio_mul_regularFrameIntrinsicDensity
      period hPeriod metric,
    fun hGauge =>
      regularFrameIntrinsicReferenceDensity_eq_one_of_canonicalVolumeGauge
        period hPeriod metric hGauge⟩

end
end P0EFTJanusProgramPRegularFrameCanonicalReferenceDensity4D
end JanusFormal
