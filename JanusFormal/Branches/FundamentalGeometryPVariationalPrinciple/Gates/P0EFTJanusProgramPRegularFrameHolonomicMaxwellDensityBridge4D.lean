import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D

/-! # Regular-frame to holonomic Maxwell density bridge -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMatrixInteractionDensityCovariance
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Absolute Jacobian converting the canonical holonomic frame into the
stored regular frame. -/
def regularFrameHolonomicJacobianWeight
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  |Matrix.det (regularFrameChangeMatrix period hPeriod metric patch coordinate)|

theorem regularFrameHolonomicJacobianWeight_pos
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    0 < regularFrameHolonomicJacobianWeight period hPeriod metric patch
      coordinate := by
  apply abs_pos.mpr
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (regularFrameChangeMatrix_isUnit period hPeriod metric patch coordinate))

theorem regularFrameHolonomicJacobianWeight_ne_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate ≠ 0 :=
  (regularFrameHolonomicJacobianWeight_pos period hPeriod metric patch
    coordinate).ne'

/-- The stored-frame scalar volume is the holonomic metric density multiplied
by the exact frame Jacobian. -/
theorem regularMetricVolume_eq_jacobian_mul_localMetricVolumeFactor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    metric.volume (patch.coordinateMap coordinate) =
      regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
        localMetricVolumeFactor period hPeriod metric.metric patch coordinate := by
  rw [metric.volume_eq]
  change
    Real.sqrt
        |Matrix.det
          (regularFrameMetricMatrixMap period hPeriod metric
            (patch.coordinateMap coordinate))| = _
  rw [regularFrameMetricMatrix_congruence period hPeriod metric patch coordinate]
  exact metricVolume_diagonal_weight
    (regularFrameChangeMatrix period hPeriod metric patch coordinate)
    (localMetricMatrix period hPeriod metric.metric patch coordinate)

/-- Maxwell excitation densitized by the actual holonomic metric volume. -/
def regularHolonomicMaxwellExcitationField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Fin 2 → Vector4 → Matrix4 :=
  maxwellExcitationField
    (localMetricVolumeFactor period hPeriod metric.metric patch)
    (regularIntrinsicMaxwellLocalInverseField period hPeriod metric patch)
    (regularIntrinsicMaxwellLocalCurvatureField period hPeriod potential patch)

/-- The excitation used by the action contains one additional, explicit frame
Jacobian relative to the holonomic Maxwell excitation. -/
theorem regularIntrinsicMaxwellLocalExcitationField_eq_jacobian_mul_holonomic
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) :
    regularIntrinsicMaxwellLocalExcitationField period hPeriod metric potential
        patch component coordinate first second =
      regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
        regularHolonomicMaxwellExcitationField period hPeriod metric potential
          patch component coordinate first second := by
  unfold regularIntrinsicMaxwellLocalExcitationField
    regularHolonomicMaxwellExcitationField maxwellExcitationField
    regularIntrinsicMaxwellLocalVolumeField maxwellExcitationAt
  rw [regularMetricVolume_eq_jacobian_mul_localMetricVolumeFactor]
  ring

/-- Gate marker: the formerly implicit frame dependence of the Euler density
is isolated as one positive Jacobian factor. -/
theorem regular_frame_holonomic_maxwell_density_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    (∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4),
      metric.volume (patch.coordinateMap coordinate) =
        regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
          localMetricVolumeFactor period hPeriod metric.metric patch coordinate) ∧
      (∀ (component : Fin 2)
          (patch : SmoothHolonomicFrameChart4 period hPeriod)
          (coordinate : Vector4) (first second : Index4),
        regularIntrinsicMaxwellLocalExcitationField period hPeriod metric potential
            patch component coordinate first second =
          regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
            regularHolonomicMaxwellExcitationField period hPeriod metric potential
              patch component coordinate first second) :=
  ⟨regularMetricVolume_eq_jacobian_mul_localMetricVolumeFactor period hPeriod metric,
    regularIntrinsicMaxwellLocalExcitationField_eq_jacobian_mul_holonomic
      period hPeriod metric potential⟩

end
end P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D
end JanusFormal
