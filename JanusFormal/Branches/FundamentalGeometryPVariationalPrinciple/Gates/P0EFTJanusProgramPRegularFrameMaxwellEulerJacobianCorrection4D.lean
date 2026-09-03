import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D

/-! # Jacobian correction in the regular-frame Maxwell Euler coefficient -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellEulerJacobianCorrection4D

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The frame Jacobian is intrinsically the quotient of the stored-frame
volume by the holonomic metric volume. -/
theorem regularFrameHolonomicJacobianWeight_eq_volume_div_localMetricVolumeFactor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate =
      metric.volume (patch.coordinateMap coordinate) /
        localMetricVolumeFactor period hPeriod metric.metric patch coordinate := by
  apply (eq_div_iff
    (localMetricVolumeFactor_ne_zero period hPeriod metric.metric patch
      coordinate)).2
  exact (regularMetricVolume_eq_jacobian_mul_localMetricVolumeFactor
    period hPeriod metric patch coordinate).symm

theorem regularFrameHolonomicJacobianWeight_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (regularFrameHolonomicJacobianWeight period hPeriod metric patch) := by
  have hVolume : ContDiff Real ∞ (fun coordinate =>
      metric.volume (patch.coordinateMap coordinate)) :=
    (metric.volume.contMDiff_toFun.comp patch.coordinateMap_contMDiff).contDiff
  have hEquality :
      regularFrameHolonomicJacobianWeight period hPeriod metric patch =
        fun coordinate => metric.volume (patch.coordinateMap coordinate) /
          localMetricVolumeFactor period hPeriod metric.metric patch coordinate := by
    funext coordinate
    exact
      regularFrameHolonomicJacobianWeight_eq_volume_div_localMetricVolumeFactor
        period hPeriod metric patch coordinate
  rw [hEquality]
  exact hVolume.div
    (localMetricVolumeFactor_contDiff period hPeriod metric.metric patch)
    (fun coordinate =>
      localMetricVolumeFactor_ne_zero period hPeriod metric.metric patch coordinate)

theorem regularHolonomicMaxwellExcitationField_entry_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      regularHolonomicMaxwellExcitationField period hPeriod metric potential
        patch component coordinate first second) := by
  unfold regularHolonomicMaxwellExcitationField maxwellExcitationField
    maxwellExcitationAt regularIntrinsicMaxwellLocalInverseField
    regularIntrinsicMaxwellLocalCurvatureField
  apply (localMetricVolumeFactor_contDiff period hPeriod metric.metric patch).mul
  apply ContDiff.sum
  intro lowerFirst _
  apply ContDiff.sum
  intro lowerSecond _
  exact
    ((localMetricInverseEntry_contDiff period hPeriod metric.metric patch first
        lowerFirst).mul
      (localMetricInverseEntry_contDiff period hPeriod metric.metric patch second
        lowerSecond)).mul
      (localGaugeCurvatureMatrix_entry_contDiff period hPeriod potential
        component patch lowerFirst lowerSecond)

/-- Exact product rule: the action's stored-frame Euler coefficient is the
holonomic coefficient multiplied by the frame Jacobian, plus the unavoidable
derivative-of-Jacobian correction. -/
theorem regularMaxwellEulerCoefficient_eq_jacobian_mul_holonomic_add_correction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (second : Index4) :
    maxwellEulerCoefficient
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential patch component) coordinate second =
      regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
          maxwellEulerCoefficient
            (regularHolonomicMaxwellExcitationField period hPeriod metric
              potential patch component) coordinate second +
        ∑ first : Index4,
          coordinatePartial
              (regularFrameHolonomicJacobianWeight period hPeriod metric patch)
              coordinate first *
            regularHolonomicMaxwellExcitationField period hPeriod metric potential
              patch component coordinate first second := by
  unfold maxwellEulerCoefficient
  have hJacobian : DifferentiableAt Real
      (regularFrameHolonomicJacobianWeight period hPeriod metric patch)
      coordinate :=
    (regularFrameHolonomicJacobianWeight_contDiff period hPeriod metric patch)
      |>.differentiable (by simp) coordinate
  have hHolonomic (first : Index4) : DifferentiableAt Real
      (fun current =>
        regularHolonomicMaxwellExcitationField period hPeriod metric potential
          patch component current first second) coordinate :=
    (regularHolonomicMaxwellExcitationField_entry_contDiff period hPeriod metric
      potential component patch first second).differentiable (by simp) coordinate
  have hPartial (first : Index4) :
      coordinatePartial
          (fun current =>
            regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
              potential patch component current first second)
          coordinate first =
        coordinatePartial
            (regularFrameHolonomicJacobianWeight period hPeriod metric patch)
            coordinate first *
            regularHolonomicMaxwellExcitationField period hPeriod metric potential
              patch component coordinate first second +
          regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
            coordinatePartial
              (fun current =>
                regularHolonomicMaxwellExcitationField period hPeriod metric
                  potential patch component current first second)
              coordinate first := by
    have hField :
        (fun current =>
          regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
            potential patch component current first second) =
          fun current =>
            regularFrameHolonomicJacobianWeight period hPeriod metric patch current *
              regularHolonomicMaxwellExcitationField period hPeriod metric
                potential patch component current first second := by
      funext current
      exact
        regularIntrinsicMaxwellLocalExcitationField_eq_jacobian_mul_holonomic
          period hPeriod metric potential component patch current first second
    rw [hField]
    unfold coordinatePartial
    change
      (fderiv Real
          (regularFrameHolonomicJacobianWeight period hPeriod metric patch *
            fun current =>
              regularHolonomicMaxwellExcitationField period hPeriod metric
                potential patch component current first second)
          coordinate) (Pi.single first 1) = _
    rw [fderiv_mul hJacobian (hHolonomic first)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hPartial, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  ring

/-- Gate marker for the exact Jacobian correction obstructing a direct
identification with the source-free Levi--Civita Maxwell equation. -/
theorem regular_frame_maxwell_euler_jacobian_correction_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (second : Index4),
      maxwellEulerCoefficient
          (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
            potential patch component) coordinate second =
        regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
            maxwellEulerCoefficient
              (regularHolonomicMaxwellExcitationField period hPeriod metric
                potential patch component) coordinate second +
          ∑ first : Index4,
            coordinatePartial
                (regularFrameHolonomicJacobianWeight period hPeriod metric patch)
                coordinate first *
              regularHolonomicMaxwellExcitationField period hPeriod metric
                potential patch component coordinate first second :=
  regularMaxwellEulerCoefficient_eq_jacobian_mul_holonomic_add_correction
    period hPeriod metric potential

end
end P0EFTJanusProgramPRegularFrameMaxwellEulerJacobianCorrection4D
end JanusFormal
