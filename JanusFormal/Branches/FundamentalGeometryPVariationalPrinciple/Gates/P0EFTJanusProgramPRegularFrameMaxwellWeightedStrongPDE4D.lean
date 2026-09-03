import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularHolonomicMaxwellEulerStrongPDE4D

/-! # Stored-frame Maxwell Euler residual and its strong PDE -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellWeightedStrongPDE4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellEulerJacobianCorrection4D
open P0EFTJanusProgramPRegularGeneralMetricStrongMaxwellPDE4D
open P0EFTJanusProgramPRegularHolonomicMaxwellDensityDivergence4D
open P0EFTJanusProgramPRegularHolonomicMaxwellEulerStrongPDE4D

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

/-- The derivative-of-frame-Jacobian contribution to the stored-action Euler
coefficient. -/
def regularFrameMaxwellJacobianCorrection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (second : Index4) : Real :=
  ∑ first : Index4,
    coordinatePartial
        (regularFrameHolonomicJacobianWeight period hPeriod metric patch)
        coordinate first *
      regularHolonomicMaxwellExcitationField period hPeriod metric potential
        patch component coordinate first second

/-- Exact strong residual selected by the Maxwell density currently stored in
the action. -/
def regularFrameMaxwellStrongResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (second : Index4) : Real :=
  regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
      localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
      ∑ lowerSecond : Index4,
        (localMetricMatrix period hPeriod metric.metric patch coordinate)⁻¹
            second lowerSecond *
          regularLocalMaxwellDivergenceComponent period hPeriod metric potential
            component patch coordinate lowerSecond +
    regularFrameMaxwellJacobianCorrection period hPeriod metric potential
      component patch coordinate second

/-- The local Euler coefficient of the stored Maxwell action is exactly its
weighted strong residual, including the unavoidable frame correction. -/
theorem regularIntrinsicMaxwellEulerCoefficient_eq_weightedStrongResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (second : Index4) :
    maxwellEulerCoefficient
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential patch component)
        coordinate second =
      regularFrameMaxwellStrongResidual period hPeriod metric potential component
        patch coordinate second := by
  rw [regularMaxwellEulerCoefficient_eq_jacobian_mul_holonomic_add_correction,
    regularHolonomicMaxwellEulerCoefficient_eq_volume_mul_raisedDivergence]
  simp_rw [← regularLocalMaxwellDivergenceComponent_eq_coefficient]
  rfl

/-- If the frame Jacobian is locally constant at a point, the stored-action
Euler equations there are equivalent to the intrinsic Maxwell equations. -/
theorem regularIntrinsicMaxwellEuler_eq_zero_iff_localDivergence_of_jacobianPartial_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (hJacobian : ∀ derivative : Index4,
      coordinatePartial
          (regularFrameHolonomicJacobianWeight period hPeriod metric patch)
          coordinate derivative = 0) :
    (∀ second : Index4,
      maxwellEulerCoefficient
          (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
            potential patch component)
          coordinate second = 0) ↔
      ∀ index : Index4,
        regularLocalMaxwellDivergenceComponent period hPeriod metric potential
          component patch coordinate index = 0 := by
  have hReduction (second : Index4) :
      maxwellEulerCoefficient
          (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
            potential patch component)
          coordinate second =
        regularFrameHolonomicJacobianWeight period hPeriod metric patch coordinate *
          maxwellEulerCoefficient
            (regularHolonomicMaxwellExcitationField period hPeriod metric
              potential patch component)
            coordinate second := by
    rw [regularMaxwellEulerCoefficient_eq_jacobian_mul_holonomic_add_correction]
    simp_rw [hJacobian]
    simp
  constructor
  · intro hAction
    apply (regularHolonomicMaxwellEuler_eq_zero_iff_localDivergence period
      hPeriod metric potential component patch coordinate).mp
    intro second
    have hZero := hAction second
    rw [hReduction] at hZero
    exact (mul_eq_zero.mp hZero).resolve_left
      (regularFrameHolonomicJacobianWeight_ne_zero period hPeriod metric patch
        coordinate)
  · intro hDivergence second
    rw [hReduction]
    rw [(regularHolonomicMaxwellEuler_eq_zero_iff_localDivergence period
      hPeriod metric potential component patch coordinate).mpr hDivergence second]
    simp

/-- Under local constancy of the frame Jacobian, the stored-action Euler
system is precisely the global strong Maxwell equation. -/
theorem regularGeneralMetricStrongMaxwellEquation_iff_storedEuler_of_jacobianPartial_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (hJacobian : ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (derivative : Index4),
      coordinatePartial
          (regularFrameHolonomicJacobianWeight period hPeriod metric patch)
          coordinate derivative = 0) :
    RegularGeneralMetricStrongMaxwellEquation period hPeriod metric potential ↔
      ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (second : Index4),
        maxwellEulerCoefficient
          (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
            potential patch component)
          coordinate second = 0 := by
  rw [regularGeneralMetricStrongMaxwellEquation_iff_local_components]
  constructor
  · intro hDivergence component patch coordinate
    exact
      (regularIntrinsicMaxwellEuler_eq_zero_iff_localDivergence_of_jacobianPartial_zero
        period hPeriod metric potential component patch coordinate
        (hJacobian patch coordinate)).mpr
        (hDivergence component patch coordinate)
  · intro hEuler component patch coordinate
    exact
      (regularIntrinsicMaxwellEuler_eq_zero_iff_localDivergence_of_jacobianPartial_zero
        period hPeriod metric potential component patch coordinate
        (hJacobian patch coordinate)).mp
        (hEuler component patch coordinate)

/-- Gate marker for the exact stored-frame weighted Maxwell equation. -/
theorem regular_frame_maxwell_weighted_strong_pde_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (second : Index4),
      maxwellEulerCoefficient
          (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
            potential patch component)
          coordinate second =
        regularFrameMaxwellStrongResidual period hPeriod metric potential
          component patch coordinate second :=
  regularIntrinsicMaxwellEulerCoefficient_eq_weightedStrongResidual period
    hPeriod metric potential

end
end P0EFTJanusProgramPRegularFrameMaxwellWeightedStrongPDE4D
end JanusFormal
