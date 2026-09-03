import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularHolonomicMaxwellDensityDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricStrongMaxwellPDE4D

/-! # Holonomic Maxwell Euler equation and the global strong PDE -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularHolonomicMaxwellEulerStrongPDE4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricStrongMaxwellPDE4D
open P0EFTJanusProgramPRegularHolonomicMaxwellDensityDivergence4D

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

theorem regularLocalMaxwellDivergenceComponent_eq_coefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Index4) :
    regularLocalMaxwellDivergenceComponent period hPeriod metric potential
        component patch coordinate index =
      localSymmetricTensorDivergenceCoefficient period hPeriod metric.metric
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component)
        patch coordinate index := by
  unfold regularLocalMaxwellDivergenceComponent
  exact localSymmetricTensorDivergenceModelCovector_basis period hPeriod
    metric.metric
    (regularGlobalGaugeCurvatureTensor period hPeriod metric potential component)
    patch coordinate index

/-- At one chart point, all four holonomic Euler equations are equivalent to
the four covariant Maxwell-divergence equations. -/
theorem regularHolonomicMaxwellEuler_eq_zero_iff_localDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (∀ second : Index4,
      maxwellEulerCoefficient
          (regularHolonomicMaxwellExcitationField period hPeriod metric potential
            patch component)
          coordinate second = 0) ↔
      ∀ index : Index4,
        regularLocalMaxwellDivergenceComponent period hPeriod metric potential
          component patch coordinate index = 0 := by
  let divergence : Vector4 := fun index =>
    localSymmetricTensorDivergenceCoefficient period hPeriod metric.metric
      (regularGlobalGaugeCurvatureTensor period hPeriod metric potential component)
      patch coordinate index
  let metricMatrix :=
    localMetricMatrix period hPeriod metric.metric patch coordinate
  constructor
  · intro hEuler
    have hRaised : Matrix.mulVec metricMatrix⁻¹ divergence = 0 := by
      funext second
      have hEquation := hEuler second
      rw [regularHolonomicMaxwellEulerCoefficient_eq_volume_mul_raisedDivergence]
        at hEquation
      have hVolume := localMetricVolumeFactor_ne_zero period hPeriod metric.metric
        patch coordinate
      have hSum :
          (∑ index : Index4, metricMatrix⁻¹ second index * divergence index) =
            0 :=
        (mul_eq_zero.mp hEquation).resolve_left hVolume
      simpa [Matrix.mulVec, dotProduct, metricMatrix, divergence] using hSum
    have hDet : IsUnit metricMatrix.det :=
      isUnit_iff_ne_zero.mpr
        (localMetricMatrix_det_ne_zero period hPeriod metric.metric patch
          coordinate)
    have hApplied := congrArg (fun vector => Matrix.mulVec metricMatrix vector)
      hRaised
    have hDivergence : divergence = 0 := by
      simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv metricMatrix hDet]
        using hApplied
    intro index
    rw [regularLocalMaxwellDivergenceComponent_eq_coefficient]
    exact congrFun hDivergence index
  · intro hDivergence second
    rw [regularHolonomicMaxwellEulerCoefficient_eq_volume_mul_raisedDivergence]
    simp_rw [← regularLocalMaxwellDivergenceComponent_eq_coefficient,
      hDivergence]
    simp

/-- The chart-free source-free Maxwell equation is exactly the family of
holonomic Euler equations in every chart. -/
theorem regularGeneralMetricStrongMaxwellEquation_iff_holonomicEuler
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    RegularGeneralMetricStrongMaxwellEquation period hPeriod metric potential ↔
      ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (second : Index4),
        maxwellEulerCoefficient
          (regularHolonomicMaxwellExcitationField period hPeriod metric potential
            patch component)
          coordinate second = 0 := by
  rw [regularGeneralMetricStrongMaxwellEquation_iff_local_components]
  constructor
  · intro hLocal component patch coordinate
    exact (regularHolonomicMaxwellEuler_eq_zero_iff_localDivergence period
      hPeriod metric potential component patch coordinate).mpr
        (hLocal component patch coordinate)
  · intro hEuler component patch coordinate
    exact (regularHolonomicMaxwellEuler_eq_zero_iff_localDivergence period
      hPeriod metric potential component patch coordinate).mp
        (hEuler component patch coordinate)

/-- Gate marker for the exact holonomic Euler/global Maxwell PDE bridge. -/
theorem regular_holonomic_maxwell_euler_strong_pde_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    RegularGeneralMetricStrongMaxwellEquation period hPeriod metric potential ↔
      ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (second : Index4),
        maxwellEulerCoefficient
          (regularHolonomicMaxwellExcitationField period hPeriod metric potential
            patch component)
          coordinate second = 0 :=
  regularGeneralMetricStrongMaxwellEquation_iff_holonomicEuler period hPeriod
    metric potential

end
end P0EFTJanusProgramPRegularHolonomicMaxwellEulerStrongPDE4D
end JanusFormal
