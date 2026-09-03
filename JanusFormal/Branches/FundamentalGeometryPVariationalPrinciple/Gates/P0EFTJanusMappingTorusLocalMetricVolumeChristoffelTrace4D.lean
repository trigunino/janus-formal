import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellEulerJacobianCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionFrechetNoether

/-! # Local metric-volume derivative and Christoffel trace -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4
abbrev MetricDerivative4 :=
  P0EFTJanusScalarStressLeviCivitaConnectionJet4D.MetricDerivative4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Finite-index trace identity for a Levi--Civita connection. -/
theorem leviCivitaChristoffel_trace_eq_half_inverseMetric_metricDerivative_trace
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (derivative : Index4) :
    (∑ contracted : Index4,
        leviCivitaChristoffel metric dMetric contracted derivative contracted) =
      (1 / 2 : Real) *
        Matrix.trace
          (metric.metric⁻¹ * metricDerivativeMatrix dMetric derivative) := by
  have hCross :
      (∑ first : Index4, ∑ second : Index4,
          metric.metric⁻¹ first second * dMetric first derivative second) =
        ∑ first : Index4, ∑ second : Index4,
          metric.metric⁻¹ first second * dMetric second derivative first := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rw [inverseMetric_entry_symmetric metric second first]
  have hTrace :
      Matrix.trace
          (metric.metric⁻¹ * metricDerivativeMatrix dMetric derivative) =
        ∑ first : Index4, ∑ second : Index4,
          metric.metric⁻¹ first second * dMetric derivative first second := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      metricDerivativeMatrix]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rw [hMetricDerivative derivative second first]
  have hExpand :
      (∑ contracted : Index4,
          leviCivitaChristoffel metric dMetric contracted derivative contracted) =
        (1 / 2 : Real) *
            (∑ first : Index4, ∑ second : Index4,
              metric.metric⁻¹ first second * dMetric derivative first second) +
          (1 / 2 : Real) *
            (∑ first : Index4, ∑ second : Index4,
              metric.metric⁻¹ first second * dMetric first derivative second) -
          (1 / 2 : Real) *
            (∑ first : Index4, ∑ second : Index4,
              metric.metric⁻¹ first second * dMetric second derivative first) := by
    unfold leviCivitaChristoffel
    calc
      _ = ∑ first : Index4, ∑ second : Index4,
          ((1 / 2 : Real) *
              (metric.metric⁻¹ first second *
                dMetric derivative first second) +
            (1 / 2 : Real) *
              (metric.metric⁻¹ first second *
                dMetric first derivative second) -
            (1 / 2 : Real) *
              (metric.metric⁻¹ first second *
                dMetric second derivative first)) := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
  rw [hExpand, hCross, hTrace]
  ring

/-- Genuine coordinate derivative of `sqrt |det g|`: it is the metric volume
times the trace of the local Levi--Civita connection. -/
theorem localMetricVolumeFactor_fderiv_basis_eq_christoffelTrace
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) :
    fderiv Real (localMetricVolumeFactor period hPeriod metric patch)
        coordinate (Pi.single derivative 1) =
      localMetricVolumeFactor period hPeriod metric patch coordinate *
        ∑ contracted : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            contracted derivative contracted := by
  let base : FixedSignMetric4 :=
    localFixedSignMetric period hPeriod metric patch coordinate
  let dMetric : MetricDerivative4 :=
    localMetricDerivative period hPeriod metric patch coordinate
  let variation : SymmetricMetricVariation4 :=
    { tensor := metricDerivativeMatrix dMetric derivative
      tensor_symmetric := by
        ext first second
        exact localMetricDerivative_symmetric period hPeriod metric patch
          coordinate derivative second first }
  let volumeOnMatrices : Matrix4 → Real := fun matrix =>
    Real.sqrt |Matrix.det matrix|
  have hMatrixVolume : DifferentiableAt Real volumeOnMatrices base.metric := by
    have hDet := determinant_hasFDerivAt base.metric
    unfold FrobeniusHasFDerivAt at hDet
    exact ((hDet.abs base.det_ne_zero).sqrt
      (abs_ne_zero.mpr base.det_ne_zero)).differentiableAt
  have hCurve := metricCurve_hasDerivAt base variation
  unfold FrobeniusMatrixHasDerivAt at hCurve
  have hCurveDeriv : HasDerivAt (metricCurve base variation)
      variation.tensor 0 :=
    hCurve.hasDerivAt.congr_deriv (by simp)
  have hComposed : HasDerivAt
      (fun t : Real => volumeOnMatrices (metricCurve base variation t))
      ((fderiv Real volumeOnMatrices base.metric) variation.tensor) 0 := by
    exact hMatrixVolume.hasFDerivAt.comp_hasDerivAt_of_eq 0
      hCurveDeriv (by simp)
  have hDirectional :
      (fderiv Real volumeOnMatrices base.metric) variation.tensor =
        (Real.sqrt |Matrix.det base.metric| / 2) *
          Matrix.trace (relativeMetricVariation base variation) :=
    hComposed.unique (metricMeasureCurve_hasDerivAt base variation)
  have hLocalMetric : DifferentiableAt Real
      (localMetricMatrix period hPeriod metric patch) coordinate :=
    ((localMetricMatrix_contDiff period hPeriod metric patch).differentiable
      (by simp)).differentiableAt
  have hLocalVolume := hMatrixVolume.hasFDerivAt.comp coordinate
    hLocalMetric.hasFDerivAt
  change HasFDerivAt
      (localMetricVolumeFactor period hPeriod metric patch)
      ((fderiv Real volumeOnMatrices base.metric).comp
        (fderiv Real (localMetricMatrix period hPeriod metric patch) coordinate))
      coordinate at hLocalVolume
  have hApply := congrArg
    (fun map : Vector4 →L[Real] Real => map (Pi.single derivative 1))
    hLocalVolume.fderiv
  have hTrace :=
    leviCivitaChristoffel_trace_eq_half_inverseMetric_metricDerivative_trace
      base dMetric
        (fun current first second =>
          localMetricDerivative_symmetric period hPeriod metric patch coordinate
            current first second)
      derivative
  change
    (∑ contracted : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
          contracted derivative contracted) =
      (1 / 2 : Real) *
        Matrix.trace
          (base.metric⁻¹ * metricDerivativeMatrix dMetric derivative) at hTrace
  calc
    fderiv Real (localMetricVolumeFactor period hPeriod metric patch)
        coordinate (Pi.single derivative 1) =
      (fderiv Real volumeOnMatrices base.metric)
        (fderiv Real (localMetricMatrix period hPeriod metric patch) coordinate
          (Pi.single derivative 1)) := by
            simpa only [ContinuousLinearMap.comp_apply] using hApply
    _ = (fderiv Real volumeOnMatrices base.metric) variation.tensor := by
      rw [localMetricMatrix_fderiv_basis]
    _ = (Real.sqrt |Matrix.det base.metric| / 2) *
        Matrix.trace (relativeMetricVariation base variation) := hDirectional
    _ = localMetricVolumeFactor period hPeriod metric patch coordinate *
        ((1 / 2 : Real) *
          Matrix.trace
            (base.metric⁻¹ * metricDerivativeMatrix dMetric derivative)) := by
      change
        (localMetricVolumeFactor period hPeriod metric patch coordinate / 2) *
            Matrix.trace
              ((localMetricMatrix period hPeriod metric patch coordinate)⁻¹ *
                metricDerivativeMatrix
                  (localMetricDerivative period hPeriod metric patch coordinate)
                  derivative) =
          localMetricVolumeFactor period hPeriod metric patch coordinate *
            ((1 / 2 : Real) *
              Matrix.trace
                ((localMetricMatrix period hPeriod metric patch coordinate)⁻¹ *
                  metricDerivativeMatrix
                    (localMetricDerivative period hPeriod metric patch coordinate)
                    derivative))
      ring
    _ = localMetricVolumeFactor period hPeriod metric patch coordinate *
        ∑ contracted : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            contracted derivative contracted := by
      rw [hTrace]

/-- Gate marker for the volume/connection identity required by the local
Maxwell divergence bridge. -/
theorem local_metric_volume_christoffel_trace_gate
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (derivative : Index4),
      fderiv Real (localMetricVolumeFactor period hPeriod metric patch)
          coordinate (Pi.single derivative 1) =
        localMetricVolumeFactor period hPeriod metric patch coordinate *
          ∑ contracted : Index4,
            localLeviCivitaChristoffel period hPeriod metric patch coordinate
              contracted derivative contracted :=
  localMetricVolumeFactor_fderiv_basis_eq_christoffelTrace
    period hPeriod metric

end
end P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D
end JanusFormal
