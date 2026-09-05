import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D

/-! # Canonically densitized global Maxwell residual -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalDensitizedMaxwellResidual4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameWeightedGlobalMaxwellResidualTestSeparation4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The weighted Maxwell Euler coefficients multiplied by the positive metric
volume ratio converting metric volume to canonical quotient volume. -/
def regularFrameCanonicalDensitizedMaxwellResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeFiber where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm (fun index =>
      globalMetricVolumeRatio period hPeriod metric.metric point *
        regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
          potential index.2 point
            (regularFrameSmoothDualVector period hPeriod metric index.1 point))
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm.toContinuousLinearMap
        |>.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    apply
      (globalSmoothMetricVolumeRatio period hPeriod metric.metric
        ).contMDiff_toFun.mul
    have hApplied :=
      (regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
        potential index.2).contMDiff.clm_bundle_apply
          (regularFrameSmoothDualVector period hPeriod metric index.1).contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp]
theorem regularFrameCanonicalDensitizedMaxwellResidual_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4)
    (component : Fin 2) :
    regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
        potential point (index, component) =
      globalMetricVolumeRatio period hPeriod metric.metric point *
        regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
          potential component point
            (regularFrameSmoothDualVector period hPeriod metric index point) :=
  rfl

/-- Positive densitization preserves exactly the pointwise strong Maxwell
equation. -/
theorem regularFrameCanonicalDensitizedMaxwellResidual_pointwise_zero_iff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    (∀ point : EffectiveQuotient period hPeriod,
        regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
          potential point = 0) ↔
      RegularFrameWeightedGlobalMaxwellEquation period hPeriod metric
        potential := by
  constructor
  · intro hDensitized component
    apply ContMDiffSection.ext
    intro point
    let metricMatrix := regularFrameMetricMatrixMap period hPeriod metric point
    let divergence : Fin 4 → Real := fun index =>
      regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
        potential component point (metric.frame index point)
    have hRaised : Matrix.mulVec metricMatrix⁻¹ divergence = 0 := by
      funext index
      have hCoefficient := congrArg
        (fun value : GaugeFiber => value (index, component))
        (hDensitized point)
      change globalMetricVolumeRatio period hPeriod metric.metric point *
          regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
            potential component point
              (regularFrameSmoothDualVector period hPeriod metric index point) =
        0 at hCoefficient
      have hDual := (mul_eq_zero.mp hCoefficient).resolve_left
        (ne_of_gt
          (globalMetricVolumeRatio_pos period hPeriod metric.metric point))
      simpa [regularFrameSmoothDualVector, Matrix.mulVec, dotProduct,
        metricMatrix, divergence, regularFrameMetricInverseMatrix,
        regularFrameMetricInverseMatrixMap] using hDual
    have hDet : IsUnit metricMatrix.det :=
      isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point)
    have hApplied := congrArg (fun vector => Matrix.mulVec metricMatrix vector)
      hRaised
    have hDivergence : divergence = 0 := by
      simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv metricMatrix hDet]
        using hApplied
    apply ContinuousLinearMap.ext
    intro vector
    obtain ⟨coordinates, rfl⟩ := (metric.frameEquiv point).surjective vector
    have hExpansion :
        metric.frameEquiv point coordinates =
          ∑ index : Fin 4, coordinates index • metric.frame index point := by
      calc
        metric.frameEquiv point coordinates =
            metric.frameEquiv point
              (∑ index : Fin 4,
                coordinates index • (Pi.basisFun Real (Fin 4)) index) := by
          congr 1
          exact ((Pi.basisFun Real (Fin 4)).sum_repr coordinates).symm
        _ = ∑ index : Fin 4,
            coordinates index •
              metric.frameEquiv point ((Pi.basisFun Real (Fin 4)) index) := by
          simp only [map_sum, map_smul]
        _ = ∑ index : Fin 4,
            coordinates index • metric.frame index point := by
          apply Finset.sum_congr rfl
          intro index _
          rw [RegularGeneralLorentzMetric.frame_eq_basisFun]
    rw [hExpansion, map_sum]
    apply Finset.sum_eq_zero
    intro index _
    rw [map_smul]
    have hFrame := congrFun hDivergence index
    simpa [divergence] using congrArg (fun value => coordinates index • value)
      hFrame
  · intro hResidual point
    apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).injective
    funext index
    change globalMetricVolumeRatio period hPeriod metric.metric point *
        regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
          potential index.2 point
            (regularFrameSmoothDualVector period hPeriod metric index.1 point) =
      0
    rw [hResidual index.2]
    simp

/-- Smooth intrinsic gauge tests with a nonzero coupling separate the
canonically densitized Maxwell equation. -/
theorem regularFrameCanonicalDensitizedMaxwell_coupledWeak_iff_strong
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ variation : SmoothAbelianGaugePotential period hPeriod,
        coupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
          hPeriod metric
            (regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
              potential) variation = 0) ↔
      RegularFrameWeightedGlobalMaxwellEquation period hPeriod metric
        potential := by
  calc
    _ ↔ ∀ point : EffectiveQuotient period hPeriod,
        regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
          potential point = 0 :=
      regular_frame_maxwell_smooth_gauge_test_separation_gate period hPeriod
        metric
          (regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
            potential) coupling hCoupling
    _ ↔ _ :=
      regularFrameCanonicalDensitizedMaxwellResidual_pointwise_zero_iff period
        hPeriod metric potential

/-- Gate marker: the actual canonical-volume Euler density is smooth and its
weak equation is equivalent to the weighted global Maxwell PDE. -/
theorem regular_frame_canonical_densitized_maxwell_residual_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ variation : SmoothAbelianGaugePotential period hPeriod,
        coupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
          hPeriod metric
            (regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
              potential) variation = 0) ↔
      RegularFrameWeightedGlobalMaxwellEquation period hPeriod metric
        potential :=
  regularFrameCanonicalDensitizedMaxwell_coupledWeak_iff_strong period hPeriod
    metric potential coupling hCoupling

end
end P0EFTJanusProgramPRegularFrameCanonicalDensitizedMaxwellResidual4D
end JanusFormal
