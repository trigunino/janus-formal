import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D

/-!
# Canonical-density divergence of the regular frame

The local metric density is the intrinsic canonical density multiplied by
the relative metric-volume ratio.  The exact product rule for weighted
divergence, together with canonical-volume gauge, removes the logarithmic
metric-volume derivative and leaves precisely the frame anholonomy trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalDensityDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D
open P0EFTJanusProgramPRegularFrameLeviCivitaTraceReduction4D
open P0EFTJanusProgramPRegularFrameMetricVolumeDerivative4D
open P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-! ## Exact change of density -/

/-- Multiplying a nonzero local density by a nonzero scalar ratio adds the
directional logarithmic derivative of that ratio to the weighted divergence
of a pulled regular-frame vector. -/
theorem regularFrameLocalDensityDivergence_mul
    (ratio density : Vector4 → Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4)
    (hRatio : DifferentiableAt Real ratio coordinate)
    (hDensity : DifferentiableAt Real density coordinate)
    (hRatioNe : ratio coordinate ≠ 0)
    (hDensityNe : density coordinate ≠ 0) :
    regularFrameLocalDensityDivergence period hPeriod
        (fun current => ratio current * density current)
        metric patch vector coordinate =
      regularFrameLocalDensityDivergence period hPeriod density metric patch
          vector coordinate +
        fderiv Real ratio coordinate
            (pulledRegularFrameVector period hPeriod metric patch vector
              coordinate) /
          ratio coordinate := by
  let field := pulledRegularFrameVector period hPeriod metric patch vector
  have hField : DifferentiableAt Real field coordinate :=
    (pulledRegularFrameVector_contDiff period hPeriod metric patch vector)
      |>.differentiable (by simp) coordinate
  have hComponent (derivative : Index4) : DifferentiableAt Real
      (fun current => field current derivative) coordinate := by
    fun_prop
  have hDensityField (derivative : Index4) : DifferentiableAt Real
      (fun current => density current * field current derivative) coordinate :=
    hDensity.mul (hComponent derivative)
  have hTripleProduct (derivative : Index4) :
      fderiv Real
          (fun current => ratio current * density current * field current derivative)
          coordinate (Pi.single derivative 1) =
        fderiv Real ratio coordinate (Pi.single derivative 1) *
            (density coordinate * field coordinate derivative) +
          ratio coordinate *
            fderiv Real
              (fun current => density current * field current derivative)
              coordinate (Pi.single derivative 1) := by
    have hDerivative := fderiv_mul hRatio (hDensityField derivative)
    have hApply := congrArg
      (fun derivativeMap : Vector4 →L[Real] Real =>
        derivativeMap (Pi.single derivative 1)) hDerivative
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at hApply
    rw [show
      (fun current => ratio current * density current * field current derivative) =
        ratio * (fun current => density current * field current derivative) by
      funext current
      simp only [Pi.mul_apply]
      ring]
    rw [hApply]
    ring
  have hAdvection :
      fderiv Real ratio coordinate (field coordinate) =
        ∑ derivative : Index4,
          fderiv Real ratio coordinate (Pi.single derivative 1) *
            field coordinate derivative := by
    conv_lhs => rw [pi_eq_sum_univ' (field coordinate)]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro derivative _
    ring
  have hNumerator :
      (∑ derivative : Index4,
          fderiv Real
            (fun current =>
              ratio current * density current * field current derivative)
            coordinate (Pi.single derivative 1)) =
        density coordinate * fderiv Real ratio coordinate (field coordinate) +
          ratio coordinate *
            ∑ derivative : Index4,
              fderiv Real
                (fun current => density current * field current derivative)
                coordinate (Pi.single derivative 1) := by
    simp_rw [hTripleProduct]
    rw [Finset.sum_add_distrib]
    calc
      (∑ derivative : Index4,
          fderiv Real ratio coordinate (Pi.single derivative 1) *
              (density coordinate * field coordinate derivative)) +
            ∑ derivative : Index4,
              ratio coordinate *
                fderiv Real
                  (fun current => density current * field current derivative)
                  coordinate (Pi.single derivative 1) =
          density coordinate *
              (∑ derivative : Index4,
                fderiv Real ratio coordinate (Pi.single derivative 1) *
                  field coordinate derivative) +
            ratio coordinate *
              ∑ derivative : Index4,
                fderiv Real
                  (fun current => density current * field current derivative)
                  coordinate (Pi.single derivative 1) := by
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro derivative _
          ring
        · rw [Finset.mul_sum]
      _ = _ := by rw [← hAdvection]
  unfold regularFrameLocalDensityDivergence
  change
    (∑ derivative : Index4,
        fderiv Real
          (fun current =>
            ratio current * density current * field current derivative)
          coordinate (Pi.single derivative 1)) /
          (ratio coordinate * density coordinate) =
      (∑ derivative : Index4,
          fderiv Real
            (fun current => density current * field current derivative)
            coordinate (Pi.single derivative 1)) /
          density coordinate +
        fderiv Real ratio coordinate (field coordinate) / ratio coordinate
  rw [hNumerator]
  field_simp [hRatioNe, hDensityNe]
  ring

/-- The local metric determinant factor is the local relative-volume ratio
times the intrinsic canonical determinant factor. -/
theorem localMetricVolumeFactor_eq_ratio_mul_intrinsic
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localMetricVolumeFactor period hPeriod metric.metric patch =
      fun coordinate =>
        localMetricVolumeRatio period hPeriod metric.metric patch coordinate *
          localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
            coordinate := by
  funext coordinate
  unfold localMetricVolumeRatio
  exact (div_mul_cancel₀ _
    (localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)).symm

/-- Specializing the product law to metric and intrinsic volume gives the
exact local relative-volume correction. -/
theorem regularFrameLocalMetricDivergence_eq_intrinsic_add_ratioDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    regularFrameLocalDensityDivergence period hPeriod
        (localMetricVolumeFactor period hPeriod metric.metric patch)
        metric patch vector coordinate =
      regularFrameLocalDensityDivergence period hPeriod
          (localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
          metric patch vector coordinate +
        fderiv Real
            (localMetricVolumeRatio period hPeriod metric.metric patch)
            coordinate
            (pulledRegularFrameVector period hPeriod metric patch vector
              coordinate) /
          localMetricVolumeRatio period hPeriod metric.metric patch coordinate := by
  rw [localMetricVolumeFactor_eq_ratio_mul_intrinsic period hPeriod metric patch]
  exact regularFrameLocalDensityDivergence_mul period hPeriod
    (localMetricVolumeRatio period hPeriod metric.metric patch)
    (localMetricVolumeFactor period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
    metric patch vector coordinate
    ((localMetricVolumeRatio_contDiff period hPeriod metric.metric patch)
      |>.differentiable (by simp) coordinate)
    ((localMetricVolumeFactor_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
      |>.differentiable (by simp) coordinate)
    (localMetricVolumeRatio_pos period hPeriod metric.metric patch coordinate).ne'
    (localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

/-! ## Canonical-volume gauge cancellation -/

/-- In canonical-volume gauge the directional derivative of the local
relative-volume ratio is its value times the metric half-trace. -/
theorem localMetricVolumeRatio_frameDerivative_of_canonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    fderiv Real (localMetricVolumeRatio period hPeriod metric.metric patch)
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch vector coordinate) =
      localMetricVolumeRatio period hPeriod metric.metric patch coordinate *
        regularFrameMetricHalfTraceDerivative period hPeriod metric vector
          (patch.coordinateMap coordinate) := by
  let ratioField := globalSmoothMetricVolumeRatio period hPeriod metric.metric
  have hLocalFunction :
      localMetricVolumeRatio period hPeriod metric.metric patch =
        ratioField.toFun ∘ patch.coordinateMap := by
    funext current
    exact (globalMetricVolumeRatio_eq_local period hPeriod metric.metric patch
      current).symm
  have hGaugePoint := congrArg
    (fun field : SmoothScalarField period hPeriod =>
      field (patch.coordinateMap coordinate)) hGauge
  change metric.volume (patch.coordinateMap coordinate) =
    globalMetricVolumeRatio period hPeriod metric.metric
      (patch.coordinateMap coordinate) at hGaugePoint
  calc
    fderiv Real (localMetricVolumeRatio period hPeriod metric.metric patch)
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch vector coordinate) =
        fderiv Real (ratioField.toFun ∘ patch.coordinateMap) coordinate
          (pulledRegularFrameVector period hPeriod metric patch vector coordinate) := by
      rw [hLocalFunction]
    _ = frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          ratioField (patch.coordinateMap coordinate) vector := by
      exact fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod
        metric ratioField patch coordinate vector
    _ = frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.volume (patch.coordinateMap coordinate) vector := by
      have hGaugeDerivative := congrArg
        (fun field : SmoothScalarField period hPeriod =>
          frameDerivative period hPeriod Real
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            field (patch.coordinateMap coordinate) vector) hGauge
      simpa only [ratioField] using hGaugeDerivative.symm
    _ = metric.volume (patch.coordinateMap coordinate) *
          regularFrameMetricHalfTraceDerivative period hPeriod metric vector
            (patch.coordinateMap coordinate) :=
      regularFrameMetricVolume_frameDerivative period hPeriod metric
        (patch.coordinateMap coordinate) vector
    _ = _ := by
      rw [hGaugePoint,
        globalMetricVolumeRatio_eq_local period hPeriod metric.metric patch
          coordinate]

/-- The intrinsic canonical-density divergence of each regular-frame vector
is exactly the trace of frame anholonomy in canonical-volume gauge. -/
theorem regularFrameLocalIntrinsicDensityDivergence_eq_anholonomy
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    regularFrameLocalDensityDivergence period hPeriod
        (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
        metric patch vector coordinate =
      regularFrameAnholonomyTrace period hPeriod metric vector
        (patch.coordinateMap coordinate) := by
  have hChange :=
    regularFrameLocalMetricDivergence_eq_intrinsic_add_ratioDerivative
      period hPeriod metric patch vector coordinate
  have hRatioDerivative :=
    localMetricVolumeRatio_frameDerivative_of_canonicalVolumeGauge
      period hPeriod metric hGauge patch vector coordinate
  have hRatioNe :=
    (localMetricVolumeRatio_pos period hPeriod metric.metric patch coordinate).ne'
  rw [hRatioDerivative] at hChange
  have hCancel :
      (localMetricVolumeRatio period hPeriod metric.metric patch coordinate *
          regularFrameMetricHalfTraceDerivative period hPeriod metric vector
            (patch.coordinateMap coordinate)) /
          localMetricVolumeRatio period hPeriod metric.metric patch coordinate =
        regularFrameMetricHalfTraceDerivative period hPeriod metric vector
          (patch.coordinateMap coordinate) := by
    field_simp [hRatioNe]
  rw [hCancel] at hChange
  have hTrace := congrArg
    (fun field : SmoothScalarField period hPeriod =>
      field (patch.coordinateMap coordinate))
    (regularFrameLeviCivitaTrace_eq_halfTrace_add_anholonomy period hPeriod
      metric vector)
  change
    regularFrameLeviCivitaTrace period hPeriod metric vector
        (patch.coordinateMap coordinate) =
      regularFrameMetricHalfTraceDerivative period hPeriod metric vector
          (patch.coordinateMap coordinate) +
        regularFrameAnholonomyTrace period hPeriod metric vector
          (patch.coordinateMap coordinate) at hTrace
  calc
    regularFrameLocalDensityDivergence period hPeriod
          (localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
          metric patch vector coordinate =
        regularFrameLocalDensityDivergence period hPeriod
            (localMetricVolumeFactor period hPeriod metric.metric patch)
            metric patch vector coordinate -
          regularFrameMetricHalfTraceDerivative period hPeriod metric vector
            (patch.coordinateMap coordinate) := by
      rw [hChange]
      ring
    _ = regularFrameLeviCivitaTrace period hPeriod metric vector
          (patch.coordinateMap coordinate) -
        regularFrameMetricHalfTraceDerivative period hPeriod metric vector
          (patch.coordinateMap coordinate) := by
      rw [regularFrameLocalMetricVolumeDivergence_eq_leviCivitaTrace]
    _ = _ := by rw [hTrace]; ring

/-- Gate marker for the canonical-density/anholonomy identification. -/
theorem regular_frame_canonical_density_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (vector : Index4) (coordinate : Vector4),
      regularFrameLocalDensityDivergence period hPeriod
          (localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
          metric patch vector coordinate =
        regularFrameAnholonomyTrace period hPeriod metric vector
          (patch.coordinateMap coordinate) :=
  regularFrameLocalIntrinsicDensityDivergence_eq_anholonomy period hPeriod
    metric hGauge

end
end P0EFTJanusProgramPRegularFrameCanonicalDensityDivergence4D
end JanusFormal
