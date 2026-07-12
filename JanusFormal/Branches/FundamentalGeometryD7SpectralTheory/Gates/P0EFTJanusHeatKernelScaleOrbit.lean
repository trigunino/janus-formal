import Mathlib

namespace JanusFormal
namespace P0EFTJanusHeatKernelScaleOrbit

set_option autoImplicit false

/-- Three-dimensional local heat coefficients and a UV cutoff. -/
structure ThreeDimensionalHeatScaleData where
  cutoff : ℝ
  a0 : ℝ
  a2 : ℝ
  a4 : ℝ
  cutoffNonzero : cutoff ≠ 0

/-- Common metric rescaling factor. -/
structure PositiveScale where
  factor : ℝ
  factorPositive : 0 < factor

/-- Under `g -> s^2 g`, the three-dimensional integrated coefficients scale as
`a0 -> s^3 a0`, `a2 -> s a2`, and `a4 -> a4/s`. -/
noncomputable def rescaleHeatData
    (scale : PositiveScale)
    (data : ThreeDimensionalHeatScaleData) :
    ThreeDimensionalHeatScaleData where
  cutoff := data.cutoff / scale.factor
  a0 := scale.factor ^ 3 * data.a0
  a2 := scale.factor * data.a2
  a4 := data.a4 / scale.factor
  cutoffNonzero :=
    div_ne_zero data.cutoffNonzero (ne_of_gt scale.factorPositive)

/-- Local spectral action through `a4` in dimension three. -/
noncomputable def localSpectralAction
    (volumeMoment curvatureMoment quadraticMoment : ℝ)
    (data : ThreeDimensionalHeatScaleData) : ℝ :=
  volumeMoment * data.cutoff ^ 3 * data.a0 +
    curvatureMoment * data.cutoff * data.a2 +
    quadraticMoment * data.cutoff⁻¹ * data.a4

/-- The `Lambda^3 a0` term is invariant under simultaneous metric/cutoff rescaling. -/
theorem volume_moment_scale_invariant
    (scale : PositiveScale)
    (data : ThreeDimensionalHeatScaleData) :
    (rescaleHeatData scale data).cutoff ^ 3 *
        (rescaleHeatData scale data).a0 =
      data.cutoff ^ 3 * data.a0 := by
  have hScale : scale.factor ≠ 0 := ne_of_gt scale.factorPositive
  change
    (data.cutoff / scale.factor) ^ 3 *
        (scale.factor ^ 3 * data.a0) =
      data.cutoff ^ 3 * data.a0
  field_simp [hScale]

/-- The `Lambda a2` term is invariant under simultaneous rescaling. -/
theorem curvature_moment_scale_invariant
    (scale : PositiveScale)
    (data : ThreeDimensionalHeatScaleData) :
    (rescaleHeatData scale data).cutoff *
        (rescaleHeatData scale data).a2 =
      data.cutoff * data.a2 := by
  have hScale : scale.factor ≠ 0 := ne_of_gt scale.factorPositive
  change
    (data.cutoff / scale.factor) *
        (scale.factor * data.a2) =
      data.cutoff * data.a2
  field_simp [hScale]

/-- The `Lambda^(-1) a4` term is invariant under simultaneous rescaling. -/
theorem quadratic_moment_scale_invariant
    (scale : PositiveScale)
    (data : ThreeDimensionalHeatScaleData) :
    (rescaleHeatData scale data).cutoff⁻¹ *
        (rescaleHeatData scale data).a4 =
      data.cutoff⁻¹ * data.a4 := by
  have hScale : scale.factor ≠ 0 := ne_of_gt scale.factorPositive
  have hCutoff : data.cutoff ≠ 0 := data.cutoffNonzero
  change
    (data.cutoff / scale.factor)⁻¹ *
        (data.a4 / scale.factor) =
      data.cutoff⁻¹ * data.a4
  field_simp [hScale, hCutoff]

/-- The complete local action through `a4` is invariant if the cutoff co-scales. -/
theorem local_spectral_action_common_scale_invariant
    (volumeMoment curvatureMoment quadraticMoment : ℝ)
    (scale : PositiveScale)
    (data : ThreeDimensionalHeatScaleData) :
    localSpectralAction volumeMoment curvatureMoment quadraticMoment
        (rescaleHeatData scale data) =
      localSpectralAction volumeMoment curvatureMoment quadraticMoment data := by
  have h0 := volume_moment_scale_invariant scale data
  have h2 := curvature_moment_scale_invariant scale data
  have h4 := quadratic_moment_scale_invariant scale data
  unfold localSpectralAction
  calc
    volumeMoment * (rescaleHeatData scale data).cutoff ^ 3 *
          (rescaleHeatData scale data).a0 +
        curvatureMoment * (rescaleHeatData scale data).cutoff *
          (rescaleHeatData scale data).a2 +
        quadraticMoment * (rescaleHeatData scale data).cutoff⁻¹ *
          (rescaleHeatData scale data).a4 =
      volumeMoment *
          ((rescaleHeatData scale data).cutoff ^ 3 *
            (rescaleHeatData scale data).a0) +
        curvatureMoment *
          ((rescaleHeatData scale data).cutoff *
            (rescaleHeatData scale data).a2) +
        quadraticMoment *
          ((rescaleHeatData scale data).cutoff⁻¹ *
            (rescaleHeatData scale data).a4) := by ring
    _ = volumeMoment * (data.cutoff ^ 3 * data.a0) +
        curvatureMoment * (data.cutoff * data.a2) +
        quadraticMoment * (data.cutoff⁻¹ * data.a4) := by
      rw [h0, h2, h4]
    _ = volumeMoment * data.cutoff ^ 3 * data.a0 +
        curvatureMoment * data.cutoff * data.a2 +
        quadraticMoment * data.cutoff⁻¹ * data.a4 := by ring

/-- Two distinct scale factors remain indistinguishable to the co-scaled local action. -/
theorem local_action_cannot_select_common_scale
    (volumeMoment curvatureMoment quadraticMoment : ℝ)
    (firstScale secondScale : PositiveScale)
    (data : ThreeDimensionalHeatScaleData) :
    localSpectralAction volumeMoment curvatureMoment quadraticMoment
        (rescaleHeatData firstScale data) =
      localSpectralAction volumeMoment curvatureMoment quadraticMoment
        (rescaleHeatData secondScale data) := by
  rw [local_spectral_action_common_scale_invariant,
    local_spectral_action_common_scale_invariant]

/--
A local spectral action can fix an absolute metric scale only when the cutoff or
another dimensionful datum is anchored independently of the metric rescaling.
Simply co-rescaling the UV unit leaves the entire local action unchanged.
-/
structure AbsoluteSpectralScaleStatus where
  metricScaleOrbitIdentified : Prop
  cutoffTransformationDerived : Prop
  localActionScaleInvariantProved : Prop
  independentUVAnchorDerived : Prop
  finiteRenormalizedScaleConditionDerived : Prop
  nonlocalScaleDependenceComputed : Prop
  absoluteMetricScaleSelected : Prop
  noObservedScaleImported : Prop


def absoluteSpectralScaleClosed
    (s : AbsoluteSpectralScaleStatus) : Prop :=
  s.metricScaleOrbitIdentified /\
  s.cutoffTransformationDerived /\
  s.localActionScaleInvariantProved /\
  s.independentUVAnchorDerived /\
  s.finiteRenormalizedScaleConditionDerived /\
  s.nonlocalScaleDependenceComputed /\
  s.absoluteMetricScaleSelected /\
  s.noObservedScaleImported

end P0EFTJanusHeatKernelScaleOrbit
end JanusFormal
