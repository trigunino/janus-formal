import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D

/-!
# Metric-volume warped-null fiber Stokes identity

The warped ambient metric has coordinate volume density `exp u`, exactly the
homogeneous screen area on the null face.  Weighting Gate 1042's affine current
by this density is the same as extending the weighted face density.  Its
metric-volume divergence is therefore the original face density, and the
one-fiber Stokes identity acquires the correct screen-area factor.

This remains a chart-level identity.  It does not integrate over the null
source, construct a compactly supported global current, or identify the chart
with the mapping-torus bulk.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Interval
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06RegularRadialProductCollarDivergence4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D

/-- Determinant of the explicit diagonal Lorentz metric. -/
theorem programPT06WarpedNullHyperplaneAmbientMetric_det
    (point : ProgramPT06AmbientCoordinate4) :
    Matrix.det (programPT06WarpedNullHyperplaneAmbientMetric point) =
      -(Real.exp (point 0)) ^ 2 := by
  rw [programPT06WarpedNullHyperplaneAmbientMetric, Matrix.det_diagonal]
  simp [programPT06WarpedNullHyperplaneAmbientWeight, Fin.prod_univ_four]
  ring

/-- Positive coordinate density of the explicit warped ambient metric. -/
def programPT06WarpedNullAmbientMetricVolumeDensity
    (point : ProgramPT06AmbientCoordinate4) : Real :=
  Real.sqrt |Matrix.det (programPT06WarpedNullHyperplaneAmbientMetric point)|

@[simp] theorem programPT06WarpedNullAmbientMetricVolumeDensity_eq
    (point : ProgramPT06AmbientCoordinate4) :
    programPT06WarpedNullAmbientMetricVolumeDensity point =
      Real.exp (point 0) := by
  rw [programPT06WarpedNullAmbientMetricVolumeDensity,
    programPT06WarpedNullHyperplaneAmbientMetric_det, abs_neg,
    abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

@[simp] theorem programPT06WarpedNullAmbientMetricVolumeDensity_collar
    (coordinate : ProgramPT06WarpedNullCollarCoordinate4) :
    programPT06WarpedNullAmbientMetricVolumeDensity
        (programPT06WarpedNullCollarEquiv coordinate) =
      Real.exp coordinate.1.1 := by
  rw [programPT06WarpedNullAmbientMetricVolumeDensity_eq]
  simp [programPT06WarpedNullCollarEquiv_apply]

/-- On the null face, ambient metric volume and homogeneous screen area carry
the same scalar density. -/
theorem programPT06WarpedNullMetricVolumeDensity_face_eq_screenArea
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullAmbientMetricVolumeDensity
        (programPT06WarpedNullHyperplaneEmbedding source) =
      finiteNullFaceHomogeneousScreenArea
        programPT06WarpedNullHyperplaneScreenMetric source.1 := by
  rw [← programPT06WarpedNullCollar_zeroSlice source,
    programPT06WarpedNullAmbientMetricVolumeDensity_collar,
    programPT06WarpedNullHyperplaneScreenArea]

/-- Face density multiplied by the induced homogeneous screen area. -/
def programPT06WarpedNullScreenWeightedDensity
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    ProgramPT06WarpedNullHyperplaneDensity :=
  fun source => Real.exp source.1 * density source

/-- Current densitized by the warped ambient metric volume. -/
def programPT06WarpedNullMetricVolumeCurrent
    (current : ProgramPT06AmbientCurrent4D) : ProgramPT06AmbientCurrent4D :=
  fun point =>
    programPT06WarpedNullAmbientMetricVolumeDensity point • current point

/-- Densitizing the affine collar current commutes with extension from the
face. -/
theorem programPT06WarpedNullMetricVolumeCurrent_affineExtension
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    programPT06WarpedNullMetricVolumeCurrent
        (programPT06WarpedNullCollarAffineFluxExtension density) =
      programPT06WarpedNullCollarAffineFluxExtension
        (programPT06WarpedNullScreenWeightedDensity density) := by
  funext point
  rw [← programPT06WarpedNullCollarEquiv.apply_symm_apply point]
  rw [programPT06WarpedNullMetricVolumeCurrent,
    programPT06WarpedNullAmbientMetricVolumeDensity_collar,
    programPT06WarpedNullCollarAffineFluxExtension_on_collar,
    programPT06WarpedNullCollarAffineFluxExtension_on_collar,
    ← map_smul]
  congr 1
  apply Prod.ext
  · simp
  · simp [programPT06WarpedNullScreenWeightedDensity]
    ring

/-- The metric-volume divergence is the coordinate divergence of the
densitized current divided by the positive metric density. -/
def programPT06WarpedNullMetricVolumeDivergence
    (current : ProgramPT06AmbientCurrent4D)
    (point : ProgramPT06AmbientCoordinate4) : Real :=
  programPT06AmbientCoordinateDivergence
      (programPT06WarpedNullMetricVolumeCurrent current) point /
    programPT06WarpedNullAmbientMetricVolumeDensity point

theorem programPT06WarpedNullScreenWeightedDensity_differentiableAt
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    {source : ProgramPT06NullFaceSource3}
    (hDensity : DifferentiableAt Real density source) :
    DifferentiableAt Real
      (programPT06WarpedNullScreenWeightedDensity density) source := by
  unfold programPT06WarpedNullScreenWeightedDensity
  have hExp := (Real.hasDerivAt_exp source.1).hasFDerivAt.comp source
    (hasFDerivAt_fst (𝕜 := Real))
  exact hExp.differentiableAt.mul hDensity

/-- For the affine extension, metric-volume divergence is the prescribed
unweighted face density along the whole collar fiber. -/
theorem programPT06WarpedNullCollarAffineFluxExtension_metricDivergence
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    {source : ProgramPT06NullFaceSource3} (radius : Real)
    (hDensity : DifferentiableAt Real density source) :
    programPT06WarpedNullMetricVolumeDivergence
        (programPT06WarpedNullCollarAffineFluxExtension density)
        (programPT06WarpedNullCollarEquiv (source, radius)) =
      density source := by
  have hWeighted :=
    programPT06WarpedNullScreenWeightedDensity_differentiableAt hDensity
  rw [programPT06WarpedNullMetricVolumeDivergence,
    programPT06WarpedNullMetricVolumeCurrent_affineExtension,
    programPT06WarpedNullCollarAffineFluxExtension_divergence
      (density := programPT06WarpedNullScreenWeightedDensity density)
      (source := source) radius hWeighted,
    programPT06WarpedNullAmbientMetricVolumeDensity_collar]
  simp [programPT06WarpedNullScreenWeightedDensity, Real.exp_ne_zero]

/-- The volume-densitized current has the screen-area-weighted boundary
flux. -/
theorem programPT06WarpedNullMetricVolumeCurrent_fluxRestriction
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullHyperplaneFluxRestriction
        (programPT06WarpedNullMetricVolumeCurrent
          (programPT06WarpedNullCollarAffineFluxExtension density)) source =
      finiteNullFaceHomogeneousScreenArea
          programPT06WarpedNullHyperplaneScreenMetric source.1 *
        density source := by
  rw [programPT06WarpedNullMetricVolumeCurrent_affineExtension,
    programPT06WarpedNullCollarAffineFluxExtension_rightInverse]
  simp [programPT06WarpedNullScreenWeightedDensity]

/-- Density-form Stokes identity for one metric-volume collar fiber. -/
theorem programPT06WarpedNullMetricVolumeCurrent_fiberwise_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (source : ProgramPT06NullFaceSource3)
    (hDensity : DifferentiableAt Real density source) :
    ∫ radius in (0 : Real)..1,
        programPT06AmbientCoordinateDivergence
          (programPT06WarpedNullMetricVolumeCurrent
            (programPT06WarpedNullCollarAffineFluxExtension density))
          (programPT06WarpedNullCollarEquiv (source, radius)) =
      programPT06WarpedNullHyperplaneFluxRestriction
        (programPT06WarpedNullMetricVolumeCurrent
          (programPT06WarpedNullCollarAffineFluxExtension density)) source := by
  rw [programPT06WarpedNullMetricVolumeCurrent_affineExtension]
  exact programPT06WarpedNullCollarAffineFluxExtension_fiberwise_stokes
    source
    (programPT06WarpedNullScreenWeightedDensity_differentiableAt hDensity)

/-- Scalar metric-volume form of the same one-fiber Stokes identity. -/
theorem programPT06WarpedNullMetricVolume_fiberwise_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (source : ProgramPT06NullFaceSource3)
    (hDensity : DifferentiableAt Real density source) :
    ∫ radius in (0 : Real)..1,
        programPT06WarpedNullAmbientMetricVolumeDensity
            (programPT06WarpedNullCollarEquiv (source, radius)) *
          programPT06WarpedNullMetricVolumeDivergence
            (programPT06WarpedNullCollarAffineFluxExtension density)
            (programPT06WarpedNullCollarEquiv (source, radius)) =
      finiteNullFaceHomogeneousScreenArea
          programPT06WarpedNullHyperplaneScreenMetric source.1 *
        programPT06WarpedNullHyperplaneFluxRestriction
          (programPT06WarpedNullCollarAffineFluxExtension density) source := by
  simp_rw [programPT06WarpedNullAmbientMetricVolumeDensity_collar,
    programPT06WarpedNullCollarAffineFluxExtension_metricDivergence
      (density := density) (source := source) _ hDensity]
  rw [programPT06WarpedNullCollarAffineFluxExtension_rightInverse]
  simp

end
end P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
end JanusFormal
