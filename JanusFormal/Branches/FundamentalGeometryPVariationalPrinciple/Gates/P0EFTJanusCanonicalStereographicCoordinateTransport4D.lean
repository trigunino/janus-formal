import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStereographicConeMetricVolume4D

/-! # Exact local coordinate transport of canonical volume

The concrete stereographic metric density is transported through an arbitrary
injective differentiable coordinate change on a measurable local domain.
-/

namespace JanusFormal
namespace P0EFTJanusCanonicalStereographicCoordinateTransport4D

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusMappingTorusCanonicalStereographicExactVolume4D
open P0EFTJanusStereographicConeMetricVolume4D

private abbrev Space3 := EuclideanSpace Real (Fin 3)
private abbrev Coordinates := Space3 × Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

local instance : (volume : Measure Coordinates).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Image measure for a measured embedding whose target measure is restricted
to the chart range. -/
theorem measuredEmbedding_image
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {source : Measure X} {target : Measure Y} {chart : X → Y}
    (hChart : MeasurableEmbedding chart)
    (hMeasure : MeasurePreserving chart source (target.restrict (range chart)))
    (subset : Set X) (hSubset : MeasurableSet subset) :
    target (chart '' subset) = source subset := by
  have hImage := congrArg (fun measure : Measure Y => measure (chart '' subset)) hMeasure.map_eq
  rw [hChart.map_apply, hChart.injective.preimage_image,
    Measure.restrict_apply (hChart.measurableSet_image.mpr hSubset),
    inter_eq_left.mpr (image_subset_range _ _)] at hImage
  exact hImage.symm

/-- Ambient coordinate density with the chart normalization already fixed. -/
def stereographicAmbientMetricDensity (point : Coordinates) : ℝ≥0∞ :=
  ENNReal.ofReal ((4 / (‖point.1‖ ^ 2 + 4)) ^ 3)

theorem stereographicProductCoordinateMeasure_eq_metric (pole : StandardSphere) :
    stereographicProductCoordinateMeasure pole =
      (volume : Measure Coordinates).withDensity stereographicAmbientMetricDensity := by
  rw [show stereographicProductCoordinateMeasure pole =
      (stereographicSurfaceCoordinateMeasure pole).prod (volume : Measure Real) from rfl,
    stereographicProductCoordinateMeasure_eq_withDensity]
  congr 1
  funext point
  exact stereographicExactSurfaceDensity_eq_metric pole point.1

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Exact quotient volume of any measurable subset of a stereographic strip. -/
theorem shiftedStereographicPhysicalMapAmbient_image_volume
    (shift : Real) (pole : StandardSphere) (subset : Set Coordinates)
    (hSubset : MeasurableSet subset)
    (hStrip : subset ⊆ range (canonicalInteriorStereographicCoordinateInclusion period)) :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole '' subset) =
      ∫⁻ point in subset, stereographicAmbientMetricDensity point := by
  let inclusion := canonicalInteriorStereographicCoordinateInclusion period
  let chart := shiftedCanonicalInteriorStereographicPhysicalMap period hPeriod shift pole
  have hInclusion := (canonicalInteriorStereographicCoordinateInclusion_isOpenEmbedding
    period).measurableEmbedding
  have hPreimage : MeasurableSet (inclusion ⁻¹' subset) := hInclusion.measurable hSubset
  have hImage : chart '' (inclusion ⁻¹' subset) =
      shiftedStereographicPhysicalMapAmbient period hPeriod shift pole '' subset := by
    change (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘ inclusion) ''
      (inclusion ⁻¹' subset) = _
    rw [Set.image_comp, Set.image_preimage_eq_inter_range, inter_eq_left.mpr hStrip]
  rw [← hImage, measuredEmbedding_image
    (shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
      period hPeriod shift pole).measurableEmbedding
    (shiftedCanonicalInteriorStereographicPhysicalMap_measurePreserving
      period hPeriod shift pole) _ hPreimage]
  have hSource := measuredEmbedding_image hInclusion
    (canonicalInteriorStereographicCoordinateInclusion_measurePreserving period pole)
    (inclusion ⁻¹' subset) hPreimage
  rw [Set.image_preimage_eq_inter_range, inter_eq_left.mpr hStrip,
    stereographicProductCoordinateMeasure_eq_metric, withDensity_apply _ hSubset] at hSource
  exact hSource.symm

/-- Local coordinate transport with the true derivative determinant. The
coordinate change may be local; no global inverse or full-domain map is assumed. -/
theorem canonicalVolume_local_coordinate_change
    (shift : Real) (pole : StandardSphere)
    (transition : Coordinates → Coordinates) (subset : Set Coordinates)
    (hSubset : MeasurableSet subset)
    (hDerivative : ∀ point ∈ subset, DifferentiableAt Real transition point)
    (hInjective : InjOn transition subset)
    (hStrip : transition '' subset ⊆
      range (canonicalInteriorStereographicCoordinateInclusion period)) :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod
        ((shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘ transition) '' subset) =
      ∫⁻ point in subset, ENNReal.ofReal |(fderiv Real transition point).det| *
        stereographicAmbientMetricDensity (transition point) := by
  have hWithin : ∀ point ∈ subset,
      HasFDerivWithinAt transition (fderiv Real transition point) subset point :=
    fun point hPoint => (hDerivative point hPoint).hasFDerivAt.hasFDerivWithinAt
  have hImage := measurable_image_of_fderivWithin hSubset hWithin hInjective
  rw [Set.image_comp, shiftedStereographicPhysicalMapAmbient_image_volume
    period hPeriod shift pole _ hImage hStrip]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure Coordinates) hSubset hWithin hInjective stereographicAmbientMetricDensity

private abbrev Index4 := Fin 3 ⊕ Fin 1

/-- Product Lorentz matrix in stereographic space-time coordinates. -/
def stereographicAmbientLorentzMatrix (point : Coordinates) : Matrix Index4 Index4 Real :=
  Matrix.diagonal (Sum.elim
    (fun _ : Fin 3 => (4 / (‖point.1‖ ^ 2 + 4)) ^ 2)
    (fun _ : Fin 1 => (-1 : Real)))

theorem stereographicAmbientLorentzMatrix_volume (point : Coordinates) :
    Real.sqrt |(stereographicAmbientLorentzMatrix point).det| =
      (4 / (‖point.1‖ ^ 2 + 4)) ^ 3 := by
  have hDet : (stereographicAmbientLorentzMatrix point).det =
      -((4 / (‖point.1‖ ^ 2 + 4)) ^ 6) := by
    rw [stereographicAmbientLorentzMatrix, Matrix.det_diagonal]
    simp [Fintype.prod_sum_type]
    ring
  rw [hDet, abs_neg, abs_of_nonneg (by positivity),
    show (4 / (‖point.1‖ ^ 2 + 4)) ^ 6 =
      ((4 / (‖point.1‖ ^ 2 + 4)) ^ 3) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

private def coordinateBasis : Module.Basis Index4 Real Coordinates :=
  (EuclideanSpace.basisFun (Fin 3) Real).toBasis.prod (Module.Basis.singleton (Fin 1) Real)

/-- Congruence of the actual product Lorentz matrix by the coordinate
differential; this is the metric matrix in the new local coordinates. -/
def stereographicTransitionLorentzMatrix
    (transition : Coordinates → Coordinates) (point : Coordinates) : Matrix Index4 Index4 Real :=
  let jacobian := LinearMap.toMatrix coordinateBasis coordinateBasis
    (fderiv Real transition point).toLinearMap
  jacobian.transpose * stereographicAmbientLorentzMatrix (transition point) * jacobian

theorem stereographicTransitionLorentzMatrix_volume
    (transition : Coordinates → Coordinates) (point : Coordinates) :
    Real.sqrt |(stereographicTransitionLorentzMatrix transition point).det| =
      |(fderiv Real transition point).det| *
        (4 / (‖(transition point).1‖ ^ 2 + 4)) ^ 3 := by
  let jacobian := LinearMap.toMatrix coordinateBasis coordinateBasis
    (fderiv Real transition point).toLinearMap
  have hDet : (stereographicTransitionLorentzMatrix transition point).det =
      jacobian.det ^ 2 * (stereographicAmbientLorentzMatrix (transition point)).det := by
    simp only [stereographicTransitionLorentzMatrix, jacobian,
      Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [hDet, abs_mul, abs_pow, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (abs_nonneg _), stereographicAmbientLorentzMatrix_volume]
  rw [show jacobian.det = (fderiv Real transition point).det from
    LinearMap.det_toMatrix coordinateBasis (fderiv Real transition point).toLinearMap]

/-- Exact measure transport stated entirely with the pulled-back Lorentz
metric determinant, for every admissible local coordinate change. -/
theorem canonicalVolume_local_metric_coordinate_change
    (shift : Real) (pole : StandardSphere)
    (transition : Coordinates → Coordinates) (subset : Set Coordinates)
    (hSubset : MeasurableSet subset)
    (hDerivative : ∀ point ∈ subset, DifferentiableAt Real transition point)
    (hInjective : InjOn transition subset)
    (hStrip : transition '' subset ⊆
      range (canonicalInteriorStereographicCoordinateInclusion period)) :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod
        ((shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘ transition) '' subset) =
      ∫⁻ point in subset, ENNReal.ofReal
        (Real.sqrt |(stereographicTransitionLorentzMatrix transition point).det|) := by
  rw [canonicalVolume_local_coordinate_change period hPeriod shift pole transition
    subset hSubset hDerivative hInjective hStrip]
  apply lintegral_congr
  intro point
  rw [stereographicTransitionLorentzMatrix_volume, ENNReal.ofReal_mul (abs_nonneg _)]
  rfl

end
end P0EFTJanusCanonicalStereographicCoordinateTransport4D
end JanusFormal
