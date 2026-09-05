import Mathlib.MeasureTheory.Function.Jacobian
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D

/-! # Exact stereographic surface volume from the cone Jacobian

The canonical surface measure is recovered by an exact change of variables
on the radial shell, rather than by upper and lower volume bounds.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalStereographicExactVolume4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D

private abbrev Space3 := EuclideanSpace Real (Fin 3)
private abbrev RadialSpace := Space3 × Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

def radialEuclideanIsometry : WithLp 2 RadialSpace ≃ₗᵢ[Real] EuclideanR4 := by
  have hDim : Module.finrank Real (WithLp 2 RadialSpace) = 4 := by
    rw [(WithLp.prodContinuousLinearEquiv 2 Real Space3 Real).finrank_eq]
    simp [Space3, Module.finrank_prod]
  exact ((stdOrthonormalBasis Real (WithLp 2 RadialSpace)).reindex
    (finCongr hDim)).repr

/-- Volume-preserving linear identification used only to express the cone
Jacobian as the determinant of an endomorphism. -/
def radialVolumeEquiv : EuclideanR4 ≃L[Real] RadialSpace :=
  radialEuclideanIsometry.symm.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 Real Space3 Real)

theorem radialVolumeEquiv_measurePreserving :
    MeasurePreserving radialVolumeEquiv := by
  exact (WithLp.volume_preserving_ofLp Space3 Real).comp
    radialEuclideanIsometry.symm.measurePreserving

/-- Cone expressed in the same Euclidean space on source and target. -/
def euclideanStereographicCone (pole : StandardSphere) : EuclideanR4 → EuclideanR4 :=
  stereographicConeMap pole ∘ radialVolumeEquiv

theorem euclideanStereographicCone_contDiff (pole : StandardSphere) :
    ContDiff Real ω (euclideanStereographicCone pole) :=
  (stereographicConeMap_contDiff pole).comp radialVolumeEquiv.contDiff

theorem euclideanStereographicCone_injOn_positive (pole : StandardSphere) :
    InjOn (euclideanStereographicCone pole)
      {point | 0 < (radialVolumeEquiv point).2} := by
  intro first hFirst second hSecond hEqual
  apply radialVolumeEquiv.injective
  have hInverse := congrArg (stereographicConeInverse pole) hEqual
  simpa only [euclideanStereographicCone, Function.comp_apply,
    stereographicConeInverse_leftInverse pole _ hFirst,
    stereographicConeInverse_leftInverse pole _ hSecond] using hInverse

/-- Absolute cone Jacobian in product coordinates; no volume comparison
constant or assumed density identity enters its definition. -/
def stereographicConeJacobian (pole : StandardSphere) (point : RadialSpace) : ℝ≥0∞ :=
  ENNReal.ofReal |(fderiv Real (euclideanStereographicCone pole)
    (radialVolumeEquiv.symm point)).det|

theorem stereographicConeJacobian_measurable (pole : StandardSphere) :
    Measurable (stereographicConeJacobian pole) := by
  exact (ENNReal.continuous_ofReal.comp
    ((ContinuousLinearMap.continuous_det.comp
      (((euclideanStereographicCone_contDiff pole).continuous_fderiv (by simp)).comp
        radialVolumeEquiv.symm.continuous)).abs)).measurable

/-- Exact shell change of variables, valid for every measurable spatial set. -/
theorem stereographicConeJacobian_integral_shell
    (pole : StandardSphere) (subset : Set Space3) (hSubset : MeasurableSet subset) :
    (∫⁻ point in subset ×ˢ Ico (1 : Real) 2,
      stereographicConeJacobian pole point) =
      stereographicSurfaceCoordinateMeasure pole subset *
        ENNReal.ofReal (15 / 4 : Real) := by
  let shell : Set RadialSpace := subset ×ˢ Ico (1 : Real) 2
  have hShell : MeasurableSet shell := hSubset.prod measurableSet_Ico
  have hDerivative := (euclideanStereographicCone_contDiff pole).differentiable (by simp)
  have hChange := lintegral_abs_det_fderiv_eq_addHaar_image
    (volume : Measure EuclideanR4)
    (hShell.preimage radialVolumeEquiv.continuous.measurable)
    (fun point _ => (hDerivative point).hasFDerivAt.hasFDerivWithinAt)
    ((euclideanStereographicCone_injOn_positive pole).mono
      (by intro point hPoint; exact lt_of_lt_of_le (by norm_num) hPoint.2.1))
  have hTransport := radialVolumeEquiv_measurePreserving.setLIntegral_comp_preimage_emb
    radialVolumeEquiv.toHomeomorph.measurableEmbedding
    (stereographicConeJacobian pole) shell
  have hImage : euclideanStereographicCone pole '' (radialVolumeEquiv ⁻¹' shell) =
      stereographicConeMap pole '' shell := by
    rw [euclideanStereographicCone, Set.image_comp,
      Set.image_preimage_eq _ radialVolumeEquiv.surjective]
  rw [hImage, volume_stereographicConeMap_image_shell,
    ← stereographicSurfaceCoordinateMeasure_apply] at hChange
  rw [← hTransport]
  simpa only [stereographicConeJacobian, ContinuousLinearEquiv.symm_apply_apply] using hChange

/-- Exact coordinate density obtained by integrating out the auxiliary radius. -/
def stereographicExactSurfaceDensity (pole : StandardSphere) (coordinate : Space3) : ℝ≥0∞ :=
  (ENNReal.ofReal (15 / 4 : Real))⁻¹ *
    ∫⁻ radius in Ico (1 : Real) 2, stereographicConeJacobian pole (coordinate, radius)

theorem stereographicExactSurfaceDensity_measurable (pole : StandardSphere) :
    Measurable (stereographicExactSurfaceDensity pole) :=
  measurable_const.mul (stereographicConeJacobian_measurable pole).lintegral_prod_right'

/-- The pulled-back round measure has this exact Lebesgue density. Evaluating
the determinant and identifying it with the metric density is a separate step. -/
theorem stereographicSurfaceCoordinateMeasure_eq_withDensity (pole : StandardSphere) :
    stereographicSurfaceCoordinateMeasure pole =
      (volume : Measure Space3).withDensity (stereographicExactSurfaceDensity pole) := by
  ext subset hSubset
  rw [withDensity_apply _ hSubset]
  have hShell := stereographicConeJacobian_integral_shell pole subset hSubset
  rw [show (volume : Measure RadialSpace) =
      (volume : Measure Space3).prod (volume : Measure Real) from rfl,
    ← Measure.prod_restrict,
    lintegral_prod _ (stereographicConeJacobian_measurable pole).aemeasurable] at hShell
  simp only [stereographicExactSurfaceDensity]
  rw [lintegral_const_mul' _ _ (by simp), hShell]
  rw [mul_comm (stereographicSurfaceCoordinateMeasure pole subset), ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]

/-- The same exact density applies to space-time product coordinates. -/
theorem stereographicProductCoordinateMeasure_eq_withDensity (pole : StandardSphere) :
    (stereographicSurfaceCoordinateMeasure pole).prod (volume : Measure Real) =
      (volume : Measure RadialSpace).withDensity
        (fun point => stereographicExactSurfaceDensity pole point.1) := by
  rw [stereographicSurfaceCoordinateMeasure_eq_withDensity]
  exact prod_withDensity_left (stereographicExactSurfaceDensity_measurable pole)

variable (period : Real) (hPeriod : period ≠ 0)

local instance interiorTime_isFinite :
    IsFiniteMeasure (canonicalLorentzInteriorTimeMeasure period) := by
  constructor
  change ((volume : Measure Real).comap
      (Subtype.val : canonicalLorentzInteriorTime period → Real)) univ < ⊤
  have hTime : MeasurableSet (canonicalLorentzInteriorTime period) := measurableSet_Ioo
  rw [comap_subtype_coe_apply hTime volume univ,
    Set.image_univ, Subtype.range_coe]
  unfold canonicalLorentzInteriorTime
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_lt_top

/-- Lebesgue space coordinates times the ordinary open-strip time measure. -/
def canonicalInteriorStereographicLebesgueMeasure :
    Measure (CanonicalInteriorStereographicCoordinates period) :=
  (volume : Measure Space3).prod (canonicalLorentzInteriorTimeMeasure period)

theorem canonicalInteriorStereographicMeasure_eq_withDensity (pole : StandardSphere) :
    canonicalInteriorStereographicMeasure period pole =
      (canonicalInteriorStereographicLebesgueMeasure period).withDensity
        (fun point => stereographicExactSurfaceDensity pole point.1) := by
  unfold canonicalInteriorStereographicMeasure canonicalInteriorStereographicLebesgueMeasure
  rw [stereographicSurfaceCoordinateMeasure_eq_withDensity]
  exact prod_withDensity_left (stereographicExactSurfaceDensity_measurable pole)

local instance quotientMeasurableSpace :
    MeasurableSpace (MappingTorus (reflectedSphereData period hPeriod)) := borel _

/-- Exact transport from a weighted Lebesgue chart to the canonical quotient
measure, including charts shifted across the fundamental-strip seam. -/
theorem shiftedCanonicalInteriorStereographicPhysicalMap_exactDensity_measurePreserving
    (shift : Real) (pole : StandardSphere) :
    MeasurePreserving
      (shiftedCanonicalInteriorStereographicPhysicalMap period hPeriod shift pole)
      ((canonicalInteriorStereographicLebesgueMeasure period).withDensity
        (fun point => stereographicExactSurfaceDensity pole point.1))
      ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
        (Set.range (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole))) := by
  rw [← canonicalInteriorStereographicMeasure_eq_withDensity]
  exact shiftedCanonicalInteriorStereographicPhysicalMap_measurePreserving
    period hPeriod shift pole

/-- Gate: an exact coordinate Radon--Nikodym density for canonical round
surface volume and its space-time product, with no assumed measure bridge. -/
theorem canonical_stereographic_exact_volume_gate (pole : StandardSphere) :
    stereographicSurfaceCoordinateMeasure pole =
        (volume : Measure Space3).withDensity (stereographicExactSurfaceDensity pole) ∧
      (stereographicSurfaceCoordinateMeasure pole).prod (volume : Measure Real) =
        (volume : Measure RadialSpace).withDensity
          (fun point => stereographicExactSurfaceDensity pole point.1) :=
  ⟨stereographicSurfaceCoordinateMeasure_eq_withDensity pole,
    stereographicProductCoordinateMeasure_eq_withDensity pole⟩

end
end P0EFTJanusMappingTorusCanonicalStereographicExactVolume4D
end JanusFormal
