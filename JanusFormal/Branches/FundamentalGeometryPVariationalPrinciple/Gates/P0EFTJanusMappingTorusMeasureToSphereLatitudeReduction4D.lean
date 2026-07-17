import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-!
# Reduction of physical coarea to the round-sphere latitude measure

This gate removes the mapping-torus quotient from the remaining physical
coarea input.  The sole residual statement is an inequality between the
latitude pushforward of `Measure.toSphere` on `S²` and `Measure.toSphere` on
`S³`, tensored with the same fundamental time interval.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The same round `S³` surface measure and fundamental time interval used by
the canonical Lorentz volume before quotienting. -/
def canonicalLatitudeTargetProductMeasure (period : Real) :
    Measure (StandardSphere × Real) :=
  ((volume : Measure EuclideanR4).toSphere).prod
    (volume.restrict (canonicalLatitudeTimeInterval period))

/-- Latitude map with the time coordinate retained, but before passing to the
mapping-torus quotient. -/
def canonicalLatitudeFundamentalMap
    (parameter : CanonicalLatitudeCollarParameter) :
    StandardSphere × Real :=
  (unitThreeSphereHomeomorph
      (equatorialLatitudeUncurried
        (equatorialTwoSphereHomeomorph.symm parameter.1.1, parameter.2)),
    parameter.1.2)

theorem canonicalLatitudeFundamentalMap_continuous :
    Continuous canonicalLatitudeFundamentalMap := by
  have hEquator : Continuous
      (fun parameter : CanonicalLatitudeCollarParameter =>
        equatorialTwoSphereHomeomorph.symm parameter.1.1) :=
    equatorialTwoSphereHomeomorph.symm.continuous.comp
      (continuous_fst.comp continuous_fst)
  have hLatitudeInput : Continuous
      (fun parameter : CanonicalLatitudeCollarParameter =>
        (equatorialTwoSphereHomeomorph.symm parameter.1.1, parameter.2)) :=
    hEquator.prodMk continuous_snd
  have hLatitude : Continuous
      (equatorialLatitudeUncurried ∘
        fun parameter : CanonicalLatitudeCollarParameter =>
          (equatorialTwoSphereHomeomorph.symm parameter.1.1, parameter.2)) :=
    equatorialLatitude_joint_continuous.comp hLatitudeInput
  exact (unitThreeSphereHomeomorph.continuous.comp hLatitude).prodMk
    (continuous_snd.comp continuous_fst)

/-- Public version of the fundamental-domain projection used in the canonical
Lorentz measure. -/
def canonicalLatitudeQuotientMap
    (point : StandardSphere × Real) : EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    ((coverHomeomorphProd (sphereData period hPeriod)).symm
      (unitThreeSphereHomeomorph.symm point.1, point.2))

theorem canonicalLatitudeQuotientMap_continuous :
    Continuous (canonicalLatitudeQuotientMap period hPeriod) := by
  have hProduct : Continuous
      (fun point : StandardSphere × Real =>
        (unitThreeSphereHomeomorph.symm point.1, point.2)) :=
    (unitThreeSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
      continuous_snd
  exact (mappingTorusMk_isCoveringMap
      (sphereData period hPeriod)).isLocalHomeomorph.continuous.comp
    ((coverHomeomorphProd
      (sphereData period hPeriod)).symm.continuous.comp hProduct)

theorem canonicalLatitudeCollarMap_factorization
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalLatitudeCollarMap period hPeriod parameter =
      canonicalLatitudeQuotientMap period hPeriod
        (canonicalLatitudeFundamentalMap parameter) :=
  rfl

/-- The unique coarea input stripped of all quotient geometry. -/
def CanonicalLatitudeFundamentalMeasureDomination : Prop :=
  Measure.map canonicalLatitudeFundamentalMap
      (canonicalLatitudeCollarMeasure period) ≤
    canonicalLatitudeCoareaMeasureConstant •
      canonicalLatitudeTargetProductMeasure period

/-- The canonical quotient measure is exactly the pushforward of the public
round-sphere/time product presentation above. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_eq_fundamentalMap :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod =
      Measure.map (canonicalLatitudeQuotientMap period hPeriod)
        (canonicalLatitudeTargetProductMeasure period) := by
  rfl

/-- The round-sphere latitude inequality implies the complete physical coarea
domination on the actual mapping-torus quotient. -/
theorem canonicalLatitudeMeasureToSphereCoareaDomination_of_fundamental
    (hFundamental :
      CanonicalLatitudeFundamentalMeasureDomination period) :
    CanonicalLatitudeMeasureToSphereCoareaDomination period hPeriod := by
  unfold CanonicalLatitudeMeasureToSphereCoareaDomination
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_fundamentalMap]
  calc
    Measure.map (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeCollarMeasure period) =
        Measure.map (canonicalLatitudeQuotientMap period hPeriod)
          (Measure.map canonicalLatitudeFundamentalMap
            (canonicalLatitudeCollarMeasure period)) := by
      rw [Measure.map_map
        (canonicalLatitudeQuotientMap_continuous
          period hPeriod).measurable
        canonicalLatitudeFundamentalMap_continuous.measurable]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun parameter =>
        canonicalLatitudeCollarMap_factorization period hPeriod parameter
    _ ≤ Measure.map (canonicalLatitudeQuotientMap period hPeriod)
          (canonicalLatitudeCoareaMeasureConstant •
            canonicalLatitudeTargetProductMeasure period) :=
      Measure.map_mono hFundamental
        (canonicalLatitudeQuotientMap_continuous
          period hPeriod).measurable
    _ = canonicalLatitudeCoareaMeasureConstant •
          Measure.map (canonicalLatitudeQuotientMap period hPeriod)
            (canonicalLatitudeTargetProductMeasure period) := by
      rw [Measure.map_smul]

/-- Consequently the original coarea package and physical trace follow from
the single pre-quotient sphere/time statement. -/
def canonicalLatitudeCoareaBoundOfFundamentalDomination
    (hFundamental :
      CanonicalLatitudeFundamentalMeasureDomination period) :
    CanonicalLatitudeCoareaBound period hPeriod :=
  canonicalLatitudeCoareaBoundOfMeasureToSphereDomination period hPeriod
    (canonicalLatitudeMeasureToSphereCoareaDomination_of_fundamental
      period hPeriod hFundamental)

end

end P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
end JanusFormal
