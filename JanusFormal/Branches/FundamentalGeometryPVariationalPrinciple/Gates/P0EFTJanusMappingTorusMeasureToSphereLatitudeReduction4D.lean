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
private abbrev StandardEquatorialSphere :=
  Metric.sphere (0 : EuclideanR3) 1

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

/-- Positive latitude before adjoining the independent mapping-torus time
coordinate. -/
def canonicalPositiveLatitudeMap
    (parameter : StandardEquatorialSphere × Real) : StandardSphere :=
  unitThreeSphereHomeomorph
    (equatorialLatitudeUncurried
      (equatorialTwoSphereHomeomorph.symm parameter.1, parameter.2))

theorem canonicalPositiveLatitudeMap_continuous :
    Continuous canonicalPositiveLatitudeMap := by
  exact unitThreeSphereHomeomorph.continuous.comp
    (equatorialLatitude_joint_continuous.comp
      (equatorialTwoSphereHomeomorph.symm.continuous.comp continuous_fst
        |>.prodMk continuous_snd))

/-- The pure round-sphere latitude statement.  This is the unique residual
Mathlib-level input: it contains neither the mapping-torus time coordinate nor
the quotient geometry. -/
def CanonicalPositiveLatitudeMeasureDomination : Prop :=
  Measure.map canonicalPositiveLatitudeMap
      (((volume : Measure EuclideanR3).toSphere).prod
        canonicalLatitudeUnitNormalMeasure) ≤
    canonicalLatitudeCoareaMeasureConstant •
      (volume : Measure EuclideanR4).toSphere

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

/-- Reorder `((sphere, time), normal)` as `((sphere, normal), time)`. -/
def canonicalLatitudeParameterReassociate
    (parameter : CanonicalLatitudeCollarParameter) :
    (StandardEquatorialSphere × Real) × Real :=
  ((parameter.1.1, parameter.2), parameter.1.2)

theorem canonicalLatitudeParameterReassociate_measurable :
    Measurable canonicalLatitudeParameterReassociate := by
  unfold canonicalLatitudeParameterReassociate
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

private theorem measurePreserving_canonicalLatitudeParameterReassociate
    (period : Real) :
    MeasurePreserving canonicalLatitudeParameterReassociate
      (canonicalLatitudeCollarMeasure period)
      ((((volume : Measure EuclideanR3).toSphere).prod
          canonicalLatitudeUnitNormalMeasure).prod
        (volume.restrict (canonicalLatitudeTimeInterval period))) := by
  let sphereMeasure : Measure StandardEquatorialSphere :=
    (volume : Measure EuclideanR3).toSphere
  let timeMeasure : Measure Real :=
    volume.restrict (canonicalLatitudeTimeInterval period)
  let normalMeasure : Measure Real := canonicalLatitudeUnitNormalMeasure
  have hAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        (StandardEquatorialSphere × Real) × Real ≃ᵐ
          StandardEquatorialSphere × (Real × Real))
      ((sphereMeasure.prod timeMeasure).prod normalMeasure)
      (sphereMeasure.prod (timeMeasure.prod normalMeasure)) :=
    measurePreserving_prodAssoc sphereMeasure timeMeasure normalMeasure
  have hSwap : MeasurePreserving
      (Prod.map id Prod.swap)
      (sphereMeasure.prod (timeMeasure.prod normalMeasure))
      (sphereMeasure.prod (normalMeasure.prod timeMeasure)) :=
    by
      simpa only [Measure.map_id] using
        (measurable_id.measurePreserving sphereMeasure).prod
          (Measure.measurePreserving_swap
            (μ := timeMeasure) (ν := normalMeasure))
  have hUnassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        StandardEquatorialSphere × (Real × Real) ≃ᵐ
          (StandardEquatorialSphere × Real) × Real)
      (sphereMeasure.prod (normalMeasure.prod timeMeasure))
      ((sphereMeasure.prod normalMeasure).prod timeMeasure) :=
    (measurePreserving_prodAssoc sphereMeasure normalMeasure timeMeasure).symm
      MeasurableEquiv.prodAssoc
  change MeasurePreserving
    (fun parameter : (StandardEquatorialSphere × Real) × Real =>
      ((parameter.1.1, parameter.2), parameter.1.2))
    (canonicalLatitudeCollarMeasure period)
    ((((volume : Measure EuclideanR3).toSphere).prod
      canonicalLatitudeUnitNormalMeasure).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  simpa [canonicalLatitudeCollarMeasure, canonicalLatitudeBaseMeasure,
    sphereMeasure, timeMeasure, normalMeasure,
    canonicalLatitudeParameterReassociate, Function.comp_def,
    MeasurableEquiv.prodAssoc] using hUnassoc.comp (hSwap.comp hAssoc)

private theorem Measure.prod_mono_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} (τ : Measure β) [SFinite τ]
    (hμν : μ ≤ ν) : μ.prod τ ≤ ν.prod τ := by
  rw [Measure.le_iff]
  intro set hSet
  rw [Measure.prod_apply hSet, Measure.prod_apply hSet]
  exact lintegral_mono' hμν le_rfl

/-- Mapping the full collar is exactly the product of the pure latitude
pushforward and the unchanged time measure. -/
theorem canonicalLatitudeFundamentalMap_map_eq_prod (period : Real) :
    Measure.map canonicalLatitudeFundamentalMap
        (canonicalLatitudeCollarMeasure period) =
      (Measure.map canonicalPositiveLatitudeMap
          (((volume : Measure EuclideanR3).toSphere).prod
            canonicalLatitudeUnitNormalMeasure)).prod
        (volume.restrict (canonicalLatitudeTimeInterval period)) := by
  let sourceMeasure : Measure (StandardEquatorialSphere × Real) :=
    ((volume : Measure EuclideanR3).toSphere).prod
      canonicalLatitudeUnitNormalMeasure
  let timeMeasure : Measure Real :=
    volume.restrict (canonicalLatitudeTimeInterval period)
  have hReassociate :=
    measurePreserving_canonicalLatitudeParameterReassociate period
  calc
    Measure.map canonicalLatitudeFundamentalMap
        (canonicalLatitudeCollarMeasure period) =
        Measure.map (Prod.map canonicalPositiveLatitudeMap id)
          (Measure.map canonicalLatitudeParameterReassociate
            (canonicalLatitudeCollarMeasure period)) := by
      rw [Measure.map_map
        (canonicalPositiveLatitudeMap_continuous.measurable.prodMap measurable_id)
        canonicalLatitudeParameterReassociate_measurable]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun parameter => rfl
    _ = Measure.map (Prod.map canonicalPositiveLatitudeMap id)
          (sourceMeasure.prod timeMeasure) := by
      rw [hReassociate.map_eq]
    _ = (Measure.map canonicalPositiveLatitudeMap sourceMeasure).prod
          timeMeasure := by
      rw [← Measure.map_prod_map sourceMeasure timeMeasure
        canonicalPositiveLatitudeMap_continuous.measurable measurable_id,
        Measure.map_id]
    _ = _ := rfl

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

/-- Tensoring the pure latitude inequality with the unchanged finite time
measure proves the full fundamental-domain statement. -/
theorem canonicalLatitudeFundamentalMeasureDomination_of_positiveLatitude
    (hLatitude : CanonicalPositiveLatitudeMeasureDomination) :
    CanonicalLatitudeFundamentalMeasureDomination period := by
  unfold CanonicalLatitudeFundamentalMeasureDomination
  rw [canonicalLatitudeFundamentalMap_map_eq_prod]
  calc
    (Measure.map canonicalPositiveLatitudeMap
        (((volume : Measure EuclideanR3).toSphere).prod
          canonicalLatitudeUnitNormalMeasure)).prod
        (volume.restrict (canonicalLatitudeTimeInterval period)) ≤
        (canonicalLatitudeCoareaMeasureConstant •
          (volume : Measure EuclideanR4).toSphere).prod
          (volume.restrict (canonicalLatitudeTimeInterval period)) :=
      Measure.prod_mono_left _ hLatitude
    _ = canonicalLatitudeCoareaMeasureConstant •
        canonicalLatitudeTargetProductMeasure period := by
      change (((canonicalLatitudeCoareaMeasureConstant : NNReal) : ENNReal) •
          (volume : Measure EuclideanR4).toSphere).prod
          (volume.restrict (canonicalLatitudeTimeInterval period)) =
        ((canonicalLatitudeCoareaMeasureConstant : NNReal) : ENNReal) •
          canonicalLatitudeTargetProductMeasure period
      rw [Measure.prod_smul_left]
      rfl

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

/-- The isolated pure sphere statement already closes the quotient coarea
gate. -/
theorem canonicalLatitudeMeasureToSphereCoareaDomination_of_positiveLatitude
    (hLatitude : CanonicalPositiveLatitudeMeasureDomination) :
    CanonicalLatitudeMeasureToSphereCoareaDomination period hPeriod :=
  canonicalLatitudeMeasureToSphereCoareaDomination_of_fundamental
    period hPeriod
    (canonicalLatitudeFundamentalMeasureDomination_of_positiveLatitude
      period hLatitude)

/-- Consequently the original coarea package and physical trace follow from
the single pre-quotient sphere/time statement. -/
def canonicalLatitudeCoareaBoundOfFundamentalDomination
    (hFundamental :
      CanonicalLatitudeFundamentalMeasureDomination period) :
    CanonicalLatitudeCoareaBound period hPeriod :=
  canonicalLatitudeCoareaBoundOfMeasureToSphereDomination period hPeriod
    (canonicalLatitudeMeasureToSphereCoareaDomination_of_fundamental
      period hPeriod hFundamental)

/-- Complete physical coarea package from the pure round-sphere latitude
inequality. -/
def canonicalLatitudeCoareaBoundOfPositiveLatitudeDomination
    (hLatitude : CanonicalPositiveLatitudeMeasureDomination) :
    CanonicalLatitudeCoareaBound period hPeriod :=
  canonicalLatitudeCoareaBoundOfFundamentalDomination period hPeriod
    (canonicalLatitudeFundamentalMeasureDomination_of_positiveLatitude
      period hLatitude)

end

end P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
end JanusFormal
