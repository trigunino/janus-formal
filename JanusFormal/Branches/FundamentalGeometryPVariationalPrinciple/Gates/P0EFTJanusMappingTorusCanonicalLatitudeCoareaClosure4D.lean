import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMeasureToSphereEquatorialCoarea4D

/-!
# Canonical latitude coarea closure on the effective mapping torus

The exact weighted latitude disintegration of `Measure.toSphere` on the standard
unit three-sphere is converted here into the unweighted positive-collar
inequality used by the physical scalar trace. The two remaining operations are
then measure-theoretic functoriality only:

* take the product with one fundamental time interval;
* push the resulting estimate through the mapping-torus quotient map.

Thus `CanonicalLatitudeMeasureToSphereCoareaDomination` is proved without an
additional analytic assumption.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMeasureToSphereEquatorialCoarea4D

private abbrev StandardSphere2 := Metric.sphere (0 : EuclideanR3) 1
private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1
private abbrev LatitudeAngle := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-- The standard latitude density. -/
def standardLatitudeWeight (parameter : StandardSphere2 × Real) : ENNReal :=
  ENNReal.ofReal (Real.cos parameter.2 ^ 2)

/-- Continuity of the standard latitude map. -/
theorem standardEquatorialLatitude_continuous :
    Continuous standardEquatorialLatitude := by
  exact unitThreeSphereHomeomorph.continuous.comp
    (equatorialLatitude_joint_continuous.comp
      ((equatorialTwoSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
        continuous_snd))

/-- Measurability of the standard latitude density. -/
theorem standardLatitudeWeight_measurable :
    Measurable standardLatitudeWeight := by
  fun_prop

/-- Restatement of the exact weighted latitude pushforward. -/
theorem standardLatitude_weighted_map :
    Measure.map standardEquatorialLatitude
        (((volume : Measure EuclideanR3).toSphere.prod
          (volume.restrict LatitudeAngle)).withDensity standardLatitudeWeight) =
      (volume : Measure EuclideanR4).toSphere := by
  simpa [standardLatitudeWeight] using
    P0EFTJanusMeasureToSphereEquatorialCoarea4D.standardEquatorialLatitude_weighted_map

/-- `cos 1` is strictly positive. -/
theorem cos_one_pos : 0 < Real.cos (1 : Real) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_gt_three]

/-- The latitude Jacobian on `0 < normal ≤ 1` is bounded below by its value at
the outer endpoint. -/
theorem cos_one_sq_le_cos_sq
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    Real.cos (1 : Real) ^ 2 ≤ Real.cos normal ^ 2 := by
  have hPi : (1 : Real) ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hCos : Real.cos (1 : Real) ≤ Real.cos normal :=
    Real.cos_le_cos_of_nonneg_of_le_pi hNormal.1.le hPi hNormal.2
  have hCosNormalNonnegative : 0 ≤ Real.cos normal :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_gt_three])
  nlinarith [cos_one_pos]

/-- Pointwise reciprocal-Jacobian estimate on the positive collar. -/
theorem one_le_coareaConstant_mul_weight
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    (1 : ENNReal) ≤
      canonicalLatitudeCoareaMeasureConstant *
        ENNReal.ofReal (Real.cos normal ^ 2) := by
  have hCosOne : Real.cos (1 : Real) ≠ 0 := ne_of_gt cos_one_pos
  have hLower := cos_one_sq_le_cos_sq hNormal
  rw [canonicalLatitudeCoareaMeasureConstant]
  norm_cast
  have hInvNonnegative : 0 ≤ (Real.cos (1 : Real))⁻¹ ^ 2 := sq_nonneg _
  rw [← ENNReal.ofReal_mul hInvNonnegative]
  apply ENNReal.ofReal_le_ofReal
  field_simp
  nlinarith

/-- The positive unit collar lies in the regular latitude strip. -/
theorem unitCollar_subset_latitudeAngle :
    Set.Ioc (0 : Real) 1 ⊆ LatitudeAngle := by
  intro normal hNormal
  constructor <;> nlinarith [hNormal.1, hNormal.2, Real.pi_gt_three]

/-- The unweighted positive-latitude measure is dominated by the reciprocal
minimum of the spherical Jacobian. -/
theorem standardLatitude_positiveCollar_map_le :
    Measure.map standardEquatorialLatitude
        ((volume : Measure EuclideanR3).toSphere.prod
          (volume.restrict (Set.Ioc (0 : Real) 1))) ≤
      canonicalLatitudeCoareaMeasureConstant •
        (volume : Measure EuclideanR4).toSphere := by
  let sphereMeasure : Measure StandardSphere2 :=
    (volume : Measure EuclideanR3).toSphere
  let angleMeasure : Measure Real := volume.restrict LatitudeAngle
  let baseMeasure : Measure (StandardSphere2 × Real) :=
    sphereMeasure.prod angleMeasure
  let collar : Set (StandardSphere2 × Real) :=
    Set.univ ×ˢ Set.Ioc (0 : Real) 1
  have hCollarMeasurable : MeasurableSet collar :=
    measurableSet_univ.prod measurableSet_Ioc
  have hDensity :
      baseMeasure.restrict collar ≤
        (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          (baseMeasure.withDensity standardLatitudeWeight).restrict collar := by
    rw [restrict_withDensity' collar]
    rw [← withDensity_one (μ := baseMeasure.restrict collar)]
    calc
      (baseMeasure.restrict collar).withDensity 1 ≤
          (baseMeasure.restrict collar).withDensity
            (fun parameter =>
              (canonicalLatitudeCoareaMeasureConstant : ENNReal) *
                standardLatitudeWeight parameter) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hCollarMeasurable] with parameter hParameter
        exact one_le_coareaConstant_mul_weight hParameter.2
      _ = (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          (baseMeasure.restrict collar).withDensity standardLatitudeWeight := by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          (withDensity_smul
            (μ := baseMeasure.restrict collar)
            (canonicalLatitudeCoareaMeasureConstant : ENNReal)
            standardLatitudeWeight_measurable)
  have hMap := Measure.map_mono hDensity
    standardEquatorialLatitude_continuous.measurable
  rw [Measure.map_smul] at hMap
  have hRestrictedMap :
      Measure.map standardEquatorialLatitude
          ((baseMeasure.withDensity standardLatitudeWeight).restrict collar) ≤
        (volume : Measure EuclideanR4).toSphere := by
    calc
      Measure.map standardEquatorialLatitude
          ((baseMeasure.withDensity standardLatitudeWeight).restrict collar) ≤
        Measure.map standardEquatorialLatitude
          (baseMeasure.withDensity standardLatitudeWeight) :=
        Measure.map_mono Measure.restrict_le_self
          standardEquatorialLatitude_continuous.measurable
      _ = _ := by
        simpa [baseMeasure, sphereMeasure, angleMeasure] using
          standardLatitude_weighted_map
  have hAngleRestriction :
      angleMeasure.restrict (Set.Ioc (0 : Real) 1) =
        volume.restrict (Set.Ioc (0 : Real) 1) := by
    rw [angleMeasure, Measure.restrict_restrict measurableSet_Ioc]
    rw [inter_eq_left.2 unitCollar_subset_latitudeAngle]
  have hSource :
      sphereMeasure.prod (volume.restrict (Set.Ioc (0 : Real) 1)) =
        baseMeasure.restrict collar := by
    calc
      sphereMeasure.prod (volume.restrict (Set.Ioc (0 : Real) 1)) =
          (sphereMeasure.restrict Set.univ).prod
            (angleMeasure.restrict (Set.Ioc (0 : Real) 1)) := by
        rw [Measure.restrict_univ, hAngleRestriction]
      _ = baseMeasure.restrict collar := by
        simpa [baseMeasure, collar] using
          (Measure.prod_restrict (μ := sphereMeasure) (ν := angleMeasure)
            Set.univ (Set.Ioc (0 : Real) 1))
  have hScaledMap :
      (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          Measure.map standardEquatorialLatitude
            ((baseMeasure.withDensity standardLatitudeWeight).restrict collar) ≤
        (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          (volume : Measure EuclideanR4).toSphere := by
    gcongr
  rw [hSource]
  simpa using hMap.trans hScaledMap

private abbrev sphereData (period : Real) (hPeriod : period ≠ 0) :=
  reflectedSphereData period hPeriod
private abbrev EffectiveQuotient (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (sphereData period hPeriod)

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- Public spelling of the fundamental-domain map defining the canonical
Lorentz volume. -/
def canonicalLorentzFundamentalDomainMap
    (period : Real) (hPeriod : period ≠ 0)
    (parameter : StandardSphere3 × Real) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    ((coverHomeomorphProd (sphereData period hPeriod)).symm
      (unitThreeSphereHomeomorph.symm parameter.1, parameter.2))

/-- Continuity of the public fundamental-domain map. -/
theorem canonicalLorentzFundamentalDomainMap_continuous
    (period : Real) (hPeriod : period ≠ 0) :
    Continuous (canonicalLorentzFundamentalDomainMap period hPeriod) := by
  have hProduct : Continuous
      (fun parameter : StandardSphere3 × Real =>
        (unitThreeSphereHomeomorph.symm parameter.1, parameter.2)) :=
    (unitThreeSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
      continuous_snd
  exact (mappingTorusMk_isCoveringMap
      (sphereData period hPeriod)).isLocalHomeomorph.continuous.comp
    ((coverHomeomorphProd
      (sphereData period hPeriod)).symm.continuous.comp hProduct)

/-- The intrinsic Lorentz volume is the pushforward of round `S³` measure times
one fundamental time interval. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_eq_publicMap
    (period : Real) (hPeriod : period ≠ 0) :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod =
      Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
        ((volume : Measure EuclideanR4).toSphere.prod
          (volume.restrict (canonicalLatitudeTimeInterval period))) := by
  rfl

/-- Reassociate `(sphere,time,normal)` as `((sphere,normal),time)`. -/
def canonicalLatitudeCollarReassociate
    (parameter : CanonicalLatitudeCollarParameter) :
    (StandardSphere2 × Real) × Real :=
  ((parameter.1.1, parameter.2), parameter.1.2)

/-- Continuity of the reassociation. -/
theorem canonicalLatitudeCollarReassociate_continuous :
    Continuous canonicalLatitudeCollarReassociate := by
  fun_prop

/-- Reassociation sends the canonical collar measure to the product in which
latitude and normal are adjacent. -/
theorem canonicalLatitudeCollarReassociate_map
    (period : Real) :
    Measure.map canonicalLatitudeCollarReassociate
        (canonicalLatitudeCollarMeasure period) =
      (((volume : Measure EuclideanR3).toSphere.prod
          canonicalLatitudeUnitNormalMeasure).prod
        (volume.restrict (canonicalLatitudeTimeInterval period))) := by
  let sphereMeasure : Measure StandardSphere2 :=
    (volume : Measure EuclideanR3).toSphere
  let timeMeasure : Measure Real :=
    volume.restrict (canonicalLatitudeTimeInterval period)
  let normalMeasure : Measure Real := canonicalLatitudeUnitNormalMeasure
  letI : IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
    canonicalLatitudeBaseMeasure_isFinite period
  letI : IsFiniteMeasure (canonicalLatitudeCollarMeasure period) := by
    unfold canonicalLatitudeCollarMeasure
    infer_instance
  change Measure.map canonicalLatitudeCollarReassociate
      ((sphereMeasure.prod timeMeasure).prod normalMeasure) =
    (sphereMeasure.prod normalMeasure).prod timeMeasure
  apply Measure.ext_prod₃'
  intro sphereSet normalSet timeSet hSphere hNormal hTime
  rw [Measure.map_apply canonicalLatitudeCollarReassociate_continuous.measurable
    ((hSphere.prod hNormal).prod hTime)]
  have hPreimage :
      canonicalLatitudeCollarReassociate ⁻¹'
          ((sphereSet ×ˢ normalSet) ×ˢ timeSet) =
        (sphereSet ×ˢ timeSet) ×ˢ normalSet := by
    ext parameter
    simp [canonicalLatitudeCollarReassociate, and_left_comm, and_assoc]
  rw [hPreimage, Measure.prod_prod, Measure.prod_prod,
    Measure.prod_prod, Measure.prod_prod]
  ac_rfl

/-- Latitude on `S³`, leaving time unchanged. -/
def canonicalLatitudeProductMap
    (parameter : (StandardSphere2 × Real) × Real) :
    StandardSphere3 × Real :=
  (standardEquatorialLatitude parameter.1, parameter.2)

/-- Continuity of product latitude. -/
theorem canonicalLatitudeProductMap_continuous :
    Continuous canonicalLatitudeProductMap :=
  (standardEquatorialLatitude_continuous.comp continuous_fst).prodMk
    continuous_snd

/-- Tensor the positive-collar estimate with the fundamental time measure. -/
theorem canonicalLatitudeProductMap_map_le
    (period : Real) :
    Measure.map canonicalLatitudeProductMap
        (Measure.map canonicalLatitudeCollarReassociate
          (canonicalLatitudeCollarMeasure period)) ≤
      canonicalLatitudeCoareaMeasureConstant •
        ((volume : Measure EuclideanR4).toSphere.prod
          (volume.restrict (canonicalLatitudeTimeInterval period))) := by
  let timeMeasure : Measure Real :=
    volume.restrict (canonicalLatitudeTimeInterval period)
  rw [canonicalLatitudeCollarReassociate_map]
  have hSphere :
      Measure.map standardEquatorialLatitude
          ((volume : Measure EuclideanR3).toSphere.prod
            canonicalLatitudeUnitNormalMeasure) ≤
        (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          (volume : Measure EuclideanR4).toSphere := by
    simpa [canonicalLatitudeUnitNormalMeasure] using
      standardLatitude_positiveCollar_map_le
  have hProduct := Measure.prod_mono hSphere
    (show timeMeasure ≤ timeMeasure from le_rfl)
  have hMapProduct :
      Measure.map canonicalLatitudeProductMap
          (((volume : Measure EuclideanR3).toSphere.prod
              canonicalLatitudeUnitNormalMeasure).prod timeMeasure) =
        (Measure.map standardEquatorialLatitude
            ((volume : Measure EuclideanR3).toSphere.prod
              canonicalLatitudeUnitNormalMeasure)).prod timeMeasure := by
    have h := Measure.map_prod_map
      ((volume : Measure EuclideanR3).toSphere.prod
        canonicalLatitudeUnitNormalMeasure)
      timeMeasure
      standardEquatorialLatitude_continuous.measurable
      measurable_id
    rw [Measure.map_id] at h
    simpa [canonicalLatitudeProductMap] using h.symm
  rw [hMapProduct]
  simpa [timeMeasure] using hProduct.trans_eq
    (Measure.prod_smul_left
      (ν := timeMeasure)
      (canonicalLatitudeCoareaMeasureConstant : ENNReal))

/-- The Janus collar factors through standard latitude and the public
fundamental-domain map. -/
theorem canonicalLatitudeCollarMap_factor
    (period : Real) (hPeriod : period ≠ 0)
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalLatitudeCollarMap period hPeriod parameter =
      canonicalLorentzFundamentalDomainMap period hPeriod
        (canonicalLatitudeProductMap
          (canonicalLatitudeCollarReassociate parameter)) := by
  simp [canonicalLatitudeCollarMap, canonicalLatitudeAnchor,
    quotientNormalLatitude, normalLatitudeCover,
    canonicalLorentzFundamentalDomainMap, canonicalLatitudeProductMap,
    canonicalLatitudeCollarReassociate, standardEquatorialLatitude]

/-- The exact spherical coarea domination required by the physical trace. -/
theorem canonicalLatitudeMeasureToSphereCoareaDomination
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalLatitudeMeasureToSphereCoareaDomination period hPeriod := by
  unfold CanonicalLatitudeMeasureToSphereCoareaDomination
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_publicMap]
  calc
    Measure.map (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeCollarMeasure period) =
      Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
        (Measure.map canonicalLatitudeProductMap
          (Measure.map canonicalLatitudeCollarReassociate
            (canonicalLatitudeCollarMeasure period))) := by
      rw [Measure.map_map
          canonicalLatitudeProductMap_continuous.measurable
          canonicalLatitudeCollarReassociate_continuous.measurable,
        Measure.map_map
          (canonicalLorentzFundamentalDomainMap_continuous
            period hPeriod).measurable
          ((canonicalLatitudeProductMap_continuous.comp
            canonicalLatitudeCollarReassociate_continuous).measurable)]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun parameter =>
        canonicalLatitudeCollarMap_factor period hPeriod parameter
    _ ≤ Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
        (canonicalLatitudeCoareaMeasureConstant •
          ((volume : Measure EuclideanR4).toSphere.prod
            (volume.restrict (canonicalLatitudeTimeInterval period)))) :=
      Measure.map_mono (canonicalLatitudeProductMap_map_le period)
        (canonicalLorentzFundamentalDomainMap_continuous
          period hPeriod).measurable
    _ = canonicalLatitudeCoareaMeasureConstant •
        Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
          ((volume : Measure EuclideanR4).toSphere.prod
            (volume.restrict (canonicalLatitudeTimeInterval period))) := by
      rw [Measure.map_smul]

end
end P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
end JanusFormal
