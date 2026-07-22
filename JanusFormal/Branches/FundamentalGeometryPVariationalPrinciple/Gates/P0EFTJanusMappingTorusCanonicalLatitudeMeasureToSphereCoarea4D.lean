import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMeasureToSphereEquatorialCoarea4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D

/-!
# Canonical latitude coarea domination on the mapping torus

This file installs the two geometric layers above the exact spherical coarea
formula:

1. on the positive unit collar `0 < ν ≤ 1`, remove the spherical Jacobian
   `cos² ν` at the sharp uniform cost `cos(1)⁻²`;
2. take the product with one fundamental time interval, reassociate the three
   factors, and push the estimate to the effective mapping torus.

The resulting theorem discharges the former measure-theoretic frontier in the
physical scalar `H¹` trace construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeMeasureToSphereCoarea4D

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
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMeasureToSphereEquatorialCoarea4D

private abbrev StandardSphere2 := Metric.sphere (0 : EuclideanR3) 1
private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1
private abbrev LatitudeAngle := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-! ## Removing the latitude Jacobian on the physical collar -/

/-- `cos 1` is strictly positive. -/
theorem cos_one_pos : 0 < Real.cos (1 : Real) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_gt_three]

/-- The physical unit collar lies inside the global latitude strip. -/
theorem unitNormalCollar_subset_latitudeAngle :
    Set.Ioc (0 : Real) 1 ⊆ LatitudeAngle := by
  intro normal hNormal
  constructor <;> nlinarith [hNormal.1, hNormal.2, Real.pi_gt_three]

/-- On `0 < ν ≤ 1`, the latitude density is bounded below by `cos² 1`. -/
theorem cos_one_sq_le_cos_sq
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    Real.cos (1 : Real) ^ 2 ≤ Real.cos normal ^ 2 := by
  have hPi : (1 : Real) ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hCos : Real.cos (1 : Real) ≤ Real.cos normal :=
    Real.cos_le_cos_of_nonneg_of_le_pi hNormal.1.le hPi hNormal.2
  have hNormalCosNonnegative : 0 ≤ Real.cos normal :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [hNormal.1, Real.pi_pos])
      (by nlinarith [hNormal.2, Real.pi_gt_three])
  nlinarith [cos_one_pos, hNormalCosNonnegative]

/-- Pointwise reciprocal-density estimate used to remove the Jacobian weight. -/
theorem one_le_coareaConstant_mul_weight
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    (1 : ENNReal) ≤
      (canonicalLatitudeCoareaMeasureConstant : ENNReal) *
        ENNReal.ofReal (Real.cos normal ^ 2) := by
  have hCosOne : Real.cos (1 : Real) ≠ 0 := ne_of_gt cos_one_pos
  have hLower := cos_one_sq_le_cos_sq hNormal
  have hInvNonnegative : 0 ≤ (Real.cos (1 : Real))⁻¹ ^ 2 := sq_nonneg _
  have hConstant :
      (canonicalLatitudeCoareaMeasureConstant : ENNReal) =
        ENNReal.ofReal ((Real.cos (1 : Real))⁻¹ ^ 2) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  rw [hConstant]
  rw [← ENNReal.ofReal_mul hInvNonnegative]
  have hReal : (1 : Real) ≤
      (Real.cos (1 : Real))⁻¹ ^ 2 * Real.cos normal ^ 2 := by
    calc
      (1 : Real) = (Real.cos (1 : Real))⁻¹ ^ 2 *
          Real.cos (1 : Real) ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hLower hInvNonnegative
  simpa using ENNReal.ofReal_le_ofReal hReal

/-- Latitude density on `S² × ℝ`. -/
def standardLatitudeWeight
    (parameter : StandardSphere2 × Real) : ENNReal :=
  ENNReal.ofReal (Real.cos parameter.2 ^ 2)

/-- Continuity of the standard latitude map. -/
theorem standardEquatorialLatitude_continuous :
    Continuous standardEquatorialLatitude := by
  change Continuous (fun parameter : StandardSphere2 × Real =>
    unitThreeSphereHomeomorph
      (equatorialLatitudeUncurried
        (equatorialTwoSphereHomeomorph.symm parameter.1, parameter.2)))
  exact unitThreeSphereHomeomorph.continuous.comp
    (equatorialLatitude_joint_continuous.comp
      (equatorialTwoSphereHomeomorph.symm.continuous.comp continuous_fst
        |>.prodMk continuous_snd))

theorem standardLatitudeWeight_measurable :
    Measurable standardLatitudeWeight := by
  exact ENNReal.measurable_ofReal.comp
    ((Real.continuous_cos.measurable.comp measurable_snd).pow_const 2)

/-- Restatement of the exact weighted latitude pushforward. -/
theorem standardLatitude_weighted_map :
    Measure.map standardEquatorialLatitude
        (((volume : Measure EuclideanR3).toSphere.prod
          (volume.restrict LatitudeAngle)).withDensity standardLatitudeWeight) =
      (volume : Measure EuclideanR4).toSphere := by
  change Measure.map standardEquatorialLatitude
      (((volume : Measure EuclideanR3).toSphere.prod
        (volume.restrict
          (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))).withDensity
        (fun parameter => ENNReal.ofReal (Real.cos parameter.2 ^ 2))) =
    (volume : Measure EuclideanR4).toSphere
  exact P0EFTJanusMeasureToSphereEquatorialCoarea4D.standardEquatorialLatitude_weighted_map

/-- Unweighted positive-latitude measure is dominated by the reciprocal minimum
of the spherical Jacobian. -/
theorem standardEquatorialLatitude_positiveCollar_map_le :
    Measure.map standardEquatorialLatitude
        ((volume : Measure EuclideanR3).toSphere.prod
          (volume.restrict (Set.Ioc (0 : Real) 1))) ≤
      (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
        (volume : Measure EuclideanR4).toSphere := by
  let sphereMeasure : Measure StandardSphere2 :=
    (volume : Measure EuclideanR3).toSphere
  let baseMeasure : Measure (StandardSphere2 × Real) :=
    sphereMeasure.prod (volume.restrict LatitudeAngle)
  let collar : Set (StandardSphere2 × Real) :=
    Set.univ ×ˢ Set.Ioc (0 : Real) 1
  have hCollarMeasurable : MeasurableSet collar :=
    (MeasurableSet.univ : MeasurableSet
      (Set.univ : Set StandardSphere2)).prod measurableSet_Ioc
  have hCollarMeasure :
      baseMeasure.restrict collar =
        sphereMeasure.prod (volume.restrict (Set.Ioc (0 : Real) 1)) := by
    dsimp [baseMeasure, collar]
    rw [← Measure.prod_restrict, Measure.restrict_univ,
      Measure.restrict_restrict_of_subset unitNormalCollar_subset_latitudeAngle]
  have hDensity :
      baseMeasure.restrict collar ≤
        (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          (baseMeasure.withDensity standardLatitudeWeight).restrict collar := by
    calc
      baseMeasure.restrict collar =
          (baseMeasure.restrict collar).withDensity 1 := by
        rw [withDensity_one]
      _ ≤ (baseMeasure.restrict collar).withDensity
          (fun parameter =>
            (canonicalLatitudeCoareaMeasureConstant : ENNReal) *
              standardLatitudeWeight parameter) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hCollarMeasurable] with parameter hParameter
        exact one_le_coareaConstant_mul_weight hParameter.2
      _ = (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          (baseMeasure.restrict collar).withDensity standardLatitudeWeight := by
        change (baseMeasure.restrict collar).withDensity
            ((canonicalLatitudeCoareaMeasureConstant : ENNReal) •
              standardLatitudeWeight) = _
        exact withDensity_smul
          (μ := baseMeasure.restrict collar)
          (canonicalLatitudeCoareaMeasureConstant : ENNReal)
          standardLatitudeWeight_measurable
      _ = (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          (baseMeasure.withDensity standardLatitudeWeight).restrict collar := by
        rw [restrict_withDensity']
  have hMappedDensity := Measure.map_mono hDensity
    standardEquatorialLatitude_continuous.measurable
  rw [Measure.map_smul] at hMappedDensity
  have hRestrictedWeightedMap :
      Measure.map standardEquatorialLatitude
          ((baseMeasure.withDensity standardLatitudeWeight).restrict collar) ≤
        (volume : Measure EuclideanR4).toSphere := by
    calc
      _ ≤ Measure.map standardEquatorialLatitude
          (baseMeasure.withDensity standardLatitudeWeight) :=
        Measure.map_mono Measure.restrict_le_self
          standardEquatorialLatitude_continuous.measurable
      _ = _ := by
        simpa [baseMeasure, sphereMeasure] using
          standardLatitude_weighted_map
  calc
    Measure.map standardEquatorialLatitude
        (sphereMeasure.prod (volume.restrict (Set.Ioc (0 : Real) 1))) =
      Measure.map standardEquatorialLatitude (baseMeasure.restrict collar) := by
        rw [hCollarMeasure]
    _ ≤ (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
        Measure.map standardEquatorialLatitude
          ((baseMeasure.withDensity standardLatitudeWeight).restrict collar) :=
      hMappedDensity
    _ ≤ (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
        (volume : Measure EuclideanR4).toSphere :=
      by gcongr

/-! ## Product with time and reassociation -/

private abbrev sphereData (period : Real) (hPeriod : period ≠ 0) :=
  reflectedSphereData period hPeriod

private abbrev EffectiveQuotient (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (sphereData period hPeriod)

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance (period : Real) (hPeriod : period ≠ 0) :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Reassociate and swap time with latitude normal:
`((u,t),ν) ↦ ((u,ν),t)`. -/
def canonicalLatitudeCollarReassociate
    (parameter : CanonicalLatitudeCollarParameter) :
    (StandardSphere2 × Real) × Real :=
  ((parameter.1.1, parameter.2), parameter.1.2)

@[simp] theorem canonicalLatitudeCollarReassociate_apply
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalLatitudeCollarReassociate parameter =
      ((parameter.1.1, parameter.2), parameter.1.2) :=
  rfl

/-- Continuity of the collar reassociation. -/
theorem canonicalLatitudeCollarReassociate_continuous :
    Continuous canonicalLatitudeCollarReassociate := by
  exact ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
    (continuous_snd.comp continuous_fst)

/-- Reassociation preserves the collar product measure. -/
theorem canonicalLatitudeCollarReassociate_measurePreserving
    (period : Real) :
    MeasurePreserving canonicalLatitudeCollarReassociate
      (canonicalLatitudeCollarMeasure period)
      ((((volume : Measure EuclideanR3).toSphere.prod
        canonicalLatitudeUnitNormalMeasure).prod
          (volume.restrict (canonicalLatitudeTimeInterval period)))) := by
  let sphereMeasure : Measure StandardSphere2 :=
    (volume : Measure EuclideanR3).toSphere
  let timeMeasure : Measure Real :=
    volume.restrict (canonicalLatitudeTimeInterval period)
  let normalMeasure : Measure Real := canonicalLatitudeUnitNormalMeasure
  refine ⟨canonicalLatitudeCollarReassociate_continuous.measurable, ?_⟩
  letI : IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
    canonicalLatitudeBaseMeasure_isFinite period
  letI : IsFiniteMeasure
      ((sphereMeasure.prod timeMeasure).prod normalMeasure) := by
    change IsFiniteMeasure (canonicalLatitudeCollarMeasure period)
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
    simp [canonicalLatitudeCollarReassociate, and_comm, and_left_comm]
  rw [hPreimage, Measure.prod_prod, Measure.prod_prod,
    Measure.prod_prod, Measure.prod_prod]
  ac_rfl

/-- Apply standard latitude to the space-normal pair and leave time unchanged. -/
def canonicalLatitudeSphereTimeMap
    (parameter : (StandardSphere2 × Real) × Real) :
    StandardSphere3 × Real :=
  Prod.map standardEquatorialLatitude id parameter

/-- Continuity of latitude on the space-normal pair, with time unchanged. -/
theorem canonicalLatitudeSphereTimeMap_continuous :
    Continuous canonicalLatitudeSphereTimeMap :=
  (standardEquatorialLatitude_continuous.comp continuous_fst).prodMk
    continuous_snd

/-- The full collar-to-sphere-time parameter map. -/
def canonicalLatitudeParameterSphereTimeMap
    (parameter : CanonicalLatitudeCollarParameter) :
    StandardSphere3 × Real :=
  canonicalLatitudeSphereTimeMap
    (canonicalLatitudeCollarReassociate parameter)

/-- Continuity of the full collar-to-sphere-time map. -/
theorem canonicalLatitudeParameterSphereTimeMap_continuous :
    Continuous canonicalLatitudeParameterSphereTimeMap :=
  canonicalLatitudeSphereTimeMap_continuous.comp
    canonicalLatitudeCollarReassociate_continuous

@[simp] theorem canonicalLatitudeParameterSphereTimeMap_apply
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalLatitudeParameterSphereTimeMap parameter =
      (standardEquatorialLatitude (parameter.1.1, parameter.2),
        parameter.1.2) :=
  rfl

/-- The collar parameter measure maps to at most the coarea constant times the
standard sphere-time product measure. -/
theorem canonicalLatitudeParameterSphereTimeMap_map_le
    (period : Real) :
    Measure.map canonicalLatitudeParameterSphereTimeMap
        (canonicalLatitudeCollarMeasure period) ≤
      (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
        ((volume : Measure EuclideanR4).toSphere.prod
          (volume.restrict (canonicalLatitudeTimeInterval period))) := by
  let normalParameterMeasure : Measure (StandardSphere2 × Real) :=
    (volume : Measure EuclideanR3).toSphere.prod
      canonicalLatitudeUnitNormalMeasure
  let timeMeasure : Measure Real :=
    volume.restrict (canonicalLatitudeTimeInterval period)
  letI : IsFiniteMeasure timeMeasure := by
    dsimp [timeMeasure, canonicalLatitudeTimeInterval]
    infer_instance
  have hLatitude :
      Measure.map standardEquatorialLatitude normalParameterMeasure ≤
        (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          (volume : Measure EuclideanR4).toSphere := by
    simpa [normalParameterMeasure, canonicalLatitudeUnitNormalMeasure] using
      standardEquatorialLatitude_positiveCollar_map_le
  have hProduct :
      (Measure.map standardEquatorialLatitude normalParameterMeasure).prod
          timeMeasure ≤
        (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          ((volume : Measure EuclideanR4).toSphere.prod timeMeasure) := by
    have hRaw :
        (Measure.map standardEquatorialLatitude normalParameterMeasure).prod
            timeMeasure ≤
          (((canonicalLatitudeCoareaMeasureConstant : ENNReal) •
            (volume : Measure EuclideanR4).toSphere).prod timeMeasure) := by
      refine Measure.le_iff.2 ?_
      intro measurableSet hMeasurableSet
      rw [Measure.prod_apply hMeasurableSet, Measure.prod_apply hMeasurableSet]
      exact lintegral_mono' hLatitude le_rfl
    exact hRaw.trans_eq
      (Measure.prod_smul_left
        (ν := timeMeasure)
        (canonicalLatitudeCoareaMeasureConstant : ENNReal))
  calc
    Measure.map canonicalLatitudeParameterSphereTimeMap
        (canonicalLatitudeCollarMeasure period) =
      Measure.map canonicalLatitudeSphereTimeMap
        (Measure.map canonicalLatitudeCollarReassociate
          (canonicalLatitudeCollarMeasure period)) := by
        rw [Measure.map_map
          canonicalLatitudeSphereTimeMap_continuous.measurable
          canonicalLatitudeCollarReassociate_continuous.measurable]
        rfl
    _ = Measure.map canonicalLatitudeSphereTimeMap
        (normalParameterMeasure.prod timeMeasure) := by
      rw [(canonicalLatitudeCollarReassociate_measurePreserving period).map_eq]
    _ = (Measure.map standardEquatorialLatitude normalParameterMeasure).prod
        timeMeasure := by
      change Measure.map (Prod.map standardEquatorialLatitude id)
          (normalParameterMeasure.prod timeMeasure) = _
      have h := Measure.map_prod_map normalParameterMeasure timeMeasure
        standardEquatorialLatitude_continuous.measurable measurable_id
      rw [Measure.map_id] at h
      exact h.symm
    _ ≤ _ := hProduct

/-! ## Pushforward to the mapping torus -/

/-- Public spelling of the fundamental-domain map defining the intrinsic
Lorentz volume. -/
def canonicalLorentzFundamentalDomainMap
    (period : Real) (hPeriod : period ≠ 0)
    (parameter : StandardSphere3 × Real) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    ((coverHomeomorphProd (sphereData period hPeriod)).symm
      (unitThreeSphereHomeomorph.symm parameter.1, parameter.2))

/-- The public fundamental-domain map is continuous. -/
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

/-- The intrinsic Lorentz volume is definitionally the pushforward by the public
fundamental-domain map. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_eq_publicMap
    (period : Real) (hPeriod : period ≠ 0) :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod =
      Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
        ((volume : Measure EuclideanR4).toSphere.prod
          (volume.restrict (canonicalLatitudeTimeInterval period))) := by
  rfl

/-- The physical collar map factors through standard latitude and the public
fundamental-domain map. -/
theorem canonicalLatitudeCollarMap_factor
    (period : Real) (hPeriod : period ≠ 0)
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalLatitudeCollarMap period hPeriod parameter =
      canonicalLorentzFundamentalDomainMap period hPeriod
        (canonicalLatitudeParameterSphereTimeMap parameter) := by
  rfl

/-- The exact spherical coarea domination required by the physical `H¹` trace. -/
theorem canonicalLatitudeMeasureToSphereCoareaDomination
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalLatitudeMeasureToSphereCoareaDomination period hPeriod := by
  unfold CanonicalLatitudeMeasureToSphereCoareaDomination
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_publicMap]
  calc
    Measure.map (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeCollarMeasure period) =
      Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
        (Measure.map canonicalLatitudeParameterSphereTimeMap
          (canonicalLatitudeCollarMeasure period)) := by
        rw [Measure.map_map
          (canonicalLorentzFundamentalDomainMap_continuous
            period hPeriod).measurable
          canonicalLatitudeParameterSphereTimeMap_continuous.measurable]
        apply Measure.map_congr
        exact Filter.Eventually.of_forall fun parameter =>
          canonicalLatitudeCollarMap_factor period hPeriod parameter
    _ ≤ Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
        ((canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          ((volume : Measure EuclideanR4).toSphere.prod
            (volume.restrict (canonicalLatitudeTimeInterval period)))) :=
      Measure.map_mono
        (canonicalLatitudeParameterSphereTimeMap_map_le period)
        (canonicalLorentzFundamentalDomainMap_continuous
          period hPeriod).measurable
    _ = (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
        Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
          ((volume : Measure EuclideanR4).toSphere.prod
            (volume.restrict (canonicalLatitudeTimeInterval period))) := by
      rw [Measure.map_smul]

/-! ## Unconditional closure of the physical scalar trace -/

/-- The former measure-theoretic frontier is now unconditional. -/
theorem canonicalPhysicalScalarLatitudeCoareaTheorem
    (period : Real) (hPeriod : period ≠ 0) :
    P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.CanonicalPhysicalScalarLatitudeCoareaTheorem
      period hPeriod :=
  canonicalLatitudeMeasureToSphereCoareaDomination period hPeriod

/-- Completed physical scalar trace obtained from the proved coarea formula. -/
def canonicalPhysicalScalarH1TraceOfSphereCoarea
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.canonicalPhysicalScalarH1TraceOfCoarea
    period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)

/-- Agreement of the unconditional completed trace with smooth restriction. -/
theorem canonicalPhysicalScalarH1TraceOfSphereCoarea_agrees_on_smooth
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarH1TraceOfSphereCoarea period hPeriod
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field :=
  P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.canonicalPhysicalScalarH1TraceOfCoarea_agrees_on_smooth
    period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) field

/-- The physical scalar `H¹` trace now exists without an external coarea
assumption. -/
theorem canonicalPhysicalH1TraceExists_unconditional
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalPhysicalH1TraceExists period hPeriod :=
  P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.canonicalPhysicalH1TraceExists_ofCoarea
    period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)

/-- Closure certificate with the explicit coarea constant. -/
theorem canonicalPhysicalH1TraceCoareaClosure_certificate_unconditional
    (period : Real) (hPeriod : period ≠ 0) :
    Nonempty (CanonicalPhysicalH1TraceBound period hPeriod) ∧
      CanonicalPhysicalH1TraceExists period hPeriod ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 ≤
          (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.canonicalPhysicalScalarH1TraceCoareaConstant
            period hPeriod
            (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)) ^ 2 *
          ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2) :=
  P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.canonicalPhysicalH1TraceCoareaClosure_certificate
    period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)

end
end P0EFTJanusMappingTorusCanonicalLatitudeMeasureToSphereCoarea4D
end JanusFormal
