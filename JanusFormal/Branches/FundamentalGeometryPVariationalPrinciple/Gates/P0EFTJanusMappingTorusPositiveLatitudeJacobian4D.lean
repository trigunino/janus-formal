import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D

/-!
# The exact positive-latitude Jacobian reduction

This gate separates the standard latitude change-of-variables formula on the
round sphere from the elementary uniform lower bound on its Jacobian.  The
remaining measure input has the exact density `cos normal ^ 2`; everything
needed to recover the unweighted collar estimate is proved here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPositiveLatitudeJacobian4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped ENNReal
open MeasureTheory Set
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev StandardEquatorialSphere :=
  Metric.sphere (0 : EuclideanR3) 1

private abbrev positiveLatitudeSourceMeasure :
    Measure (StandardEquatorialSphere × Real) :=
  ((volume : Measure EuclideanR3).toSphere).prod
    canonicalLatitudeUnitNormalMeasure

def canonicalPositiveLatitudeAmbientSourceMeasure :
    Measure (StandardEquatorialSphere × Real) :=
  ((volume : Measure EuclideanR3).toSphere).prod volume

def canonicalPositiveLatitudeDomain :
    Set (StandardEquatorialSphere × Real) :=
  Set.univ ×ˢ Set.Ioc (0 : Real) 1

theorem positiveLatitudeSourceMeasure_eq_restrict :
    positiveLatitudeSourceMeasure =
      canonicalPositiveLatitudeAmbientSourceMeasure.restrict
        canonicalPositiveLatitudeDomain := by
  simpa [positiveLatitudeSourceMeasure,
    canonicalPositiveLatitudeAmbientSourceMeasure,
    canonicalPositiveLatitudeDomain, canonicalLatitudeUnitNormalMeasure] using
    (Measure.prod_restrict
      (μ := (volume : Measure EuclideanR3).toSphere)
      (ν := (volume : Measure Real)) Set.univ (Set.Ioc (0 : Real) 1))

/-- The surface Jacobian of latitude coordinates on `S³`. -/
def canonicalPositiveLatitudeJacobian
    (parameter : StandardEquatorialSphere × Real) : ENNReal :=
  ENNReal.ofReal (Real.cos parameter.2 ^ 2)

@[simp]
theorem canonicalPositiveLatitudeMap_firstCoordinate
    (parameter : StandardEquatorialSphere × Real) :
    (EuclideanSpace.equiv (Fin 4) Real
      (canonicalPositiveLatitudeMap parameter).1) 0 =
        Real.sin parameter.2 := by
  rfl

@[simp]
theorem canonicalPositiveLatitudeMap_tailCoordinate
    (parameter : StandardEquatorialSphere × Real) (index : Fin 3) :
    (EuclideanSpace.equiv (Fin 4) Real
      (canonicalPositiveLatitudeMap parameter).1) index.succ =
        Real.cos parameter.2 *
          (EuclideanSpace.equiv (Fin 3) Real parameter.1.1) index := by
  rfl

/-- Positive latitude coordinates are one-to-one on the measured collar. -/
theorem canonicalPositiveLatitudeMap_injOn :
    Set.InjOn canonicalPositiveLatitudeMap
      canonicalPositiveLatitudeDomain := by
  intro first hFirst second hSecond hEqual
  have hSin : Real.sin first.2 = Real.sin second.2 := by
    calc
      Real.sin first.2 = (EuclideanSpace.equiv (Fin 4) Real
          (canonicalPositiveLatitudeMap first).1) 0 :=
        (canonicalPositiveLatitudeMap_firstCoordinate first).symm
      _ = (EuclideanSpace.equiv (Fin 4) Real
          (canonicalPositiveLatitudeMap second).1) 0 := congrArg
        (fun point : StandardSphere =>
          (EuclideanSpace.equiv (Fin 4) Real point.1) 0) hEqual
      _ = Real.sin second.2 :=
        canonicalPositiveLatitudeMap_firstCoordinate second
  have hFirstRange : first.2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [hFirst.2.1, Real.pi_pos]
    · linarith [hFirst.2.2, Real.pi_gt_three]
  have hSecondRange : second.2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [hSecond.2.1, Real.pi_pos]
    · linarith [hSecond.2.2, Real.pi_gt_three]
  have hNormal : first.2 = second.2 :=
    Real.injOn_sin hFirstRange hSecondRange hSin
  apply Prod.ext
  · apply Subtype.ext
    apply (EuclideanSpace.equiv (Fin 3) Real).injective
    funext index
    have hTail := congrArg
      (fun point : StandardSphere =>
        (EuclideanSpace.equiv (Fin 4) Real point.1) index.succ) hEqual
    rw [canonicalPositiveLatitudeMap_tailCoordinate,
      canonicalPositiveLatitudeMap_tailCoordinate, ← hNormal] at hTail
    have hAbs : |first.2| ≤ 1 := by
      rw [abs_of_pos hFirst.2.1]
      exact hFirst.2.2
    exact (mul_left_cancel₀
      (ne_of_gt (Real.cos_pos_of_le_one hAbs)) hTail)
  · exact hNormal

/-- The positive collar is a genuine measurable coordinate embedding into
the round three-sphere. -/
theorem canonicalPositiveLatitudeMap_measurableEmbedding :
    MeasurableEmbedding
      (canonicalPositiveLatitudeDomain.restrict
        canonicalPositiveLatitudeMap) :=
  canonicalPositiveLatitudeMap_continuous.continuousOn.measurableEmbedding
    (MeasurableSet.univ.prod measurableSet_Ioc)
    canonicalPositiveLatitudeMap_injOn

theorem canonicalPositiveLatitudeMap_image_measurable :
    MeasurableSet
      (canonicalPositiveLatitudeMap '' canonicalPositiveLatitudeDomain) := by
  simpa only [Set.range_restrict] using
    canonicalPositiveLatitudeMap_measurableEmbedding.measurableSet_range

theorem canonicalPositiveLatitudeJacobian_measurable :
    Measurable canonicalPositiveLatitudeJacobian := by
  unfold canonicalPositiveLatitudeJacobian
  exact ((Real.continuous_cos.comp continuous_snd).pow 2).measurable.ennreal_ofReal

/-- The source measure carrying the exact latitude surface Jacobian. -/
def canonicalPositiveLatitudeJacobianMeasure :
    Measure (StandardEquatorialSphere × Real) :=
  positiveLatitudeSourceMeasure.withDensity
    canonicalPositiveLatitudeJacobian

theorem canonicalPositiveLatitudeJacobianMeasure_eq_restrict :
    canonicalPositiveLatitudeJacobianMeasure =
      (canonicalPositiveLatitudeAmbientSourceMeasure.withDensity
        canonicalPositiveLatitudeJacobian).restrict
          canonicalPositiveLatitudeDomain := by
  rw [canonicalPositiveLatitudeJacobianMeasure,
    positiveLatitudeSourceMeasure_eq_restrict]
  exact (restrict_withDensity
    (MeasurableSet.univ.prod measurableSet_Ioc)
    canonicalPositiveLatitudeJacobian).symm

/-- The remaining standard change-of-variables statement: weighted latitude
coordinates give the round surface measure restricted to their image. -/
def CanonicalPositiveLatitudeWeightedMapFormula : Prop :=
  Measure.map canonicalPositiveLatitudeMap
      canonicalPositiveLatitudeJacobianMeasure =
    ((volume : Measure EuclideanR4).toSphere).restrict
      (canonicalPositiveLatitudeMap '' canonicalPositiveLatitudeDomain)

theorem canonicalPositiveLatitudeWeightedMapDomination_of_formula
    (hFormula : CanonicalPositiveLatitudeWeightedMapFormula) :
    Measure.map canonicalPositiveLatitudeMap
        canonicalPositiveLatitudeJacobianMeasure ≤
      (volume : Measure EuclideanR4).toSphere := by
  rw [hFormula]
  exact Measure.restrict_le_self

private theorem one_le_scaled_latitudeJacobian
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    (1 : ENNReal) ≤
      (canonicalLatitudeCoareaMeasureConstant : ENNReal) *
        ENNReal.ofReal (Real.cos normal ^ 2) := by
  have hCosOne : 0 < Real.cos 1 :=
    Real.cos_pos_of_le_one (by norm_num)
  have hCos : Real.cos 1 ≤ Real.cos normal := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi hNormal.1.le
      (by linarith [Real.pi_gt_three]) hNormal.2
  have hReal :
      (1 : Real) ≤ (Real.cos 1)⁻¹ ^ 2 * Real.cos normal ^ 2 := by
    field_simp
    nlinarith
  rw [← ENNReal.ofReal_one]
  rw [ENNReal.coe_nnreal_eq]
  change ENNReal.ofReal 1 ≤
    ENNReal.ofReal ((Real.cos 1)⁻¹ ^ 2) *
      ENNReal.ofReal (Real.cos normal ^ 2)
  rw [← ENNReal.ofReal_mul (sq_nonneg ((Real.cos 1)⁻¹))]
  exact ENNReal.ofReal_le_ofReal hReal

private theorem positiveLatitudeSourceMeasure_le_scaledJacobian :
    positiveLatitudeSourceMeasure ≤
      canonicalLatitudeCoareaMeasureConstant •
        canonicalPositiveLatitudeJacobianMeasure := by
  have hNormal : ∀ᵐ parameter ∂positiveLatitudeSourceMeasure,
      parameter.2 ∈ Set.Ioc (0 : Real) 1 := by
    exact Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem measurableSet_Ioc)
  have hDensity : (λ _ : StandardEquatorialSphere × Real => (1 : ENNReal))
      ≤ᵐ[positiveLatitudeSourceMeasure]
        (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          canonicalPositiveLatitudeJacobian := by
    filter_upwards [hNormal] with parameter hParameter
    simpa [Pi.smul_apply, smul_eq_mul,
      canonicalPositiveLatitudeJacobian] using
      one_le_scaled_latitudeJacobian hParameter
  calc
    positiveLatitudeSourceMeasure =
        positiveLatitudeSourceMeasure.withDensity 1 := by simp
    _ ≤ positiveLatitudeSourceMeasure.withDensity
          ((canonicalLatitudeCoareaMeasureConstant : ENNReal) •
            canonicalPositiveLatitudeJacobian) :=
      withDensity_mono hDensity
    _ = canonicalLatitudeCoareaMeasureConstant •
          canonicalPositiveLatitudeJacobianMeasure := by
      change positiveLatitudeSourceMeasure.withDensity
          ((canonicalLatitudeCoareaMeasureConstant : ENNReal) •
            canonicalPositiveLatitudeJacobian) =
        (canonicalLatitudeCoareaMeasureConstant : ENNReal) •
          positiveLatitudeSourceMeasure.withDensity
            canonicalPositiveLatitudeJacobian
      rw [withDensity_smul _
        canonicalPositiveLatitudeJacobian_measurable]

/-- The exact weighted latitude formula implies the original unweighted
positive-collar domination, with the sharp uniform reciprocal-cosine bound. -/
theorem canonicalPositiveLatitudeMeasureDomination_of_weightedMapFormula
    (hFormula : CanonicalPositiveLatitudeWeightedMapFormula) :
    CanonicalPositiveLatitudeMeasureDomination := by
  unfold CanonicalPositiveLatitudeMeasureDomination
  calc
    Measure.map canonicalPositiveLatitudeMap
        positiveLatitudeSourceMeasure ≤
        Measure.map canonicalPositiveLatitudeMap
          (canonicalLatitudeCoareaMeasureConstant •
            canonicalPositiveLatitudeJacobianMeasure) :=
      Measure.map_mono positiveLatitudeSourceMeasure_le_scaledJacobian
        canonicalPositiveLatitudeMap_continuous.measurable
    _ = canonicalLatitudeCoareaMeasureConstant •
          Measure.map canonicalPositiveLatitudeMap
            canonicalPositiveLatitudeJacobianMeasure := by
      rw [Measure.map_smul]
    _ ≤ canonicalLatitudeCoareaMeasureConstant •
          (volume : Measure EuclideanR4).toSphere :=
      by
        have hWeighted :=
          canonicalPositiveLatitudeWeightedMapDomination_of_formula hFormula
        change ((canonicalLatitudeCoareaMeasureConstant : NNReal) : ENNReal) •
              Measure.map canonicalPositiveLatitudeMap
                canonicalPositiveLatitudeJacobianMeasure ≤
            ((canonicalLatitudeCoareaMeasureConstant : NNReal) : ENNReal) •
              (volume : Measure EuclideanR4).toSphere
        rw [Measure.le_iff]
        intro set hSet
        rw [Measure.smul_apply, Measure.smul_apply]
        exact mul_le_mul_right (hWeighted set) _

/-- The weighted round-sphere formula closes the complete physical coarea
package through the quotient reductions already established upstream. -/
def canonicalLatitudeCoareaBoundOfWeightedMapFormula
    (period : Real) (hPeriod : period ≠ 0)
    (hFormula : CanonicalPositiveLatitudeWeightedMapFormula) :
    CanonicalLatitudeCoareaBound period hPeriod :=
  canonicalLatitudeCoareaBoundOfPositiveLatitudeDomination period hPeriod
    (canonicalPositiveLatitudeMeasureDomination_of_weightedMapFormula hFormula)

end

end P0EFTJanusMappingTorusPositiveLatitudeJacobian4D
end JanusFormal
