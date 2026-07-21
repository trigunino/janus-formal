import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceMeasuredStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMetricCollarMeasureBridge4D

/-!
# Intrinsic metric-volume bridge for the glued centered cutoff divergence
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Set MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
open P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceMeasuredStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeMetricCollarMeasureBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusPositiveLatitudeJacobian4D
open P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDensitizedDivergence4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricNormalDivergence4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricTangentialCompensation4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
open P0EFTJanusMappingTorusCutBulkEqualMassEulerGreenNormalDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := Fin 4 → Real

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev StandardEquatorialSphere := Metric.sphere (0 : EuclideanR3) 1

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Coordinate density of the glued scalar divergence against the unweighted
collar product measure; multiplication by `cos²` is exactly the metric volume
factor. -/
def canonicalLatitudeCenteredMetricCutoffDivergenceDensity
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (parameter : CanonicalLatitudeCollarParameter) : Real :=
  canonicalPositiveLatitudeWeight parameter.2 *
    canonicalLatitudeCenteredGlobalCutoffDivergenceDensity period hPeriod
      massSquared field test parameter

theorem canonicalLatitudeCenteredMetricCutoffDivergenceDensity_eq_local
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (baseMap : Vector4 → CanonicalLatitudeBase)
    (hFree : localActualScalarGreenCoordinateDivergence period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test 0 = 0) :
    canonicalLatitudeCenteredMetricCutoffDivergenceDensity period hPeriod
        massSquared field test (base, normal) =
      canonicalPositiveLatitudeWeight normal *
        localActualCutoffScalarGreenCoordinateDivergence period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
          (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
            period hPeriod normal baseMap) 0 := by
  rw [canonicalLatitudeCenteredMetricCutoffDivergenceDensity,
    canonicalLatitudeCenteredGlobalCutoffDivergenceDensity_eq_local
      period hPeriod massSquared field test hField hTest base normal hNormal
        chart baseMap hFree]

/-- The metric-volume density of the recollated full local divergence is the
normal densitized divergence plus the weighted tangential compensation. -/
theorem canonicalLatitudeCenteredMetricCutoffDivergenceDensity_eq_metricDensitized_add_compensation
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1) :
    canonicalLatitudeCenteredMetricCutoffDivergenceDensity period hPeriod
        massSquared field test (base, normal) =
      canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
          massSquared field test (base, normal) +
        canonicalPositiveLatitudeWeight normal *
          canonicalCutBulkSmoothCutoffGreenMetricTangentialCompensation
            period hPeriod field test base normal := by
  rw [canonicalLatitudeCenteredMetricCutoffDivergenceDensity,
    canonicalLatitudeCenteredGlobalCutoffDivergenceDensity, if_pos hNormal]
  unfold P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceGluing4D.canonicalLatitudeCenteredGlobalCutoffDivergence
  rw [mul_add,
    canonicalPositiveLatitudeWeight_mul_metricNormalDivergence
      period hPeriod massSquared field test (base, normal)
        ⟨hNormal.1.le, hNormal.2.le⟩]

/-- Intrinsic positive-latitude metric-volume pushforward of the glued local
divergence.  The Jacobian is carried by the source measure itself. -/
def canonicalLatitudeCenteredIntrinsicMetricCutoffDivergenceMeasure
    (massSquared : Real) (field test : SmoothScalarField period hPeriod) :
    VectorMeasure (EffectiveQuotient period hPeriod) Real :=
  ((canonicalPositiveLatitudeJacobianMeasure.prod
      (volume.restrict (canonicalLatitudeTimeInterval period))).withDensityᵥ
    (fun parameter : (StandardEquatorialSphere × Real) × Real =>
      canonicalLatitudeCenteredGlobalCutoffDivergenceDensity period hPeriod
        massSquared field test
          (canonicalLatitudeMetricCollarReassociate parameter))).map
    (canonicalLatitudeCollarMap period hPeriod ∘
      canonicalLatitudeMetricCollarReassociate)

/-- Total positive-half-collar integral of the recollated local divergence
against the exact metric density. -/
def canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
    (massSquared : Real) (field test : SmoothScalarField period hPeriod) : Real :=
  ∫ base, (∫ normal in (0 : Real)..1,
      canonicalLatitudeCenteredMetricCutoffDivergenceDensity period hPeriod
        massSquared field test (base, normal))
    ∂canonicalLatitudeBaseMeasure period

/-- Exact residual condition: after integration over the closed tangential
base, the weighted compensation contributes no net bulk term. -/
def CanonicalLatitudeCenteredMetricTangentialCancellation
    (massSquared : Real) (field test : SmoothScalarField period hPeriod) : Prop :=
  canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
      massSquared field test =
    ∫ base, (∫ normal in (0 : Real)..1,
      canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test (base, normal))
      ∂canonicalLatitudeBaseMeasure period

/-- Once the now-isolated tangential cancellation is proved, the established
normal FTC gives the complete metric-volume Stokes formula immediately. -/
theorem two_mul_canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_neg_flux_of_tangentialCancellation
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hCancellation :
      CanonicalLatitudeCenteredMetricTangentialCancellation period hPeriod
        massSquared field test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
        massSquared field test =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) := by
  rw [hCancellation,
    productHalfCollarIntegral_metricDensitizedDivergence_eq_neg_throatFlux,
    canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test 0 (by norm_num)]
  ring

private theorem centeredMetricCutoffDivergenceDensity_zero_of_dirichletEuler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1) :
    canonicalLatitudeCenteredMetricCutoffDivergenceDensity period hPeriod
        massSquared field test (base, normal) = 0 := by
  rw [canonicalLatitudeCenteredMetricCutoffDivergenceDensity,
    canonicalLatitudeCenteredGlobalCutoffDivergenceDensity_eq_genuine_of_euler
      period hPeriod massSquared field test hField.euler hTest.euler,
    canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_cutoffDerivative_mul_flux_of_euler
      period hPeriod massSquared field test hField.euler hTest.euler
        (base, normal) ⟨hNormal.1.le, hNormal.2.le⟩,
    canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test base normal ⟨hNormal.1.le, hNormal.2.le⟩,
    canonicalLatitudeScalarGreenCurrent_zero_of_dirichletEuler
      period hPeriod massSquared field test hField hTest base normal]
  ring

private theorem metricDensitizedDivergence_zero_of_dirichletEuler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1) :
    canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence period hPeriod
        massSquared field test (base, normal) = 0 := by
  rw [canonicalCutBulkSmoothCutoffGreenMetricDensitizedDivergence_eq_weightedCutoffDerivative_mul_flux_of_euler
      period hPeriod massSquared field test hField.euler hTest.euler base normal
        hNormal,
    canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test base normal ⟨hNormal.1.le, hNormal.2.le⟩,
    canonicalLatitudeScalarGreenCurrent_zero_of_dirichletEuler
      period hPeriod massSquared field test hField hTest base normal]
  ring

/-- Homogeneous Dirichlet Euler data close the residual cancellation
unconditionally because their Green current vanishes on every latitude. -/
theorem canonicalLatitudeCenteredMetricTangentialCancellation_of_dirichletEuler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test) :
    CanonicalLatitudeCenteredMetricTangentialCancellation period hPeriod
      massSquared field test := by
  unfold CanonicalLatitudeCenteredMetricTangentialCancellation
    canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base => by
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le zero_le_one]
    filter_upwards [(volume : Measure Real).ae_ne (1 : Real)] with normal hNe hMem
    have hNormal : normal ∈ Ioo (0 : Real) 1 :=
      ⟨hMem.1, lt_of_le_of_ne hMem.2 hNe⟩
    rw [centeredMetricCutoffDivergenceDensity_zero_of_dirichletEuler
        period hPeriod massSquared field test hField hTest base normal hNormal,
      metricDensitizedDivergence_zero_of_dirichletEuler
        period hPeriod massSquared field test hField hTest base normal hNormal]

/-- Complete metric-volume Stokes for the already closed Dirichlet sector. -/
theorem two_mul_canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_neg_flux_of_dirichletEuler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
        massSquared field test =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) :=
  two_mul_canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_neg_flux_of_tangentialCancellation
    period hPeriod massSquared field test
      (canonicalLatitudeCenteredMetricTangentialCancellation_of_dirichletEuler
        period hPeriod massSquared field test hField hTest)

/-- Scalar coefficient left after using Euler conservation to freeze the
normal Green current along each latitude fiber. -/
def canonicalLatitudeCenteredMetricCutoffWeightIntegral : Real :=
  ∫ normal in (0 : Real)..1,
    canonicalPositiveLatitudeWeight normal *
      deriv canonicalLatitudeCollarCutoff normal

private theorem deriv_canonicalPositiveLatitudeWeight (normal : Real) :
    deriv canonicalPositiveLatitudeWeight normal =
      -2 * Real.cos normal * Real.sin normal := by
  change deriv (fun current : Real => Real.cos current ^ 2) normal = _
  have hFun : (fun current : Real => Real.cos current ^ 2) =
      Real.cos ^ (2 : Nat) := by
    rfl
  rw [hFun, deriv_pow (Real.differentiable_cos.differentiableAt) 2,
    Real.deriv_cos]
  ring

private theorem metricTangentialCutoffWeight_continuous :
    Continuous (fun normal : Real =>
      -(deriv canonicalPositiveLatitudeWeight normal *
        canonicalLatitudeCollarCutoff normal)) := by
  have hWeight : ContDiff Real ∞ canonicalPositiveLatitudeWeight := by
    unfold canonicalPositiveLatitudeWeight
    exact Real.contDiff_cos.pow 2
  exact (hWeight.continuous_deriv (by simp)).mul
    canonicalLatitudeCollarCutoff_contDiff.continuous |>.neg

/-- The cutoff/Jacobian coefficient is genuinely nondegenerate. -/
theorem canonicalLatitudeCenteredMetricCutoffWeightIntegral_add_one_pos :
    0 < canonicalLatitudeCenteredMetricCutoffWeightIntegral + 1 := by
  have hWeight : ∀ normal : Real,
      HasDerivAt canonicalPositiveLatitudeWeight
        (deriv canonicalPositiveLatitudeWeight normal) normal := fun normal =>
    ((show ContDiff Real ∞ canonicalPositiveLatitudeWeight by
      unfold canonicalPositiveLatitudeWeight
      exact Real.contDiff_cos.pow 2).differentiable
        (by simp)).differentiableAt.hasDerivAt
  have hCutoff : ∀ normal : Real,
      HasDerivAt canonicalLatitudeCollarCutoff
        (deriv canonicalLatitudeCollarCutoff normal) normal := fun normal =>
    (canonicalLatitudeCollarCutoff_contDiff.differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hIPP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : Real)) (b := 1)
    (u := canonicalPositiveLatitudeWeight)
    (v := canonicalLatitudeCollarCutoff)
    (u' := deriv canonicalPositiveLatitudeWeight)
    (v' := deriv canonicalLatitudeCollarCutoff)
    (fun normal _ => hWeight normal)
    (fun normal _ => hCutoff normal)
    (((show ContDiff Real ∞ canonicalPositiveLatitudeWeight by
      unfold canonicalPositiveLatitudeWeight
      exact Real.contDiff_cos.pow 2).continuous_deriv
        (by simp)).intervalIntegrable 0 1)
    ((canonicalLatitudeCollarCutoff_contDiff.continuous_deriv
      (by simp)).intervalIntegrable 0 1)
  have hIdentity :
      canonicalLatitudeCenteredMetricCutoffWeightIntegral + 1 =
        ∫ normal in (0 : Real)..1,
          -(deriv canonicalPositiveLatitudeWeight normal *
            canonicalLatitudeCollarCutoff normal) := by
    unfold canonicalLatitudeCenteredMetricCutoffWeightIntegral
    rw [hIPP,
      canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs 1 (by norm_num),
      canonicalLatitudeCollarCutoff_eq_one 0 (by norm_num)]
    simp [canonicalPositiveLatitudeWeight]
    ring
  rw [hIdentity]
  apply intervalIntegral.integral_pos zero_lt_one
  · exact metricTangentialCutoffWeight_continuous.continuousOn
  · intro normal hNormal
    rw [deriv_canonicalPositiveLatitudeWeight]
    have hCos : 0 < Real.cos normal := by
      apply Real.cos_pos_of_le_one
      rw [abs_of_nonneg hNormal.1.le]
      exact hNormal.2
    have hSin : 0 ≤ Real.sin normal :=
      Real.sin_nonneg_of_nonneg_of_le_pi hNormal.1.le
        (hNormal.2.trans (by linarith [Real.pi_gt_three]))
    have hCutoff : 0 ≤ canonicalLatitudeCollarCutoff normal :=
      canonicalLatitudeCollarCutoff.nonneg
    nlinarith [mul_nonneg (mul_nonneg hCos.le hSin) hCutoff]
  · refine ⟨1 / 2, by norm_num, ?_⟩
    rw [deriv_canonicalPositiveLatitudeWeight,
      canonicalLatitudeCollarCutoff_eq_one (1 / 2) (by norm_num)]
    have hCos : 0 < Real.cos (1 / 2) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hSin : 0 < Real.sin (1 / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by norm_num)
        (by linarith [Real.pi_gt_three])
    nlinarith [mul_pos hCos hSin]

theorem canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_weight_mul_measuredGreenCurrent_of_euler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
        massSquared field test =
      canonicalLatitudeCenteredMetricCutoffWeightIntegral *
        canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 := by
  unfold canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
    canonicalLatitudeMeasuredScalarGreenCurrent
  calc
    (∫ base, (∫ normal in (0 : Real)..1,
        canonicalLatitudeCenteredMetricCutoffDivergenceDensity period hPeriod
          massSquared field test (base, normal))
      ∂canonicalLatitudeBaseMeasure period) =
        ∫ base,
          canonicalLatitudeCenteredMetricCutoffWeightIntegral *
            canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0
          ∂canonicalLatitudeBaseMeasure period := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun base => by
        calc
          (∫ normal in (0 : Real)..1,
              canonicalLatitudeCenteredMetricCutoffDivergenceDensity
                period hPeriod massSquared field test (base, normal)) =
              ∫ normal in (0 : Real)..1,
                (canonicalPositiveLatitudeWeight normal *
                    deriv canonicalLatitudeCollarCutoff normal) *
                  canonicalLatitudeScalarGreenCurrent period hPeriod
                    field test base 0 := by
            apply intervalIntegral.integral_congr_ae
            rw [uIoc_of_le zero_le_one]
            filter_upwards [(volume : Measure Real).ae_ne (1 : Real)] with
              normal hNe hMem
            have hNormal : normal ∈ Ioo (0 : Real) 1 :=
              ⟨hMem.1, lt_of_le_of_ne hMem.2 hNe⟩
            rw [canonicalLatitudeCenteredMetricCutoffDivergenceDensity,
              canonicalLatitudeCenteredGlobalCutoffDivergenceDensity_eq_genuine_of_euler
                period hPeriod massSquared field test hField hTest,
              canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_cutoffDerivative_mul_flux_of_euler
                period hPeriod massSquared field test hField hTest (base, normal)
                  ⟨hNormal.1.le, hNormal.2.le⟩,
              canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
                period hPeriod field test base normal
                  ⟨hNormal.1.le, hNormal.2.le⟩,
              canonicalLatitudeScalarGreenCurrent_eq_of_euler period hPeriod
                massSquared field test hField hTest base normal 0]
            ring
          _ = canonicalLatitudeCenteredMetricCutoffWeightIntegral *
              canonicalLatitudeScalarGreenCurrent period hPeriod field test
                base 0 := by
            rw [canonicalLatitudeCenteredMetricCutoffWeightIntegral,
              intervalIntegral.integral_mul_const]
    _ = _ := by
      rw [integral_const_mul]

/-- A vanishing measured throat flux is sufficient for the general Euler
sector: both the full metric integral and the normal FTC integral then vanish. -/
theorem canonicalLatitudeCenteredMetricTangentialCancellation_of_euler_of_measuredGreenCurrent_zero
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (hFlux : canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod
      field test 0 = 0) :
    CanonicalLatitudeCenteredMetricTangentialCancellation period hPeriod
      massSquared field test := by
  unfold CanonicalLatitudeCenteredMetricTangentialCancellation
  rw [canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_weight_mul_measuredGreenCurrent_of_euler
      period hPeriod massSquared field test hField hTest,
    hFlux, mul_zero,
    productHalfCollarIntegral_metricDensitizedDivergence_eq_neg_throatFlux,
    hFlux, neg_zero]

theorem two_mul_canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_neg_flux_of_euler_of_measuredGreenCurrent_zero
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (hFlux : canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod
      field test 0 = 0) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
        massSquared field test =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) :=
  two_mul_canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_neg_flux_of_tangentialCancellation
    period hPeriod massSquared field test
      (canonicalLatitudeCenteredMetricTangentialCancellation_of_euler_of_measuredGreenCurrent_zero
        period hPeriod massSquared field test hField hTest hFlux)

/-- Exact algebraic form of the remaining general Euler obstruction. -/
theorem canonicalLatitudeCenteredMetricTangentialCancellation_iff_weight_add_one_mul_measuredGreenCurrent_eq_zero_of_euler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    CanonicalLatitudeCenteredMetricTangentialCancellation period hPeriod
        massSquared field test ↔
      (canonicalLatitudeCenteredMetricCutoffWeightIntegral + 1) *
        canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 = 0 := by
  unfold CanonicalLatitudeCenteredMetricTangentialCancellation
  rw [canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_weight_mul_measuredGreenCurrent_of_euler
      period hPeriod massSquared field test hField hTest,
    productHalfCollarIntegral_metricDensitizedDivergence_eq_neg_throatFlux]
  constructor
  · intro h
    calc
      (canonicalLatitudeCenteredMetricCutoffWeightIntegral + 1) *
          canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 =
        canonicalLatitudeCenteredMetricCutoffWeightIntegral *
            canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 +
          canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 := by ring
      _ = 0 := by rw [h]; ring
  · intro h
    calc
      canonicalLatitudeCenteredMetricCutoffWeightIntegral *
          canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 =
        (canonicalLatitudeCenteredMetricCutoffWeightIntegral + 1) *
            canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 -
          canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 := by ring
      _ = -canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 := by
        rw [h]
        ring

theorem canonicalLatitudeCenteredMetricTangentialCancellation_iff_measuredGreenCurrent_zero_of_euler
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    CanonicalLatitudeCenteredMetricTangentialCancellation period hPeriod
        massSquared field test ↔
      canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 = 0 := by
  rw [canonicalLatitudeCenteredMetricTangentialCancellation_iff_weight_add_one_mul_measuredGreenCurrent_eq_zero_of_euler
    period hPeriod massSquared field test hField hTest, mul_eq_zero]
  exact or_iff_right
    (ne_of_gt canonicalLatitudeCenteredMetricCutoffWeightIntegral_add_one_pos)

end
end P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
end JanusFormal
