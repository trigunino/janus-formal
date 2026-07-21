import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalH1FunctionQuotient4D

/-!
# Descent of the canonical H1 trace to the function quotient

The radial--polar collar estimate admits a scaled one-dimensional form.  It
separates the spacetime `L2` value from the bounded first-jet part.  On a
vertical graph limit the value term vanishes, while the first-jet term can be
multiplied by an arbitrary positive scale.  Hence the already constructed
physical trace vanishes on the vertical kernel and descends unconditionally
to the genuine function quotient.

This proves trace descent only.  It does not identify all vertical first jets
with zero and therefore does not claim injectivity of the graph projection.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalH1TraceFunctionQuotientDescent4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Filter Topology
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceFinalReduction4D
open P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D
open P0EFTJanusMappingTorusCanonicalH1FunctionQuotient4D

private abbrev sphereData (period : Real) (hPeriod : period ≠ 0) :=
  reflectedSphereData period hPeriod
private abbrev throatData (period : Real) (hPeriod : period ≠ 0) :=
  fixedEquatorData period hPeriod
private abbrev EffectiveQuotient (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (throatData period hPeriod)
private abbrev EffectiveCover (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorusCover (sphereData period hPeriod)

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance (period : Real) (hPeriod : period ≠ 0) :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance (period : Real) (hPeriod : period ≠ 0) :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

variable (period : Real) (hPeriod : period ≠ 0)

/-- Scaled one-dimensional trace inequality.  Unlike the fixed graph-norm
bound, it keeps the value and derivative energies separate. -/
theorem unitNormal_point_trace_sq_le_scaled
    (value derivative : Real → Real) (scale : Real)
    (hScale : 0 < scale)
    (hValue : ∀ coordinate, HasDerivAt value (derivative coordinate) coordinate)
    (hDerivative : Continuous derivative) :
    value 0 ^ 2 ≤
      (1 + scale⁻¹ ^ 2) *
          (∫ coordinate in (0 : Real)..1, value coordinate ^ 2) +
        scale ^ 2 *
          (∫ coordinate in (0 : Real)..1, derivative coordinate ^ 2) := by
  let product : Real → Real := fun coordinate =>
    (1 - coordinate) * value coordinate ^ 2
  let productDerivative : Real → Real := fun coordinate =>
    -(value coordinate ^ 2) +
      2 * (1 - coordinate) * value coordinate * derivative coordinate
  let squareValue : Real → Real := fun coordinate => value coordinate ^ 2
  let cross : Real → Real := fun coordinate =>
    2 * (1 - coordinate) * value coordinate * derivative coordinate
  have hValueContinuous : Continuous value :=
    continuous_iff_continuousAt.2 fun coordinate =>
      (hValue coordinate).continuousAt
  have hProductDerivativeContinuous : Continuous productDerivative := by
    dsimp [productDerivative]
    fun_prop
  have hProductDerivative : ∀ coordinate,
      HasDerivAt product (productDerivative coordinate) coordinate := by
    intro coordinate
    dsimp [product, productDerivative]
    have hRaw :=
      ((hasDerivAt_const coordinate 1).sub (hasDerivAt_id coordinate)).mul
        ((hValue coordinate).pow 2)
    convert! hRaw using 1
    simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  have hFTC :
      (∫ coordinate in (0 : Real)..1, productDerivative coordinate) =
        -(value 0 ^ 2) := by
    have hIntegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : Real)) (b := 1)
      (fun coordinate _ => hProductDerivative coordinate)
      (hProductDerivativeContinuous.intervalIntegrable 0 1)
    simpa [product] using hIntegral
  have hSquareValueContinuous : Continuous squareValue := by
    dsimp [squareValue]
    fun_prop
  have hCrossContinuous : Continuous cross := by
    dsimp [cross]
    fun_prop
  have hIdentity :
      value 0 ^ 2 =
        (∫ coordinate in (0 : Real)..1, squareValue coordinate) -
          ∫ coordinate in (0 : Real)..1, cross coordinate := by
    have hRewritten := hFTC
    change
      (∫ coordinate in (0 : Real)..1,
        -squareValue coordinate + cross coordinate) = -(value 0 ^ 2)
      at hRewritten
    rw [intervalIntegral.integral_add
        (hSquareValueContinuous.neg.intervalIntegrable 0 1)
        (hCrossContinuous.intervalIntegrable 0 1),
      intervalIntegral.integral_neg] at hRewritten
    linarith
  have hScaleNe : scale ≠ 0 := ne_of_gt hScale
  have hPointwise : ∀ coordinate ∈ Set.Icc (0 : Real) 1,
      -cross coordinate ≤
        scale⁻¹ ^ 2 * squareValue coordinate +
          scale ^ 2 * derivative coordinate ^ 2 := by
    intro coordinate hCoordinate
    have hWeightNonnegative : 0 ≤ 1 - coordinate :=
      sub_nonneg.mpr hCoordinate.2
    have hWeightLeOne : 1 - coordinate ≤ 1 := by
      linarith [hCoordinate.1]
    have hWeightSquare : (1 - coordinate) ^ 2 ≤ 1 := by
      nlinarith
    have hYoung := two_mul_le_add_sq
      (-value coordinate / scale)
      (scale * (1 - coordinate) * derivative coordinate)
    have hFactorNonnegative :
        0 ≤ scale ^ 2 * derivative coordinate ^ 2 :=
      mul_nonneg (sq_nonneg scale) (sq_nonneg (derivative coordinate))
    have hWeightedDerivative :
        (scale * (1 - coordinate) * derivative coordinate) ^ 2 ≤
          (scale * derivative coordinate) ^ 2 := by
      calc
        (scale * (1 - coordinate) * derivative coordinate) ^ 2 =
            (scale ^ 2 * derivative coordinate ^ 2) *
              (1 - coordinate) ^ 2 := by ring
        _ ≤ (scale ^ 2 * derivative coordinate ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hWeightSquare hFactorNonnegative
        _ = (scale * derivative coordinate) ^ 2 := by ring
    calc
      -cross coordinate =
          2 * (-value coordinate / scale) *
            (scale * (1 - coordinate) * derivative coordinate) := by
        dsimp [cross]
        field_simp [hScaleNe]
      _ ≤ (-value coordinate / scale) ^ 2 +
          (scale * (1 - coordinate) * derivative coordinate) ^ 2 := hYoung
      _ ≤ (-value coordinate / scale) ^ 2 +
          (scale * derivative coordinate) ^ 2 :=
        add_le_add_right hWeightedDerivative _
      _ = scale⁻¹ ^ 2 * squareValue coordinate +
          scale ^ 2 * derivative coordinate ^ 2 := by
        dsimp [squareValue]
        field_simp [hScaleNe]
  have hScaledContinuous : Continuous (fun coordinate =>
      scale⁻¹ ^ 2 * squareValue coordinate +
        scale ^ 2 * derivative coordinate ^ 2) :=
    (hSquareValueContinuous.const_mul (scale⁻¹ ^ 2)).add
      ((hDerivative.pow 2).const_mul (scale ^ 2))
  have hNegativeCross :
      (∫ coordinate in (0 : Real)..1, -cross coordinate) ≤
        ∫ coordinate in (0 : Real)..1,
          scale⁻¹ ^ 2 * squareValue coordinate +
            scale ^ 2 * derivative coordinate ^ 2 := by
    exact intervalIntegral.integral_mono_on (a := (0 : Real)) (b := 1)
      (by norm_num)
      (hCrossContinuous.neg.intervalIntegrable 0 1)
      (hScaledContinuous.intervalIntegrable 0 1)
      hPointwise
  rw [hIdentity, sub_eq_add_neg, ← intervalIntegral.integral_neg]
  calc
    (∫ coordinate in (0 : Real)..1, squareValue coordinate) +
          ∫ coordinate in (0 : Real)..1, -cross coordinate ≤
        (∫ coordinate in (0 : Real)..1, squareValue coordinate) +
          ∫ coordinate in (0 : Real)..1,
            scale⁻¹ ^ 2 * squareValue coordinate +
              scale ^ 2 * derivative coordinate ^ 2 :=
      add_le_add_right hNegativeCross _
    _ = (1 + scale⁻¹ ^ 2) *
          (∫ coordinate in (0 : Real)..1, value coordinate ^ 2) +
        scale ^ 2 *
          (∫ coordinate in (0 : Real)..1, derivative coordinate ^ 2) := by
      rw [intervalIntegral.integral_add
          (hSquareValueContinuous.const_mul
            (scale⁻¹ ^ 2) |>.intervalIntegrable 0 1)
          (hDerivative.pow 2 |>.const_mul
            (scale ^ 2) |>.intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      dsimp [squareValue]
      ring

private def canonicalLatitudeValueEnergy
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  ∫ normal in (0 : Real)..1,
    canonicalLatitudeValue period hPeriod field base normal ^ 2

private def canonicalLatitudeDerivativeEnergy
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  ∫ normal in (0 : Real)..1,
    canonicalLatitudeDerivative period hPeriod field base normal ^ 2

private theorem canonicalLatitudeValueEnergy_continuous
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (canonicalLatitudeValueEnergy period hPeriod field) := by
  unfold canonicalLatitudeValueEnergy
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (canonicalLatitudeValue_uncurry_continuous
    period hPeriod field).pow 2

private theorem canonicalLatitudeDerivativeEnergy_continuous
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (canonicalLatitudeDerivativeEnergy period hPeriod field) := by
  unfold canonicalLatitudeDerivativeEnergy
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (canonicalLatitudeDerivative_uncurry_continuous_of_normalLift
    period hPeriod
    (canonicalLatitudeNormalLift_continuous period hPeriod) field).pow 2

private theorem canonicalLatitudeValueEnergy_integrable
    (field : SmoothQuotientField period hPeriod Real) :
    Integrable (canonicalLatitudeValueEnergy period hPeriod field)
      (canonicalLatitudeBaseMeasure period) :=
  continuous_integrable_canonicalLatitudeBaseMeasure period _
    (canonicalLatitudeValueEnergy_continuous period hPeriod field)

private theorem canonicalLatitudeDerivativeEnergy_integrable
    (field : SmoothQuotientField period hPeriod Real) :
    Integrable (canonicalLatitudeDerivativeEnergy period hPeriod field)
      (canonicalLatitudeBaseMeasure period) :=
  continuous_integrable_canonicalLatitudeBaseMeasure period _
    (canonicalLatitudeDerivativeEnergy_continuous period hPeriod field)

private def radialPolarFrameEnergyComparison :
    CanonicalLatitudeFrameEnergyComparison period hPeriod :=
  canonicalLatitudeFrameEnergyComparisonOfWeightedMapFormula period hPeriod
    canonicalPositiveLatitudeWeightedMapFormula_radialPolar

private theorem smoothCanonicalPhysicalScalarL2_norm_sq_eq_integral
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothCanonicalPhysicalScalarL2 period hPeriod field‖ ^ 2 =
      ∫ point : EffectiveQuotient period hPeriod,
        field point ^ 2
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  let mu := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let value := smoothCanonicalPhysicalScalarL2 period hPeriod field
  have hValueAe :
      (value : EffectiveQuotient period hPeriod → Real) =ᵐ[mu]
        field.toFun := by
    change
      (smoothFieldToL2 period hPeriod Real mu field :
        EffectiveQuotient period hPeriod → Real) =ᵐ[mu] field.toFun
    exact smoothFieldToL2_ae period hPeriod Real mu field
  calc
    ‖smoothCanonicalPhysicalScalarL2 period hPeriod field‖ ^ 2 =
        inner Real value value := by
      exact (real_inner_self_eq_norm_sq value).symm
    _ = ∫ point, inner Real (value point) (value point) ∂mu :=
      L2.inner_def value value
    _ = ∫ point : EffectiveQuotient period hPeriod,
        field point ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards [hValueAe] with point hPoint
      rw [hPoint]
      simp [pow_two]

private theorem canonicalLatitudeValueEnergy_integral_le_L2
    (field : SmoothQuotientField period hPeriod Real) :
    (∫ base : CanonicalLatitudeBase,
        canonicalLatitudeValueEnergy period hPeriod field base
        ∂(canonicalLatitudeBaseMeasure period)) ≤
      (canonicalLatitudeCoareaMeasureConstant : Real) *
        ‖smoothCanonicalPhysicalScalarL2 period hPeriod field‖ ^ 2 := by
  let coarea : CanonicalLatitudeMeasureToSphereCoareaDomination
      period hPeriod :=
    canonicalLatitudeMeasureToSphereCoareaDomination_of_positiveLatitude
      period hPeriod canonicalPositiveLatitudeMeasureDomination_radialPolar
  have hCoarea :=
    canonicalLatitudeCollar_integral_le_of_measureToSphereCoarea
      period hPeriod coarea (fun point => field point ^ 2)
      (field.contMDiff_toFun.continuous.pow 2)
      (fun point => sq_nonneg (field point))
  rw [smoothCanonicalPhysicalScalarL2_norm_sq_eq_integral
    period hPeriod field]
  simpa [canonicalLatitudeValueEnergy, canonicalLatitudeValue,
    canonicalNormalSlice, canonicalLatitudeCollarMap] using hCoarea

private theorem canonicalLatitudeDerivativeEnergy_integral_le_graph
    (field : SmoothQuotientField period hPeriod Real) :
    (∫ base : CanonicalLatitudeBase,
        canonicalLatitudeDerivativeEnergy period hPeriod field base
        ∂(canonicalLatitudeBaseMeasure period)) ≤
      (radialPolarFrameEnergyComparison period hPeriod).constant ^ 2 *
        ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
  let comparison := radialPolarFrameEnergyComparison period hPeriod
  have hPointwise : ∀ base : CanonicalLatitudeBase,
      canonicalLatitudeDerivativeEnergy period hPeriod field base ≤
        unitNormalH1Energy
          (canonicalLatitudeValue period hPeriod field base)
          (canonicalLatitudeDerivative period hPeriod field base) := by
    intro base
    unfold canonicalLatitudeDerivativeEnergy unitNormalH1Energy
    apply intervalIntegral.integral_mono_on (a := (0 : Real)) (b := 1)
      (by norm_num)
    · exact (canonicalLatitudeDerivative_continuous
        period hPeriod field base).pow 2 |>.intervalIntegrable 0 1
    · exact (((canonicalNormalSlice_contDiff period hPeriod field
          (canonicalLatitudeAnchor period hPeriod base)).continuous.pow 2).const_mul 2 |>.add
        ((canonicalLatitudeDerivative_continuous
          period hPeriod field base).pow 2)).intervalIntegrable 0 1
    · intro normal _
      exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg _))
  exact (integral_mono
      (canonicalLatitudeDerivativeEnergy_integrable period hPeriod field)
      (comparison.normalEnergyIntegrable field)
      hPointwise).trans
    (comparison.collarEnergy_le_graph field)

/-- Interpolated physical trace bound on the smooth core. -/
theorem smoothCanonicalPhysicalTrace_interpolated_bound
    (field : SmoothQuotientField period hPeriod Real)
    (scale : Real) (hScale : 0 < scale) :
    ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 ≤
      ((1 + scale⁻¹ ^ 2) *
          (canonicalLatitudeCoareaMeasureConstant : Real)) *
          ‖smoothCanonicalPhysicalScalarL2 period hPeriod field‖ ^ 2 +
        (scale ^ 2 *
          (radialPolarFrameEnergyComparison period hPeriod).constant ^ 2) *
          ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
  have hPointwise : ∀ base : CanonicalLatitudeBase,
      canonicalLatitudeValue period hPeriod field base 0 ^ 2 ≤
        (1 + scale⁻¹ ^ 2) *
            canonicalLatitudeValueEnergy period hPeriod field base +
          scale ^ 2 *
            canonicalLatitudeDerivativeEnergy period hPeriod field base :=
    fun base => unitNormal_point_trace_sq_le_scaled
      (canonicalLatitudeValue period hPeriod field base)
      (canonicalLatitudeDerivative period hPeriod field base)
      scale hScale
      (canonicalLatitudeValue_hasDerivAt period hPeriod field base)
      (canonicalLatitudeDerivative_continuous period hPeriod field base)
  have hRightIntegrable : Integrable (fun base : CanonicalLatitudeBase =>
      (1 + scale⁻¹ ^ 2) *
          canonicalLatitudeValueEnergy period hPeriod field base +
        scale ^ 2 *
          canonicalLatitudeDerivativeEnergy period hPeriod field base)
      (canonicalLatitudeBaseMeasure period) :=
    ((canonicalLatitudeValueEnergy_integrable period hPeriod field).const_mul _).add
      ((canonicalLatitudeDerivativeEnergy_integrable
        period hPeriod field).const_mul _)
  rw [smoothCanonicalPhysicalTrace_norm_sq_eq_latitudeIntegral]
  calc
    (∫ base : CanonicalLatitudeBase,
        canonicalLatitudeValue period hPeriod field base 0 ^ 2
        ∂(canonicalLatitudeBaseMeasure period)) ≤
        ∫ base : CanonicalLatitudeBase,
          ((1 + scale⁻¹ ^ 2) *
              canonicalLatitudeValueEnergy period hPeriod field base +
            scale ^ 2 *
              canonicalLatitudeDerivativeEnergy period hPeriod field base)
          ∂(canonicalLatitudeBaseMeasure period) :=
      integral_mono
        (canonicalLatitudeTraceSquare_integrable period hPeriod field)
        hRightIntegrable hPointwise
    _ = (1 + scale⁻¹ ^ 2) *
          (∫ base : CanonicalLatitudeBase,
            canonicalLatitudeValueEnergy period hPeriod field base
            ∂(canonicalLatitudeBaseMeasure period)) +
        scale ^ 2 *
          (∫ base : CanonicalLatitudeBase,
            canonicalLatitudeDerivativeEnergy period hPeriod field base
            ∂(canonicalLatitudeBaseMeasure period)) := by
      rw [integral_add,
        integral_const_mul, integral_const_mul]
      · exact (canonicalLatitudeValueEnergy_integrable
          period hPeriod field).const_mul _
      · exact (canonicalLatitudeDerivativeEnergy_integrable
          period hPeriod field).const_mul _
    _ ≤ (1 + scale⁻¹ ^ 2) *
          ((canonicalLatitudeCoareaMeasureConstant : Real) *
            ‖smoothCanonicalPhysicalScalarL2 period hPeriod field‖ ^ 2) +
        scale ^ 2 *
          ((radialPolarFrameEnergyComparison period hPeriod).constant ^ 2 *
            ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (canonicalLatitudeValueEnergy_integral_le_L2
            period hPeriod field)
          (add_nonneg (by norm_num) (sq_nonneg scale⁻¹))
      · exact mul_le_mul_of_nonneg_left
          (canonicalLatitudeDerivativeEnergy_integral_le_graph
            period hPeriod field)
          (sq_nonneg scale)
    _ = ((1 + scale⁻¹ ^ 2) *
          (canonicalLatitudeCoareaMeasureConstant : Real)) *
          ‖smoothCanonicalPhysicalScalarL2 period hPeriod field‖ ^ 2 +
        (scale ^ 2 *
          (radialPolarFrameEnergyComparison period hPeriod).constant ^ 2) *
          ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
      ring

theorem canonicalPhysicalH1ToL2_agrees_on_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalH1ToL2 period hPeriod
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothCanonicalPhysicalScalarL2 period hPeriod field := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact h1GraphToL2_agrees_on_smooth period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field

/-- The scaled estimate extends from the dense smooth core to every element of
the completed first-jet graph. -/
theorem canonicalPhysicalH1TraceRadialPolar_interpolated_bound
    (scale : Real) (hScale : 0 < scale)
    (field : CanonicalPhysicalScalarH1 period hPeriod) :
    ‖canonicalPhysicalH1TraceRadialPolar period hPeriod field‖ ^ 2 ≤
      ((1 + scale⁻¹ ^ 2) *
          (canonicalLatitudeCoareaMeasureConstant : Real)) *
          ‖canonicalPhysicalH1ToL2 period hPeriod field‖ ^ 2 +
        (scale ^ 2 *
          (radialPolarFrameEnergyComparison period hPeriod).constant ^ 2) *
          ‖field‖ ^ 2 := by
  refine (smoothToCanonicalPhysicalScalarH1_denseRange
    period hPeriod).induction_on field ?_ ?_
  · exact isClosed_le
      ((canonicalPhysicalH1TraceRadialPolar
        period hPeriod).continuous.norm.pow 2)
      (((canonicalPhysicalH1ToL2 period hPeriod).continuous.norm.pow 2).const_mul
          ((1 + scale⁻¹ ^ 2) *
            (canonicalLatitudeCoareaMeasureConstant : Real)) |>.add
        ((continuous_norm.pow 2).const_mul
          (scale ^ 2 *
            (radialPolarFrameEnergyComparison period hPeriod).constant ^ 2)))
  · intro smoothField
    rw [canonicalPhysicalH1TraceRadialPolar_agrees_on_smooth,
      canonicalPhysicalH1ToL2_agrees_on_smooth]
    exact smoothCanonicalPhysicalTrace_interpolated_bound
      period hPeriod smoothField scale hScale

/-- Every vertical graph limit has zero physical trace. -/
theorem canonicalPhysicalH1ToL2_ker_le_trace_ker :
    (canonicalPhysicalH1ToL2 period hPeriod).ker ≤
      (canonicalPhysicalH1TraceRadialPolar period hPeriod).ker := by
  intro field hField
  change canonicalPhysicalH1ToL2 period hPeriod field = 0 at hField
  change canonicalPhysicalH1TraceRadialPolar period hPeriod field = 0
  apply norm_eq_zero.mp
  have hLimit : Tendsto (fun n : Nat =>
      ((1 / ((n : Real) + 1)) ^ 2 *
        (radialPolarFrameEnergyComparison period hPeriod).constant ^ 2) *
          ‖field‖ ^ 2) atTop (𝓝 0) := by
    have hScaleLimit : Tendsto (fun n : Nat =>
        (1 / ((n : Real) + 1))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using
      ((hScaleLimit.pow 2).mul_const
        ((radialPolarFrameEnergyComparison
          period hPeriod).constant ^ 2) |>.mul_const (‖field‖ ^ 2))
  have hNonpositive :
      ‖canonicalPhysicalH1TraceRadialPolar period hPeriod field‖ ^ 2 ≤ 0 :=
    ge_of_tendsto hLimit (Filter.Eventually.of_forall fun n => by
      have hDenominator : 0 < (n : Real) + 1 :=
        add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
      have hBound :=
        canonicalPhysicalH1TraceRadialPolar_interpolated_bound
          period hPeriod (1 / ((n : Real) + 1))
            (one_div_pos.mpr hDenominator) field
      simpa only [hField, norm_zero, pow_two, zero_mul, mul_zero, zero_add]
        using hBound)
  nlinarith [norm_nonneg
    (canonicalPhysicalH1TraceRadialPolar period hPeriod field)]

/-- The exact formerly conditional quotient-trace hypothesis is now proved
from the radial--polar collar geometry. -/
theorem canonicalH1TraceDescendsToFunctionQuotient_radialPolar :
    CanonicalH1TraceDescendsToFunctionQuotient period hPeriod :=
  canonicalPhysicalH1ToL2_ker_le_trace_ker period hPeriod

end

end P0EFTJanusMappingTorusCanonicalH1TraceFunctionQuotientDescent4D
end JanusFormal
