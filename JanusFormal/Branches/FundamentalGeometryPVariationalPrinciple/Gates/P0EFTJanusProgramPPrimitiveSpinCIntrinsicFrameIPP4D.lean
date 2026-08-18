import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusInvariantMeasureFlowIPP4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameCoordinateDerivatives4D

/-!
# Integration by parts for the intrinsic SpinC frame

The canonical throat measure is invariant under quotient time translation and
all three round-sphere rotations.  The intrinsic Dirac frame is the
variable-coefficient combination of those four generators proved previously.
Differentiating the coefficients gives the exact divergence defect `-2 nᵢ`.

This file combines these facts into a genuine integration-by-parts identity
for arbitrary smooth vector-valued throat fields:

`∫ eᵢ(f) = -∫ div(eᵢ) • f = -∫ (-2 nᵢ) • f`.

The proof differentiates invariant integrals; no boundary condition, Stokes
contract, spectral assumption or D10 direction is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameIPP4D

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section

open Filter Set Topology
open scoped Manifold ContDiff BigOperators InnerProductSpace
open MeasureTheory
open P0EFTJanusInvariantMeasureFlowIPP4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameDecomposition4D
open P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameCoordinateDerivatives4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatBaseCompactSpace : CompactSpace (ThroatBase period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance throatBaseMeasurableSpace :
    MeasurableSpace (ThroatBase period hPeriod) := borel _

local instance throatBaseBorelSpace : BorelSpace (ThroatBase period hPeriod) where
  measurable_eq := rfl

local instance canonicalThroatFiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private def d9TimeGeneratorIndex :
    Fin (canonicalDivergenceFreeLLFrame period hPeriod).count := by
  simpa [canonicalDivergenceFreeLLFrame] using (Fin.last 3)

private def d9RotationGeneratorIndex (axis : Fin 3) :
    Fin (canonicalDivergenceFreeLLFrame period hPeriod).count := by
  simpa [canonicalDivergenceFreeLLFrame] using (Fin.castSucc axis)

/-! ## Smooth derivative fields for the invariant generators -/

/-- Smooth derivative along quotient time translation. -/
def d9TimeGeneratorDerivativeField
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber) :
    SmoothThroatField period hPeriod Fiber where
  toFun base :=
    throatFrameDerivative period hPeriod Fiber
      (canonicalDivergenceFreeLLFrame period hPeriod) field base
        (d9TimeGeneratorIndex period hPeriod)
  contMDiff_toFun := by
    have hDerivative :=
      throatFrameDerivative_contMDiff period hPeriod Fiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field
    rw [contMDiff_pi_space] at hDerivative
    exact hDerivative (d9TimeGeneratorIndex period hPeriod)

/-- Smooth derivative along one quotient rotation generator. -/
def d9RotationGeneratorDerivativeField
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (axis : Fin 3) (field : SmoothThroatField period hPeriod Fiber) :
    SmoothThroatField period hPeriod Fiber where
  toFun base :=
    throatFrameDerivative period hPeriod Fiber
      (canonicalDivergenceFreeLLFrame period hPeriod) field base
        (d9RotationGeneratorIndex period hPeriod axis)
  contMDiff_toFun := by
    have hDerivative :=
      throatFrameDerivative_contMDiff period hPeriod Fiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field
    rw [contMDiff_pi_space] at hDerivative
    exact hDerivative (d9RotationGeneratorIndex period hPeriod axis)

@[simp]
theorem d9TimeGeneratorDerivativeField_apply
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (base : ThroatBase period hPeriod) :
    d9TimeGeneratorDerivativeField period hPeriod field base =
      mvfderiv throatCoverModelWithCorners field.toFun base
        (throatTimeTranslationGhost period hPeriod base) := by
  have hVector :
      (canonicalDivergenceFreeLLFrame period hPeriod).vectorAt base
      (d9TimeGeneratorIndex period hPeriod) =
        throatTimeTranslationGhost period hPeriod base := by
    rfl
  change throatFrameDerivative period hPeriod Fiber
    (canonicalDivergenceFreeLLFrame period hPeriod) field base
      (d9TimeGeneratorIndex period hPeriod) = _
  rw [throatFrameDerivative_eq_mvfderiv, hVector]

@[simp]
theorem d9RotationGeneratorDerivativeField_apply
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (axis : Fin 3) (field : SmoothThroatField period hPeriod Fiber)
    (base : ThroatBase period hPeriod) :
    d9RotationGeneratorDerivativeField period hPeriod axis field base =
      mvfderiv throatCoverModelWithCorners field.toFun base
        (throatSpatialRotationGhost period hPeriod axis base) := by
  change throatFrameDerivative period hPeriod Fiber
    (canonicalDivergenceFreeLLFrame period hPeriod) field base
      (d9RotationGeneratorIndex period hPeriod axis) = _
  rw [throatFrameDerivative_eq_mvfderiv]
  simp [d9RotationGeneratorIndex, canonicalDivergenceFreeLLFrame]

/-- Smooth radial-coordinate coefficient. -/
def d9BaseUnitRadialCoordinateField
    (direction : Fin 3) : SmoothThroatField period hPeriod Real where
  toFun := d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction
  contMDiff_toFun :=
    d9PrimitiveMonopoleBaseCoordinate_contMDiff period hPeriod direction

/-- Smooth rotational coefficient `(n × eᵢ)ₐ`. -/
def d9IntrinsicRotationCoefficientField
    (direction axis : Fin 3) : SmoothThroatField period hPeriod Real where
  toFun := d9IntrinsicRotationCoefficient period hPeriod direction axis
  contMDiff_toFun := by
    fin_cases direction <;> fin_cases axis <;>
      first
      | exact contMDiff_const
      | exact d9PrimitiveMonopoleBaseCoordinate_contMDiff period hPeriod 0
      | exact d9PrimitiveMonopoleBaseCoordinate_contMDiff period hPeriod 1
      | exact d9PrimitiveMonopoleBaseCoordinate_contMDiff period hPeriod 2
      | exact (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod 0).neg
      | exact (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod 1).neg
      | exact (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod 2).neg

/-! ## Curve derivatives for arbitrary smooth fields -/

private def d9TimeFlowCurve
    (base : ThroatBase period hPeriod) (parameter : Real) :
    ThroatBase period hPeriod :=
  throatTimeFlow period hPeriod parameter base

private theorem d9TimeFlowCurve_contMDiff
    (base : ThroatBase period hPeriod) :
    ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ∞
      (d9TimeFlowCurve period hPeriod base) := by
  have hBase : ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ∞
      (fun _ : Real => base) := contMDiff_const
  exact (((throatJointTimeFlow_contMDiff period hPeriod).of_le (by simp)).comp
    (contMDiff_id.prodMk hBase)).congr (fun _ => rfl)

private theorem d9SmoothThroatField_curve_hasDerivAt_zero
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [ContinuousSMul Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (curve : Real → ThroatBase period hPeriod)
    (hCurve : ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ∞ curve) :
    HasDerivAt (fun parameter => field (curve parameter))
      (mvfderiv throatCoverModelWithCorners field.toFun (curve 0)
        (mfderiv 𝓘(Real, Real) throatCoverModelWithCorners curve 0 1)) 0 := by
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      throatCoverModelWithCorners curve 0 :=
    hCurve.mdifferentiableAt (by simp)
  have hFieldAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, Fiber) field.toFun (curve 0) :=
    field.contMDiff_toFun.mdifferentiableAt (by simp)
  have hComp := HasMFDerivAt.comp 0
    hFieldAt.hasMFDerivAt hCurveAt.hasMFDerivAt
  have hCompF : HasFDerivAt (field.toFun ∘ curve)
      ((mfderiv throatCoverModelWithCorners 𝓘(Real, Fiber)
        field.toFun (curve 0)).comp
          (mfderiv 𝓘(Real, Real) throatCoverModelWithCorners curve 0)) 0 :=
    hComp.hasFDerivAt
  have hDeriv : HasDerivAt (field.toFun ∘ curve)
      (((mfderiv throatCoverModelWithCorners 𝓘(Real, Fiber)
        field.toFun (curve 0)).comp
          (mfderiv 𝓘(Real, Real) throatCoverModelWithCorners curve 0)) 1) 0 :=
    hasFDerivAt_iff_hasDerivAt.mp hCompF
  change HasDerivAt (field.toFun ∘ curve) _ 0
  convert hDeriv using 1
  simp only [ContinuousLinearMap.comp_apply]
  rfl

private theorem smoothThroatField_timeFlow_hasDerivAt_zero
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (base : ThroatBase period hPeriod) :
    HasDerivAt
      (fun parameter => field (throatTimeFlow period hPeriod parameter base))
      (d9TimeGeneratorDerivativeField period hPeriod field base) 0 := by
  have h := d9SmoothThroatField_curve_hasDerivAt_zero
    period hPeriod field (d9TimeFlowCurve period hPeriod base)
      (d9TimeFlowCurve_contMDiff period hPeriod base)
  have hCurveZero : d9TimeFlowCurve period hPeriod base 0 = base := by
    simp [d9TimeFlowCurve, throatTimeFlow_zero]
  rw [hCurveZero] at h
  change HasDerivAt
    (fun parameter => field (d9TimeFlowCurve period hPeriod base parameter)) _ 0
  convert h using 1
  rw [d9TimeGeneratorDerivativeField_apply]
  apply congrArg (mvfderiv throatCoverModelWithCorners field.toFun base)
  change throatTimeTranslationVelocity period hPeriod base = _
  rw [throatTimeTranslationVelocity_eq_curve_mfderiv]
  rfl

private theorem smoothThroatField_timeFlow_hasDerivAt
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (parameter : Real) (base : ThroatBase period hPeriod) :
    HasDerivAt
      (fun t => field (throatTimeFlow period hPeriod t base))
      (d9TimeGeneratorDerivativeField period hPeriod field
        (throatTimeFlow period hPeriod parameter base)) parameter := by
  have hZero := smoothThroatField_timeFlow_hasDerivAt_zero period hPeriod field
    (throatTimeFlow period hPeriod parameter base)
  have hShift : HasDerivAt (fun t : Real => t - parameter) 1 parameter :=
    (hasDerivAt_id parameter).sub_const parameter
  have hComp := hZero.scomp_of_eq parameter hShift (by simp)
  have hResult : HasDerivAt
      (fun t => field (throatTimeFlow period hPeriod t base))
      ((1 : Real) • d9TimeGeneratorDerivativeField period hPeriod field
        (throatTimeFlow period hPeriod parameter base)) parameter := by
    apply hComp.congr_of_eventuallyEq
    filter_upwards with t
    simp only [Function.comp_apply]
    rw [← throatTimeFlow_add]
    congr 2
    ring
  simpa only [one_smul] using hResult

private theorem smoothThroatField_rotationFlow_hasDerivAt
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (axis : Fin 3) (field : SmoothThroatField period hPeriod Fiber)
    (parameter : Real) (base : ThroatBase period hPeriod) :
    HasDerivAt
      (fun t => field
        (throatSpatialRotationFlow period hPeriod axis t base))
      (d9RotationGeneratorDerivativeField period hPeriod axis field
        (throatSpatialRotationFlow period hPeriod axis parameter base))
      parameter := by
  have hZero := smoothThroatField_spatialRotation_hasDerivAt_zero
    period hPeriod field axis
      (throatSpatialRotationFlow period hPeriod axis parameter base)
  rw [← d9RotationGeneratorDerivativeField_apply] at hZero
  have hShift : HasDerivAt (fun t : Real => t - parameter) 1 parameter :=
    (hasDerivAt_id parameter).sub_const parameter
  have hComp := hZero.scomp_of_eq parameter hShift (by simp)
  have hResult : HasDerivAt
      (fun t => field
        (throatSpatialRotationFlow period hPeriod axis t base))
      ((1 : Real) • d9RotationGeneratorDerivativeField period hPeriod axis field
        (throatSpatialRotationFlow period hPeriod axis parameter base))
      parameter := by
    apply hComp.congr_of_eventuallyEq
    filter_upwards with t
    simp only [Function.comp_apply]
    rw [← throatSpatialRotationFlow_add]
    congr 2
    ring
  simpa only [one_smul] using hResult

private def d9TimeFlowHomeomorph
    (shift : Real) : ThroatBase period hPeriod ≃ₜ ThroatBase period hPeriod where
  toFun := throatTimeFlow period hPeriod shift
  invFun := throatTimeFlow period hPeriod (-shift)
  left_inv base := by rw [← throatTimeFlow_add]; simp
  right_inv base := by rw [← throatTimeFlow_add]; simp
  continuous_toFun := (throatTimeFlow_contMDiff period hPeriod shift).continuous
  continuous_invFun :=
    (throatTimeFlow_contMDiff period hPeriod (-shift)).continuous

private theorem d9TimeFlow_measurableEmbedding (shift : Real) :
    MeasurableEmbedding (throatTimeFlow period hPeriod shift) :=
  (d9TimeFlowHomeomorph period hPeriod shift).measurableEmbedding

/-! ## Variable-coefficient IPP for invariant generators -/

/-- Integration by parts for a variable coefficient times the quotient-time
derivative. -/
theorem d9TimeGenerator_integral_smul_derivative_eq_neg
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [SecondCountableTopology Fiber]
    (coefficient : SmoothThroatField period hPeriod Real)
    (field : SmoothThroatField period hPeriod Fiber) :
    (∫ base,
      coefficient base • d9TimeGeneratorDerivativeField period hPeriod field base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      -∫ base,
        d9TimeGeneratorDerivativeField period hPeriod coefficient base •
          field base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let F : Real → ThroatBase period hPeriod → Fiber := fun parameter base =>
    coefficient (throatTimeFlow period hPeriod parameter base) •
      field (throatTimeFlow period hPeriod parameter base)
  let F' : Real → ThroatBase period hPeriod → Fiber := fun parameter base =>
    coefficient (throatTimeFlow period hPeriod parameter base) •
        d9TimeGeneratorDerivativeField period hPeriod field
          (throatTimeFlow period hPeriod parameter base) +
      d9TimeGeneratorDerivativeField period hPeriod coefficient
          (throatTimeFlow period hPeriod parameter base) •
        field (throatTimeFlow period hPeriod parameter base)
  have hF : Continuous (fun input : Real × ThroatBase period hPeriod =>
      F input.1 input.2) :=
    (coefficient.contMDiff_toFun.continuous.comp
      (throatJointTimeFlow_contMDiff period hPeriod).continuous).smul
      (field.contMDiff_toFun.continuous.comp
        (throatJointTimeFlow_contMDiff period hPeriod).continuous)
  have hF' : Continuous (fun input : Real × ThroatBase period hPeriod =>
      F' input.1 input.2) :=
    ((coefficient.contMDiff_toFun.continuous.comp
        (throatJointTimeFlow_contMDiff period hPeriod).continuous).smul
      ((d9TimeGeneratorDerivativeField period hPeriod field).contMDiff_toFun
        |>.continuous.comp
          (throatJointTimeFlow_contMDiff period hPeriod).continuous)).add
      (((d9TimeGeneratorDerivativeField period hPeriod coefficient).contMDiff_toFun
        |>.continuous.comp
          (throatJointTimeFlow_contMDiff period hPeriod).continuous).smul
        (field.contMDiff_toFun.continuous.comp
          (throatJointTimeFlow_contMDiff period hPeriod).continuous))
  have hDerivative : ∀ parameter base,
      HasDerivAt (fun t => F t base) (F' parameter base) parameter := by
    intro parameter base
    dsimp only [F, F']
    apply ((smoothThroatField_timeFlow_hasDerivAt
      period hPeriod coefficient parameter base).smul
        (smoothThroatField_timeFlow_hasDerivAt
          period hPeriod field parameter base)).congr_of_eventuallyEq
    filter_upwards with t
    rfl
  have hInvariant : ∀ parameter,
      (∫ base, F parameter base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ base, F 0 base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
    intro parameter
    simpa [F, throatTimeFlow_zero] using
      (intrinsicCanonicalThroatVolumeMeasure_timeTranslation_measurePreserving
        period hPeriod parameter).integral_comp
          (d9TimeFlow_measurableEmbedding period hPeriod parameter)
          (fun base => coefficient base • field base)
  have hZero := integral_derivative_eq_zero_of_invariant_vector
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) F F'
    hF hF' hDerivative hInvariant
  simp only [F', throatTimeFlow_zero] at hZero
  have hFirst : Integrable
      (fun base => coefficient base •
        d9TimeGeneratorDerivativeField period hPeriod field base)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (coefficient.contMDiff_toFun.continuous.smul
      (d9TimeGeneratorDerivativeField period hPeriod field).contMDiff_toFun.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSecond : Integrable
      (fun base => d9TimeGeneratorDerivativeField period hPeriod coefficient base •
        field base) (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    ((d9TimeGeneratorDerivativeField period hPeriod coefficient).contMDiff_toFun
        |>.continuous.smul field.contMDiff_toFun.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add hFirst hSecond] at hZero
  calc
    _ = (_ + ∫ base,
        d9TimeGeneratorDerivativeField period hPeriod coefficient base •
          field base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        -(∫ base,
          d9TimeGeneratorDerivativeField period hPeriod coefficient base •
            field base
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by abel
    _ = _ := by rw [hZero]; simp

/-- Integration by parts for a variable coefficient times one rotation
derivative. -/
theorem d9RotationGenerator_integral_smul_derivative_eq_neg
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [SecondCountableTopology Fiber]
    (axis : Fin 3)
    (coefficient : SmoothThroatField period hPeriod Real)
    (field : SmoothThroatField period hPeriod Fiber) :
    (∫ base,
      coefficient base •
        d9RotationGeneratorDerivativeField period hPeriod axis field base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      -∫ base,
        d9RotationGeneratorDerivativeField period hPeriod axis coefficient base •
          field base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let flow := throatSpatialRotationFlow period hPeriod axis
  let jointFlow := throatJointSpatialRotationFlow period hPeriod axis
  let F : Real → ThroatBase period hPeriod → Fiber := fun parameter base =>
    coefficient (flow parameter base) • field (flow parameter base)
  let F' : Real → ThroatBase period hPeriod → Fiber := fun parameter base =>
    coefficient (flow parameter base) •
        d9RotationGeneratorDerivativeField period hPeriod axis field
          (flow parameter base) +
      d9RotationGeneratorDerivativeField period hPeriod axis coefficient
          (flow parameter base) • field (flow parameter base)
  have hF : Continuous (fun input : Real × ThroatBase period hPeriod =>
      F input.1 input.2) :=
    (coefficient.contMDiff_toFun.continuous.comp
      (throatJointSpatialRotationFlow_contMDiff period hPeriod axis).continuous).smul
      (field.contMDiff_toFun.continuous.comp
        (throatJointSpatialRotationFlow_contMDiff period hPeriod axis).continuous)
  have hF' : Continuous (fun input : Real × ThroatBase period hPeriod =>
      F' input.1 input.2) :=
    ((coefficient.contMDiff_toFun.continuous.comp
        (throatJointSpatialRotationFlow_contMDiff period hPeriod axis).continuous).smul
      ((d9RotationGeneratorDerivativeField period hPeriod axis field).contMDiff_toFun
        |>.continuous.comp
          (throatJointSpatialRotationFlow_contMDiff period hPeriod axis).continuous)).add
      (((d9RotationGeneratorDerivativeField period hPeriod axis coefficient)
        |>.contMDiff_toFun.continuous.comp
          (throatJointSpatialRotationFlow_contMDiff period hPeriod axis).continuous).smul
        (field.contMDiff_toFun.continuous.comp
          (throatJointSpatialRotationFlow_contMDiff period hPeriod axis).continuous))
  have hDerivative : ∀ parameter base,
      HasDerivAt (fun t => F t base) (F' parameter base) parameter := by
    intro parameter base
    dsimp only [F, F', flow]
    apply ((smoothThroatField_rotationFlow_hasDerivAt
      period hPeriod axis coefficient parameter base).smul
        (smoothThroatField_rotationFlow_hasDerivAt
          period hPeriod axis field parameter base)).congr_of_eventuallyEq
    filter_upwards with t
    rfl
  have hInvariant : ∀ parameter,
      (∫ base, F parameter base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ base, F 0 base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
    intro parameter
    simpa [F, flow, throatSpatialRotationFlow_zero] using
      (intrinsicCanonicalThroatVolumeMeasure_spatialRotation_measurePreserving
        period hPeriod axis parameter).integral_comp
          (throatSpatialRotationFlow_measurableEmbedding period hPeriod axis
            parameter)
          (fun base => coefficient base • field base)
  have hZero := integral_derivative_eq_zero_of_invariant_vector
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) F F'
    hF hF' hDerivative hInvariant
  simp only [F', flow, throatSpatialRotationFlow_zero] at hZero
  have hFirst : Integrable
      (fun base => coefficient base •
        d9RotationGeneratorDerivativeField period hPeriod axis field base)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (coefficient.contMDiff_toFun.continuous.smul
      ((d9RotationGeneratorDerivativeField period hPeriod axis field)
        |>.contMDiff_toFun.continuous))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSecond : Integrable
      (fun base =>
        d9RotationGeneratorDerivativeField period hPeriod axis coefficient base •
          field base) (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    ((d9RotationGeneratorDerivativeField period hPeriod axis coefficient)
        |>.contMDiff_toFun.continuous.smul field.contMDiff_toFun.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add hFirst hSecond] at hZero
  calc
    _ = (_ + ∫ base,
        d9RotationGeneratorDerivativeField period hPeriod axis coefficient base •
          field base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        -(∫ base,
          d9RotationGeneratorDerivativeField period hPeriod axis coefficient base •
            field base
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by abel
    _ = _ := by rw [hZero]; simp

/-! ## Intrinsic-frame integration by parts -/

/-- Integration by parts for one true intrinsic Dirac-frame direction. -/
theorem d9IntrinsicThroatFrame_integral_mvfderiv
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [SecondCountableTopology Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (direction : Fin 3) :
    (∫ base,
      mvfderiv throatCoverModelWithCorners field.toFun base
        (d9IntrinsicThroatFrame period hPeriod direction base)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      -∫ base,
        (-2 * d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod direction base) • field base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let radial := d9BaseUnitRadialCoordinateField period hPeriod direction
  let rotation := fun axis =>
    d9IntrinsicRotationCoefficientField period hPeriod direction axis
  have hPointwise (base : ThroatBase period hPeriod) :
      mvfderiv throatCoverModelWithCorners field.toFun base
          (d9IntrinsicThroatFrame period hPeriod direction base) =
        radial base • d9TimeGeneratorDerivativeField period hPeriod field base +
          ∑ axis : Fin 3,
            rotation axis base •
              d9RotationGeneratorDerivativeField period hPeriod axis field base := by
    rw [d9IntrinsicThroatFrame_decomposition]
    simp only [map_add, map_smul, map_sum]
    rw [d9TimeGeneratorDerivativeField_apply]
    simp_rw [d9RotationGeneratorDerivativeField_apply]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hPointwise)]
  have hTimeIntegrable : Integrable
      (fun base => radial base •
        d9TimeGeneratorDerivativeField period hPeriod field base)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (radial.contMDiff_toFun.continuous.smul
      (d9TimeGeneratorDerivativeField period hPeriod field).contMDiff_toFun.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRotationIntegrable (axis : Fin 3) : Integrable
      (fun base => rotation axis base •
        d9RotationGeneratorDerivativeField period hPeriod axis field base)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    ((rotation axis).contMDiff_toFun.continuous.smul
      ((d9RotationGeneratorDerivativeField period hPeriod axis field)
        |>.contMDiff_toFun.continuous))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRotationSumIntegrable : Integrable
      (fun base => ∑ axis : Fin 3,
        rotation axis base •
          d9RotationGeneratorDerivativeField period hPeriod axis field base)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    integrable_finsetSum Finset.univ fun axis _ => hRotationIntegrable axis
  rw [integral_add hTimeIntegrable hRotationSumIntegrable,
    integral_finsetSum Finset.univ (fun axis _ => hRotationIntegrable axis)]
  rw [d9TimeGenerator_integral_smul_derivative_eq_neg
      period hPeriod radial field]
  simp_rw [d9RotationGenerator_integral_smul_derivative_eq_neg
    period hPeriod]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum]
  · rw [← neg_add, ← integral_add]
    · apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards with base
      rw [← Finset.sum_smul, ← add_smul]
      rw [d9TimeGeneratorDerivativeField_apply]
      simp_rw [d9RotationGeneratorDerivativeField_apply]
      apply congrArg (fun scalar : Real => scalar • field base)
      change
        mvfderiv throatCoverModelWithCorners
            (d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod direction) base
              (throatTimeTranslationGhost period hPeriod base) +
          ∑ axis : Fin 3,
            mvfderiv throatCoverModelWithCorners
              (d9IntrinsicRotationCoefficient
                period hPeriod direction axis) base
              (throatSpatialRotationGhost period hPeriod axis base) = _
      exact d9IntrinsicFrameCoefficientDivergence
        period hPeriod direction base
    · exact
        ((d9TimeGeneratorDerivativeField period hPeriod radial).contMDiff_toFun
          |>.continuous.smul field.contMDiff_toFun.continuous)
          |>.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
    · exact integrable_finsetSum Finset.univ fun axis _ =>
        ((d9RotationGeneratorDerivativeField period hPeriod axis
          (rotation axis)).contMDiff_toFun.continuous.smul
            field.contMDiff_toFun.continuous)
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro axis _
    exact
      ((d9RotationGeneratorDerivativeField period hPeriod axis
        (rotation axis)).contMDiff_toFun.continuous.smul
          field.contMDiff_toFun.continuous)
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

/-- Equivalent positive form of the divergence correction. -/
theorem d9IntrinsicThroatFrame_integral_mvfderiv_eq_two
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [SecondCountableTopology Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (direction : Fin 3) :
    (∫ base,
      mvfderiv throatCoverModelWithCorners field.toFun base
        (d9IntrinsicThroatFrame period hPeriod direction base)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      (2 : Real) •
        ∫ base,
          d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
            field base
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [d9IntrinsicThroatFrame_integral_mvfderiv]
  rw [← integral_smul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with base
  module

/-- Public certificate for integration by parts in all three intrinsic Dirac
frame directions. -/
structure ProgramPPrimitiveSpinCIntrinsicFrameIPPCertificate4D : Prop where
  ipp : ∀
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
      [SecondCountableTopology Fiber]
    (field : SmoothThroatField period hPeriod Fiber) (direction : Fin 3),
    (∫ base,
      mvfderiv throatCoverModelWithCorners field.toFun base
        (d9IntrinsicThroatFrame period hPeriod direction base)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      -∫ base,
        (-2 * d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod direction base) • field base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The measure-preserving time and rotation flows supply the certificate
unconditionally. -/
def programPPrimitiveSpinCIntrinsicFrameIPPCertificate4D :
    ProgramPPrimitiveSpinCIntrinsicFrameIPPCertificate4D period hPeriod where
  ipp := d9IntrinsicThroatFrame_integral_mvfderiv period hPeriod

end
end P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameIPP4D
end JanusFormal
