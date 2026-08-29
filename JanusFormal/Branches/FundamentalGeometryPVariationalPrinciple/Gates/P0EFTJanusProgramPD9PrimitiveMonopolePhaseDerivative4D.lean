import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D

/-!
# First derivative of the primitive monopole clutching phase

This gate computes the real Fréchet derivative of complex normalization away
from zero.  It is the analytic identity needed to identify the derivative of
the explicit north/south clutching phase with the angular one-form.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveMonopolePhaseDerivative4D

set_option autoImplicit false
noncomputable section

open scoped Manifold RealInnerProductSpace

/-- Complex normalization viewed as a real differentiable map. -/
def primitiveMonopoleComplexNormalize (value : Complex) : Complex :=
  Complex.ofRealCLM ‖value‖⁻¹ * value

theorem primitiveMonopoleComplexNormalize_differentiableAt
    (value : Complex) (hValue : value ≠ 0) :
    DifferentiableAt Real primitiveMonopoleComplexNormalize value := by
  have hInv :
      DifferentiableAt Real
        (fun current : Complex => ‖current‖⁻¹) value :=
    (differentiableAt_id.norm Complex hValue).inv
      (norm_ne_zero_iff.mpr hValue)
  have hScalar :
      DifferentiableAt Real
        (fun current : Complex =>
          Complex.ofRealCLM ‖current‖⁻¹) value := by
    change DifferentiableAt Real
      (Complex.ofRealCLM ∘ fun current : Complex => ‖current‖⁻¹) value
    exact Complex.ofRealCLM.differentiableAt.comp value hInv
  exact hScalar.mul differentiableAt_id

/-- Directional derivative of the complex norm away from zero. -/
theorem complex_fderiv_norm_apply
    (value increment : Complex) (hValue : value ≠ 0) :
    fderiv Real (fun current : Complex => ‖current‖) value increment =
      (value.re * increment.re + value.im * increment.im) / ‖value‖ := by
  have hSq :
      DifferentiableAt Real
        (fun current : Complex => ‖current‖ ^ 2) value :=
    differentiableAt_id.norm_sq Complex
  have hSqNe : ‖value‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hValue)
  rw [show (fun current : Complex => ‖current‖) =
      fun current => Real.sqrt (‖current‖ ^ 2) by
        funext current
        simp]
  rw [fderiv_sqrt hSq hSqNe]
  rw [fderiv_norm_sq_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [Real.sqrt_sq_eq_abs, abs_norm]
  simp [Complex.inner, Complex.mul_re]
  field_simp

/-- Directional derivative of the reciprocal complex norm away from zero. -/
theorem complex_fderiv_inv_norm_apply
    (value increment : Complex) (hValue : value ≠ 0) :
    fderiv Real (fun current : Complex => ‖current‖⁻¹) value increment =
      -(value.re * increment.re + value.im * increment.im) / ‖value‖ ^ 3 := by
  have hNorm :
      DifferentiableAt Real
        (fun current : Complex => ‖current‖) value :=
    differentiableAt_id.norm Complex hValue
  have hInv :
      DifferentiableAt Real
        (fun current : Real => current⁻¹) ‖value‖ :=
    differentiableAt_inv (norm_ne_zero_iff.mpr hValue)
  rw [show (fun current : Complex => ‖current‖⁻¹) =
      (fun current : Real => current⁻¹) ∘
        (fun current : Complex => ‖current‖) by rfl]
  rw [fderiv_comp value hInv hNorm]
  simp only [ContinuousLinearMap.comp_apply, fderiv_inv,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [complex_fderiv_norm_apply value increment hValue]
  simp only [smul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hValue]

/-- Coercing the reciprocal norm to `Complex` commutes with its real
Fréchet derivative. -/
theorem complex_fderiv_ofReal_inv_norm_apply
    (value increment : Complex) (hValue : value ≠ 0) :
    fderiv Real
        (fun current : Complex =>
          Complex.ofRealCLM ‖current‖⁻¹)
        value increment =
      Complex.ofRealCLM
        (-(value.re * increment.re + value.im * increment.im) /
          ‖value‖ ^ 3) := by
  have hInv :
      DifferentiableAt Real
        (fun current : Complex => ‖current‖⁻¹) value :=
    (differentiableAt_id.norm Complex hValue).inv
      (norm_ne_zero_iff.mpr hValue)
  rw [show
      (fun current : Complex => Complex.ofRealCLM ‖current‖⁻¹) =
        Complex.ofRealCLM ∘
          (fun current : Complex => ‖current‖⁻¹) by rfl]
  rw [fderiv_comp value Complex.ofRealCLM.differentiableAt hInv]
  simp only [ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply]
  rw [complex_fderiv_inv_norm_apply value increment hValue]

/-- Product-rule form of the derivative of complex normalization. -/
theorem primitiveMonopoleComplexNormalize_fderiv_product
    (value increment : Complex) (hValue : value ≠ 0) :
    fderiv Real primitiveMonopoleComplexNormalize value increment =
      Complex.ofRealCLM ‖value‖⁻¹ * increment +
        Complex.ofRealCLM
            (-(value.re * increment.re + value.im * increment.im) /
              ‖value‖ ^ 3) *
          value := by
  have hInv :
      DifferentiableAt Real
        (fun current : Complex => ‖current‖⁻¹) value :=
    (differentiableAt_id.norm Complex hValue).inv
      (norm_ne_zero_iff.mpr hValue)
  have hScalar :
      DifferentiableAt Real
        (fun current : Complex =>
          Complex.ofRealCLM ‖current‖⁻¹) value := by
    change DifferentiableAt Real
      (Complex.ofRealCLM ∘
        fun current : Complex => ‖current‖⁻¹) value
    exact Complex.ofRealCLM.differentiableAt.comp value hInv
  rw [show primitiveMonopoleComplexNormalize =
      fun current : Complex =>
        Complex.ofRealCLM ‖current‖⁻¹ * current by rfl]
  change
    (fderiv Real
      ((fun current : Complex =>
          Complex.ofRealCLM ‖current‖⁻¹) * id)
      value) increment = _
  rw [(hScalar.hasFDerivAt.mul
    (hasFDerivAt_id value)).fderiv]
  simp only [add_apply, ContinuousLinearMap.smul_apply,
    fderiv_id, ContinuousLinearMap.id_apply, id_eq, smul_eq_mul]
  rw [complex_fderiv_ofReal_inv_norm_apply value increment hValue]
  ring

/-- The derivative of normalization is the angular one-form times the
infinitesimal `U(1)` generator. -/
theorem primitiveMonopoleComplexNormalize_fderiv_angular
    (value increment : Complex) (hValue : value ≠ 0) :
    fderiv Real primitiveMonopoleComplexNormalize value increment =
      Complex.ofRealCLM
          ((value.re * increment.im - value.im * increment.re) /
            (value.re ^ 2 + value.im ^ 2)) *
        (Complex.I * primitiveMonopoleComplexNormalize value) := by
  rw [primitiveMonopoleComplexNormalize_fderiv_product
    value increment hValue]
  have hNorm : ‖value‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hValue
  have hDenominator :
      value.re ^ 2 + value.im ^ 2 ≠ 0 := by
    intro hZero
    apply hValue
    apply Complex.normSq_eq_zero.mp
    simpa [Complex.normSq_apply, pow_two] using hZero
  have hNormSq :
      ‖value‖ ^ 2 = value.re ^ 2 + value.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  apply Complex.ext
  · simp only [primitiveMonopoleComplexNormalize,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofRealCLM_apply, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, sub_zero, mul_zero, zero_add, add_zero]
    field_simp [hNorm, hDenominator]
    rw [hNormSq]
    ring
  · simp only [primitiveMonopoleComplexNormalize,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofRealCLM_apply, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, sub_zero, mul_zero, zero_add, add_zero]
    field_simp [hNorm, hDenominator]
    rw [hNormSq]
    ring

/-- Manifold-derivative form of the angular normalization identity, with
the canonical tangent-space identifications made explicit. -/
theorem primitiveMonopoleComplexNormalize_mfderiv_angular
    (value increment : Complex) (hValue : value ≠ 0) :
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (primitiveMonopoleComplexNormalize value)
        (mfderiv 𝓘(Real, Complex) 𝓘(Real, Complex)
          primitiveMonopoleComplexNormalize value
          ((NormedSpace.fromTangentSpace
            (𝕜 := Real) (E := Complex) value).symm increment)) =
      Complex.ofRealCLM
          ((value.re * increment.im - value.im * increment.re) /
            (value.re ^ 2 + value.im ^ 2)) *
        (Complex.I * primitiveMonopoleComplexNormalize value) := by
  rw [mfderiv_eq_fderiv]
  change
    fderiv Real primitiveMonopoleComplexNormalize value increment = _
  exact primitiveMonopoleComplexNormalize_fderiv_angular
    value increment hValue

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleSmoothClutching4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Equatorial complex coordinate pulled back to the actual D9 throat. -/
def d9PrimitiveMonopoleBaseXY
    (base : ThroatBase period hPeriod) : Complex :=
  monopoleSphereXY
    (d9ThroatMonopoleSphereProjection period hPeriod base)

theorem d9PrimitiveMonopoleBaseXY_contMDiff :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
      (d9PrimitiveMonopoleBaseXY period hPeriod) :=
  monopoleSphereXY_contMDiff.comp
    ((d9ThroatMonopoleSphereProjection_contMDiff
      period hPeriod).of_le (by simp))

@[simp]
theorem d9PrimitiveMonopoleBaseXY_re
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveMonopoleBaseXY period hPeriod base).re =
      d9PrimitiveMonopoleBaseCoordinate period hPeriod 0 base :=
  rfl

@[simp]
theorem d9PrimitiveMonopoleBaseXY_im
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveMonopoleBaseXY period hPeriod base).im =
      d9PrimitiveMonopoleBaseCoordinate period hPeriod 1 base :=
  rfl

/-- The real component of the pulled-back complex differential is the
established `x` coordinate frame derivative. -/
theorem d9PrimitiveMonopoleBaseXY_mfderiv_re
    (direction : Fin 3) (base : ThroatBase period hPeriod) :
    (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (d9PrimitiveMonopoleBaseXY period hPeriod) base
        (d9IntrinsicThroatFrame period hPeriod direction base)).re =
      d9PrimitiveMonopoleCoordinateFrameDerivative
        period hPeriod 0 direction base := by
  have hXY :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex)
        (d9PrimitiveMonopoleBaseXY period hPeriod) base :=
    (d9PrimitiveMonopoleBaseXY_contMDiff
      period hPeriod).mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply base
    Complex.reCLM.mdifferentiableAt hXY
    (d9IntrinsicThroatFrame period hPeriod direction base)
  simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
  have hChainReal := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real) (E := Real)
      (d9PrimitiveMonopoleBaseCoordinate
        period hPeriod 0 base)) hChain
  have hLeft :
      (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (d9PrimitiveMonopoleBaseXY period hPeriod) base
          (d9IntrinsicThroatFrame period hPeriod direction base)).re =
        NormedSpace.fromTangentSpace (𝕜 := Real) (E := Real)
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod 0 base)
          (Complex.reCLM
            (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
              (d9PrimitiveMonopoleBaseXY period hPeriod) base
              (d9IntrinsicThroatFrame period hPeriod direction base))) := by
    rfl
  have hRight :
      NormedSpace.fromTangentSpace (𝕜 := Real) (E := Real)
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod 0 base)
          (mfderiv throatCoverModelWithCorners 𝓘(Real, Real)
            (Complex.reCLM ∘
              d9PrimitiveMonopoleBaseXY period hPeriod)
            base
            (d9IntrinsicThroatFrame period hPeriod direction base)) =
        d9PrimitiveMonopoleCoordinateFrameDerivative
          period hPeriod 0 direction base := by
    rfl
  exact hLeft.trans (hChainReal.symm.trans hRight)

/-- The imaginary component of the pulled-back complex differential is the
established `y` coordinate frame derivative. -/
theorem d9PrimitiveMonopoleBaseXY_mfderiv_im
    (direction : Fin 3) (base : ThroatBase period hPeriod) :
    (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (d9PrimitiveMonopoleBaseXY period hPeriod) base
        (d9IntrinsicThroatFrame period hPeriod direction base)).im =
      d9PrimitiveMonopoleCoordinateFrameDerivative
        period hPeriod 1 direction base := by
  have hXY :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex)
        (d9PrimitiveMonopoleBaseXY period hPeriod) base :=
    (d9PrimitiveMonopoleBaseXY_contMDiff
      period hPeriod).mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply base
    Complex.imCLM.mdifferentiableAt hXY
    (d9IntrinsicThroatFrame period hPeriod direction base)
  simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
  have hChainReal := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real) (E := Real)
      (d9PrimitiveMonopoleBaseCoordinate
        period hPeriod 1 base)) hChain
  have hLeft :
      (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (d9PrimitiveMonopoleBaseXY period hPeriod) base
          (d9IntrinsicThroatFrame period hPeriod direction base)).im =
        NormedSpace.fromTangentSpace (𝕜 := Real) (E := Real)
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod 1 base)
          (Complex.imCLM
            (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
              (d9PrimitiveMonopoleBaseXY period hPeriod) base
              (d9IntrinsicThroatFrame period hPeriod direction base))) := by
    rfl
  have hRight :
      NormedSpace.fromTangentSpace (𝕜 := Real) (E := Real)
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod 1 base)
          (mfderiv throatCoverModelWithCorners 𝓘(Real, Real)
            (Complex.imCLM ∘
              d9PrimitiveMonopoleBaseXY period hPeriod)
            base
            (d9IntrinsicThroatFrame period hPeriod direction base)) =
        d9PrimitiveMonopoleCoordinateFrameDerivative
          period hPeriod 1 direction base := by
    rfl
  exact hLeft.trans (hChainReal.symm.trans hRight)

theorem d9PrimitiveMonopoleBaseXY_ne_zero_of_mem_overlap
    (base : ThroatBase period hPeriod)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    d9PrimitiveMonopoleBaseXY period hPeriod base ≠ 0 :=
  monopoleSphereXY_ne_zero_of_mem_overlap
    (d9ThroatMonopoleSphereProjection period hPeriod base)
    hNorth hSouth

/-- On the north/south overlap, the actual charge-one transition is exactly
complex normalization of the pulled-back equatorial coordinate. -/
theorem d9PrimitiveSpinCPhaseTransition_north_south_coe
    (base : ThroatBase period hPeriod)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    (d9PrimitiveSpinCPhaseTransition
        period hPeriod .north .south base : Complex) =
      primitiveMonopoleComplexNormalize
        (d9PrimitiveMonopoleBaseXY period hPeriod base) := by
  have hXY :=
    d9PrimitiveMonopoleBaseXY_ne_zero_of_mem_overlap
      period hPeriod base hNorth hSouth
  simp only [d9PrimitiveSpinCPhaseTransition,
    primitiveMonopoleTransition, zpow_one]
  rw [monopoleSphereXYPhase_coe_of_ne_zero
    (d9ThroatMonopoleSphereProjection period hPeriod base) hXY]
  rfl

/-- The pulled-back normalized equatorial coordinate has logarithmic
derivative equal to the established Cartesian angular coefficient. -/
theorem d9PrimitiveMonopoleNormalizedBaseXY_mfderiv
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (primitiveMonopoleComplexNormalize ∘
          d9PrimitiveMonopoleBaseXY period hPeriod)
        base
        (d9IntrinsicThroatFrame period hPeriod direction base) =
      Complex.ofRealCLM
          (d9PrimitiveMonopoleAngularFrameCoefficient
            period hPeriod direction base) *
        (Complex.I *
          primitiveMonopoleComplexNormalize
            (d9PrimitiveMonopoleBaseXY period hPeriod base)) := by
  have hValue :=
    d9PrimitiveMonopoleBaseXY_ne_zero_of_mem_overlap
      period hPeriod base hNorth hSouth
  have hNormalize :
      MDifferentiableAt 𝓘(Real, Complex) 𝓘(Real, Complex)
        primitiveMonopoleComplexNormalize
        (d9PrimitiveMonopoleBaseXY period hPeriod base) :=
    (primitiveMonopoleComplexNormalize_differentiableAt
      (d9PrimitiveMonopoleBaseXY period hPeriod base)
      hValue).mdifferentiableAt
  have hXY :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex)
        (d9PrimitiveMonopoleBaseXY period hPeriod) base :=
    (d9PrimitiveMonopoleBaseXY_contMDiff
      period hPeriod).mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply base hNormalize hXY
    (d9IntrinsicThroatFrame period hPeriod direction base)
  let baseXYDerivative :=
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
      (d9PrimitiveMonopoleBaseXY period hPeriod) base
      (d9IntrinsicThroatFrame period hPeriod direction base)
  let increment : Complex :=
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
      (d9PrimitiveMonopoleBaseXY period hPeriod base)
      baseXYDerivative
  have hOuter :=
    primitiveMonopoleComplexNormalize_mfderiv_angular
      (d9PrimitiveMonopoleBaseXY period hPeriod base)
      increment hValue
  have hOuter' :
      NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
          (primitiveMonopoleComplexNormalize
            (d9PrimitiveMonopoleBaseXY period hPeriod base))
          (mfderiv 𝓘(Real, Complex) 𝓘(Real, Complex)
            primitiveMonopoleComplexNormalize
            (d9PrimitiveMonopoleBaseXY period hPeriod base)
            baseXYDerivative) =
        Complex.ofRealCLM
            (((d9PrimitiveMonopoleBaseXY period hPeriod base).re *
                increment.im -
              (d9PrimitiveMonopoleBaseXY period hPeriod base).im *
                increment.re) /
              ((d9PrimitiveMonopoleBaseXY period hPeriod base).re ^ 2 +
                (d9PrimitiveMonopoleBaseXY period hPeriod base).im ^ 2)) *
          (Complex.I *
            primitiveMonopoleComplexNormalize
              (d9PrimitiveMonopoleBaseXY period hPeriod base)) := by
    simpa [increment] using hOuter
  have hChainComplex := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
      (primitiveMonopoleComplexNormalize
        (d9PrimitiveMonopoleBaseXY period hPeriod base))) hChain
  have hResult := hChainComplex.trans hOuter'
  have hIncrementRe :
      increment.re =
        d9PrimitiveMonopoleCoordinateFrameDerivative
          period hPeriod 0 direction base := by
    change baseXYDerivative.re = _
    exact d9PrimitiveMonopoleBaseXY_mfderiv_re
      period hPeriod direction base
  have hIncrementIm :
      increment.im =
        d9PrimitiveMonopoleCoordinateFrameDerivative
          period hPeriod 1 direction base := by
    change baseXYDerivative.im = _
    exact d9PrimitiveMonopoleBaseXY_mfderiv_im
      period hPeriod direction base
  rw [hIncrementRe, hIncrementIm] at hResult
  have hResult' :
      NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
          (primitiveMonopoleComplexNormalize
            (d9PrimitiveMonopoleBaseXY period hPeriod base))
          (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (primitiveMonopoleComplexNormalize ∘
              d9PrimitiveMonopoleBaseXY period hPeriod)
            base
            (d9IntrinsicThroatFrame period hPeriod direction base)) =
        Complex.ofRealCLM
            (d9PrimitiveMonopoleAngularFrameCoefficient
              period hPeriod direction base) *
          (Complex.I *
            primitiveMonopoleComplexNormalize
              (d9PrimitiveMonopoleBaseXY period hPeriod base)) := by
    simpa [d9PrimitiveMonopoleAngularFrameCoefficient,
      d9PrimitiveMonopoleBaseCoordinate,
      primitiveMonopoleAngularCoefficient,
      primitiveMonopoleAngularNumerator] using hResult
  exact hResult'

/-- Exact logarithmic derivative of the actual north/south clutching phase
on the genuine D9 overlap. -/
theorem d9PrimitiveSpinCPhaseTransition_north_south_mfderiv
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun current : ThroatBase period hPeriod =>
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod .north .south current : Complex))
        base
        (d9IntrinsicThroatFrame period hPeriod direction base) =
      Complex.ofRealCLM
          (d9PrimitiveMonopoleAngularFrameCoefficient
            period hPeriod direction base) *
        (Complex.I *
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod .north .south base : Complex)) := by
  have hOverlapOpen :
      IsOpen
        (d9PrimitiveMonopoleChartDomain period hPeriod .north ∩
          d9PrimitiveMonopoleChartDomain period hPeriod .south) :=
    (d9PrimitiveMonopoleChartDomain_isOpen
      period hPeriod .north).inter
      (d9PrimitiveMonopoleChartDomain_isOpen
        period hPeriod .south)
  have hEventually :
      (fun current : ThroatBase period hPeriod =>
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod .north .south current : Complex)) =ᶠ[𝓝 base]
        (primitiveMonopoleComplexNormalize ∘
          d9PrimitiveMonopoleBaseXY period hPeriod) := by
    apply Filter.eventuallyEq_of_mem
      (hOverlapOpen.mem_nhds ⟨hNorth, hSouth⟩)
    intro current hCurrent
    exact d9PrimitiveSpinCPhaseTransition_north_south_coe
      period hPeriod current hCurrent.1 hCurrent.2
  have hDerivative :=
    Filter.EventuallyEq.mfderiv_eq
      (I := throatCoverModelWithCorners)
      (I' := 𝓘(Real, Complex)) hEventually
  have hApply := congrArg
    (fun derivative =>
      derivative
        (d9IntrinsicThroatFrame period hPeriod direction base))
    hDerivative
  calc
    _ = mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (primitiveMonopoleComplexNormalize ∘
            d9PrimitiveMonopoleBaseXY period hPeriod)
          base
          (d9IntrinsicThroatFrame period hPeriod direction base) :=
      hApply
    _ = Complex.ofRealCLM
          (d9PrimitiveMonopoleAngularFrameCoefficient
            period hPeriod direction base) *
        (Complex.I *
          primitiveMonopoleComplexNormalize
            (d9PrimitiveMonopoleBaseXY period hPeriod base)) :=
      d9PrimitiveMonopoleNormalizedBaseXY_mfderiv
        period hPeriod direction base hNorth hSouth
    _ = _ := by
      rw [← d9PrimitiveSpinCPhaseTransition_north_south_coe
        period hPeriod base hNorth hSouth]

/-- The complex scalar representation, bundled as a continuous real-linear
map in its scalar parameter. -/
def d9PrimitiveSpinCComplexActionParameterCLM :
    Complex →L[Real]
      (D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) :=
  (ContinuousLinearMap.compL Real D9DoubledMatterFiber
      D9DoubledMatterSpinor D9DoubledMatterFiber
      d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv.symm.toContinuousLinearMap).comp
    (((ContinuousLinearMap.compL Real D9DoubledMatterFiber
        D9DoubledMatterSpinor D9DoubledMatterSpinor).flip
        d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv.toContinuousLinearMap).comp
      (ContinuousLinearMap.lsmul Real Complex))

@[simp]
theorem d9PrimitiveSpinCComplexActionParameterCLM_apply
    (scalar : Complex) :
    d9PrimitiveSpinCComplexActionParameterCLM scalar =
      d9PrimitiveSpinCComplexActionCLM scalar :=
  rfl

/-- Evaluation of the complex representation on a scalar/fiber pair. -/
def d9PrimitiveSpinCComplexActionPair
    (input : Complex × D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCComplexActionCLM input.1 input.2

theorem d9PrimitiveSpinCComplexActionPair_differentiable :
    Differentiable Real d9PrimitiveSpinCComplexActionPair := by
  let scalarMap :
      (Complex × D9DoubledMatterFiber) →L[Real]
        (D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) :=
    d9PrimitiveSpinCComplexActionParameterCLM.comp
      (ContinuousLinearMap.fst Real Complex D9DoubledMatterFiber)
  let matterMap :
      (Complex × D9DoubledMatterFiber) →L[Real]
        D9DoubledMatterFiber :=
    ContinuousLinearMap.snd Real Complex D9DoubledMatterFiber
  change Differentiable Real
    (fun current => scalarMap current (matterMap current))
  exact scalarMap.differentiable.clm_apply matterMap.differentiable

/-- Ordinary real Fréchet product rule for the complex fiber action. -/
theorem d9PrimitiveSpinCComplexActionPair_fderiv
    (input increment : Complex × D9DoubledMatterFiber) :
    fderiv Real d9PrimitiveSpinCComplexActionPair input increment =
      d9PrimitiveSpinCComplexActionCLM input.1 increment.2 +
        d9PrimitiveSpinCComplexActionCLM increment.1 input.2 := by
  let scalarMap :
      (Complex × D9DoubledMatterFiber) →L[Real]
        (D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) :=
    d9PrimitiveSpinCComplexActionParameterCLM.comp
      (ContinuousLinearMap.fst Real Complex D9DoubledMatterFiber)
  let matterMap :
      (Complex × D9DoubledMatterFiber) →L[Real]
        D9DoubledMatterFiber :=
    ContinuousLinearMap.snd Real Complex D9DoubledMatterFiber
  change
    (fderiv Real (fun current => scalarMap current (matterMap current))
      input) increment = _
  rw [fderiv_clm_apply scalarMap.differentiableAt
    matterMap.differentiableAt]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.fderiv, scalarMap, matterMap,
    d9PrimitiveSpinCComplexActionParameterCLM_apply]
  rfl

/-- Manifold-derivative form of the complex-action product rule. -/
theorem d9PrimitiveSpinCComplexActionPair_mfderiv
    (input increment : Complex × D9DoubledMatterFiber) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9PrimitiveSpinCComplexActionPair input)
        (mfderiv 𝓘(Real, Complex × D9DoubledMatterFiber)
          𝓘(Real, D9DoubledMatterFiber)
          d9PrimitiveSpinCComplexActionPair input
          ((NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := Complex × D9DoubledMatterFiber) input).symm
            increment)) =
      d9PrimitiveSpinCComplexActionCLM input.1 increment.2 +
        d9PrimitiveSpinCComplexActionCLM increment.1 input.2 := by
  rw [mfderiv_eq_fderiv]
  change
    fderiv Real d9PrimitiveSpinCComplexActionPair input increment = _
  exact d9PrimitiveSpinCComplexActionPair_fderiv input increment

@[simp]
theorem d9PrimitiveSpinCComplexAction_phase
    (phase : Circle) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM (phase : Complex) matter =
      d9PrimitiveSpinCPhaseActionCLM phase matter :=
  rfl

@[simp]
theorem d9PrimitiveSpinCComplexAction_I
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM Complex.I matter =
      d9PrimitiveSpinCImaginaryAction matter :=
  rfl

theorem d9PrimitiveSpinCComplexAction_ofReal_mul
    (coefficient : Real) (scalar : Complex)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM
        (Complex.ofRealCLM coefficient * scalar) matter =
      coefficient •
        d9PrimitiveSpinCComplexActionCLM scalar matter := by
  rw [show
      Complex.ofRealCLM coefficient * scalar =
        coefficient • scalar by
      rw [Complex.real_smul, Complex.ofRealCLM_apply]]
  change
    d9PrimitiveSpinCComplexActionParameterCLM
        (coefficient • scalar) matter =
      coefficient •
        d9PrimitiveSpinCComplexActionParameterCLM scalar matter
  rw [map_smul]
  rfl

/-- A logarithmic phase derivative acts as the expected infinitesimal
imaginary generator on the phase-transformed fiber. -/
theorem d9PrimitiveSpinCComplexAction_angular_phase
    (coefficient : Real) (phase : Circle)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM
        (Complex.ofRealCLM coefficient *
          (Complex.I * (phase : Complex))) matter =
      coefficient •
        d9PrimitiveSpinCImaginaryAction
          (d9PrimitiveSpinCPhaseActionCLM phase matter) := by
  rw [d9PrimitiveSpinCComplexAction_ofReal_mul]
  congr 1
  rw [d9PrimitiveSpinCComplexAction_mul]
  rfl

theorem d9PrimitiveSpinCComplexAction_coe_angular_phase
    (coefficient : Real) (phase : Circle)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM
        ((coefficient : Complex) *
          (Complex.I * (phase : Complex))) matter =
      coefficient •
        d9PrimitiveSpinCImaginaryAction
          (d9PrimitiveSpinCPhaseActionCLM phase matter) := by
  simpa only [Complex.ofRealCLM_apply] using
    d9PrimitiveSpinCComplexAction_angular_phase
      coefficient phase matter

/-- The ordinary local derivative satisfies the exact north/south clutching
Leibniz rule.  This discharges the former `hFlat` hypothesis from the local
geometric Dirac construction. -/
theorem d9PrimitiveSpinCLocalFlatFrameDerivative_north_south_exact
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (normalIndex : ThroatCover period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hNormal : base ∈ normalBundleBaseSet period hPeriod normalIndex)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod choice family
        (normalIndex, .south) direction base =
      d9PrimitiveSpinCGaugeTransformedDirectionalPartial
        (d9PrimitiveMonopoleAngularFrameCoefficient
          period hPeriod direction base)
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod .north .south base)
        (d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family
          (normalIndex, .north) direction base)
        (family.localValue (normalIndex, .north) base) := by
  let phaseField : ThroatBase period hPeriod → Complex :=
    primitiveMonopoleComplexNormalize ∘
      d9PrimitiveMonopoleBaseXY period hPeriod
  let northField : ThroatBase period hPeriod →
      D9DoubledMatterFiber :=
    family.localValue (normalIndex, .north)
  let pairField : ThroatBase period hPeriod →
      Complex × D9DoubledMatterFiber :=
    fun current => (phaseField current, northField current)
  let transformedField : ThroatBase period hPeriod →
      D9DoubledMatterFiber :=
    d9PrimitiveSpinCComplexActionPair ∘ pairField
  let tangent :=
    d9IntrinsicThroatFrame period hPeriod direction base
  have hValue :=
    d9PrimitiveMonopoleBaseXY_ne_zero_of_mem_overlap
      period hPeriod base hNorth hSouth
  have hNormalize :
      MDifferentiableAt 𝓘(Real, Complex) 𝓘(Real, Complex)
        primitiveMonopoleComplexNormalize
        (d9PrimitiveMonopoleBaseXY period hPeriod base) :=
    (primitiveMonopoleComplexNormalize_differentiableAt
      (d9PrimitiveMonopoleBaseXY period hPeriod base)
      hValue).mdifferentiableAt
  have hBaseXY :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex)
        (d9PrimitiveMonopoleBaseXY period hPeriod) base :=
    (d9PrimitiveMonopoleBaseXY_contMDiff
      period hPeriod).mdifferentiableAt (by simp)
  have hPhase :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex) phaseField base := by
    dsimp [phaseField]
    exact hNormalize.comp base hBaseXY
  have hNorthAt :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) ∞
        northField base := by
    dsimp [northField]
    exact
      (family.contMDiffOn_localValue
        (normalIndex, .north)).contMDiffAt
          ((d9PrimitiveSpinCBaseSet_isOpen
            period hPeriod (normalIndex, .north)).mem_nhds
              ⟨hNormal, hNorth⟩)
  have hNorthDiff :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) northField base :=
    hNorthAt.mdifferentiableAt (by simp)
  have hPair :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex × D9DoubledMatterFiber)
        pairField base := by
    dsimp [pairField]
    exact hPhase.prodMk_space hNorthDiff
  have hAction :
      MDifferentiableAt
        𝓘(Real, Complex × D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber)
        d9PrimitiveSpinCComplexActionPair
        (pairField base) :=
    (d9PrimitiveSpinCComplexActionPair_differentiable
      (pairField base)).mdifferentiableAt
  have hPairMap :
      mfderiv throatCoverModelWithCorners
          𝓘(Real, Complex × D9DoubledMatterFiber)
          pairField base =
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, Complex) phaseField base).prod
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber) northField base) := by
    dsimp [pairField]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact mfderiv_prodMk hPhase hNorthDiff
  let pairDerivative :=
    mfderiv throatCoverModelWithCorners
      𝓘(Real, Complex × D9DoubledMatterFiber)
      pairField base tangent
  let pairIncrement : Complex × D9DoubledMatterFiber :=
    NormedSpace.fromTangentSpace (𝕜 := Real)
      (E := Complex × D9DoubledMatterFiber)
      (pairField base) pairDerivative
  have hPairIncrement :
      pairIncrement =
        (NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
            (phaseField base)
            (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
              phaseField base tangent),
          NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := D9DoubledMatterFiber)
            (northField base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, D9DoubledMatterFiber)
              northField base tangent)) := by
    dsimp [pairIncrement, pairDerivative]
    rw [hPairMap]
    rfl
  have hChain :=
    mfderiv_comp_apply base hAction hPair tangent
  have hOuter :=
    d9PrimitiveSpinCComplexActionPair_mfderiv
      (pairField base) pairIncrement
  have hOuter' :
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (d9PrimitiveSpinCComplexActionPair (pairField base))
          (mfderiv
            𝓘(Real, Complex × D9DoubledMatterFiber)
            𝓘(Real, D9DoubledMatterFiber)
            d9PrimitiveSpinCComplexActionPair
            (pairField base) pairDerivative) =
        d9PrimitiveSpinCComplexActionCLM
            (pairField base).1 pairIncrement.2 +
          d9PrimitiveSpinCComplexActionCLM
            pairIncrement.1 (pairField base).2 := by
    simpa [pairIncrement] using hOuter
  have hChainFiber := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (E := D9DoubledMatterFiber)
      (d9PrimitiveSpinCComplexActionPair (pairField base)))
    hChain
  have hActionResult := hChainFiber.trans hOuter'
  rw [hPairIncrement] at hActionResult
  have hPhaseDerivative :
      NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
          (phaseField base)
          (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            phaseField base tangent) =
        Complex.ofRealCLM
            (d9PrimitiveMonopoleAngularFrameCoefficient
              period hPeriod direction base) *
          (Complex.I * phaseField base) := by
    dsimp [phaseField, tangent]
    exact d9PrimitiveMonopoleNormalizedBaseXY_mfderiv
      period hPeriod direction base hNorth hSouth
  have hNorthDerivative :
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (northField base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            northField base tangent) =
        d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family
          (normalIndex, .north) direction base := by
    rfl
  have hPhaseBase :
      phaseField base =
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod .north .south base : Complex) := by
    exact
      (d9PrimitiveSpinCPhaseTransition_north_south_coe
        period hPeriod base hNorth hSouth).symm
  rw [hPhaseDerivative, hNorthDerivative] at hActionResult
  dsimp [pairField] at hActionResult
  rw [hPhaseBase] at hActionResult
  rw [d9PrimitiveSpinCComplexAction_phase,
    d9PrimitiveSpinCComplexAction_coe_angular_phase] at hActionResult
  dsimp [northField] at hActionResult
  have hTransformedDerivative :
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (transformedField base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            transformedField base tangent) =
        d9PrimitiveSpinCGaugeTransformedDirectionalPartial
          (d9PrimitiveMonopoleAngularFrameCoefficient
            period hPeriod direction base)
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod .north .south base)
          (d9PrimitiveSpinCLocalFlatFrameDerivative
            period hPeriod choice family
            (normalIndex, .north) direction base)
          (family.localValue (normalIndex, .north) base) := by
    dsimp [transformedField, pairField, northField]
    rw [hPhaseBase]
    unfold d9PrimitiveSpinCGaugeTransformedDirectionalPartial
    convert hActionResult using 1 <;> rfl
  have hCommonOpen :
      IsOpen
        ((normalBundleBaseSet period hPeriod normalIndex ∩
            d9PrimitiveMonopoleChartDomain period hPeriod .north) ∩
          d9PrimitiveMonopoleChartDomain period hPeriod .south) :=
    ((normalBundleBaseSet_isOpen period hPeriod normalIndex).inter
      (d9PrimitiveMonopoleChartDomain_isOpen
        period hPeriod .north)).inter
      (d9PrimitiveMonopoleChartDomain_isOpen
        period hPeriod .south)
  have hEventually :
      family.localValue (normalIndex, .south) =ᶠ[𝓝 base]
        transformedField := by
    apply Filter.eventuallyEq_of_mem
      (hCommonOpen.mem_nhds ⟨⟨hNormal, hNorth⟩, hSouth⟩)
    intro current hCurrent
    have hLocal :=
      d9PrimitiveSpinCLocalValue_north_south
        period hPeriod choice family normalIndex current
        hCurrent.1.1 hCurrent.1.2 hCurrent.2
    dsimp [transformedField, pairField, phaseField, northField]
    rw [← d9PrimitiveSpinCPhaseTransition_north_south_coe
      period hPeriod current hCurrent.1.2 hCurrent.2]
    exact hLocal
  have hDerivative :=
    Filter.EventuallyEq.mfderiv_eq
      (I := throatCoverModelWithCorners)
      (I' := 𝓘(Real, D9DoubledMatterFiber)) hEventually
  have hApply := congrArg (fun derivative => derivative tangent) hDerivative
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  rw [hApply]
  exact hTransformedDerivative

/-- Exact north/south covariance of the Levi--Civita SpinC derivative,
with no additional first-derivative hypothesis. -/
theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_north_south_exact
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (normalIndex : ThroatCover period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hNormal : base ∈ normalBundleBaseSet period hPeriod normalIndex)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice family
        (normalIndex, .south) direction base =
      d9PrimitiveSpinCGaugeTransformedDirectionalPartial
        (d9PrimitiveMonopoleAngularFrameCoefficient
          period hPeriod direction base)
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod .north .south base)
        (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice family
          (normalIndex, .north) direction base)
        (family.localValue (normalIndex, .north) base) := by
  exact d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_north_south
    period hPeriod choice family normalIndex direction base
    hNormal hNorth hSouth
    (d9PrimitiveSpinCLocalFlatFrameDerivative_north_south_exact
      period hPeriod choice family normalIndex direction base
      hNormal hNorth hSouth)

/-- Exact north/south covariance of the complete local geometric SpinC
Dirac expression. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_north_south_exact
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (normalIndex : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hNormal : base ∈ normalBundleBaseSet period hPeriod normalIndex)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice family (normalIndex, .south) base =
      d9PrimitiveSpinCPhaseActionCLM
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod .north .south base)
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family (normalIndex, .north) base) := by
  exact d9PrimitiveSpinCLocalGeometricDirac_north_south
    period hPeriod choice family normalIndex base hNormal hNorth hSouth
    (fun direction =>
      d9PrimitiveSpinCLocalFlatFrameDerivative_north_south_exact
        period hPeriod choice family normalIndex direction base
        hNormal hNorth hSouth)

end
end P0EFTJanusProgramPD9PrimitiveMonopolePhaseDerivative4D
end JanusFormal
