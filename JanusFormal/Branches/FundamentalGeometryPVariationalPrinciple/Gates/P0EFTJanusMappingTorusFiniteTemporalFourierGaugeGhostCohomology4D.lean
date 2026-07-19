import Mathlib.Analysis.Calculus.Deriv.Shift
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D

/-!
# Finite temporal Fourier ghosts: exact zero-mode cohomology

The genuine quotient time-translation velocity differentiates each finite
temporal Fourier coefficient by the exact multiplier `2π i n / period`.
Evaluating the intrinsic exact gauge potential on this single true tangent
direction therefore detects every nonzero temporal mode.  Consequently, on
this finite Fourier subspace, the kernel of `c ↦ dc` is exactly the range of
the constant zero-mode inclusion.

This is a finite-mode statement.  It does not identify the kernel on all
smooth ghosts and supplies no Sobolev, Fredholm, regulator, or global BRST
cohomology result.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D

variable (period : Real) [hPeriodPos : Fact (0 < period)]

private abbrev sphereData :=
  reflectedSphereData period hPeriodPos.out.ne'

private abbrev EffectiveCover :=
  MappingTorusCover (sphereData period)

private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period) :=
  reflectedSphereQuotientChartedSpace period hPeriodPos.out.ne'

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period) :=
  reflectedSphereQuotient_isManifold period hPeriodPos.out.ne'

/-- The exact complex temporal-frequency multiplier. -/
def temporalFourierDerivativeMultiplier (mode : Int) : Complex :=
  2 * Real.pi * Complex.I * mode / period

/-- Coefficients of the temporal derivative of a finite Fourier field. -/
def temporalFourierDerivativeCoefficients
    (coefficients : FiniteTemporalFourierCoefficients) :
    FiniteTemporalFourierCoefficients :=
  Finsupp.onFinset coefficients.support
    (fun mode =>
      coefficients mode * temporalFourierDerivativeMultiplier period mode)
    (by
      intro mode hNonzero
      exact Finsupp.mem_support_iff.mpr (fun hCoefficient =>
        hNonzero (by rw [hCoefficient, zero_mul])))

@[simp]
theorem temporalFourierDerivativeCoefficients_single
    (mode : Int) (coefficient : Complex) :
    temporalFourierDerivativeCoefficients period
        (Finsupp.single mode coefficient) =
      Finsupp.single mode
        (coefficient * temporalFourierDerivativeMultiplier period mode) := by
  classical
  apply Finsupp.ext
  intro current
  change (Finsupp.single mode coefficient) current *
      temporalFourierDerivativeMultiplier period current =
    (Finsupp.single mode
      (coefficient * temporalFourierDerivativeMultiplier period mode)) current
  by_cases hCurrent : current = mode
  · subst current
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne hCurrent,
      Finsupp.single_eq_of_ne hCurrent, zero_mul]

@[simp]
theorem temporalFourierDerivativeCoefficients_apply
    (coefficients : FiniteTemporalFourierCoefficients) (mode : Int) :
    temporalFourierDerivativeCoefficients period coefficients mode =
      coefficients mode * temporalFourierDerivativeMultiplier period mode := by
  rfl

theorem temporalFourierDerivativeCoefficients_add
    (first second : FiniteTemporalFourierCoefficients) :
    temporalFourierDerivativeCoefficients period (first + second) =
      temporalFourierDerivativeCoefficients period first +
        temporalFourierDerivativeCoefficients period second := by
  classical
  apply Finsupp.ext
  intro mode
  simp only [temporalFourierDerivativeCoefficients_apply, Finsupp.add_apply]
  exact add_mul _ _ _

/-- Restriction of a finite quotient Fourier field to one genuine time-flow
orbit. -/
def finiteTemporalFourierTimeSlice
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : EffectiveQuotient period) (parameter : Real) : Complex :=
  finiteTemporalFourierFieldLinearMap period coefficients
    (effectiveTimeFlow period hPeriodPos.out.ne' parameter point)

/-- Ordinary differentiation of a time-flow slice is the intrinsic manifold
derivative evaluated on the true time-translation velocity. -/
theorem finiteTemporalFourierTimeSlice_deriv_eq_mvfderiv
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : EffectiveQuotient period) :
    deriv (finiteTemporalFourierTimeSlice period coefficients point) 0 =
      mfderiv coverModelWithCorners 𝓘(Real, Complex)
        (finiteTemporalFourierFieldLinearMap period coefficients).toFun point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point) := by
  unfold finiteTemporalFourierTimeSlice
  rw [← fderiv_apply_one_eq_deriv,
    ← mfderiv_eq_fderiv
      (f := fun parameter : Real =>
        finiteTemporalFourierFieldLinearMap period coefficients
          (effectiveTimeFlow period hPeriodPos.out.ne' parameter point)),
    effectiveTimeTranslationVelocity_eq_timeFlow_mfderiv]
  have hComp := mfderiv_comp_apply 0
      ((finiteTemporalFourierFieldLinearMap period coefficients
        ).contMDiff_toFun.mdifferentiable (by simp)
          (effectiveTimeFlow period hPeriodPos.out.ne' 0 point))
      ((effectiveTimeFlow_orbit_contMDiff period hPeriodPos.out.ne' point
        ).mdifferentiable (by simp) 0) 1
  rw [effectiveTimeFlow_zero] at hComp
  convert hComp using 1 <;> rfl

/-- One Fourier mode, including its coefficient, has the expected derivative
along the genuine quotient time flow. -/
theorem finiteTemporalFourierTimeSlice_single_hasDerivAt
    (mode : Int) (coefficient : Complex)
    (point : EffectiveQuotient period) :
    HasDerivAt
      (finiteTemporalFourierTimeSlice period
        (Finsupp.single mode coefficient) point)
      (finiteTemporalFourierFieldLinearMap period
        (temporalFourierDerivativeCoefficients period
          (Finsupp.single mode coefficient)) point) 0 := by
  obtain ⟨representative, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period) point
  have hShift : HasDerivAt
      (fun parameter : Real =>
        fourier mode
          ((representative.time + parameter : Real) : AddCircle period))
      (temporalFourierDerivativeMultiplier period mode *
        fourier mode (representative.time : AddCircle period)) 0 := by
    simpa [temporalFourierDerivativeMultiplier] using
      ((hasDerivAt_fourier period mode (representative.time + 0)
        ).comp_const_add representative.time 0)
  have hScaled := HasDerivAt.const_mul coefficient hShift
  have hSlice : finiteTemporalFourierTimeSlice period
        (Finsupp.single mode coefficient)
        (mappingTorusMk (sphereData period) representative) =
      fun parameter : Real => coefficient *
        fourier mode
          ((representative.time + parameter : Real) : AddCircle period) := by
    funext parameter
    unfold finiteTemporalFourierTimeSlice
    rw [effectiveTimeFlow_mk,
      finiteTemporalFourierField_mk_eq_circle,
      temporalFourierPolynomialCircleLinearMap_single]
    rfl
  have hDerivative : finiteTemporalFourierFieldLinearMap period
        (temporalFourierDerivativeCoefficients period
          (Finsupp.single mode coefficient))
        (mappingTorusMk (sphereData period) representative) =
      coefficient * (temporalFourierDerivativeMultiplier period mode *
        fourier mode (representative.time : AddCircle period)) := by
    rw [temporalFourierDerivativeCoefficients_single,
      finiteTemporalFourierFieldLinearMap_single]
    change (coefficient * temporalFourierDerivativeMultiplier period mode) *
        temporalComplexFourierQuotientField period mode
          (mappingTorusMk (sphereData period) representative) = _
    rw [temporalComplexFourierQuotientField_mk]
    exact mul_assoc _ _ _
  rw [hSlice, hDerivative]
  exact hScaled

/-- Every finite Fourier polynomial obeys the same multiplier formula along
the genuine quotient time flow. -/
theorem finiteTemporalFourierTimeSlice_hasDerivAt
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : EffectiveQuotient period) :
    HasDerivAt (finiteTemporalFourierTimeSlice period coefficients point)
      (finiteTemporalFourierFieldLinearMap period
        (temporalFourierDerivativeCoefficients period coefficients) point) 0 := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      have hSlice : finiteTemporalFourierTimeSlice period 0 point =
          fun _ : Real => (0 : Complex) := by
        funext parameter
        change (finiteTemporalFourierFieldLinearMap period 0).toFun
          (effectiveTimeFlow period hPeriodPos.out.ne' parameter point) = 0
        rw [map_zero]
        rfl
      have hDerivative : finiteTemporalFourierFieldLinearMap period
          (temporalFourierDerivativeCoefficients period 0) point = 0 := by
        have hCoefficients :
            temporalFourierDerivativeCoefficients period 0 = 0 := by
          apply Finsupp.ext
          intro mode
          simp
        rw [hCoefficients, map_zero]
        rfl
      rw [hSlice, hDerivative]
      exact hasDerivAt_const (x := (0 : Real)) (c := (0 : Complex))
  | single_add mode coefficient rest hCoefficient hMode ih =>
      have hSingle := finiteTemporalFourierTimeSlice_single_hasDerivAt
        period mode coefficient point
      have hSlice : finiteTemporalFourierTimeSlice period
          (Finsupp.single mode coefficient + rest) point =
          fun parameter =>
            finiteTemporalFourierTimeSlice period
                (Finsupp.single mode coefficient) point parameter +
              finiteTemporalFourierTimeSlice period rest point parameter := by
        funext parameter
        have hFields : finiteTemporalFourierFieldLinearMap period
              (Finsupp.single mode coefficient + rest) =
            finiteTemporalFourierFieldLinearMap period
                (Finsupp.single mode coefficient) +
              finiteTemporalFourierFieldLinearMap period rest :=
          map_add _ _ _
        have hEvaluated := congrArg
          (fun field : SmoothQuotientField period hPeriodPos.out.ne' Complex =>
            field.toFun
              (effectiveTimeFlow period hPeriodPos.out.ne' parameter point))
          hFields
        exact hEvaluated
      have hDerivative : finiteTemporalFourierFieldLinearMap period
          (temporalFourierDerivativeCoefficients period
            (Finsupp.single mode coefficient + rest)) point =
          finiteTemporalFourierFieldLinearMap period
              (temporalFourierDerivativeCoefficients period
                (Finsupp.single mode coefficient)) point +
            finiteTemporalFourierFieldLinearMap period
              (temporalFourierDerivativeCoefficients period rest) point := by
        rw [temporalFourierDerivativeCoefficients_add, map_add]
        rfl
      rw [hSlice, hDerivative]
      exact hSingle.add ih

/-- Public intrinsic derivative formula for the finite Fourier field.  The
coefficient at mode `n` is multiplied by `2π i n / period`. -/
theorem finiteTemporalFourierField_mvfderiv_timeTranslationVelocity
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : EffectiveQuotient period) :
    mfderiv coverModelWithCorners 𝓘(Real, Complex)
        (finiteTemporalFourierFieldLinearMap period coefficients).toFun point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point) =
      finiteTemporalFourierFieldLinearMap period
        (temporalFourierDerivativeCoefficients period coefficients) point := by
  rw [← finiteTemporalFourierTimeSlice_deriv_eq_mvfderiv]
  exact (finiteTemporalFourierTimeSlice_hasDerivAt period coefficients point).deriv

/-- The real coordinate of the complex-to-`U(1)^2` equivalence. -/
def complexGaugeCoordinateCLM (component : Fin 2) : Complex →L[Real] Real :=
  (EuclideanSpace.proj component).comp
    complexGaugeLieAlgebraEquiv.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem complexGaugeCoordinateCLM_apply
    (component : Fin 2) (value : Complex) :
    complexGaugeCoordinateCLM component value =
      (complexGaugeLieAlgebraEquiv value) component :=
  rfl

/-- The temporal component of the intrinsic exact gauge potential is exactly
the corresponding real coordinate of the Fourier multiplier field. -/
theorem finiteTemporalFourierExactGauge_timeTranslationVelocity
    (coefficients : FiniteTemporalFourierCoefficients)
    (component : Fin 2) (point : EffectiveQuotient period) :
    (finiteTemporalFourierExactGaugeLinearMap period coefficients).toFun
        component point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point) =
      (complexGaugeLieAlgebraEquiv
        (finiteTemporalFourierFieldLinearMap period
          (temporalFourierDerivativeCoefficients period coefficients) point))
        component := by
  change mvfderiv coverModelWithCorners
      (fun quotientPoint => complexGaugeCoordinateCLM component
        (finiteTemporalFourierFieldLinearMap period coefficients quotientPoint))
      point (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point) = _
  have hCoordinate : MDifferentiableAt 𝓘(Real, Complex) 𝓘(Real, Real)
      (complexGaugeCoordinateCLM component)
      (finiteTemporalFourierFieldLinearMap period coefficients point) :=
    (complexGaugeCoordinateCLM component).differentiableAt.mdifferentiableAt
  have hField : MDifferentiableAt coverModelWithCorners 𝓘(Real, Complex)
      (finiteTemporalFourierFieldLinearMap period coefficients).toFun point :=
    (finiteTemporalFourierFieldLinearMap period coefficients
      ).contMDiff_toFun.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply point hCoordinate hField
    (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point)
  rw [finiteTemporalFourierField_mvfderiv_timeTranslationVelocity] at hComp
  simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hComp
  convert hComp using 1 <;> rfl

private theorem finiteTemporalFourierDerivativeField_eq_zero_of_exact
    (coefficients : FiniteTemporalFourierCoefficients)
    (hExact : finiteTemporalFourierExactGaugeLinearMap period coefficients = 0) :
    finiteTemporalFourierFieldLinearMap period
        (temporalFourierDerivativeCoefficients period coefficients) = 0 := by
  change exactGaugePotential period hPeriodPos.out.ne'
      (finiteTemporalFourierGaugeGhostLinearMap period coefficients) = 0 at hExact
  apply SmoothQuotientField.ext period hPeriodPos.out.ne' Complex
  intro point
  change finiteTemporalFourierFieldLinearMap period
      (temporalFourierDerivativeCoefficients period coefficients) point = 0
  apply complexGaugeLieAlgebraEquiv.injective
  rw [map_zero]
  apply PiLp.ext
  intro component
  have hEvaluation := congrArg
    (fun potential : SmoothAbelianGaugePotential period hPeriodPos.out.ne' =>
      potential.toFun component point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point))
    hExact
  change (finiteTemporalFourierExactGaugeLinearMap period coefficients).toFun
      component point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point) = 0
    at hEvaluation
  rw [finiteTemporalFourierExactGauge_timeTranslationVelocity] at hEvaluation
  exact hEvaluation

private theorem temporalFourierDerivativeMultiplier_ne_zero
    (mode : Int) (hMode : mode ≠ 0) :
    temporalFourierDerivativeMultiplier period mode ≠ 0 := by
  have hPi : (Real.pi : Complex) ≠ 0 := by
    exact_mod_cast Real.pi_pos.ne'
  have hModeComplex : (mode : Complex) ≠ 0 := by
    exact_mod_cast hMode
  have hPeriodComplex : (period : Complex) ≠ 0 := by
    exact_mod_cast hPeriodPos.out.ne'
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hPi)
      Complex.I_ne_zero) hModeComplex) hPeriodComplex

private theorem coefficient_eq_zero_of_exact_of_ne_zero
    (coefficients : FiniteTemporalFourierCoefficients)
    (hExact : finiteTemporalFourierExactGaugeLinearMap period coefficients = 0)
    (mode : Int) (hMode : mode ≠ 0) :
    coefficients mode = 0 := by
  have hDerivativeField :=
    finiteTemporalFourierDerivativeField_eq_zero_of_exact period coefficients hExact
  have hDerivativeCoefficients :
      temporalFourierDerivativeCoefficients period coefficients = 0 := by
    apply finiteTemporalFourierFieldLinearMap_injective period
    simpa using hDerivativeField
  have hModeCoefficient := congrArg
    (fun values : FiniteTemporalFourierCoefficients => values mode)
    hDerivativeCoefficients
  have hProduct : coefficients mode *
      temporalFourierDerivativeMultiplier period mode = 0 := by
    simpa only [temporalFourierDerivativeCoefficients_apply,
      Finsupp.zero_apply] using hModeCoefficient
  exact (mul_eq_zero.mp hProduct).resolve_right
    (temporalFourierDerivativeMultiplier_ne_zero period mode hMode)

/-- Converse zero-mode inclusion: within the finite temporal Fourier
subspace, an exact-potential kernel element has no nonzero coefficient. -/
theorem finiteTemporalFourierExactGauge_kernel_le_zeroMode_range :
    LinearMap.ker (finiteTemporalFourierExactGaugeLinearMap period) ≤
      LinearMap.range temporalZeroModeCoefficientLinearMap := by
  intro coefficients hKernel
  change finiteTemporalFourierExactGaugeLinearMap period coefficients = 0 at hKernel
  refine ⟨coefficients 0, ?_⟩
  apply Finsupp.ext
  intro mode
  by_cases hMode : mode = 0
  · subst mode
    simp [temporalZeroModeCoefficientLinearMap]
  · have hCoefficient := coefficient_eq_zero_of_exact_of_ne_zero
      period coefficients hKernel mode hMode
    simp [temporalZeroModeCoefficientLinearMap, Finsupp.single_apply,
      hMode, hCoefficient]

/-- Exact finite-mode kernel computation for the genuine temporal Fourier
`U(1)^2` ghost realization. -/
theorem finiteTemporalFourierExactGauge_kernel_eq_zeroMode_range :
    LinearMap.ker (finiteTemporalFourierExactGaugeLinearMap period) =
      LinearMap.range temporalZeroModeCoefficientLinearMap := by
  apply le_antisymm
  · exact finiteTemporalFourierExactGauge_kernel_le_zeroMode_range period
  · exact temporalZeroMode_range_le_exactGauge_kernel period

end

end P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
end JanusFormal
