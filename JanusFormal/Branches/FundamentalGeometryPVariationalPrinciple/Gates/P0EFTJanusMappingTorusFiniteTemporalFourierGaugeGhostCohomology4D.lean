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
  coefficients.sum fun mode coefficient =>
    Finsupp.single mode
      (coefficient * temporalFourierDerivativeMultiplier period mode)

@[simp]
theorem temporalFourierDerivativeCoefficients_single
    (mode : Int) (coefficient : Complex) :
    temporalFourierDerivativeCoefficients period
        (Finsupp.single mode coefficient) =
      Finsupp.single mode
        (coefficient * temporalFourierDerivativeMultiplier period mode) := by
  unfold temporalFourierDerivativeCoefficients
  rw [Finsupp.sum_single_index]
  simp

@[simp]
theorem temporalFourierDerivativeCoefficients_apply
    (coefficients : FiniteTemporalFourierCoefficients) (mode : Int) :
    temporalFourierDerivativeCoefficients period coefficients mode =
      coefficients mode * temporalFourierDerivativeMultiplier period mode := by
  classical
  rw [temporalFourierDerivativeCoefficients, Finsupp.sum_apply,
    Finsupp.sum_eq_single mode, Finsupp.single_eq_same]
  · intro other _ hOther
    exact Finsupp.single_eq_of_ne' hOther
  · intro hMode
    rw [Finsupp.not_mem_support_iff.mp hMode]
    simp

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
      mvfderiv coverModelWithCorners
        (finiteTemporalFourierFieldLinearMap period coefficients).toFun point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point) := by
  unfold finiteTemporalFourierTimeSlice
  rw [← fderiv_apply_one_eq_deriv,
    ← mfderiv_eq_fderiv
      (f := fun parameter : Real =>
        finiteTemporalFourierFieldLinearMap period coefficients
          (effectiveTimeFlow period hPeriodPos.out.ne' parameter point)),
    effectiveTimeTranslationVelocity_eq_timeFlow_mfderiv]
  simpa only [Function.comp_apply, effectiveTimeFlow_zero] using
    (mfderiv_comp_apply 0
      ((finiteTemporalFourierFieldLinearMap period coefficients
        ).contMDiff_toFun.mdifferentiable (by simp)
          (effectiveTimeFlow period hPeriodPos.out.ne' 0 point))
      ((effectiveTimeFlow_orbit_contMDiff period hPeriodPos.out.ne' point
        ).mdifferentiable (by simp) 0) 1)

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
  simpa [finiteTemporalFourierTimeSlice,
    temporalFourierDerivativeMultiplier, mul_assoc] using
    HasDerivAt.const_mul coefficient
      ((hasDerivAt_fourier period mode representative.time
        ).comp_const_add representative.time 0)

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
      simpa [finiteTemporalFourierTimeSlice,
        temporalFourierDerivativeCoefficients] using
        (hasDerivAt_const (x := (0 : Real)) (c := (0 : Complex)))
  | single_add mode coefficient rest hCoefficient hMode ih =>
      have hSingle := finiteTemporalFourierTimeSlice_single_hasDerivAt
        period mode coefficient point
      simpa [finiteTemporalFourierTimeSlice,
        temporalFourierDerivativeCoefficients_add] using hSingle.add ih

/-- Public intrinsic derivative formula for the finite Fourier field.  The
coefficient at mode `n` is multiplied by `2π i n / period`. -/
theorem finiteTemporalFourierField_mvfderiv_timeTranslationVelocity
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : EffectiveQuotient period) :
    mvfderiv coverModelWithCorners
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
  have hComp := mfderiv_comp_apply point
    (complexGaugeCoordinateCLM component).contDiff.mdifferentiableAt
    ((finiteTemporalFourierFieldLinearMap period coefficients
      ).contMDiff_toFun.mdifferentiableAt (by simp))
    (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point)
  rw [finiteTemporalFourierField_mvfderiv_timeTranslationVelocity] at hComp
  simpa only [Function.comp_apply, mfderiv_eq_fderiv,
    ContinuousLinearMap.fderiv, complexGaugeCoordinateCLM_apply] using hComp

private theorem finiteTemporalFourierDerivativeField_eq_zero_of_exact
    (coefficients : FiniteTemporalFourierCoefficients)
    (hExact : finiteTemporalFourierExactGaugeLinearMap period coefficients = 0) :
    finiteTemporalFourierFieldLinearMap period
        (temporalFourierDerivativeCoefficients period coefficients) = 0 := by
  apply SmoothQuotientField.ext period hPeriodPos.out.ne' Complex
  intro point
  apply complexGaugeLieAlgebraEquiv.injective
  apply DFunLike.ext _ _
  intro component
  have hEvaluation := congrArg
    (fun potential : SmoothAbelianGaugePotential period hPeriodPos.out.ne' =>
      potential.toFun component point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point))
    hExact
  rw [finiteTemporalFourierExactGauge_timeTranslationVelocity] at hEvaluation
  simpa using hEvaluation

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
