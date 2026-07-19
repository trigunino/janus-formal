import Mathlib.Analysis.Fourier.AddCircle
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevMappingTorusTimeModeBridge4D

/-!
# Finite temporal Fourier polynomials on the effective mapping torus

For a positive mapping-torus period, this gate realizes every finitely
supported complex sequence on `Z` as a genuine smooth complex field on the
effective D8 quotient.  Its pullback upstairs is the expected finite Fourier
sum, it is exactly deck invariant, and normalized Haar Fourier coefficients
recover the input sequence.  Hence the realization is injective.

The real cosine line of the preceding gate is contained in this finite span
through the usual pair of modes `+1` and `-1`.  No infinite series, Sobolev
completion, spatial `Z^3` mode, norm comparison, nontrivial physical bundle or
boundary statement is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusReflectionFixedThroat

variable (period : Real) [hPeriodPos : Fact (0 < period)]

private abbrev sphereData :=
  reflectedSphereData period hPeriodPos.out.ne'

private abbrev EffectiveCover :=
  MappingTorusCover (sphereData period)

private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period)

private def temporalWitnessFiber : UnitThreeSphere :=
  ⟨fun index => if index = 0 then 1 else 0, by
    simp [OnUnitThreeSphere, radiusSquared]⟩

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period) :=
  reflectedSphereCoverChartedSpace period hPeriodPos.out.ne'

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period) :=
  reflectedSphereCover_isManifold period hPeriodPos.out.ne'

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period) :=
  reflectedSphereQuotientChartedSpace period hPeriodPos.out.ne'

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period) :=
  reflectedSphereQuotient_isManifold period hPeriodPos.out.ne'

/-- Multiplication by a fixed complex number, regarded only as a real
continuous linear map. -/
def complexRightMulRealCLM (scalar : Complex) :
    Complex →L[Real] Complex :=
  (ContinuousLinearMap.toSpanSingleton Complex scalar).restrictScalars Real

@[simp]
theorem complexRightMulRealCLM_apply
    (scalar value : Complex) :
    complexRightMulRealCLM scalar value = value * scalar :=
  rfl

/-- Real phase of the temporal Fourier mode indexed by `mode`. -/
def temporalFourierPhase
    (mode : Int) (point : EffectiveCover period) : Real :=
  (2 * Real.pi / period) * (mode : Real) * point.time

/-- A genuine smooth deck-invariant complex Fourier mode upstairs. -/
def temporalComplexFourierCoverField
    (mode : Int) :
    SmoothDeckInvariantField period hPeriodPos.out.ne' Complex where
  toFun := fun point =>
    (Real.cos (temporalFourierPhase period mode point) : Complex) +
      (Real.sin (temporalFourierPhase period mode point) : Complex) *
        Complex.I
  contMDiff_toFun := by
    let productEquiv := coverHomeomorphProd (sphereData period)
    have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      productEquiv
    have hTime : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point : EffectiveCover period => point.time) :=
      contMDiff_snd.comp hTo
    have hPhase : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point : EffectiveCover period =>
          temporalFourierPhase period mode point) := by
      exact contMDiff_const.mul hTime
    have hCos : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point : EffectiveCover period =>
          Real.cos (temporalFourierPhase period mode point)) :=
      Real.contDiff_cos.contMDiff.comp hPhase
    have hSin : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point : EffectiveCover period =>
          Real.sin (temporalFourierPhase period mode point)) :=
      Real.contDiff_sin.contMDiff.comp hPhase
    have hCosComplex : ContMDiff coverModelWithCorners 𝓘(Real, Complex) ∞
        (fun point : EffectiveCover period =>
          (Real.cos (temporalFourierPhase period mode point) : Complex)) := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.contDiff.contMDiff.comp hCos
    have hSinComplex : ContMDiff coverModelWithCorners 𝓘(Real, Complex) ∞
        (fun point : EffectiveCover period =>
          (Real.sin (temporalFourierPhase period mode point) : Complex)) := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.contDiff.contMDiff.comp hSin
    have hSinI : ContMDiff coverModelWithCorners 𝓘(Real, Complex) ∞
        (fun point : EffectiveCover period =>
          (Real.sin (temporalFourierPhase period mode point) : Complex) *
            Complex.I) := by
      simpa only [Function.comp_def, complexRightMulRealCLM_apply] using
        (complexRightMulRealCLM Complex.I).contMDiff.comp hSinComplex
    exact hCosComplex.add hSinI
  deck_invariant := by
    intro winding point
    have hPhase :
        temporalFourierPhase period mode (winding +ᵥ point) =
          temporalFourierPhase period mode point +
            ((mode * winding : Int) : Real) * (2 * Real.pi) := by
      change
        (2 * Real.pi / period) * (mode : Real) *
            (point.time + (winding : Real) * period) =
          (2 * Real.pi / period) * (mode : Real) * point.time +
            ((mode * winding : Int) : Real) * (2 * Real.pi)
      push_cast
      field_simp [hPeriodPos.out.ne'] <;> ring
    rw [hPhase, Real.cos_add_int_mul_two_pi,
      Real.sin_add_int_mul_two_pi]

/-- Descent of one complex Fourier mode to the actual smooth D8 quotient. -/
def temporalComplexFourierQuotientField
    (mode : Int) :
    SmoothQuotientField period hPeriodPos.out.ne' Complex :=
  descendSmooth period hPeriodPos.out.ne' Complex
    (temporalComplexFourierCoverField period mode)

@[simp]
theorem temporalComplexFourierQuotientField_mk
    (mode : Int) (point : EffectiveCover period) :
    temporalComplexFourierQuotientField period mode
        (mappingTorusMk (sphereData period) point) =
      fourier mode (point.time : AddCircle period) := by
  rw [fourier_coe_apply]
  change
    (Real.cos (temporalFourierPhase period mode point) : Complex) +
        (Real.sin (temporalFourierPhase period mode point) : Complex) *
          Complex.I =
      Complex.exp
        (2 * Real.pi * Complex.I * mode * point.time / period)
  have hExponent :
      (2 * Real.pi * Complex.I * mode * point.time / period : Complex) =
        (temporalFourierPhase period mode point : Complex) *
          Complex.I := by
    simp only [temporalFourierPhase]
    push_cast
    field_simp [hPeriodPos.out.ne'] <;> ring
  rw [hExponent, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- A finite temporal coefficient sequence.  Finite support is part of the
`Finsupp` type, not an additional proposition. -/
abbrev FiniteTemporalFourierCoefficients := Int →₀ Complex

/-- The same finite sequence as a continuous Fourier polynomial on the
ordinary time circle. -/
def temporalFourierPolynomialCircleLinearMap :
    FiniteTemporalFourierCoefficients →ₗ[Complex]
      C(AddCircle period, Complex) :=
  Finsupp.linearCombination Complex (fun mode : Int => fourier mode)

@[simp]
theorem temporalFourierPolynomialCircleLinearMap_single
    (mode : Int) (coefficient : Complex) :
    temporalFourierPolynomialCircleLinearMap period
        (Finsupp.single mode coefficient) =
      coefficient • fourier mode := by
  exact Finsupp.linearCombination_single Complex coefficient mode

private theorem temporalFourierPolynomialCircleLinearMap_apply_eq_sum
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : AddCircle period) :
    temporalFourierPolynomialCircleLinearMap period coefficients point =
      coefficients.sum fun mode coefficient =>
        coefficient * fourier mode point := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [temporalFourierPolynomialCircleLinearMap]
  | single_add mode coefficient rest hCoefficient hMode ih =>
      rw [map_add]
      have hSingle :
          temporalFourierPolynomialCircleLinearMap period
              (Finsupp.single mode coefficient) point =
            (Finsupp.single mode coefficient).sum
              (fun index value => value * fourier index point) := by
        rw [temporalFourierPolynomialCircleLinearMap_single]
        change coefficient * fourier mode point =
          (Finsupp.single mode coefficient).sum
            (fun index value => value * fourier index point)
        rw [Finsupp.sum_single_index (zero_mul _)]
      change
        temporalFourierPolynomialCircleLinearMap period
              (Finsupp.single mode coefficient) point +
            temporalFourierPolynomialCircleLinearMap period rest point =
          (Finsupp.single mode coefficient + rest).sum
            (fun index value => value * fourier index point)
      rw [Finsupp.sum_add_index'
        (fun _ => zero_mul _)
        (fun _ first second => add_mul first second _)]
      rw [hSingle, ih]

/-- A complex coefficient multiplying one quotient Fourier mode, packaged as
a real-linear map without installing any complex module structure on the
smooth field space. -/
def temporalModeCoefficientFieldLinearMap
    (mode : Int) :
    Complex →ₗ[Real]
      SmoothQuotientField period hPeriodPos.out.ne' Complex where
  toFun := fun coefficient =>
    { toFun := fun point =>
        coefficient * temporalComplexFourierQuotientField period mode point
      contMDiff_toFun := by
        simpa only [Function.comp_def, complexRightMulRealCLM_apply,
          mul_comm] using
          (complexRightMulRealCLM coefficient).contMDiff.comp
            (temporalComplexFourierQuotientField period mode).contMDiff_toFun }
  map_add' := by
    intro first second
    ext point
    exact add_mul first second _
  map_smul' := by
    intro scalar coefficient
    ext point
    change ((scalar : Complex) * coefficient) *
        temporalComplexFourierQuotientField period mode point =
      (scalar : Complex) *
        (coefficient * temporalComplexFourierQuotientField period mode point)
    exact mul_assoc _ _ _

/-- Genuine real-linear realization of all finite complex temporal Fourier
sequences as smooth fields on the effective D8 quotient. -/
def finiteTemporalFourierFieldLinearMap :
    FiniteTemporalFourierCoefficients →ₗ[Real]
      SmoothQuotientField period hPeriodPos.out.ne' Complex :=
  Finsupp.lsum Real (temporalModeCoefficientFieldLinearMap period)

@[simp]
theorem finiteTemporalFourierFieldLinearMap_single
    (mode : Int) (coefficient : Complex) :
    finiteTemporalFourierFieldLinearMap period
        (Finsupp.single mode coefficient) =
      temporalModeCoefficientFieldLinearMap period mode coefficient := by
  exact Finsupp.lsum_single Real
    (temporalModeCoefficientFieldLinearMap period) mode coefficient

/-- Exact equality between the true quotient field and the ordinary circle
Fourier polynomial on every cover representative. -/
theorem finiteTemporalFourierField_mk_eq_circle
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : EffectiveCover period) :
    finiteTemporalFourierFieldLinearMap period coefficients
        (mappingTorusMk (sphereData period) point) =
      temporalFourierPolynomialCircleLinearMap period coefficients
        (point.time : AddCircle period) := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp only [map_zero]
      rfl
  | single_add mode coefficient rest hCoefficient hMode ih =>
      rw [map_add, map_add]
      change
        finiteTemporalFourierFieldLinearMap period
              (Finsupp.single mode coefficient)
              (mappingTorusMk (sphereData period) point) +
            finiteTemporalFourierFieldLinearMap period rest
              (mappingTorusMk (sphereData period) point) =
          temporalFourierPolynomialCircleLinearMap period
              (Finsupp.single mode coefficient)
              (point.time : AddCircle period) +
            temporalFourierPolynomialCircleLinearMap period rest
              (point.time : AddCircle period)
      rw [ih]
      congr 1
      rw [finiteTemporalFourierFieldLinearMap_single,
        temporalFourierPolynomialCircleLinearMap_single]
      change coefficient * temporalComplexFourierQuotientField period mode
          (mappingTorusMk (sphereData period) point) =
        coefficient * fourier mode (point.time : AddCircle period)
      rw [temporalComplexFourierQuotientField_mk]

/-- Explicit upstairs finite-sum formula. -/
theorem finiteTemporalFourierField_lift_formula
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : EffectiveCover period) :
    liftSmooth period hPeriodPos.out.ne' Complex
        (finiteTemporalFourierFieldLinearMap period coefficients)
        point =
      coefficients.sum fun mode coefficient =>
        coefficient * Complex.exp
          (2 * Real.pi * Complex.I * mode * point.time / period) := by
  rw [liftSmooth_apply,
    finiteTemporalFourierField_mk_eq_circle]
  rw [temporalFourierPolynomialCircleLinearMap_apply_eq_sum]
  apply Finsupp.sum_congr
  intro mode _
  rw [fourier_coe_apply]

/-- Exact deck cocycle of every finite Fourier polynomial. -/
theorem finiteTemporalFourierField_lift_deck_invariant
    (coefficients : FiniteTemporalFourierCoefficients)
    (winding : Int) (point : EffectiveCover period) :
    liftSmooth period hPeriodPos.out.ne' Complex
        (finiteTemporalFourierFieldLinearMap period coefficients)
        (winding +ᵥ point) =
      liftSmooth period hPeriodPos.out.ne' Complex
        (finiteTemporalFourierFieldLinearMap period coefficients)
        point :=
  (liftSmooth period hPeriodPos.out.ne' Complex
    (finiteTemporalFourierFieldLinearMap period coefficients)).deck_invariant
      winding point

theorem temporalFourierPolynomialCircle_integrable
    (coefficients : FiniteTemporalFourierCoefficients) :
    Integrable (temporalFourierPolynomialCircleLinearMap period coefficients)
      AddCircle.haarAddCircle := by
  simpa using
    ((temporalFourierPolynomialCircleLinearMap period coefficients).continuous.continuousOn.integrableOn_compact
      (μ := AddCircle.haarAddCircle) isCompact_univ)

/-- Normalized Haar Fourier coefficients recover every input coefficient. -/
theorem temporalFourierPolynomialCircle_coefficient
    (coefficients : FiniteTemporalFourierCoefficients) (mode : Int) :
    fourierCoeff
        (temporalFourierPolynomialCircleLinearMap period coefficients) mode =
      coefficients mode := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [temporalFourierPolynomialCircleLinearMap, fourierCoeff]
  | single_add index coefficient rest hCoefficient hIndex ih =>
      rw [map_add]
      change fourierCoeff
          (fun point =>
            temporalFourierPolynomialCircleLinearMap period
                (Finsupp.single index coefficient) point +
              temporalFourierPolynomialCircleLinearMap period rest point)
          mode =
        (Finsupp.single index coefficient + rest) mode
      have hAddMode := congrFun
        (fourierCoeff.add
          (temporalFourierPolynomialCircle_integrable period
            (Finsupp.single index coefficient))
          (temporalFourierPolynomialCircle_integrable period rest)) mode
      have hPointwise :
          (fun point =>
            temporalFourierPolynomialCircleLinearMap period
                (Finsupp.single index coefficient) point +
              temporalFourierPolynomialCircleLinearMap period rest point) =
            ((temporalFourierPolynomialCircleLinearMap period
                (Finsupp.single index coefficient) : AddCircle period → Complex) +
              (temporalFourierPolynomialCircleLinearMap period rest :
                AddCircle period → Complex)) := by
        funext point
        rfl
      rw [hPointwise, hAddMode, Pi.add_apply, ih, Finsupp.add_apply]
      congr 1
      rw [temporalFourierPolynomialCircleLinearMap_single]
      have hScalarPointwise :
          (⇑(coefficient • fourier index) : AddCircle period → Complex) =
            (fun point => coefficient * fourier index point) := by
        funext point
        rfl
      rw [hScalarPointwise, fourierCoeff.const_mul]
      have hFourier := congrFun
        (fourierCoeff_fourier (T := period) index) mode
      rw [hFourier]
      by_cases hSame : index = mode
      · subst mode
        simp only [Pi.single_apply, Finsupp.single_apply, if_pos, mul_one]
      · have hMode : mode ≠ index := fun h => hSame h.symm
        simp only [Pi.single_apply, Finsupp.single_apply, hSame, hMode, if_false, mul_zero]

theorem temporalFourierPolynomialCircleLinearMap_injective :
    Function.Injective
      (temporalFourierPolynomialCircleLinearMap period) := by
  intro first second hEqual
  apply Finsupp.ext
  intro mode
  have hCoefficient := congrArg
    (fun polynomial : C(AddCircle period, Complex) =>
      fourierCoeff polynomial mode) hEqual
  simpa only [temporalFourierPolynomialCircle_coefficient period]
    using hCoefficient

/-- The true mapping-torus realization loses no finite temporal Fourier
coefficient. -/
theorem finiteTemporalFourierFieldLinearMap_injective :
    Function.Injective
      (finiteTemporalFourierFieldLinearMap period) := by
  intro first second hEqual
  apply temporalFourierPolynomialCircleLinearMap_injective period
  apply ContinuousMap.ext
  intro circlePoint
  induction circlePoint using QuotientAddGroup.induction_on with
  | H time =>
      have hValue := congrArg
        (fun field : SmoothQuotientField period hPeriodPos.out.ne' Complex =>
          field (mappingTorusMk (sphereData period)
            ⟨temporalWitnessFiber, time⟩)) hEqual
      simpa only [finiteTemporalFourierField_mk_eq_circle period]
        using hValue

theorem shiftedSobolev_mappingTorus_finiteTemporalFourier_bridge4D :
    Function.Injective
        (finiteTemporalFourierFieldLinearMap period) ∧
      (∀ coefficients : FiniteTemporalFourierCoefficients,
        ∀ mode : Int,
          fourierCoeff
              (temporalFourierPolynomialCircleLinearMap period coefficients)
              mode = coefficients mode) ∧
      (∀ coefficients : FiniteTemporalFourierCoefficients,
        ∀ winding : Int, ∀ point : EffectiveCover period,
          liftSmooth period hPeriodPos.out.ne' Complex
              (finiteTemporalFourierFieldLinearMap period coefficients)
              (winding +ᵥ point) =
            liftSmooth period hPeriodPos.out.ne' Complex
              (finiteTemporalFourierFieldLinearMap period coefficients)
              point) := by
  exact ⟨finiteTemporalFourierFieldLinearMap_injective period,
    temporalFourierPolynomialCircle_coefficient period,
    finiteTemporalFourierField_lift_deck_invariant period⟩

end

end P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D
end JanusFormal
