import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalLLWorldvolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# Exact variation of the global LL worldvolume action

The already selected LL action is algebraic in the independent measure and
flux coefficient fields.  This gate varies both fields on the actual compact
throat, proves the exact cubic expansion and differentiates the integral for
every finite Borel measure.  Its pointwise Euler system is equivalent to the
zero-flux branch.  The auxiliary LL metric is absent from the selected action,
and its zero response is recorded explicitly rather than hidden.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalLLVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open Asymptotics
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Select the scalar normed-field module in derivative statements, avoiding
the irrelevant `Real` module instance diamond. -/
local instance realNormedModule : Module Real Real :=
  NormedField.toNormedSpace.toModule

/-- Independent LL measure and flux directions. -/
structure LLVariation where
  measureDirection : SmoothThroatField period hPeriod Real
  fieldDirection : SmoothThroatField period hPeriod LLFieldFiber

/-- Simultaneous affine curve of the two LL fields entering the action. -/
def llAffineCurve
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (epsilon : Real) : IndependentFields period hPeriod :=
  { fields with
    llMeasure := fields.llMeasure + epsilon • variation.measureDirection
    llField := fields.llField + epsilon • variation.fieldDirection }

@[simp]
theorem llAffineCurve_zero
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod) :
    llAffineCurve period hPeriod fields variation 0 = fields := by
  cases fields
  simp [llAffineCurve]

/-- Linear coefficient of the exact LL density expansion. -/
def llFirstVariationDensity
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  variation.measureDirection point * ‖fields.llField point‖ ^ 2 +
    2 * fields.llMeasure point *
      inner Real (fields.llField point) (variation.fieldDirection point)

/-- Quadratic coefficient when measure and flux vary simultaneously. -/
def llSecondVariationCoefficient
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  fields.llMeasure point * ‖variation.fieldDirection point‖ ^ 2 +
    2 * variation.measureDirection point *
      inner Real (fields.llField point) (variation.fieldDirection point)

/-- Cubic coefficient caused by varying the measure and quadratic flux at the
same time. -/
def llThirdVariationCoefficient
    (variation : LLVariation period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  variation.measureDirection point * ‖variation.fieldDirection point‖ ^ 2

theorem llWorldvolumeDensity_affine
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    llWorldvolumeDensity period hPeriod
        (llAffineCurve period hPeriod fields variation epsilon) point =
      llWorldvolumeDensity period hPeriod fields point +
        epsilon * llFirstVariationDensity period hPeriod fields variation point +
        epsilon ^ 2 *
          llSecondVariationCoefficient period hPeriod fields variation point +
        epsilon ^ 3 * llThirdVariationCoefficient period hPeriod variation point := by
  change
    (fields.llMeasure point + epsilon * variation.measureDirection point) *
        ‖fields.llField point + epsilon • variation.fieldDirection point‖ ^ 2 = _
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  unfold llWorldvolumeDensity llFlux llFirstVariationDensity
    llSecondVariationCoefficient llThirdVariationCoefficient
  ring

theorem llFirstVariationDensity_continuous
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod) :
    Continuous (llFirstVariationDensity period hPeriod fields variation) := by
  exact
    (variation.measureDirection.contMDiff_toFun.continuous.mul
      (fields.llField.contMDiff_toFun.continuous.norm.pow 2)).add
    ((continuous_const.mul fields.llMeasure.contMDiff_toFun.continuous).mul
      (fields.llField.contMDiff_toFun.continuous.inner
        variation.fieldDirection.contMDiff_toFun.continuous))

theorem llSecondVariationCoefficient_continuous
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod) :
    Continuous (llSecondVariationCoefficient period hPeriod fields variation) := by
  exact
    (fields.llMeasure.contMDiff_toFun.continuous.mul
      (variation.fieldDirection.contMDiff_toFun.continuous.norm.pow 2)).add
    ((continuous_const.mul variation.measureDirection.contMDiff_toFun.continuous).mul
      (fields.llField.contMDiff_toFun.continuous.inner
        variation.fieldDirection.contMDiff_toFun.continuous))

theorem llThirdVariationCoefficient_continuous
    (variation : LLVariation period hPeriod) :
    Continuous (llThirdVariationCoefficient period hPeriod variation) := by
  exact variation.measureDirection.contMDiff_toFun.continuous.mul
    (variation.fieldDirection.contMDiff_toFun.continuous.norm.pow 2)

private theorem continuous_integrable
    (function : EffectiveThroat period hPeriod → Real)
    (hContinuous : Continuous function)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable function mu :=
  hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace function)

/-- Integrated first variation. -/
def globalLLFirstVariation
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, llFirstVariationDensity period hPeriod fields variation point ∂mu

private def globalLLSecondCoefficient
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, llSecondVariationCoefficient period hPeriod fields variation point ∂mu

private def globalLLThirdCoefficient
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, llThirdVariationCoefficient period hPeriod variation point ∂mu

/-- Exact integrated cubic expansion.  Compactness and finite measure discharge
all integrability obligations. -/
theorem globalLLAction_affine
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    globalLLAction period hPeriod
        (llAffineCurve period hPeriod fields variation epsilon) mu =
      globalLLAction period hPeriod fields mu +
        epsilon * globalLLFirstVariation period hPeriod fields variation mu +
        epsilon ^ 2 *
          globalLLSecondCoefficient period hPeriod fields variation mu +
        epsilon ^ 3 * globalLLThirdCoefficient period hPeriod variation mu := by
  have hBase := llWorldvolumeDensity_integrable period hPeriod fields mu
  have hFirst := continuous_integrable period hPeriod
    (llFirstVariationDensity period hPeriod fields variation)
    (llFirstVariationDensity_continuous period hPeriod fields variation) mu
  have hSecond := continuous_integrable period hPeriod
    (llSecondVariationCoefficient period hPeriod fields variation)
    (llSecondVariationCoefficient_continuous period hPeriod fields variation) mu
  have hThird := continuous_integrable period hPeriod
    (llThirdVariationCoefficient period hPeriod variation)
    (llThirdVariationCoefficient_continuous period hPeriod variation) mu
  unfold globalLLAction globalLLFirstVariation globalLLSecondCoefficient
    globalLLThirdCoefficient
  simp_rw [llWorldvolumeDensity_affine period hPeriod fields variation epsilon]
  calc
    ∫ point,
        llWorldvolumeDensity period hPeriod fields point +
              epsilon * llFirstVariationDensity period hPeriod fields variation point +
            epsilon ^ 2 * llSecondVariationCoefficient period hPeriod fields variation point +
          epsilon ^ 3 * llThirdVariationCoefficient period hPeriod variation point ∂mu =
        (∫ point,
          llWorldvolumeDensity period hPeriod fields point +
              epsilon * llFirstVariationDensity period hPeriod fields variation point +
            epsilon ^ 2 * llSecondVariationCoefficient period hPeriod fields variation point ∂mu) +
          ∫ point, epsilon ^ 3 *
            llThirdVariationCoefficient period hPeriod variation point ∂mu := by
      simpa only [Pi.add_apply] using
        integral_add
          ((hBase.add (hFirst.const_mul epsilon)).add
            (hSecond.const_mul (epsilon ^ 2)))
          (hThird.const_mul (epsilon ^ 3))
    _ = ((∫ point,
          llWorldvolumeDensity period hPeriod fields point +
            epsilon * llFirstVariationDensity period hPeriod fields variation point ∂mu) +
          ∫ point, epsilon ^ 2 *
            llSecondVariationCoefficient period hPeriod fields variation point ∂mu) +
          ∫ point, epsilon ^ 3 *
            llThirdVariationCoefficient period hPeriod variation point ∂mu := by
      exact congrArg (fun value => value +
          ∫ point, epsilon ^ 3 *
            llThirdVariationCoefficient period hPeriod variation point ∂mu)
        (by
          simpa only [Pi.add_apply] using
            integral_add (hBase.add (hFirst.const_mul epsilon))
              (hSecond.const_mul (epsilon ^ 2)))
    _ = (((∫ point, llWorldvolumeDensity period hPeriod fields point ∂mu) +
          ∫ point, epsilon *
            llFirstVariationDensity period hPeriod fields variation point ∂mu) +
          ∫ point, epsilon ^ 2 *
            llSecondVariationCoefficient period hPeriod fields variation point ∂mu) +
          ∫ point, epsilon ^ 3 *
            llThirdVariationCoefficient period hPeriod variation point ∂mu := by
      exact congrArg (fun value =>
          (value + ∫ point, epsilon ^ 2 *
            llSecondVariationCoefficient period hPeriod fields variation point ∂mu) +
          ∫ point, epsilon ^ 3 *
            llThirdVariationCoefficient period hPeriod variation point ∂mu)
        (by
          simpa only [Pi.add_apply] using
            integral_add hBase (hFirst.const_mul epsilon))
    _ = _ := by
      simp only [integral_const_mul]

/-- Actual derivative of the global LL action for every finite measure. -/
theorem globalLLAction_affine_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real => globalLLAction period hPeriod
        (llAffineCurve period hPeriod fields variation epsilon) mu)
      (globalLLFirstVariation period hPeriod fields variation mu) 0 := by
  letI : Norm Real := Real.normedAddCommGroup.toNorm
  rw [show (fun epsilon : Real => globalLLAction period hPeriod
      (llAffineCurve period hPeriod fields variation epsilon) mu) =
      (fun epsilon : Real => globalLLAction period hPeriod fields mu +
        epsilon * globalLLFirstVariation period hPeriod fields variation mu +
        epsilon ^ 2 * globalLLSecondCoefficient period hPeriod fields variation mu +
        epsilon ^ 3 * globalLLThirdCoefficient period hPeriod variation mu) from by
      funext epsilon
      exact globalLLAction_affine period hPeriod fields variation mu epsilon]
  let action := globalLLAction period hPeriod fields mu
  let first := globalLLFirstVariation period hPeriod fields variation mu
  let second := globalLLSecondCoefficient period hPeriod fields variation mu
  let third := globalLLThirdCoefficient period hPeriod variation mu
  change HasDerivAt
    (fun epsilon : Real => action + epsilon * first + epsilon ^ 2 * second +
      epsilon ^ 3 * third) first 0
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero, zero_mul, zero_pow (by norm_num : (2 : Nat) ≠ 0),
    zero_pow (by norm_num : (3 : Nat) ≠ 0), add_zero]
  apply (isLittleO_iff_tendsto (fun epsilon hZero => by
    subst epsilon
    simp)).2
  have hRatio :
      (fun epsilon : Real =>
        (action + epsilon * first + epsilon ^ 2 * second + epsilon ^ 3 * third -
          action - epsilon • first) / epsilon) =
        (fun epsilon : Real => epsilon * second + epsilon ^ 2 * third) := by
    funext epsilon
    change
      (action + epsilon * first + epsilon ^ 2 * second + epsilon ^ 3 * third -
        action - epsilon * first) / epsilon = _
    by_cases hEpsilon : epsilon = 0
    · simp [hEpsilon]
    · field_simp
      ring
  rw [hRatio]
  have hContinuous : ContinuousAt
      (fun epsilon : Real => epsilon * second + epsilon ^ 2 * third) 0 := by
    fun_prop
  simpa only [ContinuousAt, zero_mul,
    zero_pow (by norm_num : (2 : Nat) ≠ 0), add_zero] using hContinuous

/-- Euler coefficient dual to the independent measure field. -/
def llMeasureEuler
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  ‖fields.llField point‖ ^ 2

/-- Euler vector dual to the independent LL flux field. -/
def llFieldEuler
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) : LLFieldFiber :=
  (2 * fields.llMeasure point) • fields.llField point

theorem llFirstVariationDensity_eq_euler_pairing
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    llFirstVariationDensity period hPeriod fields variation point =
      variation.measureDirection point * llMeasureEuler period hPeriod fields point +
        inner Real (llFieldEuler period hPeriod fields point)
          (variation.fieldDirection point) := by
  simp [llFirstVariationDensity, llMeasureEuler, llFieldEuler,
    real_inner_smul_left]

/-- The pointwise LL Euler system of the selected algebraic action. -/
def LLStationaryAt
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) : Prop :=
  llMeasureEuler period hPeriod fields point = 0 ∧
    llFieldEuler period hPeriod fields point = 0

/-- The complete pointwise Euler system is exactly the zero-flux branch. -/
theorem llStationaryAt_iff_zeroFlux
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    LLStationaryAt period hPeriod fields point ↔ fields.llField point = 0 := by
  constructor
  · intro hStationary
    have hNormSq : ‖fields.llField point‖ ^ 2 = 0 := hStationary.1
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hNormSq)
  · intro hZero
    simp [LLStationaryAt, llMeasureEuler, llFieldEuler, hZero]

/-- The selected LL action is independent of the auxiliary LL metric. -/
def llAuxMetricAffineCurve
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (epsilon : Real) : IndependentFields period hPeriod :=
  { fields with llAuxMetric := fields.llAuxMetric + epsilon • direction }

theorem globalLLAction_auxMetricAffineCurve
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (epsilon : Real) (mu : Measure (EffectiveThroat period hPeriod)) :
    globalLLAction period hPeriod
      (llAuxMetricAffineCurve period hPeriod fields direction epsilon) mu =
        globalLLAction period hPeriod fields mu := by
  rfl

/-- Compact closure statement for facade and audit integration. -/
theorem global_ll_variation_closure
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    (∀ variation : LLVariation period hPeriod,
      HasDerivAt
        (fun epsilon : Real => globalLLAction period hPeriod
          (llAffineCurve period hPeriod fields variation epsilon) mu)
        (globalLLFirstVariation period hPeriod fields variation mu) 0) ∧
      (∀ point, LLStationaryAt period hPeriod fields point ↔
        fields.llField point = 0) ∧
      (∀ direction epsilon,
        globalLLAction period hPeriod
          (llAuxMetricAffineCurve period hPeriod fields direction epsilon) mu =
            globalLLAction period hPeriod fields mu) := by
  exact ⟨fun variation =>
      globalLLAction_affine_hasDerivAt period hPeriod fields variation mu,
    llStationaryAt_iff_zeroFlux period hPeriod fields,
    fun direction epsilon =>
      globalLLAction_auxMetricAffineCurve period hPeriod fields direction epsilon mu⟩

end

end P0EFTJanusMappingTorusGlobalLLVariation4D
end JanusFormal
