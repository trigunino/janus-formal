import Mathlib.Analysis.Asymptotics.Lemmas
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient

/-!
# Scalar Robin junction balance on the actual D8 throat

Two smooth bulk scalars are restricted along the genuine throat inclusion.
A quadratic interface action couples those traces to an independent smooth
throat scalar.  Its exact first variation gives the sum of the two Robin
fluxes, so stationarity implies their weak integrated balance.

This is a scalar transmission model.  It does not construct metric normal
derivatives, extrinsic curvature, an Israel condition, or a null junction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarRobinJunctionBalance4D

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
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
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

/-- The selected scalar module in derivative statements. -/
local instance realNormedModule : Module Real Real :=
  NormedField.toNormedSpace.toModule

/-- Robin flux from the plus bulk trace into the throat field. -/
def robinFluxPlus
    (kPlus : Real)
    (bulkPlus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real) :
    SmoothThroatField period hPeriod Real :=
  kPlus • (junction - throatTrace period hPeriod Real bulkPlus)

/-- Robin flux from the minus bulk trace into the throat field. -/
def robinFluxMinus
    (kMinus : Real)
    (bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real) :
    SmoothThroatField period hPeriod Real :=
  kMinus • (junction - throatTrace period hPeriod Real bulkMinus)

/-- Sum of the two constitutive interface fluxes. -/
def junctionResidual
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real) :
    SmoothThroatField period hPeriod Real :=
  robinFluxPlus period hPeriod kPlus bulkPlus junction +
    robinFluxMinus period hPeriod kMinus bulkMinus junction

/-- Quadratic interface energy density on the genuine throat. -/
def robinJunctionDensity
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) : Real :=
  kPlus / 2 *
      (junction point - throatTrace period hPeriod Real bulkPlus point) ^ 2 +
    kMinus / 2 *
      (junction point - throatTrace period hPeriod Real bulkMinus point) ^ 2

/-- The actual throat action for any finite Borel measure. -/
def robinJunctionAction
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, robinJunctionDensity period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction point ∂mu

/-- Affine variation of the independent throat scalar. -/
def junctionAffineCurve
    (junction test : SmoothThroatField period hPeriod Real)
    (epsilon : Real) : SmoothThroatField period hPeriod Real :=
  junction + epsilon • test

/-- Weak first-variation density: total Robin flux paired with a test field. -/
def robinFirstVariationDensity
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) : Real :=
  junctionResidual period hPeriod kPlus kMinus bulkPlus bulkMinus junction point *
    test point

/-- Integrated weak first variation. -/
def robinFirstVariation
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, robinFirstVariationDensity period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction test point ∂mu

private def robinSecondCoefficientDensity
    (kPlus kMinus : Real)
    (test : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) : Real :=
  (kPlus + kMinus) / 2 * test point ^ 2

private def robinSecondCoefficient
    (kPlus kMinus : Real)
    (test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, robinSecondCoefficientDensity period hPeriod kPlus kMinus test point ∂mu

theorem robinJunctionDensity_affine
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothThroatField period hPeriod Real)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction test epsilon) point =
      robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction point +
        epsilon * robinFirstVariationDensity period hPeriod kPlus kMinus
          bulkPlus bulkMinus junction test point +
        epsilon ^ 2 *
          robinSecondCoefficientDensity period hPeriod kPlus kMinus test point := by
  change
    kPlus / 2 *
          (junction point + epsilon * test point -
            throatTrace period hPeriod Real bulkPlus point) ^ 2 +
        kMinus / 2 *
          (junction point + epsilon * test point -
            throatTrace period hPeriod Real bulkMinus point) ^ 2 =
      (kPlus / 2 *
            (junction point - throatTrace period hPeriod Real bulkPlus point) ^ 2 +
          kMinus / 2 *
            (junction point - throatTrace period hPeriod Real bulkMinus point) ^ 2) +
        epsilon *
          ((kPlus *
                (junction point - throatTrace period hPeriod Real bulkPlus point) +
              kMinus *
                (junction point - throatTrace period hPeriod Real bulkMinus point)) *
            test point) +
        epsilon ^ 2 * ((kPlus + kMinus) / 2 * test point ^ 2)
  ring

theorem robinJunctionDensity_continuous
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real) :
    Continuous (robinJunctionDensity period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction) := by
  exact
    (continuous_const.mul
      ((junction.contMDiff_toFun.continuous.sub
        (throatTrace period hPeriod Real bulkPlus).contMDiff_toFun.continuous).pow 2)).add
    (continuous_const.mul
      ((junction.contMDiff_toFun.continuous.sub
        (throatTrace period hPeriod Real bulkMinus).contMDiff_toFun.continuous).pow 2))

theorem robinFirstVariationDensity_continuous
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothThroatField period hPeriod Real) :
    Continuous (robinFirstVariationDensity period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction test) := by
  exact
    (junctionResidual period hPeriod kPlus kMinus bulkPlus bulkMinus junction).contMDiff_toFun.continuous.mul
      test.contMDiff_toFun.continuous

private theorem robinSecondCoefficientDensity_continuous
    (kPlus kMinus : Real)
    (test : SmoothThroatField period hPeriod Real) :
    Continuous (robinSecondCoefficientDensity period hPeriod kPlus kMinus test) := by
  exact continuous_const.mul (test.contMDiff_toFun.continuous.pow 2)

private theorem continuous_integrable
    (function : EffectiveThroat period hPeriod → Real)
    (hContinuous : Continuous function)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable function mu :=
  hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace function)

/-- Exact integrated quadratic expansion of the genuine interface action. -/
theorem robinJunctionAction_affine
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction test epsilon) mu =
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus junction mu +
        epsilon * robinFirstVariation period hPeriod kPlus kMinus
          bulkPlus bulkMinus junction test mu +
        epsilon ^ 2 * robinSecondCoefficient period hPeriod kPlus kMinus test mu := by
  have hBase := continuous_integrable period hPeriod
    (robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus junction)
    (robinJunctionDensity_continuous period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction) mu
  have hFirst := continuous_integrable period hPeriod
    (robinFirstVariationDensity period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction test)
    (robinFirstVariationDensity_continuous period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction test) mu
  have hSecond := continuous_integrable period hPeriod
    (robinSecondCoefficientDensity period hPeriod kPlus kMinus test)
    (robinSecondCoefficientDensity_continuous period hPeriod kPlus kMinus test) mu
  unfold robinJunctionAction robinFirstVariation robinSecondCoefficient
  simp_rw [robinJunctionDensity_affine period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction test epsilon]
  calc
    ∫ point,
        robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus junction point +
            epsilon * robinFirstVariationDensity period hPeriod kPlus kMinus
              bulkPlus bulkMinus junction test point +
          epsilon ^ 2 * robinSecondCoefficientDensity period hPeriod
            kPlus kMinus test point ∂mu =
        (∫ point,
          robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus junction point +
            epsilon * robinFirstVariationDensity period hPeriod kPlus kMinus
              bulkPlus bulkMinus junction test point ∂mu) +
          ∫ point, epsilon ^ 2 *
            robinSecondCoefficientDensity period hPeriod kPlus kMinus test point ∂mu := by
      simpa only [Pi.add_apply] using
        integral_add (hBase.add (hFirst.const_mul epsilon))
          (hSecond.const_mul (epsilon ^ 2))
    _ = ((∫ point,
          robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus junction point ∂mu) +
          ∫ point, epsilon * robinFirstVariationDensity period hPeriod
            kPlus kMinus bulkPlus bulkMinus junction test point ∂mu) +
          ∫ point, epsilon ^ 2 *
            robinSecondCoefficientDensity period hPeriod kPlus kMinus test point ∂mu := by
      exact congrArg (fun value => value +
          ∫ point, epsilon ^ 2 *
            robinSecondCoefficientDensity period hPeriod kPlus kMinus test point ∂mu)
        (by
          simpa only [Pi.add_apply] using
            integral_add hBase (hFirst.const_mul epsilon))
    _ = _ := by
      simp only [integral_const_mul]

/-- The first variation is the derivative of the interface action. -/
theorem robinJunctionAction_affine_hasDerivAt
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real => robinJunctionAction period hPeriod kPlus kMinus
        bulkPlus bulkMinus (junctionAffineCurve period hPeriod junction test epsilon) mu)
      (robinFirstVariation period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction test mu) 0 := by
  letI : Norm Real := Real.normedAddCommGroup.toNorm
  rw [show (fun epsilon : Real => robinJunctionAction period hPeriod kPlus kMinus
      bulkPlus bulkMinus (junctionAffineCurve period hPeriod junction test epsilon) mu) =
      (fun epsilon : Real =>
        robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus junction mu +
          epsilon * robinFirstVariation period hPeriod kPlus kMinus
            bulkPlus bulkMinus junction test mu +
          epsilon ^ 2 * robinSecondCoefficient period hPeriod kPlus kMinus test mu) from by
      funext epsilon
      exact robinJunctionAction_affine period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction test mu epsilon]
  let action := robinJunctionAction period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction mu
  let first := robinFirstVariation period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction test mu
  let second := robinSecondCoefficient period hPeriod kPlus kMinus test mu
  change HasDerivAt
    (fun epsilon : Real => action + epsilon * first + epsilon ^ 2 * second) first 0
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero, zero_mul, zero_pow (by norm_num : (2 : Nat) ≠ 0), add_zero]
  apply (isLittleO_iff_tendsto (fun epsilon hZero => by
    subst epsilon
    simp)).2
  have hRatio :
      (fun epsilon : Real =>
        (action + epsilon * first + epsilon ^ 2 * second - action -
          epsilon • first) / epsilon) =
        (fun epsilon : Real => epsilon * second) := by
    funext epsilon
    change
      (action + epsilon * first + epsilon ^ 2 * second - action -
        epsilon * first) / epsilon = _
    by_cases hEpsilon : epsilon = 0
    · simp [hEpsilon]
    · field_simp
      ring
  rw [hRatio]
  have hContinuous : ContinuousAt (fun epsilon : Real => epsilon * second) 0 := by
    fun_prop
  simpa only [ContinuousAt, zero_mul] using hContinuous

/-- Stationarity means vanishing derivative along every smooth throat test. -/
def RobinStationary
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Prop :=
  ∀ test : SmoothThroatField period hPeriod Real,
    HasDerivAt
      (fun epsilon : Real => robinJunctionAction period hPeriod kPlus kMinus
        bulkPlus bulkMinus (junctionAffineCurve period hPeriod junction test epsilon) mu)
      0 0

/-- Stationarity of the action derives, rather than assumes, weak flux balance. -/
theorem stationary_weak_robin_balance
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (hStationary : RobinStationary period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction mu)
    (test : SmoothThroatField period hPeriod Real) :
    robinFirstVariation period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction test mu = 0 :=
  (robinJunctionAction_affine_hasDerivAt period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction test mu).unique (hStationary test)

/-- Testing with the smooth residual gives its integrated square balance. -/
theorem stationary_residual_sq_integral_zero
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (hStationary : RobinStationary period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction mu) :
    ∫ point, (junctionResidual period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction point) ^ 2 ∂mu = 0 := by
  have hWeak := stationary_weak_robin_balance period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction mu hStationary
    (junctionResidual period hPeriod kPlus kMinus bulkPlus bulkMinus junction)
  simpa only [robinFirstVariation, robinFirstVariationDensity, pow_two] using hWeak

/-- Closure package: exact action derivative and stationary weak balance. -/
theorem scalar_robin_junction_balance_closure
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    (∀ test : SmoothThroatField period hPeriod Real,
      HasDerivAt
        (fun epsilon : Real => robinJunctionAction period hPeriod kPlus kMinus
          bulkPlus bulkMinus (junctionAffineCurve period hPeriod junction test epsilon) mu)
        (robinFirstVariation period hPeriod kPlus kMinus
          bulkPlus bulkMinus junction test mu) 0) ∧
    (RobinStationary period hPeriod kPlus kMinus bulkPlus bulkMinus junction mu →
      ∀ test : SmoothThroatField period hPeriod Real,
        robinFirstVariation period hPeriod kPlus kMinus
          bulkPlus bulkMinus junction test mu = 0) := by
  constructor
  · intro test
    exact robinJunctionAction_affine_hasDerivAt period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction test mu
  · intro hStationary test
    exact stationary_weak_robin_balance period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction mu hStationary test

end

end P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
end JanusFormal
