import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarRobinJunctionBalance4D

/-!
# Exact Hessian of the scalar Robin junction action

The Hessian of the quadratic Robin action on the genuine compact throat is
the integrated bilinear form with coefficient `kPlus + kMinus`.  This gate
constructs that bilinear map, proves symmetry, its sign and exact kernel
modulo the chosen finite Borel measure, and identifies it with the exact
linearization of the weak balance operator.

The result remains a scalar Robin transmission statement.  It does not
construct geometric normal derivatives, extrinsic curvature, Israel data,
null-junction data, or coercivity in a Sobolev norm.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarRobinJunctionHessian4D

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
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D

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

/-- The selected scalar module in derivative statements. -/
local instance realNormedModule : Module Real Real :=
  NormedField.toNormedSpace.toModule

/-- Pointwise mixed second variation of the Robin density. -/
def robinHessianDensity
    (kPlus kMinus : Real)
    (first second : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) : Real :=
  (kPlus + kMinus) * first point * second point

/-- Integrated mixed Hessian of the Robin action. -/
def robinHessian
    (kPlus kMinus : Real)
    (first second : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, robinHessianDensity period hPeriod kPlus kMinus first second point ∂mu

theorem robinHessianDensity_continuous
    (kPlus kMinus : Real)
    (first second : SmoothThroatField period hPeriod Real) :
    Continuous (robinHessianDensity period hPeriod kPlus kMinus first second) := by
  exact (continuous_const.mul first.contMDiff_toFun.continuous).mul
    second.contMDiff_toFun.continuous

private theorem continuous_integrable
    (function : EffectiveThroat period hPeriod → Real)
    (hContinuous : Continuous function)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable function mu :=
  hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace function)

private theorem robinHessianDensity_integrable
    (kPlus kMinus : Real)
    (first second : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (robinHessianDensity period hPeriod kPlus kMinus first second) mu :=
  continuous_integrable period hPeriod _
    (robinHessianDensity_continuous period hPeriod kPlus kMinus first second) mu

/-- The Hessian is encoded as a genuine bilinear map on smooth throat fields. -/
def robinHessianBilinear
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    SmoothThroatField period hPeriod Real →ₗ[Real]
      SmoothThroatField period hPeriod Real →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun first second => robinHessian period hPeriod kPlus kMinus first second mu)
    (fun first second third => by
      change
        (∫ point, (kPlus + kMinus) * (first point + second point) * third point ∂mu) =
          (∫ point, (kPlus + kMinus) * first point * third point ∂mu) +
            ∫ point, (kPlus + kMinus) * second point * third point ∂mu
      rw [show (fun point =>
          (kPlus + kMinus) * (first point + second point) * third point) =
          (fun point => (kPlus + kMinus) * first point * third point +
            (kPlus + kMinus) * second point * third point) from by
        funext point
        ring]
      exact integral_add
        (robinHessianDensity_integrable period hPeriod kPlus kMinus first third mu)
        (robinHessianDensity_integrable period hPeriod kPlus kMinus second third mu))
    (fun scalar first second => by
      change
        (∫ point, (kPlus + kMinus) * (scalar * first point) * second point ∂mu) =
          scalar * ∫ point, (kPlus + kMinus) * first point * second point ∂mu
      rw [show (fun point =>
          (kPlus + kMinus) * (scalar * first point) * second point) =
          (fun point => scalar *
            ((kPlus + kMinus) * first point * second point)) from by
        funext point
        ring]
      simp only [integral_const_mul])
    (fun first second third => by
      change
        (∫ point, (kPlus + kMinus) * first point *
          (second point + third point) ∂mu) =
          (∫ point, (kPlus + kMinus) * first point * second point ∂mu) +
            ∫ point, (kPlus + kMinus) * first point * third point ∂mu
      rw [show (fun point => (kPlus + kMinus) * first point *
          (second point + third point)) =
          (fun point => (kPlus + kMinus) * first point * second point +
            (kPlus + kMinus) * first point * third point) from by
        funext point
        ring]
      exact integral_add
        (robinHessianDensity_integrable period hPeriod kPlus kMinus first second mu)
        (robinHessianDensity_integrable period hPeriod kPlus kMinus first third mu))
    (fun scalar first second => by
      change
        (∫ point, (kPlus + kMinus) * first point *
          (scalar * second point) ∂mu) =
          scalar * ∫ point, (kPlus + kMinus) * first point * second point ∂mu
      rw [show (fun point => (kPlus + kMinus) * first point *
          (scalar * second point)) =
          (fun point => scalar *
            ((kPlus + kMinus) * first point * second point)) from by
        funext point
        ring]
      simp only [integral_const_mul])

@[simp]
theorem robinHessianBilinear_apply
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : SmoothThroatField period hPeriod Real) :
    robinHessianBilinear period hPeriod kPlus kMinus mu first second =
      robinHessian period hPeriod kPlus kMinus first second mu :=
  rfl

/-- The exact mixed Hessian is symmetric for arbitrary real couplings. -/
theorem robinHessian_symmetric
    (kPlus kMinus : Real)
    (first second : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    robinHessian period hPeriod kPlus kMinus first second mu =
      robinHessian period hPeriod kPlus kMinus second first mu := by
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [robinHessianDensity]
  ring

/-- The quadratic Hessian is its coupling sum times the integrated square. -/
theorem robinHessian_self_eq
    (kPlus kMinus : Real)
    (field : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    robinHessian period hPeriod kPlus kMinus field field mu =
      (kPlus + kMinus) * ∫ point, field point ^ 2 ∂mu := by
  unfold robinHessian robinHessianDensity
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with point
  ring

/-- Nonnegative total coupling gives a positive-semidefinite Hessian. -/
theorem robinHessian_nonnegative
    (kPlus kMinus : Real)
    (hCoupling : 0 ≤ kPlus + kMinus)
    (field : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    0 ≤ robinHessian period hPeriod kPlus kMinus field field mu := by
  rw [robinHessian_self_eq period hPeriod]
  exact mul_nonneg hCoupling (integral_nonneg fun point => sq_nonneg (field point))

/-- In particular, two nonnegative Robin couplings give a semidefinite Hessian. -/
theorem robinHessian_nonnegative_of_couplings
    (kPlus kMinus : Real)
    (hPlus : 0 ≤ kPlus) (hMinus : 0 ≤ kMinus)
    (field : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    0 ≤ robinHessian period hPeriod kPlus kMinus field field mu :=
  robinHessian_nonnegative period hPeriod kPlus kMinus
    (add_nonneg hPlus hMinus) field mu

/-- Negative total coupling gives the corresponding negative-semidefinite form. -/
theorem robinHessian_nonpositive
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≤ 0)
    (field : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    robinHessian period hPeriod kPlus kMinus field field mu ≤ 0 := by
  rw [robinHessian_self_eq period hPeriod]
  exact mul_nonpos_of_nonpos_of_nonneg hCoupling
    (integral_nonneg fun point => sq_nonneg (field point))

/-- For nonzero total coupling, the exact quadratic kernel is equality to zero
almost everywhere for the selected measure. -/
theorem robinHessian_self_eq_zero_iff_ae_zero
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (field : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    robinHessian period hPeriod kPlus kMinus field field mu = 0 ↔
      ∀ᵐ point ∂mu, field point = 0 := by
  have hSquareIntegrable : Integrable (fun point => field point ^ 2) mu :=
    continuous_integrable period hPeriod _
      (field.contMDiff_toFun.continuous.pow 2) mu
  rw [robinHessian_self_eq period hPeriod]
  constructor
  · intro hZero
    have hIntegral : ∫ point, field point ^ 2 ∂mu = 0 :=
      (mul_eq_zero.mp hZero).resolve_left hCoupling
    have hSquareZero : (fun point => field point ^ 2) =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun point => sq_nonneg (field point)) hSquareIntegrable).mp hIntegral
    filter_upwards [hSquareZero] with point hPoint
    exact sq_eq_zero_iff.mp hPoint
  · intro hZero
    have hSquareZero : (fun point => field point ^ 2) =ᵐ[mu] 0 := by
      filter_upwards [hZero] with point hPoint
      simp [hPoint]
    rw [integral_congr_ae hSquareZero]
    simp

/-- If the coupling sum vanishes, the full bilinear Hessian vanishes. -/
theorem robinHessian_eq_zero_of_coupling_sum_eq_zero
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus = 0)
    (first second : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    robinHessian period hPeriod kPlus kMinus first second mu = 0 := by
  simp [robinHessian, robinHessianDensity, hCoupling]

/-- The first-variation density changes exactly by the Hessian density. -/
theorem robinFirstVariationDensity_affine
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction test : SmoothThroatField period hPeriod Real)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    robinFirstVariationDensity period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction direction epsilon) test point =
      robinFirstVariationDensity period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction test point +
        epsilon * robinHessianDensity period hPeriod kPlus kMinus direction test point := by
  change
    ((kPlus *
          (junction point + epsilon * direction point -
            throatTrace period hPeriod Real bulkPlus point) +
        kMinus *
          (junction point + epsilon * direction point -
            throatTrace period hPeriod Real bulkMinus point)) * test point) =
      (kPlus *
            (junction point - throatTrace period hPeriod Real bulkPlus point) +
          kMinus *
            (junction point - throatTrace period hPeriod Real bulkMinus point)) * test point +
        epsilon * ((kPlus + kMinus) * direction point * test point)
  ring

/-- Exact affine linearization of the integrated weak balance. -/
theorem robinFirstVariation_affine
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction direction epsilon) test mu =
      robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction test mu +
        epsilon * robinHessian period hPeriod kPlus kMinus direction test mu := by
  have hBase := continuous_integrable period hPeriod
    (robinFirstVariationDensity period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction test)
    (robinFirstVariationDensity_continuous period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction test) mu
  have hHessian := robinHessianDensity_integrable period hPeriod
    kPlus kMinus direction test mu
  unfold robinFirstVariation robinHessian
  simp_rw [robinFirstVariationDensity_affine period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction direction test epsilon]
  rw [integral_add hBase (hHessian.const_mul epsilon), integral_const_mul]

/-- Weak balance as a linear functional of its smooth test field. -/
def robinWeakBalanceOperator
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    SmoothThroatField period hPeriod Real →ₗ[Real] Real where
  toFun test := robinFirstVariation period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction test mu
  map_add' first second := by
    have hFirst := continuous_integrable period hPeriod
      (robinFirstVariationDensity period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction first)
      (robinFirstVariationDensity_continuous period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction first) mu
    have hSecond := continuous_integrable period hPeriod
      (robinFirstVariationDensity period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction second)
      (robinFirstVariationDensity_continuous period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction second) mu
    unfold robinFirstVariation robinFirstVariationDensity
    change
      (∫ point, junctionResidual period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction point * (first point + second point) ∂mu) = _
    rw [show (fun point => junctionResidual period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction point * (first point + second point)) =
        (fun point => junctionResidual period hPeriod kPlus kMinus
          bulkPlus bulkMinus junction point * first point +
          junctionResidual period hPeriod kPlus kMinus bulkPlus bulkMinus
            junction point * second point) from by
      funext point
      ring]
    exact integral_add hFirst hSecond
  map_smul' scalar test := by
    unfold robinFirstVariation robinFirstVariationDensity
    change
      (∫ point, junctionResidual period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction point * (scalar * test point) ∂mu) =
        scalar * ∫ point, junctionResidual period hPeriod kPlus kMinus
          bulkPlus bulkMinus junction point * test point ∂mu
    rw [show (fun point => junctionResidual period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction point * (scalar * test point)) =
        (fun point => scalar *
          (junctionResidual period hPeriod kPlus kMinus bulkPlus bulkMinus
            junction point * test point)) from by
      funext point
      ring]
    simp only [integral_const_mul]

/-- Operator-level exact linearization: no remainder term is present. -/
theorem robinWeakBalanceOperator_affine
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    robinWeakBalanceOperator period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction direction epsilon) mu =
      robinWeakBalanceOperator period hPeriod kPlus kMinus bulkPlus bulkMinus junction mu +
        epsilon • robinHessianBilinear period hPeriod kPlus kMinus mu direction := by
  ext test
  change
    robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction direction epsilon) test mu =
      robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction test mu +
        epsilon * robinHessian period hPeriod kPlus kMinus direction test mu
  exact robinFirstVariation_affine period hPeriod kPlus kMinus bulkPlus bulkMinus
    junction direction test mu epsilon

/-- The Hessian is the derivative of the weak balance operator in every test
direction, hence the mixed second variation of the Robin action. -/
theorem robinWeakBalance_linearized_hasDerivAt
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real =>
        robinWeakBalanceOperator period hPeriod kPlus kMinus bulkPlus bulkMinus
          (junctionAffineCurve period hPeriod junction direction epsilon) mu test)
      (robinHessianBilinear period hPeriod kPlus kMinus mu direction test) 0 := by
  rw [show (fun epsilon : Real =>
      robinWeakBalanceOperator period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction direction epsilon) mu test) =
      (fun epsilon : Real =>
        robinWeakBalanceOperator period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction mu test +
        epsilon * robinHessianBilinear period hPeriod kPlus kMinus mu direction test) from by
    funext epsilon
    exact congrArg (fun operator => operator test)
      (robinWeakBalanceOperator_affine period hPeriod kPlus kMinus bulkPlus bulkMinus
        junction direction mu epsilon)]
  let base := robinWeakBalanceOperator period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction mu test
  let tangent := robinHessianBilinear period hPeriod kPlus kMinus mu direction test
  change HasDerivAt (fun epsilon : Real => base + epsilon * tangent) tangent 0
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero, zero_mul, add_zero]
  have hZero :
      (fun epsilon : Real =>
        base + epsilon * tangent - base - epsilon • tangent) =
        (fun _ => 0) := by
    funext epsilon
    change base + epsilon * tangent - base - epsilon * tangent = 0
    ring
  rw [hZero]
  exact isLittleO_zero (E' := Real)
    (g' := fun epsilon : Real => epsilon) (l := 𝓝 (0 : Real))

/-- Compact closure package for the exact Hessian and its weak linearization. -/
theorem scalar_robin_junction_hessian_closure
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    (∀ first second : SmoothThroatField period hPeriod Real,
      robinHessian period hPeriod kPlus kMinus first second mu =
        robinHessian period hPeriod kPlus kMinus second first mu) ∧
    (∀ direction test : SmoothThroatField period hPeriod Real,
      HasDerivAt
        (fun epsilon : Real =>
          robinWeakBalanceOperator period hPeriod kPlus kMinus bulkPlus bulkMinus
            (junctionAffineCurve period hPeriod junction direction epsilon) mu test)
        (robinHessian period hPeriod kPlus kMinus direction test mu) 0) := by
  constructor
  · exact fun first second =>
      robinHessian_symmetric period hPeriod kPlus kMinus first second mu
  · intro direction test
    exact robinWeakBalance_linearized_hasDerivAt period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction direction test mu

end

end P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
end JanusFormal
