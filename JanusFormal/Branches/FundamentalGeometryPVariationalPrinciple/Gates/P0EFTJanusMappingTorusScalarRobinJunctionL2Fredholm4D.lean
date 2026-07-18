import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.InnerProductSpace.Adjoint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarRobinJunctionHessian4D

/-!
# The Robin junction Hessian on the genuine throat L2 space

For a finite Borel measure on the actual compact throat, the scalar Robin
Hessian extends to the bounded operator `(kPlus + kMinus) • id` on genuine
`L2`.  It is self-adjoint.  If the coupling sum is nonzero, its kernel is
zero, its range is the full closed space, it satisfies the standard Fredholm
criterion, and its algebraic index is zero.  Pairing smooth inclusions recovers
the exact Hessian of the previously fixed action.

Mathlib currently has no general `IsFredholm` predicate for bounded operators,
so the criterion is stated explicitly as closed range plus finite-dimensional
kernel and cokernel, following the repository's existing Fredholm gates.
This does not add an intrinsic throat volume measure, Sobolev coercivity,
geometric normal derivatives, an Israel condition, or a null junction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal InnerProduct
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D

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

/-- Genuine scalar `L2` on the actual throat and the selected measure. -/
abbrev ThroatScalarL2
    (mu : Measure (EffectiveThroat period hPeriod)) :=
  Lp Real (2 : ENNReal) mu

/-- The bounded `L2` Hessian selected by the already fixed Robin action. -/
def robinL2HessianOperator
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    ThroatScalarL2 period hPeriod mu →L[Real]
      ThroatScalarL2 period hPeriod mu :=
  (kPlus + kMinus) •
    ContinuousLinearMap.id Real (ThroatScalarL2 period hPeriod mu)

@[simp]
theorem robinL2HessianOperator_apply
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod))
    (field : ThroatScalarL2 period hPeriod mu) :
    robinL2HessianOperator period hPeriod kPlus kMinus mu field =
      (kPlus + kMinus) • field := by
  simp [robinL2HessianOperator]

/-- The bounded Hessian is symmetric for the genuine `L2` inner product. -/
theorem robinL2HessianOperator_isSymmetric
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod))
    (first second : ThroatScalarL2 period hPeriod mu) :
    inner Real
        (robinL2HessianOperator period hPeriod kPlus kMinus mu first) second =
      inner Real first
        (robinL2HessianOperator period hPeriod kPlus kMinus mu second) := by
  rw [robinL2HessianOperator_apply, robinL2HessianOperator_apply,
    real_inner_smul_left, real_inner_smul_right]

/-- Actual self-adjointness in Mathlib's bounded-operator star algebra. -/
theorem robinL2HessianOperator_isSelfAdjoint
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    IsSelfAdjoint (robinL2HessianOperator period hPeriod kPlus kMinus mu) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact robinL2HessianOperator_isSymmetric period hPeriod kPlus kMinus mu

/-- Nonzero coupling sum makes the `L2` Hessian injective. -/
theorem robinL2HessianOperator_injective
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    Function.Injective (robinL2HessianOperator period hPeriod kPlus kMinus mu) := by
  intro first second hEqual
  apply (smul_right_injective
    (M := ThroatScalarL2 period hPeriod mu) hCoupling)
  simpa only [robinL2HessianOperator_apply] using hEqual

/-- Nonzero coupling sum makes the `L2` Hessian surjective. -/
theorem robinL2HessianOperator_surjective
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    Function.Surjective (robinL2HessianOperator period hPeriod kPlus kMinus mu) := by
  intro field
  refine ⟨(kPlus + kMinus)⁻¹ • field, ?_⟩
  rw [robinL2HessianOperator_apply, smul_smul,
    mul_inv_cancel₀ hCoupling, one_smul]

/-- Exact kernel for nonzero total coupling. -/
theorem robinL2HessianOperator_ker_eq_bot
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    LinearMap.ker
        (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (robinL2HessianOperator_injective period hPeriod
      kPlus kMinus hCoupling mu)

/-- Exact full range for nonzero total coupling. -/
theorem robinL2HessianOperator_range_eq_top
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    LinearMap.range
        (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr
    (robinL2HessianOperator_surjective period hPeriod
      kPlus kMinus hCoupling mu)

/-- The kernel of the continuous Hessian is closed for all couplings. -/
theorem robinL2HessianOperator_ker_isClosed
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    IsClosed
      (LinearMap.ker
        (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap :
          Set (ThroatScalarL2 period hPeriod mu)) :=
  (robinL2HessianOperator period hPeriod kPlus kMinus mu).isClosed_ker

/-- For nonzero coupling sum, the full range is closed. -/
theorem robinL2HessianOperator_range_isClosed
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    IsClosed
      (LinearMap.range
        (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap :
          Set (ThroatScalarL2 period hPeriod mu)) := by
  rw [robinL2HessianOperator_range_eq_top period hPeriod
    kPlus kMinus hCoupling mu]
  exact isClosed_univ

/-- Algebraic cokernel of the bounded throat Hessian. -/
abbrev RobinL2HessianCokernel
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :=
  ThroatScalarL2 period hPeriod mu ⧸
    LinearMap.range
      (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap

/-- The standard Fredholm criterion: closed range and finite-dimensional
kernel and cokernel.  No unavailable abstract predicate is postulated. -/
theorem robinL2HessianOperator_fredholm_criterion
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    IsClosed
        (LinearMap.range
          (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap :
            Set (ThroatScalarL2 period hPeriod mu)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap) ∧
      FiniteDimensional Real
        (RobinL2HessianCokernel period hPeriod kPlus kMinus mu) := by
  refine ⟨robinL2HessianOperator_range_isClosed period hPeriod
    kPlus kMinus hCoupling mu, ?_, ?_⟩
  · rw [robinL2HessianOperator_ker_eq_bot period hPeriod
      kPlus kMinus hCoupling mu]
    infer_instance
  · change FiniteDimensional Real
      (ThroatScalarL2 period hPeriod mu ⧸
        LinearMap.range
          (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap)
    rw [robinL2HessianOperator_range_eq_top period hPeriod
      kPlus kMinus hCoupling mu]
    infer_instance

/-- Mathlib's algebraic index of the bounded Robin Hessian. -/
def robinL2HessianIndex
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Int :=
  (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap.index

/-- The nondegenerate Robin Hessian has index zero. -/
theorem robinL2HessianIndex_zero
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    robinL2HessianIndex period hPeriod kPlus kMinus mu = 0 := by
  unfold robinL2HessianIndex
  rw [LinearMap.index_of_surjective
    (robinL2HessianOperator_surjective period hPeriod
      kPlus kMinus hCoupling mu),
    robinL2HessianOperator_ker_eq_bot period hPeriod
      kPlus kMinus hCoupling mu]
  simp

/-- Canonical inclusion of a smooth throat scalar into genuine throat `L2`. -/
def smoothThroatFieldToL2
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothThroatField period hPeriod Real) :
    ThroatScalarL2 period hPeriod mu :=
  (smoothThroatField_memLp period hPeriod Real mu field).toLp field.toFun

theorem smoothThroatFieldToL2_ae
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothThroatField period hPeriod Real) :
    (smoothThroatFieldToL2 period hPeriod mu field :
      EffectiveThroat period hPeriod → Real) =ᵐ[mu] field.toFun :=
  (smoothThroatField_memLp period hPeriod Real mu field).coeFn_toLp

/-- The genuine `L2` inner product restricts to the integrated smooth pairing. -/
theorem smoothThroatFieldToL2_inner
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : SmoothThroatField period hPeriod Real) :
    inner Real
        (smoothThroatFieldToL2 period hPeriod mu first)
        (smoothThroatFieldToL2 period hPeriod mu second) =
      ∫ point, first point * second point ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [smoothThroatFieldToL2_ae period hPeriod mu first,
      smoothThroatFieldToL2_ae period hPeriod mu second]
    with point hFirst hSecond
  rw [hFirst, hSecond]
  exact Real.inner_apply _ _

/-- Pairing the bounded operator on smooth inclusions is exactly the Hessian
of the same Robin action, with no changed density or extra conclusion. -/
theorem robinL2HessianOperator_smooth_pairing
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : SmoothThroatField period hPeriod Real) :
    inner Real
        (robinL2HessianOperator period hPeriod kPlus kMinus mu
          (smoothThroatFieldToL2 period hPeriod mu first))
        (smoothThroatFieldToL2 period hPeriod mu second) =
      robinHessian period hPeriod kPlus kMinus first second mu := by
  rw [robinL2HessianOperator_apply, real_inner_smul_left,
    smoothThroatFieldToL2_inner]
  unfold robinHessian robinHessianDensity
  calc
    (kPlus + kMinus) * ∫ point, first point * second point ∂mu =
        ∫ point, (kPlus + kMinus) * (first point * second point) ∂mu := by
      symm
      exact integral_const_mul (L := Real) (μ := mu) (kPlus + kMinus)
        (fun point : EffectiveThroat period hPeriod => first point * second point)
    _ = ∫ point, (kPlus + kMinus) * first point * second point ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with point
      ring

/-- The same `L2` pairing is the actual derivative of the weak balance, hence
the mixed second variation of the already fixed Robin action. -/
theorem robinL2HessianOperator_pairing_linearizes_action
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real =>
        robinWeakBalanceOperator period hPeriod kPlus kMinus bulkPlus bulkMinus
          (junctionAffineCurve period hPeriod junction direction epsilon) mu test)
      (inner Real
        (robinL2HessianOperator period hPeriod kPlus kMinus mu
          (smoothThroatFieldToL2 period hPeriod mu direction))
        (smoothThroatFieldToL2 period hPeriod mu test)) 0 := by
  rw [robinL2HessianOperator_smooth_pairing period hPeriod]
  exact robinWeakBalance_linearized_hasDerivAt period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction direction test mu

/-- Closure package for the nondegenerate bounded Hessian. -/
theorem scalar_robin_junction_l2_fredholm_closure
    (kPlus kMinus : Real)
    (hCoupling : kPlus + kMinus ≠ 0)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    IsSelfAdjoint (robinL2HessianOperator period hPeriod kPlus kMinus mu) ∧
      IsClosed
        (LinearMap.range
          (robinL2HessianOperator period hPeriod kPlus kMinus mu).toLinearMap :
            Set (ThroatScalarL2 period hPeriod mu)) ∧
      robinL2HessianIndex period hPeriod kPlus kMinus mu = 0 := by
  exact ⟨robinL2HessianOperator_isSelfAdjoint period hPeriod kPlus kMinus mu,
    robinL2HessianOperator_range_isClosed period hPeriod
      kPlus kMinus hCoupling mu,
    robinL2HessianIndex_zero period hPeriod kPlus kMinus hCoupling mu⟩

end

end P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
end JanusFormal
