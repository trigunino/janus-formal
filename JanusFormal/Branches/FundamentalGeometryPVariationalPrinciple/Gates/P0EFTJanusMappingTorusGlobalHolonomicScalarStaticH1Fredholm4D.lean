import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.InnerProductSpace.Adjoint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D

/-!
# Fredholm realization of the positive static D8 scalar Jacobi form

The Hilbert space is the completion of the positive time-static Jacobi energy
form from the unchanged global holonomic scalar action.  Its Riesz operator on
the completion is the identity.  It is therefore bounded, self-adjoint,
bijective and Fredholm of index zero, and its smooth pairing is exactly the
same action Hessian.

This operator does not represent the full dynamic Lorentzian scalar sector:
its dense form domain has zero time-frame derivative, whereas the omitted
Lorentzian time coefficient is strictly negative.  No compact-resolvent or
external Sobolev conclusion is made.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology InnerProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

/-- Bounded extension of the static scalar Riesz operator to its energy
Hilbert completion. -/
def completedStaticScalarJacobiOperator
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticScalarEnergyH1 period hPeriod data →L[Real]
      StaticScalarEnergyH1 period hPeriod data :=
  ContinuousLinearMap.id Real (StaticScalarEnergyH1 period hPeriod data)

@[simp]
theorem completedStaticScalarJacobiOperator_apply
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticScalarEnergyH1 period hPeriod data) :
    completedStaticScalarJacobiOperator period hPeriod data field = field :=
  rfl

theorem completedStaticScalarJacobiOperator_extends_smooth
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    completedStaticScalarJacobiOperator period hPeriod data
        (staticScalarEnergyEmbedding period hPeriod data field) =
      strongStaticScalarJacobiRiesz period hPeriod data field :=
  rfl

theorem completedStaticScalarJacobiOperator_isSymmetric
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (first second : StaticScalarEnergyH1 period hPeriod data) :
    inner Real
        (completedStaticScalarJacobiOperator period hPeriod data first) second =
      inner Real first
        (completedStaticScalarJacobiOperator period hPeriod data second) := by
  rfl

/-- Actual bounded self-adjointness in Mathlib's operator star algebra. -/
theorem completedStaticScalarJacobiOperator_isSelfAdjoint
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    IsSelfAdjoint (completedStaticScalarJacobiOperator period hPeriod data) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact completedStaticScalarJacobiOperator_isSymmetric period hPeriod data

theorem completedStaticScalarJacobiOperator_injective
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    Function.Injective
      (completedStaticScalarJacobiOperator period hPeriod data) := by
  intro first second hEqual
  exact hEqual

theorem completedStaticScalarJacobiOperator_surjective
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    Function.Surjective
      (completedStaticScalarJacobiOperator period hPeriod data) := by
  intro field
  exact ⟨field, rfl⟩

theorem completedStaticScalarJacobiOperator_ker_eq_bot
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    LinearMap.ker
        (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap =
      ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (completedStaticScalarJacobiOperator_injective period hPeriod data)

theorem completedStaticScalarJacobiOperator_range_eq_top
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    LinearMap.range
        (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap =
      ⊤ :=
  LinearMap.range_eq_top.mpr
    (completedStaticScalarJacobiOperator_surjective period hPeriod data)

theorem completedStaticScalarJacobiOperator_range_isClosed
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    IsClosed
      (LinearMap.range
        (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap :
          Set (StaticScalarEnergyH1 period hPeriod data)) := by
  rw [completedStaticScalarJacobiOperator_range_eq_top period hPeriod data]
  exact isClosed_univ

abbrev CompletedStaticScalarJacobiCokernel
    (data : PositiveStaticGlobalScalarData period hPeriod) :=
  StaticScalarEnergyH1 period hPeriod data ⧸
    LinearMap.range
      (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap

/-- Explicit standard Fredholm criterion: closed range and finite-dimensional
kernel and cokernel. -/
theorem completedStaticScalarJacobiOperator_fredholm_criterion
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    IsClosed
        (LinearMap.range
          (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap :
            Set (StaticScalarEnergyH1 period hPeriod data)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap) ∧
      FiniteDimensional Real
        (CompletedStaticScalarJacobiCokernel period hPeriod data) := by
  refine ⟨completedStaticScalarJacobiOperator_range_isClosed period hPeriod data,
    ?_, ?_⟩
  · rw [completedStaticScalarJacobiOperator_ker_eq_bot period hPeriod data]
    infer_instance
  · change FiniteDimensional Real
      (StaticScalarEnergyH1 period hPeriod data ⧸
        LinearMap.range
          (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap)
    rw [completedStaticScalarJacobiOperator_range_eq_top period hPeriod data]
    infer_instance

def completedStaticScalarJacobiIndex
    (data : PositiveStaticGlobalScalarData period hPeriod) : Int :=
  (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap.index

theorem completedStaticScalarJacobiIndex_zero
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    completedStaticScalarJacobiIndex period hPeriod data = 0 := by
  unfold completedStaticScalarJacobiIndex
  rw [LinearMap.index_of_surjective
      (completedStaticScalarJacobiOperator_surjective period hPeriod data),
    completedStaticScalarJacobiOperator_ker_eq_bot period hPeriod data]
  simp

/-- Smooth pairing of the completed operator equals the Jacobi/Hessian form
of the unchanged action. -/
theorem completedStaticScalarJacobiOperator_smooth_pairing
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (first second : StaticGlobalScalarTest period hPeriod data) :
    inner Real
        (completedStaticScalarJacobiOperator period hPeriod data
          (staticScalarEnergyEmbedding period hPeriod data first))
        (staticScalarEnergyEmbedding period hPeriod data second) =
      globalHolonomicScalarJacobiForm period hPeriod data.formData
        first.toField second.toField := by
  rw [completedStaticScalarJacobiOperator_extends_smooth]
  exact strongStaticScalarJacobiRiesz_smooth_pairing
    period hPeriod data first second

/-- The same completed pairing is the derivative of the weak Euler operator,
hence the mixed second variation of the same action. -/
theorem completedStaticScalarJacobiOperator_pairing_linearizes_action
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (base direction test : StaticGlobalScalarTest period hPeriod data) :
    HasDerivAt
      (fun epsilon : Real =>
        weakGlobalHolonomicScalarEulerOperator period hPeriod data.formData
          (scalarAffineCurve period hPeriod base.toField direction.toField epsilon)
          test.toField)
      (inner Real
        (completedStaticScalarJacobiOperator period hPeriod data
          (staticScalarEnergyEmbedding period hPeriod data direction))
        (staticScalarEnergyEmbedding period hPeriod data test)) 0 := by
  rw [completedStaticScalarJacobiOperator_smooth_pairing]
  exact weakGlobalHolonomicScalarEulerOperator_hasDerivAt
    period hPeriod data.formData base.toField direction.toField test.toField

/-- Precise scope/no-go statement: every vector represented by this form
domain is time-static, while the omitted dynamic time coefficient is negative. -/
theorem completedStaticScalarJacobiOperator_dynamic_noGo
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (∀ field : StaticGlobalScalarTest period hPeriod data,
        holonomicCovectorComponent period hPeriod field.toField point 0 = 0) ∧
      signature 0 / data.formData.magnitude point 0 < 0 := by
  exact ⟨fun field => field.time_static point,
    lorentz_time_kinetic_coefficient_neg period hPeriod
      data.formData.magnitude data.magnitude_pos point⟩

theorem completed_static_scalar_fredholm_closure
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    IsSelfAdjoint (completedStaticScalarJacobiOperator period hPeriod data) ∧
      IsClosed
        (LinearMap.range
          (completedStaticScalarJacobiOperator period hPeriod data).toLinearMap :
            Set (StaticScalarEnergyH1 period hPeriod data)) ∧
      completedStaticScalarJacobiIndex period hPeriod data = 0 :=
  ⟨completedStaticScalarJacobiOperator_isSelfAdjoint period hPeriod data,
    completedStaticScalarJacobiOperator_range_isClosed period hPeriod data,
    completedStaticScalarJacobiIndex_zero period hPeriod data⟩

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D
end JanusFormal
