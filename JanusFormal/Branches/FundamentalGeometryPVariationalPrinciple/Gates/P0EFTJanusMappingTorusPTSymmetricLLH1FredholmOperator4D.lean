import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.InnerProductSpace.Adjoint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D

/-!
# Bounded Fredholm realization of the PT-symmetric LL Jacobi form

The Hilbert space here is exactly the completion for the positive Jacobi
energy inner product constructed from the Hessian of the same PT-symmetric LL
action.  Consequently its bounded Riesz realization on the completion is the
identity.  We prove actual bounded self-adjointness, exact kernel and range,
the standard closed-range/finite-kernel/finite-cokernel Fredholm criterion and
algebraic index zero.

This is only the energy-Hilbert realization.  It does not assert compact
resolvent, comparison or coercivity with an external Sobolev space, or any D10
identification.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology InnerProduct
open MeasureTheory
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Bounded extension of the dense-domain Riesz realization to the completed
Jacobi energy Hilbert space. -/
def completedLLJacobiOperator
    (data : PositiveLLH1Data period hPeriod) :
    LLH1Space period hPeriod data →L[Real] LLH1Space period hPeriod data :=
  ContinuousLinearMap.id Real (LLH1Space period hPeriod data)

@[simp]
theorem completedLLJacobiOperator_apply
    (data : PositiveLLH1Data period hPeriod)
    (field : LLH1Space period hPeriod data) :
    completedLLJacobiOperator period hPeriod data field = field :=
  rfl

/-- The completed operator genuinely extends the previously constructed
strong Riesz operator on its smooth dense domain. -/
theorem completedLLJacobiOperator_extends_smooth
    (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data) :
    completedLLJacobiOperator period hPeriod data
        (llH1SmoothEmbedding period hPeriod data direction) =
      strongLLJacobiH1Operator period hPeriod data direction :=
  rfl

theorem completedLLJacobiOperator_isSymmetric
    (data : PositiveLLH1Data period hPeriod)
    (first second : LLH1Space period hPeriod data) :
    inner Real (completedLLJacobiOperator period hPeriod data first) second =
      inner Real first
        (completedLLJacobiOperator period hPeriod data second) := by
  rfl

/-- Actual self-adjointness in Mathlib's bounded-operator star algebra. -/
theorem completedLLJacobiOperator_isSelfAdjoint
    (data : PositiveLLH1Data period hPeriod) :
    IsSelfAdjoint (completedLLJacobiOperator period hPeriod data) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact completedLLJacobiOperator_isSymmetric period hPeriod data

theorem completedLLJacobiOperator_injective
    (data : PositiveLLH1Data period hPeriod) :
    Function.Injective (completedLLJacobiOperator period hPeriod data) := by
  intro first second hEqual
  exact hEqual

theorem completedLLJacobiOperator_surjective
    (data : PositiveLLH1Data period hPeriod) :
    Function.Surjective (completedLLJacobiOperator period hPeriod data) := by
  intro field
  exact ⟨field, rfl⟩

theorem completedLLJacobiOperator_ker_eq_bot
    (data : PositiveLLH1Data period hPeriod) :
    LinearMap.ker (completedLLJacobiOperator period hPeriod data).toLinearMap =
      ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (completedLLJacobiOperator_injective period hPeriod data)

theorem completedLLJacobiOperator_range_eq_top
    (data : PositiveLLH1Data period hPeriod) :
    LinearMap.range
        (completedLLJacobiOperator period hPeriod data).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr
    (completedLLJacobiOperator_surjective period hPeriod data)

theorem completedLLJacobiOperator_range_isClosed
    (data : PositiveLLH1Data period hPeriod) :
    IsClosed
      (LinearMap.range
        (completedLLJacobiOperator period hPeriod data).toLinearMap :
          Set (LLH1Space period hPeriod data)) := by
  rw [completedLLJacobiOperator_range_eq_top period hPeriod data]
  exact isClosed_univ

/-- Algebraic cokernel of the completed Jacobi operator. -/
abbrev CompletedLLJacobiCokernel
    (data : PositiveLLH1Data period hPeriod) :=
  LLH1Space period hPeriod data ⧸
    LinearMap.range
      (completedLLJacobiOperator period hPeriod data).toLinearMap

/-- The standard Fredholm criterion, stated explicitly because Mathlib has no
general bounded `IsFredholm` predicate. -/
theorem completedLLJacobiOperator_fredholm_criterion
    (data : PositiveLLH1Data period hPeriod) :
    IsClosed
        (LinearMap.range
          (completedLLJacobiOperator period hPeriod data).toLinearMap :
            Set (LLH1Space period hPeriod data)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (completedLLJacobiOperator period hPeriod data).toLinearMap) ∧
      FiniteDimensional Real (CompletedLLJacobiCokernel period hPeriod data) := by
  refine ⟨completedLLJacobiOperator_range_isClosed period hPeriod data,
    ?_, ?_⟩
  · rw [completedLLJacobiOperator_ker_eq_bot period hPeriod data]
    infer_instance
  · change FiniteDimensional Real
      (LLH1Space period hPeriod data ⧸
        LinearMap.range
          (completedLLJacobiOperator period hPeriod data).toLinearMap)
    rw [completedLLJacobiOperator_range_eq_top period hPeriod data]
    infer_instance

/-- Mathlib's algebraic index of the completed bounded Jacobi operator. -/
def completedLLJacobiIndex
    (data : PositiveLLH1Data period hPeriod) : Int :=
  (completedLLJacobiOperator period hPeriod data).toLinearMap.index

theorem completedLLJacobiIndex_zero
    (data : PositiveLLH1Data period hPeriod) :
    completedLLJacobiIndex period hPeriod data = 0 := by
  unfold completedLLJacobiIndex
  rw [LinearMap.index_of_surjective
      (completedLLJacobiOperator_surjective period hPeriod data),
    completedLLJacobiOperator_ker_eq_bot period hPeriod data]
  simp

/-- On embedded smooth fields, the bounded pairing is exactly the Hessian of
the unchanged PT-symmetric differential LL action. -/
theorem completedLLJacobiOperator_smooth_pairing
    (data : PositiveLLH1Data period hPeriod)
    (first second : LLH1Smooth period hPeriod data) :
    inner Real
        (completedLLJacobiOperator period hPeriod data
          (llH1SmoothEmbedding period hPeriod data first))
        (llH1SmoothEmbedding period hPeriod data second) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) data.fields
        first.toTest second.toTest data.mu := by
  rw [completedLLJacobiOperator_extends_smooth]
  exact strongLLJacobiH1Operator_iff_weak_on_smooth
    period hPeriod data first second

/-- The same pairing is the derivative of the weak Euler operator, hence the
mixed second derivative of the same action. -/
theorem completedLLJacobiOperator_pairing_linearizes_action
    (data : PositiveLLH1Data period hPeriod)
    (first second : LLH1Smooth period hPeriod data) :
    HasDerivAt
      (fun epsilon : Real =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod)
          (differentialLLFluxCurve period hPeriod data.fields
            first.toTest epsilon) second.toTest data.mu)
      (inner Real
        (completedLLJacobiOperator period hPeriod data
          (llH1SmoothEmbedding period hPeriod data first))
        (llH1SmoothEmbedding period hPeriod data second)) 0 := by
  letI : IsFiniteMeasure data.mu := data.finiteMeasure
  rw [completedLLJacobiOperator_smooth_pairing]
  exact
    globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
      period hPeriod (finiteSmoothThroatGeneratingFrame period hPeriod)
      data.fields first.toTest second.toTest data.mu

/-- Closure package for the completed positive-energy Jacobi realization. -/
theorem completed_ll_jacobi_fredholm_closure
    (data : PositiveLLH1Data period hPeriod) :
    IsSelfAdjoint (completedLLJacobiOperator period hPeriod data) ∧
      IsClosed
        (LinearMap.range
          (completedLLJacobiOperator period hPeriod data).toLinearMap :
            Set (LLH1Space period hPeriod data)) ∧
      completedLLJacobiIndex period hPeriod data = 0 :=
  ⟨completedLLJacobiOperator_isSelfAdjoint period hPeriod data,
    completedLLJacobiOperator_range_isClosed period hPeriod data,
    completedLLJacobiIndex_zero period hPeriod data⟩

end

end P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
end JanusFormal
