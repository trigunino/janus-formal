import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarStaticCoerciveVariationalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalHolonomicScalarActionReconstruction4D

/-!
# Physical action bridge for the positive static scalar sector

The positive static completion was built from the Jacobi form of the unchanged
global scalar action.  This file records the exact action-level identification:
on every smooth static field, the completed quadratic source action is the
unchanged global action with its Hessian source coupling.

Thus the static coercive minimizer is a minimizer of the physical scalar action
restricted to the positive time-static sector.  No identification with the
full Lorentzian dynamic Hessian or with the independent intrinsic elliptic
regulator is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarStaticPhysicalActionBridge4D

set_option autoImplicit false
noncomputable section

open scoped InnerProduct
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStaticCoerciveVariationalClosure4D
open P0EFTJanusGlobalHolonomicScalarActionReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The unchanged global action restricted to static fields, with the linear
source coupling supplied by its genuine mixed Hessian. -/
def globalHolonomicStaticScalarSourcedAction
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source field : StaticGlobalScalarTest period hPeriod data) : Real :=
  globalHolonomicScalarAction period hPeriod data.formData.massSquared
      data.formData.magnitude field.toField data.formData.measure -
    globalHolonomicScalarActionMixedHessian period hPeriod data.formData
      (0 : GlobalScalarTestSpace period hPeriod) source.toField field.toField

/-- The canonical embedding of the smooth static core into its energy
completion is injective. -/
theorem staticScalarEnergyEmbedding_injective
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    Function.Injective (staticScalarEnergyEmbedding period hPeriod data) := by
  intro first second h
  change (first : StaticScalarEnergyH1 period hPeriod data) =
    (second : StaticScalarEnergyH1 period hPeriod data) at h
  exact UniformSpace.Completion.coe_injective _ h

/-- Half the squared completed energy norm is exactly the unchanged physical
scalar action on the smooth static core. -/
theorem staticScalarQuadraticAction_smooth_eq_globalHolonomicScalarAction
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    (1 / 2 : Real) *
        ‖staticScalarEnergyEmbedding period hPeriod data field‖ ^ 2 =
      globalHolonomicScalarAction period hPeriod data.formData.massSquared
        data.formData.magnitude field.toField data.formData.measure := by
  rw [← real_inner_self_eq_norm_sq]
  change (1 / 2 : Real) *
      inner Real
        (strongStaticScalarJacobiRiesz period hPeriod data field)
        (staticScalarEnergyEmbedding period hPeriod data field) = _
  rw [strongStaticScalarJacobiRiesz_smooth_pairing period hPeriod data]
  rw [globalHolonomicScalarAction_eq_half_actualMixedHessian period hPeriod
    data.formData field.toField field.toField]
  rw [globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod
    data.formData field.toField field.toField field.toField]
  rfl

/-- The completed source pairing is the genuine mixed Hessian coupling of the
unchanged physical action. -/
theorem staticScalarSourcePairing_smooth_eq_actualMixedHessian
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source field : StaticGlobalScalarTest period hPeriod data) :
    inner Real
        (staticScalarEnergyEmbedding period hPeriod data source)
        (staticScalarEnergyEmbedding period hPeriod data field) =
      globalHolonomicScalarActionMixedHessian period hPeriod data.formData
        (0 : GlobalScalarTestSpace period hPeriod) source.toField
          field.toField := by
  rw [globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod
    data.formData]
  exact strongStaticScalarJacobiRiesz_smooth_pairing
    period hPeriod data source field

/-- Exact pullback of the completed coercive source action to the unchanged
physical scalar action on the static smooth core. -/
theorem staticScalarSourceAction_smooth_eq_physicalAction
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source field : StaticGlobalScalarTest period hPeriod data) :
    staticScalarSourceAction period hPeriod data
        (staticScalarEnergyEmbedding period hPeriod data source)
        (staticScalarEnergyEmbedding period hPeriod data field) =
      globalHolonomicStaticScalarSourcedAction period hPeriod data
        source field := by
  unfold staticScalarSourceAction globalHolonomicStaticScalarSourcedAction
  rw [staticScalarQuadraticAction_smooth_eq_globalHolonomicScalarAction
      period hPeriod data field,
    staticScalarSourcePairing_smooth_eq_actualMixedHessian
      period hPeriod data source field]

/-- With zero source, the completed action restricts exactly to the unchanged
global scalar action. -/
theorem staticScalarSourceAction_zero_smooth_eq_globalHolonomicScalarAction
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    staticScalarSourceAction period hPeriod data 0
        (staticScalarEnergyEmbedding period hPeriod data field) =
      globalHolonomicScalarAction period hPeriod data.formData.massSquared
        data.formData.magnitude field.toField data.formData.measure := by
  unfold staticScalarSourceAction
  simp only [inner_zero_left, sub_zero]
  exact staticScalarQuadraticAction_smooth_eq_globalHolonomicScalarAction
    period hPeriod data field

/-- Exact square completion of the sourced physical action on the static
smooth core. -/
theorem globalHolonomicStaticScalarSourcedAction_completion
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source field : StaticGlobalScalarTest period hPeriod data) :
    globalHolonomicStaticScalarSourcedAction period hPeriod data source field =
      globalHolonomicStaticScalarSourcedAction period hPeriod data source
          source +
        (1 / 2 : Real) *
          ‖staticScalarEnergyEmbedding period hPeriod data (field - source)‖ ^ 2 := by
  have hCompletion :=
    staticScalarSourceAction_completion period hPeriod data
      (staticScalarEnergyEmbedding period hPeriod data source)
      (staticScalarEnergyEmbedding period hPeriod data field)
  rw [staticScalarSourceSolution_apply] at hCompletion
  rw [staticScalarSourceAction_smooth_eq_physicalAction period hPeriod data
      source field,
    staticScalarSourceAction_smooth_eq_physicalAction period hPeriod data
      source source] at hCompletion
  simpa only [map_sub] using hCompletion

/-- The smooth source field is the unique global minimizer of the physical
source action inside the smooth positive static sector. -/
theorem globalHolonomicStaticScalarSourcedAction_unique_minimizer
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticGlobalScalarTest period hPeriod data) :
    (∀ field : StaticGlobalScalarTest period hPeriod data,
      globalHolonomicStaticScalarSourcedAction period hPeriod data source
          source ≤
        globalHolonomicStaticScalarSourcedAction period hPeriod data source
          field) ∧
      (∀ field : StaticGlobalScalarTest period hPeriod data,
        globalHolonomicStaticScalarSourcedAction period hPeriod data source
            field =
          globalHolonomicStaticScalarSourcedAction period hPeriod data source
            source →
        field = source) := by
  constructor
  · intro field
    rw [globalHolonomicStaticScalarSourcedAction_completion period hPeriod
      data source field]
    nlinarith [sq_nonneg
      ‖staticScalarEnergyEmbedding period hPeriod data (field - source)‖]
  · intro field hAction
    apply staticScalarEnergyEmbedding_injective period hPeriod data
    have hCompleted :
        staticScalarSourceAction period hPeriod data
            (staticScalarEnergyEmbedding period hPeriod data source)
            (staticScalarEnergyEmbedding period hPeriod data field) =
          staticScalarSourceAction period hPeriod data
            (staticScalarEnergyEmbedding period hPeriod data source)
            (staticScalarEnergyEmbedding period hPeriod data source) := by
      rw [staticScalarSourceAction_smooth_eq_physicalAction period hPeriod
          data source field,
        staticScalarSourceAction_smooth_eq_physicalAction period hPeriod
          data source source]
      exact hAction
    have hUnique :=
      (staticScalarSourceSolution_unique_minimizer period hPeriod data
        (staticScalarEnergyEmbedding period hPeriod data source)).2
        (staticScalarEnergyEmbedding period hPeriod data field) hCompleted
    simpa only [staticScalarSourceSolution_apply] using hUnique

/-- On the smooth core, the completed Riesz operator pairing is exactly the
actual mixed Hessian of the unchanged global action. -/
theorem completedStaticScalarJacobiOperator_smooth_pairing_eq_actualHessian
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (base first second : StaticGlobalScalarTest period hPeriod data) :
    inner Real
        (completedStaticScalarJacobiOperator period hPeriod data
          (staticScalarEnergyEmbedding period hPeriod data first))
        (staticScalarEnergyEmbedding period hPeriod data second) =
      globalHolonomicScalarActionMixedHessian period hPeriod data.formData
        base.toField first.toField second.toField := by
  rw [completedStaticScalarJacobiOperator_smooth_pairing period hPeriod data]
  rw [globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod
    data.formData]
  rfl

/-- Complete physical-action identification certificate for the positive
static scalar sector. -/
theorem canonicalPhysicalScalarStaticPhysicalActionBridge_certificate
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticGlobalScalarTest period hPeriod data) :
    (∀ field : StaticGlobalScalarTest period hPeriod data,
      staticScalarSourceAction period hPeriod data
          (staticScalarEnergyEmbedding period hPeriod data source)
          (staticScalarEnergyEmbedding period hPeriod data field) =
        globalHolonomicStaticScalarSourcedAction period hPeriod data
          source field) ∧
      (∀ base first second : StaticGlobalScalarTest period hPeriod data,
        inner Real
            (completedStaticScalarJacobiOperator period hPeriod data
              (staticScalarEnergyEmbedding period hPeriod data first))
            (staticScalarEnergyEmbedding period hPeriod data second) =
          globalHolonomicScalarActionMixedHessian period hPeriod data.formData
            base.toField first.toField second.toField) ∧
      (∀ field : StaticGlobalScalarTest period hPeriod data,
        globalHolonomicStaticScalarSourcedAction period hPeriod data source
            source ≤
          globalHolonomicStaticScalarSourcedAction period hPeriod data source
            field) ∧
      (∀ field : StaticGlobalScalarTest period hPeriod data,
        globalHolonomicStaticScalarSourcedAction period hPeriod data source
            field =
          globalHolonomicStaticScalarSourcedAction period hPeriod data source
            source →
        field = source) := by
  exact
    ⟨staticScalarSourceAction_smooth_eq_physicalAction
        period hPeriod data source,
      completedStaticScalarJacobiOperator_smooth_pairing_eq_actualHessian
        period hPeriod data,
      (globalHolonomicStaticScalarSourcedAction_unique_minimizer
        period hPeriod data source).1,
      (globalHolonomicStaticScalarSourcedAction_unique_minimizer
        period hPeriod data source).2⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalScalarStaticPhysicalActionBridge4D
end JanusFormal
