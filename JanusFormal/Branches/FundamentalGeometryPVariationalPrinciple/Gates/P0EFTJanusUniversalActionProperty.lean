import Mathlib

namespace JanusFormal
namespace P0EFTJanusUniversalActionProperty

set_option autoImplicit false

/-- One-dimensional quadratic action used to isolate the universal-property logic. -/
@[ext] structure QuadraticAction where
  hessian : ℝ
  linear : ℝ
  constant : ℝ

/-- Action value. -/
noncomputable def actionValue
    (action : QuadraticAction)
    (coordinate : ℝ) : ℝ :=
  action.hessian * coordinate ^ 2 / 2 +
    action.linear * coordinate + action.constant

/-- First derivative. -/
def actionGradient (action : QuadraticAction) (coordinate : ℝ) : ℝ :=
  action.hessian * coordinate + action.linear

/-- Add an affine functional, which is invisible to the Hessian. -/
def affineShift
    (action : QuadraticAction)
    (linearShift constantShift : ℝ) : QuadraticAction :=
  { hessian := action.hessian
    linear := action.linear + linearShift
    constant := action.constant + constantShift }

/-- Affine shifts leave the Hessian coefficient unchanged. -/
@[simp] theorem affine_shift_preserves_hessian
    (action : QuadraticAction)
    (linearShift constantShift : ℝ) :
    (affineShift action linearShift constantShift).hessian =
      action.hessian := by
  rfl

/-- Actions with the same Hessian differ by an affine functional. -/
theorem same_hessian_difference_is_affine
    (first second : QuadraticAction)
    (hHessian : first.hessian = second.hessian)
    (coordinate : ℝ) :
    actionValue first coordinate - actionValue second coordinate =
      (first.linear - second.linear) * coordinate +
        (first.constant - second.constant) := by
  unfold actionValue
  rw [hHessian]
  ring

/-- Bare Hessian data never determine an action uniquely. -/
theorem fixed_hessian_supports_distinct_actions
    (hessian : ℝ) :
    ∃ first second : QuadraticAction,
      first.hessian = hessian /\
      second.hessian = hessian /\
      first ≠ second := by
  refine ⟨
    { hessian := hessian, linear := 0, constant := 0 },
    { hessian := hessian, linear := 1, constant := 0 },
    rfl, rfl, ?_⟩
  intro hEqual
  have hLinear := congrArg QuadraticAction.linear hEqual
  norm_num at hLinear

/-- Data sufficient to characterize a normalized quadratic action. -/
structure ActionSpecification where
  hessian : ℝ
  criticalPoint : ℝ
  referenceValue : ℝ
  hessianNonzero : hessian ≠ 0

/-- Canonical action realizing the full specification. -/
noncomputable def canonicalAction
    (specification : ActionSpecification) : QuadraticAction :=
  { hessian := specification.hessian
    linear := -specification.hessian * specification.criticalPoint
    constant := specification.referenceValue +
      specification.hessian * specification.criticalPoint ^ 2 / 2 }

/-- Realization predicate for the relative universal property. -/
def RealizesSpecification
    (specification : ActionSpecification)
    (action : QuadraticAction) : Prop :=
  action.hessian = specification.hessian /\
  actionGradient action specification.criticalPoint = 0 /\
  actionValue action specification.criticalPoint =
    specification.referenceValue

/-- The canonical action has the requested Hessian. -/
@[simp] theorem canonical_action_hessian
    (specification : ActionSpecification) :
    (canonicalAction specification).hessian = specification.hessian := by
  rfl

/-- The requested point is critical. -/
theorem canonical_action_critical
    (specification : ActionSpecification) :
    actionGradient (canonicalAction specification)
      specification.criticalPoint = 0 := by
  unfold actionGradient canonicalAction
  ring

/-- The requested normalization is satisfied. -/
theorem canonical_action_reference_value
    (specification : ActionSpecification) :
    actionValue (canonicalAction specification)
      specification.criticalPoint = specification.referenceValue := by
  unfold actionValue canonicalAction
  ring

/-- Existence of a realization. -/
theorem canonical_action_realizes_specification
    (specification : ActionSpecification) :
    RealizesSpecification specification
      (canonicalAction specification) := by
  exact ⟨canonical_action_hessian specification,
    canonical_action_critical specification,
    canonical_action_reference_value specification⟩

/-- Full Hessian, critical-point and value data determine the action uniquely. -/
theorem realization_action_unique
    (specification : ActionSpecification)
    (action : QuadraticAction)
    (hRealizes : RealizesSpecification specification action) :
    action = canonicalAction specification := by
  rcases hRealizes with ⟨hHessian, hCritical, hValue⟩
  have hLinear :
      action.linear =
        -specification.hessian * specification.criticalPoint := by
    unfold actionGradient at hCritical
    rw [hHessian] at hCritical
    linarith
  have hConstant :
      action.constant = specification.referenceValue +
        specification.hessian * specification.criticalPoint ^ 2 / 2 := by
    unfold actionValue at hValue
    rw [hHessian, hLinear] at hValue
    nlinarith
  apply QuadraticAction.ext
  · exact hHessian
  · simpa [canonicalAction] using hLinear
  · simpa [canonicalAction] using hConstant

/-- Fiber of all actions realizing one specification. -/
def SpecificationFiber
    (specification : ActionSpecification) :=
  { action : QuadraticAction //
    RealizesSpecification specification action }

/-- The realization fiber is nonempty. -/
theorem specification_fiber_nonempty
    (specification : ActionSpecification) :
    Nonempty (SpecificationFiber specification) := by
  exact ⟨⟨canonicalAction specification,
    canonical_action_realizes_specification specification⟩⟩

/-- The realization fiber is a subsingleton. -/
theorem specification_fiber_subsingleton
    (specification : ActionSpecification) :
    Subsingleton (SpecificationFiber specification) := by
  constructor
  intro first second
  apply Subtype.ext
  calc
    first.1 = canonicalAction specification :=
      realization_action_unique specification first.1 first.2
    _ = second.1 :=
      (realization_action_unique specification second.1 second.2).symm

/-- Contractibility-style relative universal property. -/
theorem specification_fiber_unique_existence
    (specification : ActionSpecification) :
    (Nonempty (SpecificationFiber specification)) /\
      Subsingleton (SpecificationFiber specification) := by
  exact ⟨specification_fiber_nonempty specification,
    specification_fiber_subsingleton specification⟩

/--
P-A verdict: a terminal/unique action exists only relative to a specification
that already contains the Hessian, a critical point and one normalization.  The
moduli category or principal symbol alone does not provide those data.
-/
structure UniversalActionPhysicalStatus where
  admissibleActionCategoryConstructed : Prop
  variationallyTrivialTermsQuotiented : Prop
  hessianClassDerived : Prop
  criticalPointDerived : Prop
  actionNormalizationDerived : Prop
  terminalActionClassProved : Prop
  parentBulkOrMicroscopicSourceDerived : Prop
  noTargetRadiusUsed : Prop


def universalActionPhysicalClosure
    (s : UniversalActionPhysicalStatus) : Prop :=
  s.admissibleActionCategoryConstructed /\
  s.variationallyTrivialTermsQuotiented /\
  s.hessianClassDerived /\
  s.criticalPointDerived /\
  s.actionNormalizationDerived /\
  s.terminalActionClassProved /\
  s.parentBulkOrMicroscopicSourceDerived /\
  s.noTargetRadiusUsed

end P0EFTJanusUniversalActionProperty
end JanusFormal
