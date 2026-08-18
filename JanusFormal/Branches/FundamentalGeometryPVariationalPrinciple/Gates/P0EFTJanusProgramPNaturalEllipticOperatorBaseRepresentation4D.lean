import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalEllipticFamilyExistence

/-!
# Natural elliptic operator representations over an arbitrary parameter base

The original representation bridge was specialized to a real parameter.  None
of its categorical content depends on `Real`.  This file extracts the genuine
base-independent form.

For a natural elliptic family and any parameter type `Parameter`, each parameter
selects one D11 object and source/target section coordinates into one fixed
state type.  The represented natural operator is required to agree exactly
with the chosen parameterized operator family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNaturalEllipticOperatorBaseRepresentation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence

universe u v w x y z

variable
  {Parameter State : Type*}
  {immersionCategory : SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}

/-- Representation of a D11 natural elliptic family over an arbitrary
parameter type in one fixed state space. -/
structure NaturalEllipticOperatorBaseRepresentationData
    (Parameter State : Type*)
    (immersionCategory : SpinCImmersionCategory)
    (family : NaturalEllipticOperatorFamily immersionCategory)
    (representedOperator : Parameter → State → State) where
  objectAt : Parameter → immersionCategory.category.Obj
  sourceEquiv : ∀ parameter,
    family.sourceFunctor.Section (objectAt parameter) ≃ State
  targetEquiv : ∀ parameter,
    family.targetFunctor.Section (objectAt parameter) ≃ State
  operator_agreement : ∀ parameter state,
    targetEquiv parameter
      (family.operator.apply (objectAt parameter)
        ((sourceEquiv parameter).symm state)) =
      representedOperator parameter state

namespace NaturalEllipticOperatorBaseRepresentationData

/-- Natural operator represented on the fixed state type. -/
def representedNaturalOperator
    {representedOperator : Parameter → State → State}
    (data : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (parameter : Parameter) : State → State :=
  fun state =>
    data.targetEquiv parameter
      (family.operator.apply (data.objectAt parameter)
        ((data.sourceEquiv parameter).symm state))

/-- Exact agreement with the supplied represented operator family. -/
theorem representedNaturalOperator_eq
    {representedOperator : Parameter → State → State}
    (data : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (parameter : Parameter) :
    data.representedNaturalOperator parameter = representedOperator parameter := by
  funext state
  exact data.operator_agreement parameter state

/-- Source pullback represented in the fixed state coordinates. -/
def representedSourcePullback
    {representedOperator : Parameter → State → State}
    (data : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    {first second : Parameter}
    (morphism : AdmissibleMorphism immersionCategory
      (data.objectAt first) (data.objectAt second)) : State → State :=
  fun state =>
    data.sourceEquiv first
      (family.sourceFunctor.pullback morphism
        ((data.sourceEquiv second).symm state))

/-- Target pullback represented in the fixed state coordinates. -/
def representedTargetPullback
    {representedOperator : Parameter → State → State}
    (data : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    {first second : Parameter}
    (morphism : AdmissibleMorphism immersionCategory
      (data.objectAt first) (data.objectAt second)) : State → State :=
  fun state =>
    data.targetEquiv first
      (family.targetFunctor.pullback morphism
        ((data.targetEquiv second).symm state))

/-- D11 naturality becomes exact equivariance of the represented operator under
represented source/target pullbacks. -/
theorem represented_naturality
    {representedOperator : Parameter → State → State}
    (data : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    {first second : Parameter}
    (morphism : AdmissibleMorphism immersionCategory
      (data.objectAt first) (data.objectAt second))
    (state : State) :
    data.representedTargetPullback morphism
        (representedOperator second state) =
      representedOperator first
        (data.representedSourcePullback morphism state) := by
  rw [← data.representedNaturalOperator_eq second,
    ← data.representedNaturalOperator_eq first]
  unfold representedNaturalOperator representedSourcePullback
    representedTargetPullback
  simp only [Equiv.symm_apply_apply]
  rw [family.operator.naturality]

/-- Pull a base representation back along any parameter map. -/
def pullback
    {representedOperator : Parameter → State → State}
    (data : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    {NewParameter : Type*} (map : NewParameter → Parameter) :
    NaturalEllipticOperatorBaseRepresentationData
      NewParameter State immersionCategory family
        (fun parameter => representedOperator (map parameter)) where
  objectAt := fun parameter => data.objectAt (map parameter)
  sourceEquiv := fun parameter => data.sourceEquiv (map parameter)
  targetEquiv := fun parameter => data.targetEquiv (map parameter)
  operator_agreement := fun parameter => data.operator_agreement (map parameter)

/-- Public arbitrary-base natural representation checkpoint. -/
theorem natural_elliptic_operator_base_representation_gate
    (representedOperator : Parameter → State → State)
    (data : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator) :
    (∀ parameter,
      data.representedNaturalOperator parameter = representedOperator parameter) ∧
    (∀ {first second : Parameter}
      (morphism : AdmissibleMorphism immersionCategory
        (data.objectAt first) (data.objectAt second))
      (state : State),
      data.representedTargetPullback morphism
          (representedOperator second state) =
        representedOperator first
          (data.representedSourcePullback morphism state)) :=
  ⟨data.representedNaturalOperator_eq, data.represented_naturality⟩

end NaturalEllipticOperatorBaseRepresentationData

end
end P0EFTJanusProgramPNaturalEllipticOperatorBaseRepresentation4D
end JanusFormal
