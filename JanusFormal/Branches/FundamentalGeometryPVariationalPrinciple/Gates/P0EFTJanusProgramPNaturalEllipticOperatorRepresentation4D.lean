import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalEllipticFamilyExistence

/-!
# Representation of a D11 natural elliptic family on one fixed state space

The D11 natural family is intrinsically typed over the varying objects of the
SpinC immersion category.  Program P works with one fixed ambient Hilbert space.
This file isolates the exact bridge: choose one D11 object at each parameter and
identify its source and target section types with a fixed representation type.

No new operator is selected.  The representation certificate requires that the
conjugated D11 operator is exactly the supplied fixed-space family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusNaturalOperatorJets
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusNaturalSymbolCalculus

variable {State : Type*}

/-- Exact representation of one D11 natural elliptic operator family on a fixed
state type.  Source and target coordinates are kept separate because D11 does
not require the two natural section functors to coincide definitionally. -/
structure NaturalEllipticOperatorRepresentationData
    (immersionCategory : SpinCImmersionCategory)
    (family : NaturalEllipticOperatorFamily immersionCategory)
    (representedOperator : Real → State → State) where
  objectAt : Real → immersionCategory.category.Obj
  sourceEquiv : ∀ parameter,
    family.sourceFunctor.Section (objectAt parameter) ≃ State
  targetEquiv : ∀ parameter,
    family.targetFunctor.Section (objectAt parameter) ≃ State
  operator_agreement : ∀ parameter sectionValue,
    targetEquiv parameter
        (family.operator.apply (objectAt parameter) sectionValue) =
      representedOperator parameter (sourceEquiv parameter sectionValue)

namespace NaturalEllipticOperatorRepresentationData

/-- D11 operator conjugated to the fixed representation type. -/
def representedNaturalOperator
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (parameter : Real) (state : State) : State :=
  data.targetEquiv parameter
    (family.operator.apply (data.objectAt parameter)
      ((data.sourceEquiv parameter).symm state))

/-- The conjugated D11 operator is exactly the supplied represented family. -/
theorem representedNaturalOperator_eq
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (parameter : Real) :
    data.representedNaturalOperator parameter = representedOperator parameter := by
  funext state
  unfold representedNaturalOperator
  rw [data.operator_agreement]
  simp

/-- Source pullback transported to the fixed representation type. -/
def representedSourcePullback
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    {first second : Real}
    (morphism : AdmissibleMorphism immersionCategory
      (data.objectAt first) (data.objectAt second))
    (state : State) : State :=
  data.sourceEquiv first
    (family.sourceFunctor.pullback morphism
      ((data.sourceEquiv second).symm state))

/-- Represented source pullback preserves identities. -/
@[simp]
theorem representedSourcePullback_identity
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (parameter : Real) (state : State) :
    data.representedSourcePullback
        (admissibleIdentity immersionCategory (data.objectAt parameter)) state =
      state := by
  unfold representedSourcePullback
  rw [family.sourceFunctor.pullbackIdentity]
  exact Equiv.apply_symm_apply (data.sourceEquiv parameter) state

/-- Represented source pullback reverses admissible composition. -/
theorem representedSourcePullback_compose
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    {first second third : Real}
    (secondMorphism : AdmissibleMorphism immersionCategory
      (data.objectAt second) (data.objectAt third))
    (firstMorphism : AdmissibleMorphism immersionCategory
      (data.objectAt first) (data.objectAt second))
    (state : State) :
    data.representedSourcePullback
        (admissibleCompose immersionCategory secondMorphism firstMorphism) state =
      data.representedSourcePullback firstMorphism
        (data.representedSourcePullback secondMorphism state) := by
  unfold representedSourcePullback
  rw [family.sourceFunctor.pullbackComposition]
  simp only [Equiv.symm_apply_apply]

/-- Target pullback transported to the fixed representation type. -/
def representedTargetPullback
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    {first second : Real}
    (morphism : AdmissibleMorphism immersionCategory
      (data.objectAt first) (data.objectAt second))
    (state : State) : State :=
  data.targetEquiv first
    (family.targetFunctor.pullback morphism
      ((data.targetEquiv second).symm state))

/-- Naturality of the D11 operator becomes an exact covariance equation for the
represented fixed-space family. -/
theorem representedOperator_naturality
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    {first second : Real}
    (morphism : AdmissibleMorphism immersionCategory
      (data.objectAt first) (data.objectAt second))
    (state : State) :
    data.representedTargetPullback morphism
        (representedOperator second state) =
      representedOperator first
        (data.representedSourcePullback morphism state) := by
  unfold representedTargetPullback representedSourcePullback
  rw [← data.representedNaturalOperator_eq second]
  rw [← data.representedNaturalOperator_eq first]
  unfold representedNaturalOperator
  simp only [Equiv.symm_apply_apply]
  rw [family.operator.naturality morphism]

/-- Same-jet relation transported from the D11 source jet functor. -/
def RepresentedSameJetThrough
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (parameter : Real) (first second : State) : Prop :=
  SameJetThrough immersionCategory family.sourceFunctor family.sourceJets
    (data.objectAt parameter) family.finiteOrder.order
    ((data.sourceEquiv parameter).symm first)
    ((data.sourceEquiv parameter).symm second)

/-- The represented operator depends only on the same certified finite D11 jet. -/
theorem representedOperator_depends_only_on_jet
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (parameter : Real) (first second : State)
    (hJet : data.RepresentedSameJetThrough parameter first second) :
    representedOperator parameter first = representedOperator parameter second := by
  rw [← data.representedNaturalOperator_eq parameter]
  unfold representedNaturalOperator
  congr 1
  exact finite_order_depends_only_on_jet
    immersionCategory family.sourceFunctor family.targetFunctor family.sourceJets
      family.operator family.finiteOrder (data.objectAt parameter)
      ((data.sourceEquiv parameter).symm first)
      ((data.sourceEquiv parameter).symm second) hJet

/-- The represented family inherits the already certified D11 natural,
finite-order and elliptic package. -/
theorem natural_elliptic_representation_gate
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (data : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator) :
    (∀ parameter,
      data.representedNaturalOperator parameter = representedOperator parameter) ∧
    (∀ {first second}
      (morphism : AdmissibleMorphism immersionCategory
        (data.objectAt first) (data.objectAt second))
      (state : State),
      data.representedTargetPullback morphism
          (representedOperator second state) =
        representedOperator first
          (data.representedSourcePullback morphism state)) ∧
    (∀ parameter first second,
      data.RepresentedSameJetThrough parameter first second →
        representedOperator parameter first = representedOperator parameter second) ∧
    IsElliptic immersionCategory family.symbolFamily :=
  ⟨data.representedNaturalOperator_eq,
    data.representedOperator_naturality,
    data.representedOperator_depends_only_on_jet,
    family.elliptic⟩

end NaturalEllipticOperatorRepresentationData

end
end P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
end JanusFormal
