import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusAdmissibleMorphismIsomorphism
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCoherentLinearNaturalRepresentationPullbackTransport4D

/-!
# Linear represented transport from admissible D11 isomorphisms

A coherent family of admissible isomorphisms gives forward and reverse section
pullbacks.  Once those represented pullbacks are proved real-linear, the
reverse pullback is automatically a linear equivalence: its inverse is the
forward pullback, and both inverse laws follow from functoriality plus the two
isomorphism equations.

This layer therefore removes the represented `LinearEquiv` itself from the list
of external inputs.  It asks only for linear maps representing forward and
reverse source pullback, agreement of reverse target pullback with the same
reverse map, and coherence of the inverse morphisms across parameters.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusAdmissibleMorphismIsomorphism
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPLinearNaturalRepresentationIsomorphismTransport4D
open P0EFTJanusProgramPCoherentLinearNaturalRepresentationPullbackTransport4D

variable
  {State Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup State] [InnerProductSpace Real State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  {immersionCategory : SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}
  {operator : Real → State →L[Real] State}

/-- A coherent family of admissible D11 isomorphisms with linear represented
forward/reverse pullbacks. -/
structure LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement) where
  isomorphism : ∀ first second,
    AdmissibleIsomorphism immersionCategory
      (representation.objectAt first) (representation.objectAt second)
  isomorphism_self_inv : ∀ parameter,
    (isomorphism parameter parameter).inv =
      admissibleIdentity immersionCategory (representation.objectAt parameter)
  isomorphism_trans_inv : ∀ first second third,
    admissibleCompose immersionCategory
        (isomorphism first second).inv
        (isomorphism second third).inv =
      (isomorphism first third).inv
  reverseLinear : ∀ first second, State →ₗ[Real] State
  forwardLinear : ∀ first second, State →ₗ[Real] State
  reverse_source_agreement : ∀ first second state,
    representation.representedSourcePullback
        (isomorphism first second).inv state =
      reverseLinear first second state
  forward_source_agreement : ∀ first second state,
    representation.representedSourcePullback
        (isomorphism first second).hom state =
      forwardLinear first second state
  reverse_target_agreement : ∀ first second state,
    representation.representedTargetPullback
        (isomorphism first second).inv state =
      reverseLinear first second state

namespace LinearNaturalRepresentationAdmissibleIsomorphismFamilyData

/-- Reverse represented pullback as a genuine linear equivalence, with forward
pullback as inverse. -/
def transport
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback)
    (first second : Real) : State ≃ₗ[Real] State where
  toFun := data.reverseLinear first second
  invFun := data.forwardLinear first second
  left_inv := by
    intro state
    change data.forwardLinear first second
        (data.reverseLinear first second state) = state
    rw [← data.forward_source_agreement first second
      (data.reverseLinear first second state)]
    rw [← data.reverse_source_agreement first second state]
    rw [← representation.representedSourcePullback_compose
      (data.isomorphism first second).inv
      (data.isomorphism first second).hom state]
    rw [(data.isomorphism first second).inv_hom_id]
    exact representation.representedSourcePullback_identity first state
  right_inv := by
    intro state
    change data.reverseLinear first second
        (data.forwardLinear first second state) = state
    rw [← data.reverse_source_agreement first second
      (data.forwardLinear first second state)]
    rw [← data.forward_source_agreement first second state]
    rw [← representation.representedSourcePullback_compose
      (data.isomorphism first second).hom
      (data.isomorphism first second).inv state]
    rw [(data.isomorphism first second).hom_inv_id]
    exact representation.representedSourcePullback_identity second state
  map_add' := data.reverseLinear first second |>.map_add
  map_smul' := data.reverseLinear first second |>.map_smul

@[simp]
theorem transport_apply
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback)
    (first second : Real) (state : State) :
    data.transport representation coordinates refinement pullback first second state =
      data.reverseLinear first second state :=
  rfl

/-- The admissible-isomorphism family determines coherent represented linear
pullback transport. -/
def toCoherentPullbackTransport
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback) :
    CoherentLinearNaturalRepresentationPullbackTransportData
      representation coordinates refinement pullback where
  reverseMorphism := fun first second => (data.isomorphism first second).inv
  reverseMorphism_self := data.isomorphism_self_inv
  reverseMorphism_trans := data.isomorphism_trans_inv
  transport := data.transport representation coordinates refinement pullback
  source_pullback_agreement := by
    intro first second state
    exact data.reverse_source_agreement first second state
  target_pullback_agreement := by
    intro first second state
    exact data.reverse_target_agreement first second state

/-- Upgrade directly to the full linear represented D11 transport packet. -/
def toLinearNaturalRepresentationIsomorphismTransport
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback) :
    LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement pullback :=
  (data.toCoherentPullbackTransport representation coordinates refinement
    pullback).toLinearNaturalRepresentationIsomorphismTransport representation
      coordinates refinement pullback

/-- Public admissible-isomorphism represented transport checkpoint. -/
theorem linear_natural_representation_admissible_isomorphism_family_gate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback) :
    (∀ first second,
      Function.LeftInverse
        (data.forwardLinear first second)
        (data.reverseLinear first second)) ∧
    (∀ first second,
      Function.RightInverse
        (data.forwardLinear first second)
        (data.reverseLinear first second)) ∧
    Nonempty (CoherentLinearNaturalRepresentationPullbackTransportData
      representation coordinates refinement pullback) ∧
    Nonempty (LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement pullback) := by
  refine ⟨?_, ?_,
    ⟨data.toCoherentPullbackTransport representation coordinates refinement
      pullback⟩,
    ⟨data.toLinearNaturalRepresentationIsomorphismTransport representation
      coordinates refinement pullback⟩⟩
  · intro first second state
    exact (data.transport representation coordinates refinement pullback first
      second).left_inv state
  · intro first second state
    exact (data.transport representation coordinates refinement pullback first
      second).right_inv state

end LinearNaturalRepresentationAdmissibleIsomorphismFamilyData

end
end P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
end JanusFormal
