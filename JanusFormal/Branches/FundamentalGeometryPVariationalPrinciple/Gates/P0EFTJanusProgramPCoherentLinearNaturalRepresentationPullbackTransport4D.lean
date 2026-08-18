import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationIsomorphismTransport4D

/-!
# Coherent linear represented pullbacks

The previous linear D11 transport packet records identity and composition laws
for the represented linear equivalences.  Those laws need not be independent
input.  They follow from functoriality of section pullback once the chosen
reverse admissible morphisms satisfy

`reverse(a,a) = id`

and

`reverse(a,b) ∘ reverse(b,c) = reverse(a,c)`.

This file packages only that morphism coherence, a represented linear
equivalence and source/target pullback agreement.  It derives the transport
identity and cocycle laws and then exports the full linear natural
representation transport packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCoherentLinearNaturalRepresentationPullbackTransport4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPLinearNaturalRepresentationIsomorphismTransport4D

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

/-- Coherent reverse admissible morphisms whose represented source and target
pullbacks are one real-linear equivalence of the fixed state space. -/
structure CoherentLinearNaturalRepresentationPullbackTransportData
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
  reverseMorphism : ∀ first second,
    AdmissibleMorphism immersionCategory
      (representation.objectAt second) (representation.objectAt first)
  reverseMorphism_self : ∀ parameter,
    reverseMorphism parameter parameter =
      admissibleIdentity immersionCategory (representation.objectAt parameter)
  reverseMorphism_trans : ∀ first second third,
    admissibleCompose immersionCategory
        (reverseMorphism first second)
        (reverseMorphism second third) =
      reverseMorphism first third
  transport : ∀ first second, State ≃ₗ[Real] State
  source_pullback_agreement : ∀ first second state,
    representation.representedSourcePullback
        (reverseMorphism first second) state =
      transport first second state
  target_pullback_agreement : ∀ first second state,
    representation.representedTargetPullback
        (reverseMorphism first second) state =
      transport first second state

namespace CoherentLinearNaturalRepresentationPullbackTransportData

/-- Identity of represented transport follows from pullback of the identity
morphism. -/
theorem transport_self
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
    (data : CoherentLinearNaturalRepresentationPullbackTransportData
      representation coordinates refinement pullback)
    (parameter : Real) :
    data.transport parameter parameter = LinearEquiv.refl Real State := by
  ext state
  change data.transport parameter parameter state = state
  rw [← data.source_pullback_agreement parameter parameter state]
  rw [data.reverseMorphism_self parameter]
  exact representation.representedSourcePullback_identity parameter state

/-- The represented transport cocycle follows from contravariant pullback
composition and coherence of the reverse morphisms. -/
theorem transport_trans
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
    (data : CoherentLinearNaturalRepresentationPullbackTransportData
      representation coordinates refinement pullback)
    (first second third : Real) :
    (data.transport first second).trans (data.transport second third) =
      data.transport first third := by
  ext state
  change data.transport second third
      (data.transport first second state) =
    data.transport first third state
  rw [← data.source_pullback_agreement first second state]
  rw [← data.source_pullback_agreement second third
    (representation.representedSourcePullback
      (data.reverseMorphism first second) state)]
  rw [← data.source_pullback_agreement first third state]
  rw [← representation.representedSourcePullback_compose
    (data.reverseMorphism first second)
    (data.reverseMorphism second third) state]
  rw [data.reverseMorphism_trans first second third]

/-- Upgrade coherent pullback data to the full linear D11 isomorphism transport
packet. -/
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
    (data : CoherentLinearNaturalRepresentationPullbackTransportData
      representation coordinates refinement pullback) :
    LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement pullback where
  reverseMorphism := data.reverseMorphism
  transport := data.transport
  source_pullback_agreement := data.source_pullback_agreement
  target_pullback_agreement := data.target_pullback_agreement
  transport_self := data.transport_self representation coordinates refinement
    pullback
  transport_trans := data.transport_trans representation coordinates refinement
    pullback

/-- Public coherent represented-pullback checkpoint. -/
theorem coherent_linear_natural_representation_pullback_transport_gate
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
    (data : CoherentLinearNaturalRepresentationPullbackTransportData
      representation coordinates refinement pullback) :
    (∀ parameter,
      data.transport parameter parameter = LinearEquiv.refl Real State) ∧
    (∀ first second third,
      (data.transport first second).trans (data.transport second third) =
        data.transport first third) ∧
    Nonempty (LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement pullback) :=
  ⟨data.transport_self representation coordinates refinement pullback,
    data.transport_trans representation coordinates refinement pullback,
    ⟨data.toLinearNaturalRepresentationIsomorphismTransport representation
      coordinates refinement pullback⟩⟩

end CoherentLinearNaturalRepresentationPullbackTransportData

end
end P0EFTJanusProgramPCoherentLinearNaturalRepresentationPullbackTransport4D
end JanusFormal
