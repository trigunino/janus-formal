import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D

/-!
# Linear isomorphism transport from represented D11 pullbacks

A represented D11 natural family already supplies contravariant source and
target pullbacks together with the naturality equation.  To obtain a transport
on the fixed Hilbert representation one needs three additional facts:

* choose a reverse admissible morphism from the object at the target parameter
  to the object at the source parameter;
* identify both represented pullbacks along that morphism with one real-linear
  equivalence of the fixed state space;
* prove identity and composition for those equivalences.

Naturality then becomes exactly

`H_second U_first,second = U_first,second H_first`.

When the represented pullbacks preserve the five physical sectors, the same
linear transport commutes with every physical projector.  Thus this packet is
the precise D11 input required by the ambient and actual-kernel transport
closures; invertibility and linearity are not silently inferred from the older
plain-function pullback interface.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearNaturalRepresentationIsomorphismTransport4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D

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

/-- Linear, invertible and coherent realization of reverse D11 pullbacks on the
fixed represented state space. -/
structure LinearNaturalRepresentationIsomorphismTransportData
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
  transport : ∀ first second, State ≃ₗ[Real] State
  source_pullback_agreement : ∀ first second state,
    representation.representedSourcePullback
        (reverseMorphism first second) state =
      transport first second state
  target_pullback_agreement : ∀ first second state,
    representation.representedTargetPullback
        (reverseMorphism first second) state =
      transport first second state
  transport_self : ∀ parameter,
    transport parameter parameter = LinearEquiv.refl Real State
  transport_trans : ∀ first second third,
    (transport second third).comp (transport first second) =
      transport first third

namespace LinearNaturalRepresentationIsomorphismTransportData

/-- D11 naturality becomes exact intertwining of the represented operator
family by the common linear pullback equivalence. -/
theorem operator_intertwining
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
    (data : LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement pullback)
    (first second : Real) (state : State) :
    operator second (data.transport first second state) =
      data.transport first second (operator first state) := by
  have hNatural := representation.representedOperator_naturality
    (data.reverseMorphism first second) state
  change
    representation.representedTargetPullback
        (data.reverseMorphism first second) (operator first state) =
      operator second
        (representation.representedSourcePullback
          (data.reverseMorphism first second) state) at hNatural
  calc
    operator second (data.transport first second state) =
        operator second
          (representation.representedSourcePullback
            (data.reverseMorphism first second) state) := by
      rw [data.source_pullback_agreement first second state]
    _ = representation.representedTargetPullback
          (data.reverseMorphism first second) (operator first state) :=
      hNatural.symm
    _ = data.transport first second (operator first state) :=
      data.target_pullback_agreement first second (operator first state)

/-- Sector covariance of represented source pullbacks becomes commutation of
the linear transport with every physical projector. -/
theorem transport_commutes_sectorProjector
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
    (data : LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement pullback)
    (first second : Real) (sector : FivePhysicalSector) (state : State) :
    data.transport first second (coordinates.sectorProjector sector state) =
      coordinates.sectorProjector sector
        (data.transport first second state) := by
  have hSector := pullback.source_commutes
    (data.reverseMorphism first second) sector state
  calc
    data.transport first second (coordinates.sectorProjector sector state) =
        representation.representedSourcePullback
          (data.reverseMorphism first second)
          (coordinates.sectorProjector sector state) :=
      (data.source_pullback_agreement first second
        (coordinates.sectorProjector sector state)).symm
    _ = coordinates.sectorProjector sector
          (representation.representedSourcePullback
            (data.reverseMorphism first second) state) :=
      hSector.symm
    _ = coordinates.sectorProjector sector
          (data.transport first second state) := by
      rw [data.source_pullback_agreement first second state]

/-- Adapter to the generic ambient intertwining-transport packet. -/
def toFiniteIntertwiningOperatorTransport
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
    (data : LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement pullback) :
    FiniteIntertwiningOperatorTransportData operator where
  transport := data.transport
  transport_self := data.transport_self
  transport_trans := data.transport_trans
  intertwines := data.operator_intertwining representation coordinates refinement
    pullback

/-- Public linear D11 pullback-isomorphism checkpoint. -/
theorem linear_natural_representation_isomorphism_transport_gate
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
    (data : LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement pullback) :
    (∀ first second state,
      operator second (data.transport first second state) =
        data.transport first second (operator first state)) ∧
    (∀ first second sector state,
      data.transport first second (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector
          (data.transport first second state)) ∧
    (∀ parameter,
      data.transport parameter parameter = LinearEquiv.refl Real State) ∧
    (∀ first second third,
      (data.transport second third).comp (data.transport first second) =
        data.transport first third) :=
  ⟨data.operator_intertwining representation coordinates refinement pullback,
    data.transport_commutes_sectorProjector representation coordinates refinement
      pullback,
    data.transport_self,
    data.transport_trans⟩

end LinearNaturalRepresentationIsomorphismTransportData

end
end P0EFTJanusProgramPLinearNaturalRepresentationIsomorphismTransport4D
end JanusFormal