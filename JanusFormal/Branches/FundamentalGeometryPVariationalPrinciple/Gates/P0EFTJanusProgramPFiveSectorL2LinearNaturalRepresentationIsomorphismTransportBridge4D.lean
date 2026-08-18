import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationIsomorphismTransport4D

/-!
# L² bridge to linear D11 isomorphism transports

This adapter feeds the L² pullback packet into the next existing D11 consumer,
`LinearNaturalRepresentationIsomorphismTransportData`, and transfers its
sector-commutation theorem back to the L² projectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2LinearNaturalRepresentationIsomorphismTransportBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
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

/-- Build the existing linear-isomorphism transport packet using pullback
commutation proved for the L² sector projectors. -/
def linearNaturalRepresentationIsomorphismTransportDataOfL2
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (l2Coordinates : FiveSectorL2HilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (projector_eq : ∀ sector,
      coordinates.sectorProjector sector =
        l2Coordinates.sectorProjector (fivePhysicalSectorL2SlotEquiv sector))
    (source_commutes : ∀ {first second : Real}
      (morphism : AdmissibleMorphism immersionCategory
        (representation.objectAt first) (representation.objectAt second))
      (sector : FiveSectorSlot) (state : State),
      l2Coordinates.sectorProjector sector
          (representation.representedSourcePullback morphism state) =
        representation.representedSourcePullback morphism
          (l2Coordinates.sectorProjector sector state))
    (target_commutes : ∀ {first second : Real}
      (morphism : AdmissibleMorphism immersionCategory
        (representation.objectAt first) (representation.objectAt second))
      (sector : FiveSectorSlot) (state : State),
      l2Coordinates.sectorProjector sector
          (representation.representedTargetPullback morphism state) =
        representation.representedTargetPullback morphism
          (l2Coordinates.sectorProjector sector state))
    (reverseMorphism : ∀ first second,
      AdmissibleMorphism immersionCategory
        (representation.objectAt second) (representation.objectAt first))
    (transport : Real → Real → State ≃ₗ[Real] State)
    (source_pullback_agreement : ∀ first second state,
      representation.representedSourcePullback
          (reverseMorphism first second) state =
        transport first second state)
    (target_pullback_agreement : ∀ first second state,
      representation.representedTargetPullback
          (reverseMorphism first second) state =
        transport first second state)
    (transport_self : ∀ parameter,
      transport parameter parameter = LinearEquiv.refl Real State)
    (transport_trans : ∀ first second third,
      (transport first second).trans (transport second third) =
        transport first third) :
    LinearNaturalRepresentationIsomorphismTransportData
      representation coordinates refinement
        (fiveSectorNaturalRepresentationPullbackDataOfL2
          representation coordinates refinement l2Coordinates projector_eq
          source_commutes target_commutes) where
  reverseMorphism := reverseMorphism
  transport := transport
  source_pullback_agreement := source_pullback_agreement
  target_pullback_agreement := target_pullback_agreement
  transport_self := transport_self
  transport_trans := transport_trans

/-- Any existing linear D11 transport commuting with the identified legacy
projectors also commutes with every L² sector projector. -/
theorem transport_commutes_l2SectorProjector
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
    (l2Coordinates : FiveSectorL2HilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (projector_eq : ∀ sector,
      coordinates.sectorProjector sector =
        l2Coordinates.sectorProjector (fivePhysicalSectorL2SlotEquiv sector))
    (first second : Real) (sector : FiveSectorSlot) (state : State) :
    data.transport first second (l2Coordinates.sectorProjector sector state) =
      l2Coordinates.sectorProjector sector
        (data.transport first second state) := by
  let legacySector := fivePhysicalSectorL2SlotEquiv.symm sector
  have hProjector :
      coordinates.sectorProjector legacySector =
        l2Coordinates.sectorProjector sector := by
    simpa [legacySector] using projector_eq legacySector
  rw [← hProjector]
  exact data.transport_commutes_sectorProjector representation coordinates
    refinement pullback first second legacySector state

end

end P0EFTJanusProgramPFiveSectorL2LinearNaturalRepresentationIsomorphismTransportBridge4D
end JanusFormal
