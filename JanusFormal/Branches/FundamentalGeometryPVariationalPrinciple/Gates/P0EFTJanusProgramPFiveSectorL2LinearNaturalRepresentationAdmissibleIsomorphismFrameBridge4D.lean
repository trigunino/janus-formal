import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D

/-!
# L² bridge to admissible-isomorphism D11 frames

This adapter feeds L² pullback covariance into the existing represented
basepoint-frame packet and transfers frame/projector commutation to the L²
sector projectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2LinearNaturalRepresentationAdmissibleIsomorphismFrameBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusAdmissibleMorphismIsomorphism
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D

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

/-- Build the represented admissible-isomorphism frame using pullback
commutation proved for the L² projectors. -/
def linearNaturalRepresentationAdmissibleIsomorphismFrameDataOfL2
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
    (isomorphismAt : ∀ parameter,
      AdmissibleIsomorphism immersionCategory
        (representation.objectAt 0) (representation.objectAt parameter))
    (isomorphism_zero_inv :
      (isomorphismAt 0).inv =
        admissibleIdentity immersionCategory (representation.objectAt 0))
    (reverseLinear forwardLinear : Real → State →ₗ[Real] State)
    (reverse_source_agreement : ∀ parameter state,
      representation.representedSourcePullback
          (isomorphismAt parameter).inv state =
        reverseLinear parameter state)
    (forward_source_agreement : ∀ parameter state,
      representation.representedSourcePullback
          (isomorphismAt parameter).hom state =
        forwardLinear parameter state)
    (reverse_target_agreement : ∀ parameter state,
      representation.representedTargetPullback
          (isomorphismAt parameter).inv state =
        reverseLinear parameter state) :
    LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement
        (fiveSectorNaturalRepresentationPullbackDataOfL2
          representation coordinates refinement l2Coordinates projector_eq
          source_commutes target_commutes) where
  isomorphismAt := isomorphismAt
  isomorphism_zero_inv := isomorphism_zero_inv
  reverseLinear := reverseLinear
  forwardLinear := forwardLinear
  reverse_source_agreement := reverse_source_agreement
  forward_source_agreement := forward_source_agreement
  reverse_target_agreement := reverse_target_agreement

/-- An admissible-isomorphism frame commuting with the identified legacy
projectors commutes with every L² sector projector. -/
theorem frame_commutes_l2SectorProjector
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
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (l2Coordinates : FiveSectorL2HilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (projector_eq : ∀ sector,
      coordinates.sectorProjector sector =
        l2Coordinates.sectorProjector (fivePhysicalSectorL2SlotEquiv sector))
    (parameter : Real) (sector : FiveSectorSlot) (state : State) :
    data.frame representation coordinates refinement pullback parameter
        (l2Coordinates.sectorProjector sector state) =
      l2Coordinates.sectorProjector sector
        (data.frame representation coordinates refinement pullback parameter
          state) := by
  let legacySector := fivePhysicalSectorL2SlotEquiv.symm sector
  have hProjector :
      coordinates.sectorProjector legacySector =
        l2Coordinates.sectorProjector sector := by
    simpa [legacySector] using projector_eq legacySector
  rw [← hProjector]
  exact data.frame_commutes_sectorProjector representation coordinates
    refinement pullback parameter legacySector state

end

end P0EFTJanusProgramPFiveSectorL2LinearNaturalRepresentationAdmissibleIsomorphismFrameBridge4D
end JanusFormal
