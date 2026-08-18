import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D

/-!
# L² bridge for five-sector D11 pullbacks

The first D11 interface that only needs sector projectors is the natural
representation pullback packet.  This bridge transfers L² projector
commutation into that existing packet, provided the legacy and L² projectors
are identified.  It does not claim an isometry from the L² product to the raw
maximum-norm product.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusSpinCImmersionCategory

/-- Canonical identification of the legacy and L² five-sector labels. -/
def fivePhysicalSectorL2SlotEquiv : FivePhysicalSector ≃ FiveSectorSlot where
  toFun
    | .metricDiffeomorphism => .metricDiffeomorphism
    | .abelianGauge => .abelianGauge
    | .primitiveSpinCMatter => .primitiveSpinCMatter
    | .longitudinalLL => .longitudinalLL
    | .boundaryFiniteBV => .boundaryFiniteBV
  invFun
    | .metricDiffeomorphism => .metricDiffeomorphism
    | .abelianGauge => .abelianGauge
    | .primitiveSpinCMatter => .primitiveSpinCMatter
    | .longitudinalLL => .longitudinalLL
    | .boundaryFiniteBV => .boundaryFiniteBV
  left_inv sector := by cases sector <;> rfl
  right_inv sector := by cases sector <;> rfl

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
  {representedOperator : Real → State → State}

/-- Transfer source/target pullback commutation proved with the L² projectors
to the existing D11 pullback packet. -/
def fiveSectorNaturalRepresentationPullbackDataOfL2
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
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
          (l2Coordinates.sectorProjector sector state)) :
    FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement where
  source_commutes := by
    intro first second morphism sector state
    rw [projector_eq sector]
    exact source_commutes morphism (fivePhysicalSectorL2SlotEquiv sector) state
  target_commutes := by
    intro first second morphism sector state
    rw [projector_eq sector]
    exact target_commutes morphism (fivePhysicalSectorL2SlotEquiv sector) state

end

end P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
end JanusFormal
