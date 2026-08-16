import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalBaseRepresentation4D

/-!
# Sector-preserving D11 pullbacks over an arbitrary base

The represented source and target pullbacks are required to commute with every
projector of the one fixed five-sector Hilbert geometry.  This prevents
geometric changes of representative from mixing physical sectors anywhere on
the multidimensional parameter base.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalBasePullback4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorBaseRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalBaseRepresentation4D
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusSpinCImmersionCategory

variable
  {Parameter State Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup State] [InnerProductSpace Real State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  {immersionCategory : SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}
  {representedOperator : Parameter → State → State}

/-- Sector covariance of represented geometric pullbacks over an arbitrary
parameter type. -/
structure FiveSectorNaturalBasePullbackData
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates) : Prop where
  source_commutes : ∀ {first second : Parameter}
    (morphism : AdmissibleMorphism immersionCategory
      (representation.objectAt first) (representation.objectAt second))
    (sector : FivePhysicalSector) (state : State),
    coordinates.sectorProjector sector
        (representation.representedSourcePullback morphism state) =
      representation.representedSourcePullback morphism
        (coordinates.sectorProjector sector state)
  target_commutes : ∀ {first second : Parameter}
    (morphism : AdmissibleMorphism immersionCategory
      (representation.objectAt first) (representation.objectAt second))
    (sector : FivePhysicalSector) (state : State),
    coordinates.sectorProjector sector
        (representation.representedTargetPullback morphism state) =
      representation.representedTargetPullback morphism
        (coordinates.sectorProjector sector state)

namespace FiveSectorNaturalBasePullbackData

/-- Source pullback preserves every physical sector range. -/
theorem source_mem_sector
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBasePullbackData representation coordinates refinement)
    {first second : Parameter}
    (morphism : AdmissibleMorphism immersionCategory
      (representation.objectAt first) (representation.objectAt second))
    (sector : FivePhysicalSector) {state : State}
    (hState : state ∈ coordinates.sectorSubspace sector) :
    representation.representedSourcePullback morphism state ∈
      coordinates.sectorSubspace sector := by
  refine ⟨representation.representedSourcePullback morphism state, ?_⟩
  rw [data.source_commutes morphism sector state]
  rw [coordinates.sectorProjector_eq_self_of_mem sector hState]

/-- Target pullback preserves every physical sector range. -/
theorem target_mem_sector
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBasePullbackData representation coordinates refinement)
    {first second : Parameter}
    (morphism : AdmissibleMorphism immersionCategory
      (representation.objectAt first) (representation.objectAt second))
    (sector : FivePhysicalSector) {state : State}
    (hState : state ∈ coordinates.sectorSubspace sector) :
    representation.representedTargetPullback morphism state ∈
      coordinates.sectorSubspace sector := by
  refine ⟨representation.representedTargetPullback morphism state, ?_⟩
  rw [data.target_commutes morphism sector state]
  rw [coordinates.sectorProjector_eq_self_of_mem sector hState]

/-- Public arbitrary-base pullback covariance checkpoint. -/
theorem five_sector_natural_base_pullback_gate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBasePullbackData representation coordinates refinement) :
    (∀ {first second : Parameter}
      (morphism : AdmissibleMorphism immersionCategory
        (representation.objectAt first) (representation.objectAt second))
      (sector : FivePhysicalSector) (state : State),
      coordinates.sectorProjector sector
          (representation.representedSourcePullback morphism state) =
        representation.representedSourcePullback morphism
          (coordinates.sectorProjector sector state)) ∧
    (∀ {first second : Parameter}
      (morphism : AdmissibleMorphism immersionCategory
        (representation.objectAt first) (representation.objectAt second))
      (sector : FivePhysicalSector) (state : State),
      coordinates.sectorProjector sector
          (representation.representedTargetPullback morphism state) =
        representation.representedTargetPullback morphism
          (coordinates.sectorProjector sector state)) :=
  ⟨data.source_commutes, data.target_commutes⟩

end FiveSectorNaturalBasePullbackData

end
end P0EFTJanusProgramPFiveSectorNaturalBasePullback4D
end JanusFormal
