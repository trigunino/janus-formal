import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorRepresentationCoordinates4D

/-!
# Five-sector refinement of a represented D11 elliptic family

The generic D11 representation bridge allows one equivalence from a natural
source/target section type to the fixed Hilbert state space.  For Candidate-A
that is too weak: the Hilbert space already has one physical five-sector
isometry, so the representation must factor through the same five sectors.

This file records that factorization without changing the represented operator.
The source and target equivalences are required to be the composite of

* one section-to-five-sector product equivalence;
* five separate physical coordinate equivalences;
* the existing five-sector Hilbert isometry.

Hence no opaque representation equivalence can mix metric, Abelian, primitive
SpinC matter, longitudinal/LL and boundary/finite-BV coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorRepresentationCoordinates4D
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusSpinCImmersionCategory

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

/-- A representation refinement whose source and target coordinates both use
one fixed five-sector Hilbert geometry. -/
structure FiveSectorNaturalRepresentationRefinementData
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)) where
  MetricSource : Real → Type*
  AbelianSource : Real → Type*
  MatterSource : Real → Type*
  LongitudinalSource : Real → Type*
  BoundarySource : Real → Type*
  MetricTarget : Real → Type*
  AbelianTarget : Real → Type*
  MatterTarget : Real → Type*
  LongitudinalTarget : Real → Type*
  BoundaryTarget : Real → Type*
  sourceProductEquiv : ∀ parameter,
    family.sourceFunctor.Section (representation.objectAt parameter) ≃
      MetricSource parameter ×
        (AbelianSource parameter ×
          (MatterSource parameter ×
            (LongitudinalSource parameter × BoundarySource parameter)))
  targetProductEquiv : ∀ parameter,
    family.targetFunctor.Section (representation.objectAt parameter) ≃
      MetricTarget parameter ×
        (AbelianTarget parameter ×
          (MatterTarget parameter ×
            (LongitudinalTarget parameter × BoundaryTarget parameter)))
  sourceSectorCoordinates : ∀ parameter,
    FiveSectorSectionCoordinateData
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      (MetricSource parameter) (AbelianSource parameter)
      (MatterSource parameter) (LongitudinalSource parameter)
      (BoundarySource parameter)
  targetSectorCoordinates : ∀ parameter,
    FiveSectorSectionCoordinateData
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      (MetricTarget parameter) (AbelianTarget parameter)
      (MatterTarget parameter) (LongitudinalTarget parameter)
      (BoundaryTarget parameter)
  sourceEquiv_agreement : ∀ parameter,
    representation.sourceEquiv parameter =
      (sourceProductEquiv parameter).trans
        ((sourceSectorCoordinates parameter).ambientEquiv coordinates)
  targetEquiv_agreement : ∀ parameter,
    representation.targetEquiv parameter =
      (targetProductEquiv parameter).trans
        ((targetSectorCoordinates parameter).ambientEquiv coordinates)

namespace FiveSectorNaturalRepresentationRefinementData

/-- Source representation recovers exactly the five supplied physical source
coordinates after applying the existing Hilbert decomposition. -/
theorem source_allCoordinates
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (data : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (parameter : Real)
    (sectionValue : family.sourceFunctor.Section
      (representation.objectAt parameter)) :
    fiveSectorMetricCoordinate
        (coordinates.decomposition
          (representation.sourceEquiv parameter sectionValue)) =
      (data.sourceSectorCoordinates parameter).metric
        (data.sourceProductEquiv parameter sectionValue).1 ∧
    fiveSectorAbelianCoordinate
        (coordinates.decomposition
          (representation.sourceEquiv parameter sectionValue)) =
      (data.sourceSectorCoordinates parameter).abelian
        (data.sourceProductEquiv parameter sectionValue).2.1 ∧
    fiveSectorMatterCoordinate
        (coordinates.decomposition
          (representation.sourceEquiv parameter sectionValue)) =
      (data.sourceSectorCoordinates parameter).matter
        (data.sourceProductEquiv parameter sectionValue).2.2.1 ∧
    fiveSectorLongitudinalCoordinate
        (coordinates.decomposition
          (representation.sourceEquiv parameter sectionValue)) =
      (data.sourceSectorCoordinates parameter).longitudinal
        (data.sourceProductEquiv parameter sectionValue).2.2.2.1 ∧
    fiveSectorBoundaryCoordinate
        (coordinates.decomposition
          (representation.sourceEquiv parameter sectionValue)) =
      (data.sourceSectorCoordinates parameter).boundary
        (data.sourceProductEquiv parameter sectionValue).2.2.2.2 := by
  rw [data.sourceEquiv_agreement parameter]
  exact (data.sourceSectorCoordinates parameter).ambientEquiv_allCoordinates
    coordinates (data.sourceProductEquiv parameter sectionValue)

/-- Target representation obeys the same physical-sector factorization. -/
theorem target_allCoordinates
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (data : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (parameter : Real)
    (sectionValue : family.targetFunctor.Section
      (representation.objectAt parameter)) :
    fiveSectorMetricCoordinate
        (coordinates.decomposition
          (representation.targetEquiv parameter sectionValue)) =
      (data.targetSectorCoordinates parameter).metric
        (data.targetProductEquiv parameter sectionValue).1 ∧
    fiveSectorAbelianCoordinate
        (coordinates.decomposition
          (representation.targetEquiv parameter sectionValue)) =
      (data.targetSectorCoordinates parameter).abelian
        (data.targetProductEquiv parameter sectionValue).2.1 ∧
    fiveSectorMatterCoordinate
        (coordinates.decomposition
          (representation.targetEquiv parameter sectionValue)) =
      (data.targetSectorCoordinates parameter).matter
        (data.targetProductEquiv parameter sectionValue).2.2.1 ∧
    fiveSectorLongitudinalCoordinate
        (coordinates.decomposition
          (representation.targetEquiv parameter sectionValue)) =
      (data.targetSectorCoordinates parameter).longitudinal
        (data.targetProductEquiv parameter sectionValue).2.2.2.1 ∧
    fiveSectorBoundaryCoordinate
        (coordinates.decomposition
          (representation.targetEquiv parameter sectionValue)) =
      (data.targetSectorCoordinates parameter).boundary
        (data.targetProductEquiv parameter sectionValue).2.2.2.2 := by
  rw [data.targetEquiv_agreement parameter]
  exact (data.targetSectorCoordinates parameter).ambientEquiv_allCoordinates
    coordinates (data.targetProductEquiv parameter sectionValue)

/-- Public checkpoint: both D11 representation equivalences factor through one
literal five-sector Hilbert decomposition. -/
theorem five_sector_natural_representation_refinement_gate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (data : FiveSectorNaturalRepresentationRefinementData
      representation coordinates) :
    (∀ parameter,
      representation.sourceEquiv parameter =
        (data.sourceProductEquiv parameter).trans
          ((data.sourceSectorCoordinates parameter).ambientEquiv coordinates)) ∧
    (∀ parameter,
      representation.targetEquiv parameter =
        (data.targetProductEquiv parameter).trans
          ((data.targetSectorCoordinates parameter).ambientEquiv coordinates)) :=
  ⟨data.sourceEquiv_agreement, data.targetEquiv_agreement⟩

end FiveSectorNaturalRepresentationRefinementData

end
end P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
end JanusFormal
