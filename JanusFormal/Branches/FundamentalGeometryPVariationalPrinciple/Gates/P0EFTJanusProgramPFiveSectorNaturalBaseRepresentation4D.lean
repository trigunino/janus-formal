import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalEllipticOperatorBaseRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorRepresentationCoordinates4D

/-!
# Five-sector refinement of D11 representations over arbitrary bases

The multidimensional D11 family must use the same physical five-sector Hilbert
geometry before any restriction to a one-dimensional path.  This file is the
base-independent analogue of the existing real-parameter refinement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalBaseRepresentation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorBaseRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorRepresentationCoordinates4D
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

/-- Source/target coordinate factorization through one fixed five-sector Hilbert
isometry over an arbitrary parameter type. -/
structure FiveSectorNaturalBaseRepresentationData
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)) where
  MetricSource : Parameter → Type*
  AbelianSource : Parameter → Type*
  MatterSource : Parameter → Type*
  LongitudinalSource : Parameter → Type*
  BoundarySource : Parameter → Type*
  MetricTarget : Parameter → Type*
  AbelianTarget : Parameter → Type*
  MatterTarget : Parameter → Type*
  LongitudinalTarget : Parameter → Type*
  BoundaryTarget : Parameter → Type*
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

namespace FiveSectorNaturalBaseRepresentationData

/-- The source representation recovers all five physical coordinates. -/
theorem source_allCoordinates
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (data : FiveSectorNaturalBaseRepresentationData representation coordinates)
    (parameter : Parameter)
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

/-- The target representation obeys the same factorization. -/
theorem target_allCoordinates
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (data : FiveSectorNaturalBaseRepresentationData representation coordinates)
    (parameter : Parameter)
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

/-- Public arbitrary-base five-sector representation checkpoint. -/
theorem five_sector_natural_base_representation_gate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (data : FiveSectorNaturalBaseRepresentationData representation coordinates) :
    (∀ parameter,
      representation.sourceEquiv parameter =
        (data.sourceProductEquiv parameter).trans
          ((data.sourceSectorCoordinates parameter).ambientEquiv coordinates)) ∧
    (∀ parameter,
      representation.targetEquiv parameter =
        (data.targetProductEquiv parameter).trans
          ((data.targetSectorCoordinates parameter).ambientEquiv coordinates)) :=
  ⟨data.sourceEquiv_agreement, data.targetEquiv_agreement⟩

end FiveSectorNaturalBaseRepresentationData

end
end P0EFTJanusProgramPFiveSectorNaturalBaseRepresentation4D
end JanusFormal
