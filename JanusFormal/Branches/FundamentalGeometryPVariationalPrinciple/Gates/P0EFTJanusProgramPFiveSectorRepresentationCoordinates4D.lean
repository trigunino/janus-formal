import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalFunctor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertCoordinates4D

/-!
# Sectorwise representation coordinates for five-sector natural sections

A representation of a five-sector D11 section family on a Candidate-A Hilbert
space should not be supplied as one opaque equivalence.  This file constructs
it from five separate physical-sector equivalences followed by the existing
five-sector Hilbert isometry.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorRepresentationCoordinates4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D

variable
  {E Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]

/-- Five raw section types with one physical coordinate equivalence each. -/
structure FiveSectorSectionCoordinateData
    (MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection : Type*) where
  metric : MetricSection ≃ Metric
  abelian : AbelianSection ≃ Abelian
  matter : MatterSection ≃ Matter
  longitudinal : LongitudinalSection ≃ Longitudinal
  boundary : BoundarySection ≃ Boundary

namespace FiveSectorSectionCoordinateData

/-- Componentwise equivalence from the nested five-section product to the exact
`FiveSectorProduct` used by the Candidate-A Hilbert decomposition. -/
def productEquiv
    {MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection : Type*}
    (data : FiveSectorSectionCoordinateData
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection) :
    MetricSection × (AbelianSection × (MatterSection ×
      (LongitudinalSection × BoundarySection))) ≃
      FiveSectorProduct Metric Abelian Matter Longitudinal Boundary where
  toFun value :=
    (data.metric value.1,
      (data.abelian value.2.1,
        (data.matter value.2.2.1,
          (data.longitudinal value.2.2.2.1,
            data.boundary value.2.2.2.2))))
  invFun value :=
    (data.metric.symm value.1,
      (data.abelian.symm value.2.1,
        (data.matter.symm value.2.2.1,
          (data.longitudinal.symm value.2.2.2.1,
            data.boundary.symm value.2.2.2.2))))
  left_inv := by
    intro value
    rcases value with ⟨metric, abelian, matter, longitudinal, boundary⟩
    simp
  right_inv := by
    intro value
    rcases value with ⟨metric, abelian, matter, longitudinal, boundary⟩
    simp

/-- Sectorwise sections represented in the ambient Candidate-A Hilbert space. -/
def ambientEquiv
    {MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection : Type*}
    (data : FiveSectorSectionCoordinateData
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection)
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)) :
    MetricSection × (AbelianSection × (MatterSection ×
      (LongitudinalSection × BoundarySection))) ≃ E :=
  data.productEquiv.trans coordinates.decomposition.toLinearEquiv.toEquiv.symm

/-- The represented ambient metric coordinate is exactly the supplied metric
sector equivalence. -/
theorem ambientEquiv_metricCoordinate
    {MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection : Type*}
    (data : FiveSectorSectionCoordinateData
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection)
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (sectionValue : MetricSection × (AbelianSection × (MatterSection ×
      (LongitudinalSection × BoundarySection)))) :
    fiveSectorMetricCoordinate
        (coordinates.decomposition (data.ambientEquiv coordinates sectionValue)) =
      data.metric sectionValue.1 := by
  rfl

/-- All five physical components of the represented ambient vector are the
supplied sector coordinates. -/
theorem ambientEquiv_allCoordinates
    {MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection : Type*}
    (data : FiveSectorSectionCoordinateData
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection)
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (sectionValue : MetricSection × (AbelianSection × (MatterSection ×
      (LongitudinalSection × BoundarySection)))) :
    fiveSectorMetricCoordinate
        (coordinates.decomposition (data.ambientEquiv coordinates sectionValue)) =
        data.metric sectionValue.1 ∧
    fiveSectorAbelianCoordinate
        (coordinates.decomposition (data.ambientEquiv coordinates sectionValue)) =
        data.abelian sectionValue.2.1 ∧
    fiveSectorMatterCoordinate
        (coordinates.decomposition (data.ambientEquiv coordinates sectionValue)) =
        data.matter sectionValue.2.2.1 ∧
    fiveSectorLongitudinalCoordinate
        (coordinates.decomposition (data.ambientEquiv coordinates sectionValue)) =
        data.longitudinal sectionValue.2.2.2.1 ∧
    fiveSectorBoundaryCoordinate
        (coordinates.decomposition (data.ambientEquiv coordinates sectionValue)) =
        data.boundary sectionValue.2.2.2.2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Public sector-preserving representation checkpoint. -/
theorem five_sector_representation_coordinates_gate
    {MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection : Type*}
    (data : FiveSectorSectionCoordinateData
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      MetricSection AbelianSection MatterSection LongitudinalSection BoundarySection)
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)) :
    Nonempty
      (MetricSection × (AbelianSection × (MatterSection ×
        (LongitudinalSection × BoundarySection))) ≃ E) ∧
    (∀ sectionValue,
      fiveSectorMetricCoordinate
          (coordinates.decomposition (data.ambientEquiv coordinates sectionValue)) =
          data.metric sectionValue.1) :=
  ⟨⟨data.ambientEquiv coordinates⟩,
    data.ambientEquiv_metricCoordinate coordinates⟩

end FiveSectorSectionCoordinateData

end
end P0EFTJanusProgramPFiveSectorRepresentationCoordinates4D
end JanusFormal
