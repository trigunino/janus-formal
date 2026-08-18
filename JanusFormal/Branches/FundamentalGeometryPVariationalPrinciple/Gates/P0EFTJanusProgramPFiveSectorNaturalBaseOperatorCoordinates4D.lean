import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalBaseOperatorFactorization4D

/-!
# Fixed-Hilbert block coordinates of an arbitrary-base D11 family

A componentwise natural operator on the raw sector section types becomes an
exact componentwise map in the one fixed five-sector Hilbert coordinates.  This
is the multidimensional counterpart of the established one-parameter formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalBaseOperatorCoordinates4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorBaseRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalBaseRepresentation4D
open P0EFTJanusProgramPFiveSectorNaturalBaseOperatorFactorization4D
open P0EFTJanusProgramPFiveSectorNaturalBaseOperatorFactorization4D.FiveSectorNaturalBaseOperatorFactorizationData
open P0EFTJanusNaturalEllipticFamilyExistence

variable
  {Parameter State Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup State] [InnerProductSpace Real State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  {immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}
  {representedOperator : Parameter → State → State}

namespace FiveSectorNaturalBaseOperatorFactorizationData

private theorem source_metric_raw_eq
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (parameter : Parameter) (state : State) :
    (refinement.sourceProductEquiv parameter
        ((representation.sourceEquiv parameter).symm state)).1 =
      (refinement.sourceSectorCoordinates parameter).metric.symm
        (fiveSectorMetricCoordinate (coordinates.decomposition state)) := by
  apply (refinement.sourceSectorCoordinates parameter).metric.injective
  simp only [Equiv.apply_symm_apply]
  have h := refinement.source_allCoordinates representation coordinates parameter
    ((representation.sourceEquiv parameter).symm state)
  simpa using h.1.symm

private theorem source_abelian_raw_eq
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (parameter : Parameter) (state : State) :
    (refinement.sourceProductEquiv parameter
        ((representation.sourceEquiv parameter).symm state)).2.1 =
      (refinement.sourceSectorCoordinates parameter).abelian.symm
        (fiveSectorAbelianCoordinate (coordinates.decomposition state)) := by
  apply (refinement.sourceSectorCoordinates parameter).abelian.injective
  simp only [Equiv.apply_symm_apply]
  have h := refinement.source_allCoordinates representation coordinates parameter
    ((representation.sourceEquiv parameter).symm state)
  simpa using h.2.1.symm

private theorem source_matter_raw_eq
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (parameter : Parameter) (state : State) :
    (refinement.sourceProductEquiv parameter
        ((representation.sourceEquiv parameter).symm state)).2.2.1 =
      (refinement.sourceSectorCoordinates parameter).matter.symm
        (fiveSectorMatterCoordinate (coordinates.decomposition state)) := by
  apply (refinement.sourceSectorCoordinates parameter).matter.injective
  simp only [Equiv.apply_symm_apply]
  have h := refinement.source_allCoordinates representation coordinates parameter
    ((representation.sourceEquiv parameter).symm state)
  simpa using h.2.2.1.symm

private theorem source_longitudinal_raw_eq
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (parameter : Parameter) (state : State) :
    (refinement.sourceProductEquiv parameter
        ((representation.sourceEquiv parameter).symm state)).2.2.2.1 =
      (refinement.sourceSectorCoordinates parameter).longitudinal.symm
        (fiveSectorLongitudinalCoordinate (coordinates.decomposition state)) := by
  apply (refinement.sourceSectorCoordinates parameter).longitudinal.injective
  simp only [Equiv.apply_symm_apply]
  have h := refinement.source_allCoordinates representation coordinates parameter
    ((representation.sourceEquiv parameter).symm state)
  simpa using h.2.2.2.1.symm

private theorem source_boundary_raw_eq
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (parameter : Parameter) (state : State) :
    (refinement.sourceProductEquiv parameter
        ((representation.sourceEquiv parameter).symm state)).2.2.2.2 =
      (refinement.sourceSectorCoordinates parameter).boundary.symm
        (fiveSectorBoundaryCoordinate (coordinates.decomposition state)) := by
  apply (refinement.sourceSectorCoordinates parameter).boundary.injective
  simp only [Equiv.apply_symm_apply]
  have h := refinement.source_allCoordinates representation coordinates parameter
    ((representation.sourceEquiv parameter).symm state)
  simpa using h.2.2.2.2.symm

/-- Metric coordinate formula. -/
theorem representedNaturalOperator_metricCoordinate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (state : State) :
    fiveSectorMetricCoordinate
        (coordinates.decomposition
          (representation.representedNaturalOperator parameter state)) =
      data.representedMetricBlock representation coordinates refinement parameter
        (fiveSectorMetricCoordinate (coordinates.decomposition state)) := by
  let sourceSection := (representation.sourceEquiv parameter).symm state
  have hTarget := refinement.target_allCoordinates representation coordinates
    parameter (family.operator.apply (representation.objectAt parameter) sourceSection)
  have hProduct := data.operator_product_agreement parameter sourceSection
  have hMetric := hTarget.1
  rw [hProduct] at hMetric
  have hRaw := source_metric_raw_eq representation coordinates refinement
    parameter state
  rw [hRaw] at hMetric
  simpa [NaturalEllipticOperatorBaseRepresentationData.representedNaturalOperator,
    representedMetricBlock, sourceSection] using hMetric

/-- Abelian coordinate formula. -/
theorem representedNaturalOperator_abelianCoordinate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (state : State) :
    fiveSectorAbelianCoordinate
        (coordinates.decomposition
          (representation.representedNaturalOperator parameter state)) =
      data.representedAbelianBlock representation coordinates refinement parameter
        (fiveSectorAbelianCoordinate (coordinates.decomposition state)) := by
  let sourceSection := (representation.sourceEquiv parameter).symm state
  have hTarget := refinement.target_allCoordinates representation coordinates
    parameter (family.operator.apply (representation.objectAt parameter) sourceSection)
  have hProduct := data.operator_product_agreement parameter sourceSection
  have hAbelian := hTarget.2.1
  rw [hProduct] at hAbelian
  have hRaw := source_abelian_raw_eq representation coordinates refinement
    parameter state
  rw [hRaw] at hAbelian
  simpa [NaturalEllipticOperatorBaseRepresentationData.representedNaturalOperator,
    representedAbelianBlock, sourceSection] using hAbelian

/-- Matter coordinate formula. -/
theorem representedNaturalOperator_matterCoordinate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (state : State) :
    fiveSectorMatterCoordinate
        (coordinates.decomposition
          (representation.representedNaturalOperator parameter state)) =
      data.representedMatterBlock representation coordinates refinement parameter
        (fiveSectorMatterCoordinate (coordinates.decomposition state)) := by
  let sourceSection := (representation.sourceEquiv parameter).symm state
  have hTarget := refinement.target_allCoordinates representation coordinates
    parameter (family.operator.apply (representation.objectAt parameter) sourceSection)
  have hProduct := data.operator_product_agreement parameter sourceSection
  have hMatter := hTarget.2.2.1
  rw [hProduct] at hMatter
  have hRaw := source_matter_raw_eq representation coordinates refinement
    parameter state
  rw [hRaw] at hMatter
  simpa [NaturalEllipticOperatorBaseRepresentationData.representedNaturalOperator,
    representedMatterBlock, sourceSection] using hMatter

/-- Longitudinal coordinate formula. -/
theorem representedNaturalOperator_longitudinalCoordinate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (state : State) :
    fiveSectorLongitudinalCoordinate
        (coordinates.decomposition
          (representation.representedNaturalOperator parameter state)) =
      data.representedLongitudinalBlock representation coordinates refinement
        parameter
        (fiveSectorLongitudinalCoordinate (coordinates.decomposition state)) := by
  let sourceSection := (representation.sourceEquiv parameter).symm state
  have hTarget := refinement.target_allCoordinates representation coordinates
    parameter (family.operator.apply (representation.objectAt parameter) sourceSection)
  have hProduct := data.operator_product_agreement parameter sourceSection
  have hLongitudinal := hTarget.2.2.2.1
  rw [hProduct] at hLongitudinal
  have hRaw := source_longitudinal_raw_eq representation coordinates refinement
    parameter state
  rw [hRaw] at hLongitudinal
  simpa [NaturalEllipticOperatorBaseRepresentationData.representedNaturalOperator,
    representedLongitudinalBlock, sourceSection] using hLongitudinal

/-- Boundary coordinate formula. -/
theorem representedNaturalOperator_boundaryCoordinate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (state : State) :
    fiveSectorBoundaryCoordinate
        (coordinates.decomposition
          (representation.representedNaturalOperator parameter state)) =
      data.representedBoundaryBlock representation coordinates refinement parameter
        (fiveSectorBoundaryCoordinate (coordinates.decomposition state)) := by
  let sourceSection := (representation.sourceEquiv parameter).symm state
  have hTarget := refinement.target_allCoordinates representation coordinates
    parameter (family.operator.apply (representation.objectAt parameter) sourceSection)
  have hProduct := data.operator_product_agreement parameter sourceSection
  have hBoundary := hTarget.2.2.2.2
  rw [hProduct] at hBoundary
  have hRaw := source_boundary_raw_eq representation coordinates refinement
    parameter state
  rw [hRaw] at hBoundary
  simpa [NaturalEllipticOperatorBaseRepresentationData.representedNaturalOperator,
    representedBoundaryBlock, sourceSection] using hBoundary

/-- Exact five-block product formula for the represented multidimensional D11
operator. -/
theorem representedNaturalOperator_blockFormula
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (state : State) :
    coordinates.decomposition
        (representation.representedNaturalOperator parameter state) =
      fiveSectorMetricAxis
          (data.representedMetricBlock representation coordinates refinement
            parameter (fiveSectorMetricCoordinate (coordinates.decomposition state))) +
        fiveSectorAbelianAxis
          (data.representedAbelianBlock representation coordinates refinement
            parameter (fiveSectorAbelianCoordinate (coordinates.decomposition state))) +
        fiveSectorMatterAxis
          (data.representedMatterBlock representation coordinates refinement
            parameter (fiveSectorMatterCoordinate (coordinates.decomposition state))) +
        fiveSectorLongitudinalAxis
          (data.representedLongitudinalBlock representation coordinates refinement
            parameter (fiveSectorLongitudinalCoordinate (coordinates.decomposition state))) +
        fiveSectorBoundaryAxis
          (data.representedBoundaryBlock representation coordinates refinement
            parameter (fiveSectorBoundaryCoordinate (coordinates.decomposition state))) := by
  have hDecompose := fiveSector_axis_decomposition
    (coordinates.decomposition
      (representation.representedNaturalOperator parameter state))
  rw [representedNaturalOperator_metricCoordinate representation coordinates
      refinement data parameter state,
    representedNaturalOperator_abelianCoordinate representation coordinates
      refinement data parameter state,
    representedNaturalOperator_matterCoordinate representation coordinates
      refinement data parameter state,
    representedNaturalOperator_longitudinalCoordinate representation coordinates
      refinement data parameter state,
    representedNaturalOperator_boundaryCoordinate representation coordinates
      refinement data parameter state] at hDecompose
  exact hDecompose.symm

/-- Public arbitrary-base represented block-formula checkpoint. -/
theorem five_sector_natural_base_operator_coordinates_gate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement) :
    ∀ parameter state,
      coordinates.decomposition
          (representation.representedNaturalOperator parameter state) =
        fiveSectorMetricAxis
            (data.representedMetricBlock representation coordinates refinement
              parameter (fiveSectorMetricCoordinate (coordinates.decomposition state))) +
          fiveSectorAbelianAxis
            (data.representedAbelianBlock representation coordinates refinement
              parameter (fiveSectorAbelianCoordinate (coordinates.decomposition state))) +
          fiveSectorMatterAxis
            (data.representedMatterBlock representation coordinates refinement
              parameter (fiveSectorMatterCoordinate (coordinates.decomposition state))) +
          fiveSectorLongitudinalAxis
            (data.representedLongitudinalBlock representation coordinates refinement
              parameter (fiveSectorLongitudinalCoordinate (coordinates.decomposition state))) +
          fiveSectorBoundaryAxis
            (data.representedBoundaryBlock representation coordinates refinement
              parameter (fiveSectorBoundaryCoordinate (coordinates.decomposition state))) :=
  representedNaturalOperator_blockFormula representation coordinates refinement data

end FiveSectorNaturalBaseOperatorFactorizationData

end
end P0EFTJanusProgramPFiveSectorNaturalBaseOperatorCoordinates4D
end JanusFormal
