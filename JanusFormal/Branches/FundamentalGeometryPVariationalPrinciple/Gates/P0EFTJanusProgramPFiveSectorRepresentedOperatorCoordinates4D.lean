import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D

/-!
# Fixed-Hilbert coordinates of a componentwise D11 operator

Once a represented natural operator has sectorwise source/target coordinates
and a componentwise operator factorization, each output coordinate in the fixed
Hilbert space depends only on the homologous input coordinate.  This is a pure
conjugation theorem; no linearity or additional operator hypothesis is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorRepresentedOperatorCoordinates4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D.FiveSectorNaturalRepresentationOperatorFactorizationData
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

namespace FiveSectorNaturalRepresentationOperatorFactorizationData

private theorem source_metric_raw_eq
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (parameter : Real) (state : State) :
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
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (parameter : Real) (state : State) :
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
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (parameter : Real) (state : State) :
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
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (parameter : Real) (state : State) :
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
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (parameter : Real) (state : State) :
    (refinement.sourceProductEquiv parameter
        ((representation.sourceEquiv parameter).symm state)).2.2.2.2 =
      (refinement.sourceSectorCoordinates parameter).boundary.symm
        (fiveSectorBoundaryCoordinate (coordinates.decomposition state)) := by
  apply (refinement.sourceSectorCoordinates parameter).boundary.injective
  simp only [Equiv.apply_symm_apply]
  have h := refinement.source_allCoordinates representation coordinates parameter
    ((representation.sourceEquiv parameter).symm state)
  simpa using h.2.2.2.2.symm

/-- Metric output coordinate depends only on the metric input coordinate. -/
theorem representedNaturalOperator_metricCoordinate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (state : State) :
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
  simpa [NaturalEllipticOperatorRepresentationData.representedNaturalOperator,
    representedMetricBlock, sourceSection] using hMetric

/-- Abelian output coordinate depends only on the Abelian input coordinate. -/
theorem representedNaturalOperator_abelianCoordinate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (state : State) :
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
  simpa [NaturalEllipticOperatorRepresentationData.representedNaturalOperator,
    representedAbelianBlock, sourceSection] using hAbelian

/-- Matter output coordinate depends only on the matter input coordinate. -/
theorem representedNaturalOperator_matterCoordinate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (state : State) :
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
  simpa [NaturalEllipticOperatorRepresentationData.representedNaturalOperator,
    representedMatterBlock, sourceSection] using hMatter

/-- Longitudinal output coordinate depends only on the longitudinal input. -/
theorem representedNaturalOperator_longitudinalCoordinate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (state : State) :
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
  simpa [NaturalEllipticOperatorRepresentationData.representedNaturalOperator,
    representedLongitudinalBlock, sourceSection] using hLongitudinal

/-- Boundary output coordinate depends only on the boundary input coordinate. -/
theorem representedNaturalOperator_boundaryCoordinate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (state : State) :
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
  simpa [NaturalEllipticOperatorRepresentationData.representedNaturalOperator,
    representedBoundaryBlock, sourceSection] using hBoundary

/-- Exact five-coordinate formula for the represented D11 operator. -/
theorem representedNaturalOperator_blockFormula
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (state : State) :
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

/-- Public represented block formula checkpoint. -/
theorem five_sector_represented_operator_coordinates_gate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement) :
    ∀ parameter state,
      coordinates.decomposition
          (representation.representedNaturalOperator parameter state) =
        fiveSectorMetricAxis
            (data.representedMetricBlock representation coordinates refinement
              parameter
              (fiveSectorMetricCoordinate (coordinates.decomposition state))) +
          fiveSectorAbelianAxis
            (data.representedAbelianBlock representation coordinates refinement
              parameter
              (fiveSectorAbelianCoordinate (coordinates.decomposition state))) +
          fiveSectorMatterAxis
            (data.representedMatterBlock representation coordinates refinement
              parameter
              (fiveSectorMatterCoordinate (coordinates.decomposition state))) +
          fiveSectorLongitudinalAxis
            (data.representedLongitudinalBlock representation coordinates refinement
              parameter
              (fiveSectorLongitudinalCoordinate (coordinates.decomposition state))) +
          fiveSectorBoundaryAxis
            (data.representedBoundaryBlock representation coordinates refinement
              parameter
              (fiveSectorBoundaryCoordinate (coordinates.decomposition state))) :=
  representedNaturalOperator_blockFormula representation coordinates refinement data

end FiveSectorNaturalRepresentationOperatorFactorizationData

end
end P0EFTJanusProgramPFiveSectorRepresentedOperatorCoordinates4D
end JanusFormal
