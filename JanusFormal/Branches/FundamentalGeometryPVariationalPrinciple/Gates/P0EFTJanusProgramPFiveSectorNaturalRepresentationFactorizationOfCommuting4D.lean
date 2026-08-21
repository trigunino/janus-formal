import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOperatorBlockDiagonalization4D

/-!
# Natural five-sector factorization from projector commutation

A represented bounded linear family which commutes with the five physical
projectors induces the componentwise source/target factorization required by
the refined natural representation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalRepresentationFactorizationOfCommuting4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorRepresentationCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D
open P0EFTJanusProgramPFiveSectorOperatorBlockDiagonalization4D
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

/-- The commuting data at one parameter of a represented bounded linear
family. -/
def commutingOperatorData
    (operator : Real → State →L[Real] State)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (commutes : ∀ parameter sector state,
      operator parameter (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector (operator parameter state))
    (parameter : Real) :
    FiveSectorCommutingOperatorData
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      (operator parameter) where
  coordinates := coordinates
  commutes := commutes parameter

/-- Projector commutation supplies the exact five component operators of the
refined natural representation. -/
def fiveSectorNaturalRepresentationOperatorFactorizationOfCommuting
    (operator : Real → State →L[Real] State)
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family (fun parameter => operator parameter))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (commutes : ∀ parameter sector state,
      operator parameter (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector (operator parameter state)) :
    FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement where
  metricOperator parameter value :=
    (refinement.targetSectorCoordinates parameter).metric.symm
      ((commutingOperatorData operator coordinates commutes parameter).metricBlock
        ((refinement.sourceSectorCoordinates parameter).metric value))
  abelianOperator parameter value :=
    (refinement.targetSectorCoordinates parameter).abelian.symm
      ((commutingOperatorData operator coordinates commutes parameter).abelianBlock
        ((refinement.sourceSectorCoordinates parameter).abelian value))
  matterOperator parameter value :=
    (refinement.targetSectorCoordinates parameter).matter.symm
      ((commutingOperatorData operator coordinates commutes parameter).matterBlock
        ((refinement.sourceSectorCoordinates parameter).matter value))
  longitudinalOperator parameter value :=
    (refinement.targetSectorCoordinates parameter).longitudinal.symm
      ((commutingOperatorData operator coordinates commutes parameter).longitudinalBlock
        ((refinement.sourceSectorCoordinates parameter).longitudinal value))
  boundaryOperator parameter value :=
    (refinement.targetSectorCoordinates parameter).boundary.symm
      ((commutingOperatorData operator coordinates commutes parameter).boundaryBlock
        ((refinement.sourceSectorCoordinates parameter).boundary value))
  operator_product_agreement parameter sectionValue := by
    let data := commutingOperatorData operator coordinates commutes parameter
    have hBlock := data.conjugatedOperator_blockDiagonal
      ((refinement.sourceSectorCoordinates parameter).productEquiv
        (refinement.sourceProductEquiv parameter sectionValue))
    apply ((refinement.targetSectorCoordinates parameter).ambientEquiv
      coordinates).injective
    change ((refinement.targetProductEquiv parameter).trans
        ((refinement.targetSectorCoordinates parameter).ambientEquiv coordinates))
        (family.operator.apply (representation.objectAt parameter) sectionValue) = _
    rw [← refinement.targetEquiv_agreement parameter]
    rw [representation.operator_agreement]
    rw [refinement.sourceEquiv_agreement parameter]
    apply coordinates.decomposition.injective
    simpa [data, commutingOperatorData,
      FiveSectorCommutingOperatorData.conjugatedOperator,
      FiveSectorCommutingOperatorData.toProduct,
      FiveSectorCommutingOperatorData.fromProduct,
      FiveSectorSectionCoordinateData.ambientEquiv,
      FiveSectorSectionCoordinateData.productEquiv,
      fiveSectorMetricAxis, fiveSectorAbelianAxis, fiveSectorMatterAxis,
      fiveSectorLongitudinalAxis, fiveSectorBoundaryAxis,
      fiveSectorMetricCoordinate, fiveSectorAbelianCoordinate,
      fiveSectorMatterCoordinate, fiveSectorLongitudinalCoordinate,
      fiveSectorBoundaryCoordinate] using hBlock

end
end P0EFTJanusProgramPFiveSectorNaturalRepresentationFactorizationOfCommuting4D
end JanusFormal
