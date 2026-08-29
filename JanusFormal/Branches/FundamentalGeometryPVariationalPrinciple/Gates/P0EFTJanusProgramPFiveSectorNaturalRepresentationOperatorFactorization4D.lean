import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D

/-!
# Componentwise operator factorization of a five-sector D11 representation

Sector-preserving coordinate equivalences alone do not imply that the natural
operator acts independently on the five sectors.  This file records the exact
stronger statement: in the source/target product coordinates of the refined
representation, the D11 operator is literally the product of five component
operators.

The component operators are typed on the actual source/target section sectors;
no fixed-Hilbert operator is supplied here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
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

/-- Exact product factorization of the natural operator in the source/target
sector coordinates of one refined representation. -/
structure FiveSectorNaturalRepresentationOperatorFactorizationData
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates) where
  metricOperator : ∀ parameter,
    refinement.MetricSource parameter → refinement.MetricTarget parameter
  abelianOperator : ∀ parameter,
    refinement.AbelianSource parameter → refinement.AbelianTarget parameter
  matterOperator : ∀ parameter,
    refinement.MatterSource parameter → refinement.MatterTarget parameter
  longitudinalOperator : ∀ parameter,
    refinement.LongitudinalSource parameter →
      refinement.LongitudinalTarget parameter
  boundaryOperator : ∀ parameter,
    refinement.BoundarySource parameter → refinement.BoundaryTarget parameter
  operator_product_agreement : ∀ parameter sectionValue,
    refinement.targetProductEquiv parameter
        (family.operator.apply (representation.objectAt parameter) sectionValue) =
      (metricOperator parameter
          (refinement.sourceProductEquiv parameter sectionValue).1,
        (abelianOperator parameter
            (refinement.sourceProductEquiv parameter sectionValue).2.1,
          (matterOperator parameter
              (refinement.sourceProductEquiv parameter sectionValue).2.2.1,
            (longitudinalOperator parameter
                (refinement.sourceProductEquiv parameter sectionValue).2.2.2.1,
              boundaryOperator parameter
                (refinement.sourceProductEquiv parameter sectionValue).2.2.2.2))))

namespace FiveSectorNaturalRepresentationOperatorFactorizationData

/-- Metric block represented in the fixed Candidate-A metric coordinate. -/
def representedMetricBlock
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (value : Metric) : Metric :=
  (refinement.targetSectorCoordinates parameter).metric
    (data.metricOperator parameter
      ((refinement.sourceSectorCoordinates parameter).metric.symm value))

/-- Abelian block represented in the fixed Abelian coordinate. -/
def representedAbelianBlock
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (value : Abelian) : Abelian :=
  (refinement.targetSectorCoordinates parameter).abelian
    (data.abelianOperator parameter
      ((refinement.sourceSectorCoordinates parameter).abelian.symm value))

/-- Primitive SpinC matter block in the fixed matter coordinate. -/
def representedMatterBlock
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (value : Matter) : Matter :=
  (refinement.targetSectorCoordinates parameter).matter
    (data.matterOperator parameter
      ((refinement.sourceSectorCoordinates parameter).matter.symm value))

/-- Longitudinal/LL block in the fixed longitudinal coordinate. -/
def representedLongitudinalBlock
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (value : Longitudinal) : Longitudinal :=
  (refinement.targetSectorCoordinates parameter).longitudinal
    (data.longitudinalOperator parameter
      ((refinement.sourceSectorCoordinates parameter).longitudinal.symm value))

/-- Boundary/finite-BV block in the fixed boundary coordinate. -/
def representedBoundaryBlock
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real) (value : Boundary) : Boundary :=
  (refinement.targetSectorCoordinates parameter).boundary
    (data.boundaryOperator parameter
      ((refinement.sourceSectorCoordinates parameter).boundary.symm value))

/-- The D11 output product is exactly the five component outputs. -/
theorem operator_product_formula
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Real)
    (sectionValue : family.sourceFunctor.Section
      (representation.objectAt parameter)) :=
  data.operator_product_agreement parameter sectionValue

/-- Public componentwise D11 operator checkpoint. -/
theorem five_sector_natural_representation_operator_factorization_gate
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (data : FiveSectorNaturalRepresentationOperatorFactorizationData
      representation coordinates refinement) :
    ∀ parameter sectionValue,
      refinement.targetProductEquiv parameter
          (family.operator.apply (representation.objectAt parameter) sectionValue) =
        (data.metricOperator parameter
            (refinement.sourceProductEquiv parameter sectionValue).1,
          (data.abelianOperator parameter
              (refinement.sourceProductEquiv parameter sectionValue).2.1,
            (data.matterOperator parameter
                (refinement.sourceProductEquiv parameter sectionValue).2.2.1,
              (data.longitudinalOperator parameter
                  (refinement.sourceProductEquiv parameter sectionValue).2.2.2.1,
                data.boundaryOperator parameter
                  (refinement.sourceProductEquiv parameter sectionValue).2.2.2.2)))) :=
  data.operator_product_agreement

end FiveSectorNaturalRepresentationOperatorFactorizationData

end
end P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D
end JanusFormal
