import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalBaseRepresentation4D

/-!
# Componentwise D11 operator factorization over an arbitrary base

The natural operator is required to act componentwise in the actual source and
target sector types of the multidimensional representation.  This is the
base-independent counterpart of the one-parameter factorization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalBaseOperatorFactorization4D

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

/-- Exact componentwise factorization of the natural operator in the raw
source/target sector types. -/
structure FiveSectorNaturalBaseOperatorFactorizationData
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
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

namespace FiveSectorNaturalBaseOperatorFactorizationData

/-- Fixed metric-coordinate block. -/
def representedMetricBlock
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (value : Metric) : Metric :=
  (refinement.targetSectorCoordinates parameter).metric
    (data.metricOperator parameter
      ((refinement.sourceSectorCoordinates parameter).metric.symm value))

/-- Fixed Abelian-coordinate block. -/
def representedAbelianBlock
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (value : Abelian) : Abelian :=
  (refinement.targetSectorCoordinates parameter).abelian
    (data.abelianOperator parameter
      ((refinement.sourceSectorCoordinates parameter).abelian.symm value))

/-- Fixed primitive SpinC matter block. -/
def representedMatterBlock
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (value : Matter) : Matter :=
  (refinement.targetSectorCoordinates parameter).matter
    (data.matterOperator parameter
      ((refinement.sourceSectorCoordinates parameter).matter.symm value))

/-- Fixed longitudinal/LL block. -/
def representedLongitudinalBlock
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (value : Longitudinal) : Longitudinal :=
  (refinement.targetSectorCoordinates parameter).longitudinal
    (data.longitudinalOperator parameter
      ((refinement.sourceSectorCoordinates parameter).longitudinal.symm value))

/-- Fixed boundary/finite-BV block. -/
def representedBoundaryBlock
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
      representation coordinates refinement)
    (parameter : Parameter) (value : Boundary) : Boundary :=
  (refinement.targetSectorCoordinates parameter).boundary
    (data.boundaryOperator parameter
      ((refinement.sourceSectorCoordinates parameter).boundary.symm value))

/-- Public base-independent operator factorization checkpoint. -/
theorem five_sector_natural_base_operator_factorization_gate
    (representation : NaturalEllipticOperatorBaseRepresentationData
      Parameter State immersionCategory family representedOperator)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalBaseRepresentationData
      representation coordinates)
    (data : FiveSectorNaturalBaseOperatorFactorizationData
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

end FiveSectorNaturalBaseOperatorFactorizationData

end
end P0EFTJanusProgramPFiveSectorNaturalBaseOperatorFactorization4D
end JanusFormal
