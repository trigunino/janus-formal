import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalSectionFunctorProducts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertCoordinates4D

/-!
# Five-sector D11 natural section functors and operators

This file matches the exact right-associated five-sector product used by the
Candidate-A Hilbert decomposition.  It is purely categorical: no physical
sector functor is invented here.  Given five existing natural functors and five
natural operators, it builds their canonical five-sector product and inherits
naturality componentwise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalFunctor4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusProgramPNaturalSectionFunctorProducts4D

variable {immersionCategory : SpinCImmersionCategory}

/-- Right-associated product of five natural section functors, in the same
sector order as `FiveSectorProduct`. -/
def fiveSectorNaturalSectionFunctor
    (Metric Abelian Matter Longitudinal Boundary :
      NaturalSectionFunctor immersionCategory) :
    NaturalSectionFunctor immersionCategory :=
  naturalSectionFunctorProd Metric
    (naturalSectionFunctorProd Abelian
      (naturalSectionFunctorProd Matter
        (naturalSectionFunctorProd Longitudinal Boundary)))

/-- Five-sector block-diagonal natural operator. -/
def fiveSectorNaturalOperator
    {MetricS MetricT AbelianS AbelianT MatterS MatterT
      LongitudinalS LongitudinalT BoundaryS BoundaryT :
        NaturalSectionFunctor immersionCategory}
    (metric : NaturalOperator immersionCategory MetricS MetricT)
    (abelian : NaturalOperator immersionCategory AbelianS AbelianT)
    (matter : NaturalOperator immersionCategory MatterS MatterT)
    (longitudinal : NaturalOperator immersionCategory LongitudinalS LongitudinalT)
    (boundary : NaturalOperator immersionCategory BoundaryS BoundaryT) :
    NaturalOperator immersionCategory
      (fiveSectorNaturalSectionFunctor MetricS AbelianS MatterS LongitudinalS BoundaryS)
      (fiveSectorNaturalSectionFunctor MetricT AbelianT MatterT LongitudinalT BoundaryT) :=
  naturalOperatorProd metric
    (naturalOperatorProd abelian
      (naturalOperatorProd matter
        (naturalOperatorProd longitudinal boundary)))

/-- Apply the five-sector operator in explicit physical coordinates. -/
theorem fiveSectorNaturalOperator_apply
    {MetricS MetricT AbelianS AbelianT MatterS MatterT
      LongitudinalS LongitudinalT BoundaryS BoundaryT :
        NaturalSectionFunctor immersionCategory}
    (metric : NaturalOperator immersionCategory MetricS MetricT)
    (abelian : NaturalOperator immersionCategory AbelianS AbelianT)
    (matter : NaturalOperator immersionCategory MatterS MatterT)
    (longitudinal : NaturalOperator immersionCategory LongitudinalS LongitudinalT)
    (boundary : NaturalOperator immersionCategory BoundaryS BoundaryT)
    (object : immersionCategory.category.Obj)
    (sectionValue :
      (fiveSectorNaturalSectionFunctor MetricS AbelianS MatterS LongitudinalS BoundaryS).
        Section object) :
    (fiveSectorNaturalOperator metric abelian matter longitudinal boundary).apply
        object sectionValue =
      (metric.apply object sectionValue.1,
        (abelian.apply object sectionValue.2.1,
          (matter.apply object sectionValue.2.2.1,
            (longitudinal.apply object sectionValue.2.2.2.1,
              boundary.apply object sectionValue.2.2.2.2)))) :=
  rfl

/-- Five-sector naturality is inherited from the five component operators. -/
theorem five_sector_natural_operator_gate
    {MetricS MetricT AbelianS AbelianT MatterS MatterT
      LongitudinalS LongitudinalT BoundaryS BoundaryT :
        NaturalSectionFunctor immersionCategory}
    (metric : NaturalOperator immersionCategory MetricS MetricT)
    (abelian : NaturalOperator immersionCategory AbelianS AbelianT)
    (matter : NaturalOperator immersionCategory MatterS MatterT)
    (longitudinal : NaturalOperator immersionCategory LongitudinalS LongitudinalT)
    (boundary : NaturalOperator immersionCategory BoundaryS BoundaryT) :
    ∀ {source target : immersionCategory.category.Obj}
      (morphism : AdmissibleMorphism immersionCategory source target)
      (sectionValue :
        (fiveSectorNaturalSectionFunctor MetricS AbelianS MatterS LongitudinalS BoundaryS).
          Section target),
      (fiveSectorNaturalSectionFunctor MetricT AbelianT MatterT LongitudinalT BoundaryT).
          pullback morphism
            ((fiveSectorNaturalOperator metric abelian matter longitudinal boundary).
              apply target sectionValue) =
        (fiveSectorNaturalOperator metric abelian matter longitudinal boundary).
          apply source
            ((fiveSectorNaturalSectionFunctor MetricS AbelianS MatterS LongitudinalS BoundaryS).
              pullback morphism sectionValue) :=
  (fiveSectorNaturalOperator metric abelian matter longitudinal boundary).naturality

end
end P0EFTJanusProgramPFiveSectorNaturalFunctor4D
end JanusFormal
