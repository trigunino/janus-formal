import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalLinearBaseFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementGeometricBismutFreedBaseFamily4D

/-!
# One multidimensional family for D11 naturality and Bismut--Freed geometry

A families-index theorem is only meaningful if the natural elliptic family and
the analytic BF family are the same operator family.  This packet enforces that
identity by construction: one literal

`H : Base → State →L[Real] State`

is simultaneously

* represented by a sector-covariant, componentwise D11 natural elliptic family;
* self-adjoint with a genuine actual-kernel complement family;
* the ambient source of the Green/logarithmic-trace BF connection and its local
  families-index curvature comparison.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalGeometricBismutFreedBaseFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalLinearBaseFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementGeometricBismutFreedBaseFamily4D
open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D
open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
open P0EFTJanusNaturalEllipticFamilyExistence

variable
  {Base State Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup State] [InnerProductSpace Real State] [CompleteSpace State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  {immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}

private abbrev AnchorReduced
    (operator : Base → State →L[Real] State) (anchor : Base) :=
  SelfAdjointKernelComplement (operator anchor)

/-- Unified natural/geometric multidimensional family. -/
structure FiveSectorNaturalGeometricBismutFreedBaseFamilyData
    (operator : Base → State →L[Real] State)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (anchor : Base)
    (reference : Base → AnchorReduced operator anchor →L[Real]
      AnchorReduced operator anchor) where
  natural : FiveSectorNaturalLinearBaseFamilyData
    (family := family) operator coordinates
  bismutFreed : SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData
    operator anchor reference

namespace FiveSectorNaturalGeometricBismutFreedBaseFamilyData

/-- The single ambient family is D11-natural and exactly componentwise. -/
def operator_blockFormula
    {operator : Base → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    {anchor : Base}
    {reference : Base → AnchorReduced operator anchor →L[Real]
      AnchorReduced operator anchor}
    (data : FiveSectorNaturalGeometricBismutFreedBaseFamilyData
      (family := family) operator coordinates anchor reference) :=
  data.natural.operator_blockFormula

/-- Every member of the same ambient BF family commutes with all five physical
projectors. -/
def operator_commutes_sectorProjector
    {operator : Base → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    {anchor : Base}
    {reference : Base → AnchorReduced operator anchor →L[Real]
      AnchorReduced operator anchor}
    (data : FiveSectorNaturalGeometricBismutFreedBaseFamilyData
      (family := family) operator coordinates anchor reference) :=
  data.natural.operator_commutes_sectorProjector

/-- Geometric BF one-form is the intrinsic trace one-form of the genuine
kernel-complement family of that same D11 operator. -/
theorem oneForm_eq_operatorTrace
    {operator : Base → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    {anchor : Base}
    {reference : Base → AnchorReduced operator anchor →L[Real]
      AnchorReduced operator anchor}
    (data : FiveSectorNaturalGeometricBismutFreedBaseFamilyData
      (family := family) operator coordinates anchor reference)
    (base direction : Base) :
    data.bismutFreed.geometric.geometry.oneForm base direction =
      ((data.bismutFreed.analytic.bismutFreedRealOneForm base direction : Real) :
        Complex) :=
  data.bismutFreed.oneForm_agreement base direction

/-- Derived BF curvature equals the local families-index two-form. -/
theorem curvature_eq_localIndex
    {operator : Base → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    {anchor : Base}
    {reference : Base → AnchorReduced operator anchor →L[Real]
      AnchorReduced operator anchor}
    (data : FiveSectorNaturalGeometricBismutFreedBaseFamilyData
      (family := family) operator coordinates anchor reference)
    (base first second : Base) :
    data.bismutFreed.geometric.curvature base first second =
      data.bismutFreed.localIndex.twoForm base first second :=
  data.bismutFreed.familiesIndex_agreement base first second

/-- Local index two-form also equals the intrinsic operator-trace curvature. -/
theorem localIndex_eq_operatorTraceCurvature
    {operator : Base → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    {anchor : Base}
    {reference : Base → AnchorReduced operator anchor →L[Real]
      AnchorReduced operator anchor}
    (data : FiveSectorNaturalGeometricBismutFreedBaseFamilyData
      (family := family) operator coordinates anchor reference)
    (base first second : Base) :
    data.bismutFreed.localIndex.twoForm base first second =
      ((data.bismutFreed.analytic.trace.bismutFreedTraceCurvature
        base first second : Real) : Complex) :=
  data.bismutFreed.localIndex_eq_operatorTraceCurvature base first second

/-- Public unified multidimensional family checkpoint. -/
theorem five_sector_natural_geometric_bismut_freed_base_family_gate
    (operator : Base → State →L[Real] State)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (anchor : Base)
    (reference : Base → AnchorReduced operator anchor →L[Real]
      AnchorReduced operator anchor)
    (data : FiveSectorNaturalGeometricBismutFreedBaseFamilyData
      (family := family) operator coordinates anchor reference) :
    (∀ base sector state,
      operator base (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector (operator base state)) ∧
    (∀ base direction,
      data.bismutFreed.geometric.geometry.oneForm base direction =
        ((data.bismutFreed.analytic.bismutFreedRealOneForm base direction : Real) :
          Complex)) ∧
    (∀ base first second,
      data.bismutFreed.localIndex.twoForm base first second =
        ((data.bismutFreed.analytic.trace.bismutFreedTraceCurvature
          base first second : Real) : Complex)) :=
  ⟨data.operator_commutes_sectorProjector,
    data.oneForm_eq_operatorTrace,
    data.localIndex_eq_operatorTraceCurvature⟩

end FiveSectorNaturalGeometricBismutFreedBaseFamilyData

end
end P0EFTJanusProgramPFiveSectorNaturalGeometricBismutFreedBaseFamily4D
end JanusFormal
