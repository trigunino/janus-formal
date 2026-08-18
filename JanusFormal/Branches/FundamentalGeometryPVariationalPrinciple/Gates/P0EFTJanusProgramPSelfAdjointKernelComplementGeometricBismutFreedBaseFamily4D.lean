import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedBaseFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D

/-!
# Geometric BF/families-index package rooted in a genuine ambient Hessian family

All operator-theoretic ingredients are now generated from one ambient
self-adjoint family `H_b` and its true kernel complements.  This file adds only
the genuinely geometric identifications:

* the complex BF one-form equals the complexification of the intrinsic relative
  trace one-form;
* their Frechet derivatives agree;
* the curvature thereby derived from that one-form equals the local
  families-index two-form.

No independent reduced actual family and no independent BF curvature function
are accepted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementGeometricBismutFreedBaseFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedBaseFamily4D
open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D
open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
open P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D

variable {Base E : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

private abbrev AnchorReduced
    (actual : Base → E →L[Real] E) (anchor : Base) :=
  SelfAdjointKernelComplement (actual anchor)

/-- Complete multidimensional BF/families-index comparison rooted in the true
kernel complements of one ambient actual family. -/
structure SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData
    (actual : Base → E →L[Real] E)
    (anchor : Base)
    (reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor) where
  analytic : SelfAdjointKernelComplementBismutFreedBaseFamilyData
    actual anchor reference
  geometric : DifferentiableLinearGeometricBismutFreedOneFormData Base
  oneForm_agreement : ∀ base direction,
    geometric.geometry.oneForm base direction =
      ((analytic.bismutFreedRealOneForm base direction : Real) : Complex)
  derivative_agreement : ∀ base first second,
    geometric.derivative base first second =
      ((analytic.trace.bismutFreedOneFormDerivative base first second : Real) :
        Complex)
  localIndex : LocalFamiliesIndexTwoFormData Base
  familiesIndex_agreement : ∀ base first second,
    geometric.curvature base first second =
      localIndex.twoForm base first second

namespace SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData

/-- Forget the ambient-kernel origin and recover the generic differential
operator/geometric comparison. -/
def toDifferentiableOperatorGeometricComparison
    {actual : Base → E →L[Real] E}
    {anchor : Base}
    {reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor}
    (data : SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData
      actual anchor reference) :
    DifferentiableOperatorGeometricBismutFreedComparisonData
      data.analytic.actualGap.fixedOperator reference where
  operator := data.analytic.trace
  geometric := data.geometric
  oneForm_agreement := data.oneForm_agreement
  derivative_agreement := data.derivative_agreement

/-- Full differential families-index comparison. -/
def toDifferentialFamiliesIndexComparison
    {actual : Base → E →L[Real] E}
    {anchor : Base}
    {reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor}
    (data : SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData
      actual anchor reference) :
    DifferentialFamiliesIndexComparisonData
      data.analytic.actualGap.fixedOperator reference where
  comparison := data.toDifferentiableOperatorGeometricComparison
  localIndex := data.localIndex
  familiesIndex_agreement := data.familiesIndex_agreement

/-- BF curvature equals the complexified intrinsic operator-trace curvature. -/
theorem curvature_eq_operatorTrace
    {actual : Base → E →L[Real] E}
    {anchor : Base}
    {reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor}
    (data : SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData
      actual anchor reference)
    (base first second : Base) :
    data.geometric.curvature base first second =
      ((data.analytic.trace.bismutFreedTraceCurvature base first second : Real) :
        Complex) :=
  data.toDifferentiableOperatorGeometricComparison.curvature_eq_operatorTrace
    base first second

/-- Local families-index form equals the same intrinsic trace curvature. -/
theorem localIndex_eq_operatorTraceCurvature
    {actual : Base → E →L[Real] E}
    {anchor : Base}
    {reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor}
    (data : SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData
      actual anchor reference)
    (base first second : Base) :
    data.localIndex.twoForm base first second =
      ((data.analytic.trace.bismutFreedTraceCurvature base first second : Real) :
        Complex) :=
  data.toDifferentialFamiliesIndexComparison.localIndex_eq_operatorTraceCurvature
    base first second

/-- Public genuine-ambient-family multidimensional BF checkpoint. -/
theorem self_adjoint_kernel_complement_geometric_bismut_freed_base_family_gate
    (actual : Base → E →L[Real] E)
    (anchor : Base)
    (reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor)
    (data : SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData
      actual anchor reference) :
    (∀ base direction,
      data.geometric.geometry.oneForm base direction =
        ((data.analytic.bismutFreedRealOneForm base direction : Real) : Complex)) ∧
    (∀ base first second,
      data.geometric.curvature base first second =
        ((data.analytic.trace.bismutFreedTraceCurvature base first second : Real) :
          Complex)) ∧
    (∀ base first second,
      data.localIndex.twoForm base first second =
        ((data.analytic.trace.bismutFreedTraceCurvature base first second : Real) :
          Complex)) :=
  ⟨data.oneForm_agreement,
    data.curvature_eq_operatorTrace,
    data.localIndex_eq_operatorTraceCurvature⟩

end SelfAdjointKernelComplementGeometricBismutFreedBaseFamilyData

end
end P0EFTJanusProgramPSelfAdjointKernelComplementGeometricBismutFreedBaseFamily4D
end JanusFormal
