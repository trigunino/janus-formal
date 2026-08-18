import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementBaseUniformGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D

/-!
# Multidimensional BF trace family from genuine actual-kernel complements

The arbitrary-base logarithmic trace is attached here to the reduced family
constructed from the genuine ambient kernels.  The trace packet is required to
use exactly the uniform-gap analytic family obtained by transporting
`H_b | (ker H_b)ᗮ` to the anchor complement.

Thus the operator one-form cannot be based on an independently supplied fixed
Hilbert family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedBaseFamily4D

set_option autoImplicit false
noncomputable section

universe b e

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBaseUniformGap4D
open P0EFTJanusProgramPSelfAdjointUniformGapBaseFamily4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
open P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D

variable {Base : Type b} {E : Type e}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

private abbrev AnchorReduced
    (actual : Base → E →L[Real] E) (anchor : Base) :=
  SelfAdjointKernelComplement (actual anchor)

/-- Multidimensional actual/reference logarithmic trace packet rooted in the
true kernel complements of the ambient actual family. -/
structure SelfAdjointKernelComplementBismutFreedBaseFamilyData
    (actual : Base → E →L[Real] E)
    (anchor : Base)
    (reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor) where
  actual_selfAdjoint : ∀ base, IsSelfAdjoint (actual base)
  actualGap : SelfAdjointKernelComplementBaseUniformGapTrivializationData
    actual actual_selfAdjoint anchor
  trace : DifferentiableRelativeIntrinsicTraceOneFormData.{b, e, 0}
    actualGap.fixedOperator reference
  actual_analytic_eq :
    trace.trace.actualTrace.family.analytic =
      actualGap.toUniformGapBaseFamily

namespace SelfAdjointKernelComplementBismutFreedBaseFamilyData

/-- The actual logarithmic derivative family is literally based on the genuine
transported kernel-complement Green family. -/
theorem actual_green_eq_genuine
    {actual : Base → E →L[Real] E}
    {anchor : Base}
    {reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor}
    (data : SelfAdjointKernelComplementBismutFreedBaseFamilyData
      actual anchor reference)
    (base : Base) :
    data.trace.trace.actualTrace.family.analytic.green base =
      data.actualGap.fixedGreen base := by
  rw [data.actual_analytic_eq]
  rfl

/-- Genuine reduced actual operator used by the multidimensional trace. -/
def actualReducedOperator
    {actual : Base → E →L[Real] E}
    {anchor : Base}
    {reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor}
    (data : SelfAdjointKernelComplementBismutFreedBaseFamilyData
      actual anchor reference) :=
  data.actualGap.fixedOperator

/-- Intrinsic relative BF trace one-form. -/
def bismutFreedRealOneForm
    {actual : Base → E →L[Real] E}
    {anchor : Base}
    {reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor}
    (data : SelfAdjointKernelComplementBismutFreedBaseFamilyData
      actual anchor reference)
    (base : Base) : Base →L[Real] Real :=
  data.trace.trace.bismutFreedRealOneForm base

/-- Curvature of the intrinsic trace one-form, derived from its Frechet
derivative. -/
def traceCurvature
    {actual : Base → E →L[Real] E}
    {anchor : Base}
    {reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor}
    (data : SelfAdjointKernelComplementBismutFreedBaseFamilyData
      actual anchor reference)
    (base first second : Base) : Real :=
  data.trace.bismutFreedTraceCurvature base first second

/-- Public genuine-kernel multidimensional trace checkpoint. -/
theorem self_adjoint_kernel_complement_bismut_freed_base_family_gate
    (actual : Base → E →L[Real] E)
    (anchor : Base)
    (reference : Base → AnchorReduced actual anchor →L[Real]
      AnchorReduced actual anchor)
    (data : SelfAdjointKernelComplementBismutFreedBaseFamilyData
      actual anchor reference) :
    (∀ base,
      data.trace.trace.actualTrace.family.analytic.green base =
        data.actualGap.fixedGreen base) ∧
    (∀ base,
      ‖data.actualGap.fixedGreen base‖ ≤ data.actualGap.gap⁻¹) ∧
    (∀ base first second,
      data.traceCurvature base first second =
        -data.traceCurvature base second first) :=
  ⟨data.actual_green_eq_genuine,
    data.actualGap.fixedGreen_opNorm_le,
    data.trace.bismutFreedTraceCurvature_antisymm⟩

end SelfAdjointKernelComplementBismutFreedBaseFamilyData

end
end P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedBaseFamily4D
end JanusFormal
