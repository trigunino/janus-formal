import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D

/-!
# Bismut--Freed families from varying actual-kernel complements

This file joins the two missing family-level pieces:

* a unitary trivialization of the varying genuine spaces `(ker H_a)ᗮ`;
* the intrinsic trace of the logarithmic derivative on the resulting fixed
  Hilbert space.

The actual reduced family is not supplied independently.  It is the unitary
transport of the genuine self-adjoint kernel-complement restrictions.  Once
its derivative, inverse derivative and intrinsic nuclear traces are proved,
the relative Bismut--Freed connection follows from the existing trace bridge.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000

noncomputable section

open P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

universe e i

variable {E : Type e}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

private abbrev BaseReduced
    (actual : Real → E →L[Real] E) :=
  SelfAdjointKernelComplement (actual 0)

/-- Complete family-index packet after choosing one unitary trivialization of
the genuine actual-kernel complements. -/
structure SelfAdjointKernelComplementBismutFreedFamilyData
    (actual : Real → E →L[Real] E)
    (reference : Real → BaseReduced actual →L[Real] BaseReduced actual) where
  actual_selfAdjoint : ∀ parameter, IsSelfAdjoint (actual parameter)
  actualGap :
    SelfAdjointKernelComplementUniformGapTrivializationData actual
      actual_selfAdjoint
  actualDifferentiable :
    DifferentiableSelfAdjointUniformGapFamilyData actualGap.fixedOperator
  actualAnalytic_eq :
    actualDifferentiable.analytic = actualGap.toUniformGapFamily
  actualInverse : actualDifferentiable.GreenDifferentiabilityData
  actualTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{e, i}
      (actualDifferentiable.logarithmicDerivativeOperator parameter)
  referenceTrace :
    IntrinsicLogarithmicDerivativeTraceData.{e, i} reference
  zetaFamily : RelativeHeatMellinZetaFamilyData
  coefficient_agreement : ∀ parameter,
    relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter =
      (-(intrinsicNuclearTrace (actualTraceClass parameter) -
          referenceTrace.trace parameter) : Real)

namespace SelfAdjointKernelComplementBismutFreedFamilyData

/-- Intrinsic logarithmic trace of the transported genuine reduced family. -/
def actualTrace
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (data : SelfAdjointKernelComplementBismutFreedFamilyData actual reference) :
    IntrinsicLogarithmicDerivativeTraceData data.actualGap.fixedOperator where
  family := data.actualDifferentiable
  inverse := data.actualInverse
  traceClass := data.actualTraceClass

/-- Actual-minus-reference intrinsic logarithmic trace. -/
def relativeTrace
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (data : SelfAdjointKernelComplementBismutFreedFamilyData actual reference) :
    RelativeIntrinsicLogarithmicDerivativeTraceData
      data.actualGap.fixedOperator reference where
  actualTrace := data.actualTrace
  referenceTrace := data.referenceTrace

/-- Operator-defined Bismut--Freed connection. -/
def toBismutFreed
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (data : SelfAdjointKernelComplementBismutFreedFamilyData actual reference) :
    RelativeBismutFreedTraceConnectionData data.actualGap.fixedOperator reference where
  operatorTrace := data.relativeTrace
  zetaFamily := data.zetaFamily
  coefficient_agreement := by
    intro parameter
    simpa [RelativeIntrinsicLogarithmicDerivativeTraceData.bismutFreedCoefficient,
      RelativeIntrinsicLogarithmicDerivativeTraceData.trace,
      IntrinsicLogarithmicDerivativeTraceData.trace,
      actualTrace, relativeTrace] using data.coefficient_agreement parameter

/-- At parameter zero the transported actual family is exactly the canonical
restriction of the original base operator to its true kernel complement. -/
theorem fixedOperator_zero
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (data : SelfAdjointKernelComplementBismutFreedFamilyData actual reference) :
    data.actualGap.fixedOperator 0 =
      selfAdjointKernelComplementOperator (actual 0)
        (data.actual_selfAdjoint 0) :=
  data.actualGap.trivialization.transportedReducedOperator_zero

/-- Uniform Green estimate after the genuine complement family has been
trivialized. -/
theorem actualGreen_opNorm_le
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (data : SelfAdjointKernelComplementBismutFreedFamilyData actual reference)
    (parameter : Real) :
    ‖data.actualDifferentiable.analytic.green parameter‖ ≤
      data.actualDifferentiable.analytic.gap⁻¹ :=
  data.actualDifferentiable.analytic.green_opNorm_le parameter

/-- The intrinsic relative logarithmic trace is the derivative of the
finite-part logarithmic determinant. -/
theorem finitePart_logDerivative_eq_relativeTrace
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (data : SelfAdjointKernelComplementBismutFreedFamilyData actual reference)
    (parameter : Real) :
    data.zetaFamily.finitePartFamily.logDerivative parameter =
      data.relativeTrace.trace parameter :=
  data.toBismutFreed.finitePart_logDerivative_eq_trace parameter

/-- The zeta determinant is parallel for the intrinsic trace connection. -/
theorem determinant_parallel
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (data : SelfAdjointKernelComplementBismutFreedFamilyData actual reference)
    (parameter : Real) :
    data.toBismutFreed.connectionAt parameter
        (relativeHeatMellinZetaFamilyDeterminant data.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          data.zetaFamily.toZetaFamily parameter) = 0 :=
  data.toBismutFreed.determinant_parallel parameter

/-- Public varying-complement family-index checkpoint. -/
theorem self_adjoint_kernel_complement_bismut_freed_family_gate
    (actual : Real → E →L[Real] E)
    (reference : Real → BaseReduced actual →L[Real] BaseReduced actual)
    (data : SelfAdjointKernelComplementBismutFreedFamilyData actual reference) :
    data.actualGap.fixedOperator 0 =
        selfAdjointKernelComplementOperator (actual 0)
          (data.actual_selfAdjoint 0) ∧
      (∀ parameter,
        ‖data.actualDifferentiable.analytic.green parameter‖ ≤
          data.actualDifferentiable.analytic.gap⁻¹) ∧
      (∀ parameter,
        data.zetaFamily.finitePartFamily.logDerivative parameter =
          data.relativeTrace.trace parameter) ∧
      (∀ parameter,
        data.toBismutFreed.connectionAt parameter
            (relativeHeatMellinZetaFamilyDeterminant data.zetaFamily parameter)
            (relativeZetaDeterminantCoordinateDerivative
              data.zetaFamily.toZetaFamily parameter) = 0) :=
  ⟨data.fixedOperator_zero,
    data.actualGreen_opNorm_le,
    data.finitePart_logDerivative_eq_relativeTrace,
    data.determinant_parallel⟩

end SelfAdjointKernelComplementBismutFreedFamilyData

end
end P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D
end JanusFormal
