import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPZeroLogarithmicDerivativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D

/-!
# Bismut--Freed family with zero actual derivative in fixed coordinates

After unitary trivialization of the genuine kernel complements, the preferred
D11 actual reduced family is constant.  Its displayed derivative is therefore
zero, so its logarithmic derivative and intrinsic logarithmic trace vanish.

This file turns that fact into a constructor for the existing
`SelfAdjointKernelComplementBismutFreedFamilyData` interface.  Instead of a
parameterized family of nuclear certificates for the actual logarithmic
derivative, it consumes one intrinsic nuclear certificate for the zero
operator.  The coefficient agreement simplifies to

```text
zeta connection coefficient = reference logarithmic trace.
```

The reference family, its inverse derivative and its nuclear theorem are kept
unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPZeroActualBismutFreedFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPZeroLogarithmicDerivativeTrace4D

universe e i

variable {E : Type e}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

private abbrev BaseReduced
    (actual : Real → E →L[Real] E) :=
  SelfAdjointKernelComplement (actual 0)

/-- Actual logarithmic trace packet generated from one zero trace certificate. -/
def zeroActualTrace
    {actual : Real → E →L[Real] E}
    {actual_selfAdjoint : ∀ parameter, IsSelfAdjoint (actual parameter)}
    (actualGap : SelfAdjointKernelComplementUniformGapTrivializationData actual
      actual_selfAdjoint)
    (actualDifferentiable :
      DifferentiableSelfAdjointUniformGapFamilyData actualGap.fixedOperator)
    (actualInverse : actualDifferentiable.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, actualDifferentiable.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData.{e, i}
      (0 : BaseReduced actual →L[Real] BaseReduced actual)) :
    IntrinsicLogarithmicDerivativeTraceData.{e, i} actualGap.fixedOperator :=
  intrinsicLogarithmicDerivativeTraceOfZeroDerivative actualDifferentiable
    actualInverse hDerivative zeroTrace

/-- Construct the full existing Bismut--Freed family packet when the actual
fixed-coordinate derivative vanishes. -/
def selfAdjointKernelComplementBismutFreedFamilyOfZeroActualDerivative
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (actual_selfAdjoint : ∀ parameter, IsSelfAdjoint (actual parameter))
    (actualGap : SelfAdjointKernelComplementUniformGapTrivializationData actual
      actual_selfAdjoint)
    (actualDifferentiable :
      DifferentiableSelfAdjointUniformGapFamilyData actualGap.fixedOperator)
    (actualAnalytic_eq :
      actualDifferentiable.analytic = actualGap.toUniformGapFamily)
    (actualInverse : actualDifferentiable.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, actualDifferentiable.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData.{e, i}
      (0 : BaseReduced actual →L[Real] BaseReduced actual))
    (referenceTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} reference)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (coefficient_agreement : ∀ parameter,
      relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter =
        (referenceTrace.trace parameter : Real)) :
    SelfAdjointKernelComplementBismutFreedFamilyData actual reference where
  actual_selfAdjoint := actual_selfAdjoint
  actualGap := actualGap
  actualDifferentiable := actualDifferentiable
  actualAnalytic_eq := actualAnalytic_eq
  actualInverse := actualInverse
  actualTraceClass :=
    (zeroActualTrace actualGap actualDifferentiable actualInverse hDerivative
      zeroTrace).traceClass
  referenceTrace := referenceTrace
  zetaFamily := zetaFamily
  coefficient_agreement := by
    intro parameter
    have hZero :=
      intrinsicLogarithmicDerivativeTraceOfZeroDerivative_trace
        actualDifferentiable actualInverse hDerivative zeroTrace parameter
    have hZeroActual :
        intrinsicNuclearTrace
          ((zeroActualTrace actualGap actualDifferentiable actualInverse hDerivative
            zeroTrace).traceClass parameter) = 0 := by
      simpa [zeroActualTrace, IntrinsicLogarithmicDerivativeTraceData.trace]
        using hZero
    calc
      relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter =
          (referenceTrace.trace parameter : Complex) :=
        coefficient_agreement parameter
      _ = (-(intrinsicNuclearTrace
            ((zeroActualTrace actualGap actualDifferentiable actualInverse
              hDerivative zeroTrace).traceClass parameter) -
          referenceTrace.trace parameter) : Real) := by
        rw [hZeroActual]
        norm_num

namespace SelfAdjointKernelComplementBismutFreedFamilyData

/-- For the specialized constructor, the actual intrinsic trace is zero. -/
theorem zeroActualDerivative_actualTrace
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (actual_selfAdjoint : ∀ parameter, IsSelfAdjoint (actual parameter))
    (actualGap : SelfAdjointKernelComplementUniformGapTrivializationData actual
      actual_selfAdjoint)
    (actualDifferentiable :
      DifferentiableSelfAdjointUniformGapFamilyData actualGap.fixedOperator)
    (actualAnalytic_eq :
      actualDifferentiable.analytic = actualGap.toUniformGapFamily)
    (actualInverse : actualDifferentiable.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, actualDifferentiable.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData.{e, i}
      (0 : BaseReduced actual →L[Real] BaseReduced actual))
    (referenceTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} reference)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (coefficient_agreement : ∀ parameter,
      relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter =
        (referenceTrace.trace parameter : Real))
    (parameter : Real) :
    (selfAdjointKernelComplementBismutFreedFamilyOfZeroActualDerivative
      actual_selfAdjoint actualGap actualDifferentiable actualAnalytic_eq
      actualInverse hDerivative zeroTrace referenceTrace zetaFamily
      coefficient_agreement).actualTrace.trace parameter = 0 := by
  change (zeroActualTrace actualGap actualDifferentiable actualInverse hDerivative
    zeroTrace).trace parameter = 0
  exact intrinsicLogarithmicDerivativeTraceOfZeroDerivative_trace
    actualDifferentiable actualInverse hDerivative zeroTrace parameter

/-- The relative trace reduces to minus the reference trace. -/
theorem zeroActualDerivative_relativeTrace
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (actual_selfAdjoint : ∀ parameter, IsSelfAdjoint (actual parameter))
    (actualGap : SelfAdjointKernelComplementUniformGapTrivializationData actual
      actual_selfAdjoint)
    (actualDifferentiable :
      DifferentiableSelfAdjointUniformGapFamilyData actualGap.fixedOperator)
    (actualAnalytic_eq :
      actualDifferentiable.analytic = actualGap.toUniformGapFamily)
    (actualInverse : actualDifferentiable.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, actualDifferentiable.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData.{e, i}
      (0 : BaseReduced actual →L[Real] BaseReduced actual))
    (referenceTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} reference)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (coefficient_agreement : ∀ parameter,
      relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter =
        (referenceTrace.trace parameter : Real))
    (parameter : Real) :
    (selfAdjointKernelComplementBismutFreedFamilyOfZeroActualDerivative
      actual_selfAdjoint actualGap actualDifferentiable actualAnalytic_eq
      actualInverse hDerivative zeroTrace referenceTrace zetaFamily
      coefficient_agreement).relativeTrace.trace parameter =
        -referenceTrace.trace parameter := by
  rw [RelativeIntrinsicLogarithmicDerivativeTraceData.trace]
  change (zeroActualTrace actualGap actualDifferentiable actualInverse hDerivative
    zeroTrace).trace parameter - referenceTrace.trace parameter =
      -referenceTrace.trace parameter
  have hZero :
      (zeroActualTrace actualGap actualDifferentiable actualInverse hDerivative
        zeroTrace).trace parameter = 0 := by
    simpa [zeroActualTrace] using
      (intrinsicLogarithmicDerivativeTraceOfZeroDerivative_trace
        actualDifferentiable actualInverse hDerivative zeroTrace parameter)
  rw [hZero]
  ring

/-- The Bismut--Freed coefficient is exactly the reference trace in this fixed
D11 gauge. -/
theorem zeroActualDerivative_bismutFreedCoefficient
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (actual_selfAdjoint : ∀ parameter, IsSelfAdjoint (actual parameter))
    (actualGap : SelfAdjointKernelComplementUniformGapTrivializationData actual
      actual_selfAdjoint)
    (actualDifferentiable :
      DifferentiableSelfAdjointUniformGapFamilyData actualGap.fixedOperator)
    (actualAnalytic_eq :
      actualDifferentiable.analytic = actualGap.toUniformGapFamily)
    (actualInverse : actualDifferentiable.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, actualDifferentiable.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData.{e, i}
      (0 : BaseReduced actual →L[Real] BaseReduced actual))
    (referenceTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} reference)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (coefficient_agreement : ∀ parameter,
      relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter =
        (referenceTrace.trace parameter : Real))
    (parameter : Real) :
    (selfAdjointKernelComplementBismutFreedFamilyOfZeroActualDerivative
      actual_selfAdjoint actualGap actualDifferentiable actualAnalytic_eq
      actualInverse hDerivative zeroTrace referenceTrace zetaFamily
      coefficient_agreement).relativeTrace.bismutFreedCoefficient parameter =
        (referenceTrace.trace parameter : Real) := by
  unfold RelativeIntrinsicLogarithmicDerivativeTraceData.bismutFreedCoefficient
  rw [zeroActualDerivative_relativeTrace actual_selfAdjoint actualGap
    actualDifferentiable actualAnalytic_eq actualInverse hDerivative zeroTrace
    referenceTrace zetaFamily coefficient_agreement parameter]
  norm_num

end SelfAdjointKernelComplementBismutFreedFamilyData

/-- Public zero-actual Bismut--Freed checkpoint. -/
theorem zero_actual_bismut_freed_family_gate
    {actual : Real → E →L[Real] E}
    {reference : Real → BaseReduced actual →L[Real] BaseReduced actual}
    (actual_selfAdjoint : ∀ parameter, IsSelfAdjoint (actual parameter))
    (actualGap : SelfAdjointKernelComplementUniformGapTrivializationData actual
      actual_selfAdjoint)
    (actualDifferentiable :
      DifferentiableSelfAdjointUniformGapFamilyData actualGap.fixedOperator)
    (actualAnalytic_eq :
      actualDifferentiable.analytic = actualGap.toUniformGapFamily)
    (actualInverse : actualDifferentiable.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, actualDifferentiable.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData.{e, i}
      (0 : BaseReduced actual →L[Real] BaseReduced actual))
    (referenceTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} reference)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (coefficient_agreement : ∀ parameter,
      relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter =
        (referenceTrace.trace parameter : Real)) :
    let data :=
      selfAdjointKernelComplementBismutFreedFamilyOfZeroActualDerivative
        actual_selfAdjoint actualGap actualDifferentiable actualAnalytic_eq
        actualInverse hDerivative zeroTrace referenceTrace zetaFamily
        coefficient_agreement
    (∀ parameter, data.actualTrace.trace parameter = 0) ∧
    (∀ parameter,
      data.relativeTrace.trace parameter = -referenceTrace.trace parameter) ∧
    (∀ parameter,
      data.relativeTrace.bismutFreedCoefficient parameter =
        (referenceTrace.trace parameter : Real)) := by
  dsimp only
  exact
    ⟨SelfAdjointKernelComplementBismutFreedFamilyData.zeroActualDerivative_actualTrace
        actual_selfAdjoint actualGap
          actualDifferentiable actualAnalytic_eq actualInverse hDerivative
          zeroTrace referenceTrace zetaFamily coefficient_agreement,
      SelfAdjointKernelComplementBismutFreedFamilyData.zeroActualDerivative_relativeTrace
        actual_selfAdjoint actualGap
          actualDifferentiable actualAnalytic_eq actualInverse hDerivative
          zeroTrace referenceTrace zetaFamily coefficient_agreement,
      SelfAdjointKernelComplementBismutFreedFamilyData.zeroActualDerivative_bismutFreedCoefficient
        actual_selfAdjoint actualGap
          actualDifferentiable actualAnalytic_eq actualInverse hDerivative
          zeroTrace referenceTrace zetaFamily coefficient_agreement⟩

end
end P0EFTJanusProgramPZeroActualBismutFreedFamily4D
end JanusFormal
