import Mathlib.Analysis.Calculus.SmoothSeries
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Nuclear rank-one variation of a reference counterterm

The strongest Duhamel endpoint packet still accepted

```text
countertermDerivative(a) = Tr(C_a)
```

as a scalar comparison.  This file derives the equality from a differentiable
rank-one series.

The counterterm contribution has the spectral form

```text
c(a) = sum_i coefficient(i,a) inner(left_i,right_i).
```

The coefficient derivatives admit one summable uniform majorant.  Mathlib's
termwise derivative theorem therefore gives

```text
c'(a)
  = sum_i coefficient'(i,a) inner(left_i,right_i).
```

The series on the right is simultaneously an intrinsic nuclear expansion of
the counterterm variation operator.  Presentation independence identifies the
scalar derivative with its intrinsic nuclear trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearCountertermRankOneVariation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

universe u v

variable {E : Type v}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]

/-- A differentiable scalar counterterm series whose derivative is represented
by an intrinsic nuclear operator. -/
structure ReferenceNuclearCountertermRankOneVariationData
    (countertermContribution : Real → Real) where
  Index : Type u
  coefficient : Index → Real → Real
  derivativeCoefficient : Index → Real → Real
  leftVector : Index → E
  rightVector : Index → E
  coefficient_hasDerivAt : ∀ index parameter,
    HasDerivAt (coefficient index)
      (derivativeCoefficient index parameter) parameter
  derivativeMajorant : Index → Real
  derivativeMajorant_summable : Summable derivativeMajorant
  derivative_bound : ∀ index parameter,
    ‖derivativeCoefficient index parameter *
        inner Real (leftVector index) (rightVector index)‖ ≤
      derivativeMajorant index
  baseParameter : Real
  baseSeries_summable : Summable (fun index =>
    coefficient index baseParameter *
      inner Real (leftVector index) (rightVector index))
  countertermContribution_eq_tsum : ∀ parameter,
    countertermContribution parameter = ∑' index,
      coefficient index parameter *
        inner Real (leftVector index) (rightVector index)
  derivativeOperator : Real → E →L[Real] E
  derivative_nuclearNorm_summable : ∀ parameter,
    Summable (fun index =>
      |derivativeCoefficient index parameter| * ‖leftVector index‖ *
        ‖rightVector index‖)
  derivative_trace_summable : ∀ parameter,
    Summable (fun index =>
      derivativeCoefficient index parameter *
        inner Real (leftVector index) (rightVector index))
  derivative_operator_eq_tsum : ∀ parameter,
    derivativeOperator parameter = ∑' index,
      derivativeCoefficient index parameter •
        InnerProductSpace.rankOne Real
          (leftVector index) (rightVector index)
  derivativeTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{v, u} (derivativeOperator parameter)

namespace ReferenceNuclearCountertermRankOneVariationData

/-- Rank-one expansion of the counterterm variation operator. -/
def derivativeExpansion
    {countertermContribution : Real → Real}
    (data : ReferenceNuclearCountertermRankOneVariationData.{u, v}
      (E := E) countertermContribution)
    (parameter : Real) :
    SummableRankOneOperatorExpansion.{u, v}
      (data.derivativeOperator parameter) where
  Index := data.Index
  coefficient := fun index => data.derivativeCoefficient index parameter
  leftVector := data.leftVector
  rightVector := data.rightVector
  summable_nuclearNorm := data.derivative_nuclearNorm_summable parameter
  trace_summable := data.derivative_trace_summable parameter
  operator_eq_tsum := data.derivative_operator_eq_tsum parameter

/-- Intrinsic scalar derivative supplied by the nuclear variation operator. -/
def derivative
    {countertermContribution : Real → Real}
    (data : ReferenceNuclearCountertermRankOneVariationData.{u, v}
      (E := E) countertermContribution)
    (parameter : Real) : Real :=
  intrinsicNuclearTrace (data.derivativeTraceClass parameter)

/-- The scalar counterterm contribution differentiates to the intrinsic trace
of its nuclear variation operator. -/
theorem hasDerivAt_countertermContribution
    {countertermContribution : Real → Real}
    (data : ReferenceNuclearCountertermRankOneVariationData.{u, v}
      (E := E) countertermContribution)
    (parameter : Real) :
    HasDerivAt countertermContribution (data.derivative parameter) parameter := by
  have hSeries :
      HasDerivAt
        (fun current => ∑' index,
          data.coefficient index current *
            inner Real (data.leftVector index) (data.rightVector index))
        (∑' index,
          data.derivativeCoefficient index parameter *
            inner Real (data.leftVector index) (data.rightVector index))
        parameter :=
    hasDerivAt_tsum data.derivativeMajorant_summable
      (fun index current =>
        (data.coefficient_hasDerivAt index current).mul_const
          (inner Real (data.leftVector index) (data.rightVector index)))
      data.derivative_bound data.baseSeries_summable parameter
  have hContribution :
      HasDerivAt countertermContribution
        (∑' index,
          data.derivativeCoefficient index parameter *
            inner Real (data.leftVector index) (data.rightVector index))
        parameter := by
    convert hSeries using 1
    funext current
    exact data.countertermContribution_eq_tsum current
  have hTrace :
      (∑' index,
        data.derivativeCoefficient index parameter *
          inner Real (data.leftVector index) (data.rightVector index)) =
        data.derivative parameter := by
    change (data.derivativeExpansion parameter).expansionTrace =
      intrinsicNuclearTrace (data.derivativeTraceClass parameter)
    exact (data.derivativeTraceClass parameter).expansionTrace_eq
      (data.derivativeExpansion parameter)
  rw [hTrace] at hContribution
  exact hContribution

/-- The derivative is definitionally the intrinsic operator trace. -/
@[simp]
theorem derivative_eq_intrinsicTrace
    {countertermContribution : Real → Real}
    (data : ReferenceNuclearCountertermRankOneVariationData.{u, v}
      (E := E) countertermContribution)
    (parameter : Real) :
    data.derivative parameter =
      intrinsicNuclearTrace (data.derivativeTraceClass parameter) :=
  rfl

/-- Public nuclear counterterm-variation checkpoint. -/
theorem reference_nuclear_counterterm_rank_one_variation_gate
    (countertermContribution : Real → Real)
    (data : ReferenceNuclearCountertermRankOneVariationData.{u, v}
      (E := E) countertermContribution) :
    (∀ parameter,
      HasDerivAt countertermContribution (data.derivative parameter) parameter) ∧
    (∀ parameter,
      data.derivative parameter =
        intrinsicNuclearTrace (data.derivativeTraceClass parameter)) :=
  ⟨data.hasDerivAt_countertermContribution,
    data.derivative_eq_intrinsicTrace⟩

end ReferenceNuclearCountertermRankOneVariationData

end
end P0EFTJanusProgramPReferenceNuclearCountertermRankOneVariation4D
end JanusFormal
