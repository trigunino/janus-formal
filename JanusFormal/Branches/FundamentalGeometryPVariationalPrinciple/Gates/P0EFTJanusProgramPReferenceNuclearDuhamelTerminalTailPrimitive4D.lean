import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D

/-!
# Long-time Duhamel terminal primitive from a tail integral

For a continuous real integrand that is integrable on one terminal half-line,
this file constructs the finite-boundary identity, the derivative of the tail
primitive, and its limit at infinity.  Thus these properties need not be
separate hypotheses when the terminal primitive is the actual tail integral.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelTerminalTailPrimitive4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Topology
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D

/-- A continuous real integrand with an integrable long-time tail. -/
structure ReferenceNuclearDuhamelTerminalTailPrimitiveData
    (cutoff : Real) where
  integrand : Real → Real
  integrand_continuous : Continuous integrand
  integrableOn_tail : IntegrableOn integrand (Ioi cutoff)

namespace ReferenceNuclearDuhamelTerminalTailPrimitiveData

/-- The finite-cutoff integral from the fixed cutoff. -/
def partialIntegral {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff)
    (upper : Real) : Real :=
  ∫ time in cutoff..upper, data.integrand time

/-- The genuine terminal primitive: the integral over the remaining tail. -/
def terminalPrimitive {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff)
    (upper : Real) : Real :=
  ∫ time in Ioi upper, data.integrand time

/-- The complete long-time integral. -/
def matchingIntegral {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff) : Real :=
  ∫ time in Ioi cutoff, data.integrand time

/-- Continuity supplies interval integrability at every finite cutoff. -/
theorem intervalIntegrable
    {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff)
    (lower upper : Real) :
    IntervalIntegrable data.integrand volume lower upper :=
  data.integrand_continuous.intervalIntegrable lower upper

/-- Integrability propagates from the initial tail to every later or earlier
finite tail, using continuity on the bounded intervening interval. -/
theorem integrableOn_tail_at
    {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff)
    (upper : Real) :
    IntegrableOn data.integrand (Ioi upper) := by
  by_cases h : cutoff ≤ upper
  · exact data.integrableOn_tail.mono_set (Ioi_subset_Ioi h)
  · have hUpper : upper ≤ cutoff := le_of_not_ge h
    have hFinite : IntegrableOn data.integrand (Ioc upper cutoff) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hUpper).1
        (data.intervalIntegrable upper cutoff)
    rw [← Ioc_union_Ioi_eq_Ioi hUpper]
    exact hFinite.union data.integrableOn_tail

/-- Exact finite-boundary decomposition of the full long-time integral. -/
theorem finiteBoundaryIdentity
    {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff)
    (upper : Real) :
    data.partialIntegral upper + data.terminalPrimitive upper =
      data.matchingIntegral := by
  exact intervalIntegral.integral_interval_add_Ioi
    data.integrableOn_tail (data.integrableOn_tail_at upper)

/-- The finite-cutoff integral converges to the complete long-time integral. -/
theorem partialIntegral_tendsto
    {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff) :
    Tendsto data.partialIntegral atTop (𝓝 data.matchingIntegral) := by
  exact intervalIntegral_tendsto_integral_Ioi cutoff
    data.integrableOn_tail tendsto_id

/-- Every integrable tail vanishes when its lower endpoint tends to infinity. -/
theorem terminalPrimitive_tendsto_zero
    {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff) :
    Tendsto data.terminalPrimitive atTop (𝓝 0) := by
  exact tendsto_integral_Ioi_zero (f := data.integrand) tendsto_id

/-- At a continuity point, the terminal tail has derivative `-integrand`. -/
theorem terminalPrimitive_hasDerivAt
    {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff)
    (upper : Real) :
    HasDerivAt data.terminalPrimitive (-data.integrand upper) upper := by
  have hPartial :
      HasDerivAt data.partialIntegral (data.integrand upper) upper := by
    exact intervalIntegral.integral_hasDerivAt_right
      (data.intervalIntegrable cutoff upper)
      data.integrand_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      data.integrand_continuous.continuousAt
  have hDifference :
      HasDerivAt
        (fun bound => data.matchingIntegral - data.partialIntegral bound)
        (-data.integrand upper) upper := by
    exact hPartial.const_sub data.matchingIntegral
  apply hDifference.congr_of_eventuallyEq
  filter_upwards [] with bound
  have hBoundary := data.finiteBoundaryIdentity bound
  dsimp [terminalPrimitive, partialIntegral, matchingIntegral] at hBoundary ⊢
  linarith

/-- Package the actual partial and tail integrals into the existing abstract
long-time boundary-limit interface. -/
def toLongTimeBoundaryLimit
    {cutoff : Real}
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff) :
    ReferenceNuclearDuhamelLongTimeBoundaryLimitData (atTop : Filter Real)
      data.matchingIntegral data.matchingIntegral where
  partialIntegral := data.partialIntegral
  terminalPrimitive := data.terminalPrimitive
  partialIntegral_tendsto := data.partialIntegral_tendsto
  terminalPrimitive_tendsto_zero := data.terminalPrimitive_tendsto_zero
  finiteBoundaryIdentity := data.finiteBoundaryIdentity

/-- Public checkpoint for the tail-integral construction. -/
theorem reference_nuclear_duhamel_terminal_tail_primitive_gate
    (cutoff : Real)
    (data : ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff) :
    (∀ upper, HasDerivAt data.terminalPrimitive (-data.integrand upper) upper) ∧
    (∀ upper, data.partialIntegral upper + data.terminalPrimitive upper =
      data.matchingIntegral) ∧
    Tendsto data.partialIntegral atTop (𝓝 data.matchingIntegral) ∧
    Tendsto data.terminalPrimitive atTop (𝓝 0) :=
  ⟨data.terminalPrimitive_hasDerivAt,
    data.finiteBoundaryIdentity,
    data.partialIntegral_tendsto,
    data.terminalPrimitive_tendsto_zero⟩

end ReferenceNuclearDuhamelTerminalTailPrimitiveData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelTerminalTailPrimitive4D
end JanusFormal
