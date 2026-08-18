import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D

/-!
# Operator-valued terminal Duhamel primitive

This file constructs the genuine Bochner tail primitive for a continuous
operator-valued integrand on a terminal half-line.  Clamping at the initial
cutoff gives a globally continuous extension without imposing any regularity
before the physical long-time region.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelOperatorTerminalTailPrimitive4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Topology
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- An operator-valued long-time integrand with a genuine Bochner tail. -/
structure ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData
    (E : Type u) [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E] (cutoff : Real) where
  integrand : Real → E →L[Real] E
  integrand_continuousOn : ContinuousOn integrand (Ici cutoff)
  integrableOn_tail : IntegrableOn integrand (Ioi cutoff)

namespace ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData

/-- Freeze the integrand at the cutoff before the physical terminal region. -/
def extendedIntegrand {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (time : Real) : E →L[Real] E :=
  data.integrand (max cutoff time)

theorem extendedIntegrand_continuous {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff) :
    Continuous data.extendedIntegrand := by
  have hClamp : Continuous (fun time : Real => max cutoff time) :=
    continuous_const.max continuous_id
  exact data.integrand_continuousOn.comp_continuous hClamp
    (fun time => le_max_left cutoff time)

theorem extendedIntegrand_eq {cutoff time : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (hTime : cutoff ≤ time) :
    data.extendedIntegrand time = data.integrand time := by
  simp [extendedIntegrand, max_eq_right hTime]

theorem extendedIntegrand_integrableOn_tail {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff) :
    IntegrableOn data.extendedIntegrand (Ioi cutoff) := by
  refine data.integrableOn_tail.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact (data.extendedIntegrand_eq (le_of_lt hTime)).symm

/-- Finite-cutoff Bochner integral from the fixed long-time cutoff. -/
def partialIntegral {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (upper : Real) : E →L[Real] E :=
  ∫ time in cutoff..upper, data.extendedIntegrand time

/-- The remaining operator-valued Bochner tail. -/
def terminalPrimitive {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (upper : Real) : E →L[Real] E :=
  ∫ time in Ioi upper, data.extendedIntegrand time

/-- The complete physical long-time Bochner integral. -/
def matchingOperator {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff) :
    E →L[Real] E :=
  ∫ time in Ioi cutoff, data.integrand time

theorem intervalIntegrable {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (lower upper : Real) :
    IntervalIntegrable data.extendedIntegrand volume lower upper :=
  data.extendedIntegrand_continuous.intervalIntegrable lower upper

theorem integrableOn_tail_at {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (upper : Real) :
    IntegrableOn data.extendedIntegrand (Ioi upper) := by
  by_cases h : cutoff ≤ upper
  · exact data.extendedIntegrand_integrableOn_tail.mono_set
      (Ioi_subset_Ioi h)
  · have hUpper : upper ≤ cutoff := le_of_not_ge h
    have hFinite : IntegrableOn data.extendedIntegrand (Ioc upper cutoff) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hUpper).1
        (data.intervalIntegrable upper cutoff)
    rw [← Ioc_union_Ioi_eq_Ioi hUpper]
    exact hFinite.union data.extendedIntegrand_integrableOn_tail

theorem integral_extended_eq_matchingOperator {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff) :
    (∫ time in Ioi cutoff, data.extendedIntegrand time) =
      data.matchingOperator := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact data.extendedIntegrand_eq (le_of_lt hTime)

/-- Exact Bochner decomposition at every finite upper boundary. -/
theorem finiteBoundaryIdentity {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (upper : Real) :
    data.partialIntegral upper + data.terminalPrimitive upper =
      data.matchingOperator := by
  rw [← data.integral_extended_eq_matchingOperator]
  exact intervalIntegral.integral_interval_add_Ioi
    data.extendedIntegrand_integrableOn_tail
    (data.integrableOn_tail_at upper)

/-- Finite partial Bochner integrals converge to the full operator integral. -/
theorem partialIntegral_tendsto {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff) :
    Tendsto data.partialIntegral atTop (nhds data.matchingOperator) := by
  rw [← data.integral_extended_eq_matchingOperator]
  exact intervalIntegral_tendsto_integral_Ioi cutoff
    data.extendedIntegrand_integrableOn_tail tendsto_id

/-- The operator-norm Bochner tail vanishes at infinity. -/
theorem terminalPrimitive_tendsto_zero {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff) :
    Tendsto data.terminalPrimitive atTop (nhds 0) := by
  exact tendsto_integral_Ioi_zero
    (f := data.extendedIntegrand) tendsto_id

/-- The terminal primitive differentiates in operator norm to minus the
clamped operator integrand. -/
theorem terminalPrimitive_hasDerivAt {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (upper : Real) :
    HasDerivAt data.terminalPrimitive (-data.extendedIntegrand upper) upper := by
  have hPartial :
      HasDerivAt data.partialIntegral (data.extendedIntegrand upper) upper :=
    intervalIntegral.integral_hasDerivAt_right
      (data.intervalIntegrable cutoff upper)
      data.extendedIntegrand_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      data.extendedIntegrand_continuous.continuousAt
  have hDifference :
      HasDerivAt
        (fun bound => data.matchingOperator - data.partialIntegral bound)
        (-data.extendedIntegrand upper) upper :=
    hPartial.const_sub data.matchingOperator
  apply hDifference.congr_of_eventuallyEq
  filter_upwards [] with bound
  have hBoundary := data.finiteBoundaryIdentity bound
  rw [← hBoundary]
  abel

/-- On the physical terminal region, the derivative is minus the original
operator integrand. -/
theorem terminalPrimitive_hasDerivAt_of_le {cutoff upper : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (hUpper : cutoff ≤ upper) :
    HasDerivAt data.terminalPrimitive (-data.integrand upper) upper := by
  simpa [data.extendedIntegrand_eq hUpper] using
    data.terminalPrimitive_hasDerivAt upper

/-- On every physical later tail, the primitive is the original Bochner tail. -/
theorem terminalPrimitive_eq_integral {cutoff upper : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (hUpper : cutoff ≤ upper) :
    data.terminalPrimitive upper =
      ∫ time in Ioi upper, data.integrand time := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact data.extendedIntegrand_eq (hUpper.trans (le_of_lt hTime))

/-- Canonical boundary-limit packet: both named operators are the actual full
Bochner integral. -/
def toLongTimeBoundaryLimit {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff) :
    ReferenceNuclearDuhamelLongTimeBoundaryLimitData (atTop : Filter Real)
      data.matchingOperator data.matchingOperator where
  partialIntegral := data.partialIntegral
  terminalPrimitive := data.terminalPrimitive
  partialIntegral_tendsto := data.partialIntegral_tendsto
  terminalPrimitive_tendsto_zero := data.terminalPrimitive_tendsto_zero
  finiteBoundaryIdentity := data.finiteBoundaryIdentity

/-- Transport the canonical packet to separately named integrated and matching
operators once each has been identified with the actual Bochner integral. -/
def toLongTimeBoundaryLimitOfEq {cutoff : Real}
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff)
    (integratedOperator matchingOperator : E →L[Real] E)
    (hIntegrated : data.matchingOperator = integratedOperator)
    (hMatching : data.matchingOperator = matchingOperator) :
    ReferenceNuclearDuhamelLongTimeBoundaryLimitData (atTop : Filter Real)
      integratedOperator matchingOperator := by
  subst integratedOperator
  subst matchingOperator
  exact data.toLongTimeBoundaryLimit

/-- Public operator-valued terminal-tail checkpoint. -/
theorem reference_nuclear_duhamel_operator_terminal_tail_primitive_gate
    (cutoff : Real)
    (data : ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E cutoff) :
    (∀ upper, cutoff ≤ upper →
      HasDerivAt data.terminalPrimitive (-data.integrand upper) upper) ∧
    (∀ upper, data.partialIntegral upper + data.terminalPrimitive upper =
      data.matchingOperator) ∧
    Tendsto data.partialIntegral atTop (nhds data.matchingOperator) ∧
    Tendsto data.terminalPrimitive atTop (nhds 0) :=
  ⟨fun _ hUpper => data.terminalPrimitive_hasDerivAt_of_le hUpper,
    data.finiteBoundaryIdentity,
    data.partialIntegral_tendsto,
    data.terminalPrimitive_tendsto_zero⟩

end ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelOperatorTerminalTailPrimitive4D
end JanusFormal
