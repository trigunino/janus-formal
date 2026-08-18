import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelDominatedTerminalTailPrimitive4D

/-!
# Terminal Duhamel tails from continuity only on the terminal half-line

Retracting time by `t ↦ max cutoff t` extends an integrand continuously from
`Ici cutoff` without inspecting it below the cutoff.  The extension agrees with
the original integrand on every relevant tail, so the existing genuine
tail-integral primitive supplies the terminal boundary packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelDominatedContinuousOnTerminalTailPrimitive4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Topology
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedTerminalTailPrimitive4D
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelTerminalTailPrimitive4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Extend a terminal integrand by freezing it at the cutoff. -/
def terminalClampExtension (cutoff : Real) (integrand : Real → Real)
    (time : Real) : Real :=
  integrand (max cutoff time)

theorem terminalClampExtension_continuous
    {cutoff : Real} {integrand : Real → Real}
    (hContinuous : ContinuousOn integrand (Ici cutoff)) :
    Continuous (terminalClampExtension cutoff integrand) := by
  have hClamp : Continuous (fun time : Real => max cutoff time) :=
    continuous_const.max continuous_id
  have hMaps : ∀ time : Real, max cutoff time ∈ Ici cutoff := fun time =>
    le_max_left cutoff time
  change Continuous (fun time : Real => integrand (max cutoff time))
  exact hContinuous.comp_continuous hClamp hMaps

theorem terminalClampExtension_eq
    {cutoff time : Real} {integrand : Real → Real}
    (hTime : cutoff ≤ time) :
    terminalClampExtension cutoff integrand time = integrand time := by
  simp [terminalClampExtension, max_eq_right hTime]

/-- Clamping preserves integrability on the open terminal half-line. -/
theorem terminalClampExtension_integrableOn
    {cutoff : Real} {integrand : Real → Real}
    (hIntegrable : IntegrableOn integrand (Ioi cutoff)) :
    IntegrableOn (terminalClampExtension cutoff integrand) (Ioi cutoff) := by
  refine hIntegrable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact (terminalClampExtension_eq (le_of_lt hTime)).symm

/-- Tail data obtained from continuity only on the terminal closed half-line. -/
def continuousOnTerminalTailPrimitive
    (cutoff : Real) (integrand : Real → Real)
    (hContinuous : ContinuousOn integrand (Ici cutoff))
    (hIntegrable : IntegrableOn integrand (Ioi cutoff)) :
    ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff where
  integrand := terminalClampExtension cutoff integrand
  integrand_continuous := terminalClampExtension_continuous hContinuous
  integrableOn_tail := terminalClampExtension_integrableOn hIntegrable

namespace ContinuousOnTerminalTailPrimitive

/-- The clamped construction has the original complete tail integral. -/
theorem matchingIntegral_eq
    {cutoff : Real} {integrand : Real → Real}
    (hContinuous : ContinuousOn integrand (Ici cutoff))
    (hIntegrable : IntegrableOn integrand (Ioi cutoff)) :
    (continuousOnTerminalTailPrimitive cutoff integrand hContinuous hIntegrable).matchingIntegral =
      ∫ time in Ioi cutoff, integrand time := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact terminalClampExtension_eq (le_of_lt hTime)

/-- At every later lower endpoint, the constructed primitive is the genuine
tail integral of the original integrand. -/
theorem terminalPrimitive_eq
    {cutoff : Real} {integrand : Real → Real}
    (hContinuous : ContinuousOn integrand (Ici cutoff))
    (hIntegrable : IntegrableOn integrand (Ioi cutoff))
    {upper : Real} (hUpper : cutoff ≤ upper) :
    (continuousOnTerminalTailPrimitive cutoff integrand hContinuous hIntegrable).terminalPrimitive upper =
      ∫ time in Ioi upper, integrand time := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact terminalClampExtension_eq (hUpper.trans (le_of_lt hTime))

end ContinuousOnTerminalTailPrimitive

end
end P0EFTJanusProgramPNuclearHeatDuhamelDominatedContinuousOnTerminalTailPrimitive4D

namespace P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Topology
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedTerminalTailPrimitive4D.NuclearHeatDuhamelDominatedWeightedIntegralData
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelTerminalTailPrimitive4D
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedContinuousOnTerminalTailPrimitive4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace NuclearHeatDuhamelDominatedWeightedIntegralData

/-- Dominated Duhamel data and terminal continuity produce a genuine tail
primitive without requiring continuity below the cutoff. -/
def toContinuousOnTerminalTailPrimitive
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear
      (Ioi cutoff))
    (parameter : Real)
    (hContinuous : ContinuousOn
      (extendedDuhamelTrace nuclear parameter) (Ici cutoff)) :
    ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff :=
  continuousOnTerminalTailPrimitive cutoff
    (extendedDuhamelTrace nuclear parameter) hContinuous
    (extendedDuhamelTrace_integrable data parameter)

/-- The complete integral of the constructed tail is the original Duhamel
integral on `Ioi cutoff`. -/
theorem continuousOnTail_matchingIntegral_eq
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear
      (Ioi cutoff))
    (parameter : Real)
    (hContinuous : ContinuousOn
      (extendedDuhamelTrace nuclear parameter) (Ici cutoff)) :
    (data.toContinuousOnTerminalTailPrimitive parameter hContinuous).matchingIntegral =
      ∫ time in Ioi cutoff, extendedDuhamelTrace nuclear parameter time :=
  ContinuousOnTerminalTailPrimitive.matchingIntegral_eq hContinuous
    (extendedDuhamelTrace_integrable data parameter)

/-- Direct adapter to the established long-time boundary-limit interface. -/
def toContinuousOnLongTimeBoundaryLimit
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear
      (Ioi cutoff))
    (parameter : Real)
    (hContinuous : ContinuousOn
      (extendedDuhamelTrace nuclear parameter) (Ici cutoff)) :
    ReferenceNuclearDuhamelLongTimeBoundaryLimitData (atTop : Filter Real)
      (∫ time in Ioi cutoff, extendedDuhamelTrace nuclear parameter time)
      (∫ time in Ioi cutoff, extendedDuhamelTrace nuclear parameter time) := by
  let tail := data.toContinuousOnTerminalTailPrimitive parameter hContinuous
  have hMatching : tail.matchingIntegral =
      ∫ time in Ioi cutoff,
        extendedDuhamelTrace nuclear parameter time :=
    data.continuousOnTail_matchingIntegral_eq parameter hContinuous
  exact
    { partialIntegral := tail.partialIntegral
      terminalPrimitive := tail.terminalPrimitive
      partialIntegral_tendsto := by
        rw [← hMatching]
        exact tail.partialIntegral_tendsto
      terminalPrimitive_tendsto_zero := tail.terminalPrimitive_tendsto_zero
      finiteBoundaryIdentity := fun upper => by
        rw [← hMatching]
        exact tail.finiteBoundaryIdentity upper }

/-- Public continuity-on-tail terminal checkpoint. -/
theorem nuclear_heat_duhamel_dominated_continuousOn_terminal_tail_gate
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (cutoff : Real)
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear
      (Ioi cutoff))
    (duhamelTrace_continuousOn : ∀ parameter,
      ContinuousOn (extendedDuhamelTrace nuclear parameter) (Ici cutoff)) :
    ∀ parameter,
      let tail := data.toContinuousOnTerminalTailPrimitive parameter
        (duhamelTrace_continuousOn parameter)
      Tendsto tail.terminalPrimitive atTop (𝓝 0) ∧
      (∀ upper, cutoff ≤ upper →
        tail.terminalPrimitive upper =
          ∫ time in Ioi upper,
            extendedDuhamelTrace nuclear parameter time) ∧
      Tendsto tail.partialIntegral atTop
        (𝓝 (∫ time in Ioi cutoff,
          extendedDuhamelTrace nuclear parameter time)) := by
  intro parameter
  let tail := data.toContinuousOnTerminalTailPrimitive parameter
    (duhamelTrace_continuousOn parameter)
  have hMatching := data.continuousOnTail_matchingIntegral_eq parameter
    (duhamelTrace_continuousOn parameter)
  refine ⟨tail.terminalPrimitive_tendsto_zero, ?_, ?_⟩
  · intro upper hUpper
    exact ContinuousOnTerminalTailPrimitive.terminalPrimitive_eq
      (duhamelTrace_continuousOn parameter)
      (extendedDuhamelTrace_integrable data parameter) hUpper
  · rw [← hMatching]
    exact tail.partialIntegral_tendsto

end NuclearHeatDuhamelDominatedWeightedIntegralData

end
end P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
end JanusFormal
