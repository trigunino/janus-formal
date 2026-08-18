import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelTerminalTailPrimitive4D

/-!
# Terminal tail primitive from dominated nuclear Duhamel data

The logarithmic identity `w(t) t = 1` identifies the integrable weighted heat
derivative with the negative extended Duhamel trace.  Hence dominated
differentiation already supplies the integrability needed to construct the
actual long-time tail primitive; only continuity in heat time remains.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelDominatedTerminalTailPrimitive4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Topology
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelTerminalTailPrimitive4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace NuclearHeatDuhamelDominatedWeightedIntegralData

/-- Dominated integrability of the weighted heat derivative is exactly
integrability of the Duhamel trace when `w(t)t=1`. -/
theorem extendedDuhamelTrace_integrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear timeRegion)
    (parameter : Real) :
    Integrable (extendedDuhamelTrace nuclear parameter)
      (volume.restrict timeRegion) := by
  have hDerivative :
      Integrable
        (fun time =>
          data.weight time *
            extendedHeatTraceDerivative nuclear parameter time)
        (volume.restrict timeRegion) :=
    data.toDominatedParametricIntegral.derivative_integrable parameter
  refine hDerivative.neg.congr ?_
  filter_upwards [data.weight_mul_time_eq_one] with time hWeight
  change
    -(data.weight time *
        extendedHeatTraceDerivative nuclear parameter time) =
      extendedDuhamelTrace nuclear parameter time
  rw [extendedHeatTraceDerivative_eq]
  calc
    -(data.weight time *
        (-time * extendedDuhamelTrace nuclear parameter time)) =
        (data.weight time * time) *
          extendedDuhamelTrace nuclear parameter time := by ring
    _ = extendedDuhamelTrace nuclear parameter time := by rw [hWeight, one_mul]

/-- A dominated long-time packet with continuous Duhamel trace produces the
genuine tail-integral primitive at every parameter. -/
def toTerminalTailPrimitive
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear
      (Set.Ioi cutoff))
    (parameter : Real)
    (hContinuous : Continuous (extendedDuhamelTrace nuclear parameter)) :
    ReferenceNuclearDuhamelTerminalTailPrimitiveData cutoff where
  integrand := extendedDuhamelTrace nuclear parameter
  integrand_continuous := hContinuous
  integrableOn_tail := extendedDuhamelTrace_integrable data parameter

/-- The constructed tail gives the existing long-time boundary packet with
matching operator equal to the full Duhamel integral. -/
def toLongTimeBoundaryLimit
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear
      (Set.Ioi cutoff))
    (parameter : Real)
    (hContinuous : Continuous (extendedDuhamelTrace nuclear parameter)) :
    ReferenceNuclearDuhamelLongTimeBoundaryLimitData (atTop : Filter Real)
      (∫ time in Set.Ioi cutoff, extendedDuhamelTrace nuclear parameter time)
      (∫ time in Set.Ioi cutoff, extendedDuhamelTrace nuclear parameter time) :=
  (toTerminalTailPrimitive data parameter hContinuous).toLongTimeBoundaryLimit

/-- Public dominated-to-terminal-tail checkpoint. -/
theorem nuclear_heat_duhamel_dominated_terminal_tail_primitive_gate
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (cutoff : Real)
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear
      (Set.Ioi cutoff))
    (duhamelTrace_continuous : ∀ parameter,
      Continuous (extendedDuhamelTrace nuclear parameter)) :
    (∀ parameter,
      Integrable (extendedDuhamelTrace nuclear parameter)
        (volume.restrict (Set.Ioi cutoff))) ∧
    (∀ parameter,
      let tail := toTerminalTailPrimitive data parameter
        (duhamelTrace_continuous parameter)
      Tendsto tail.terminalPrimitive atTop (𝓝 0) ∧
      (∀ upper,
        tail.partialIntegral upper + tail.terminalPrimitive upper =
          tail.matchingIntegral) ∧
      Tendsto tail.partialIntegral atTop (𝓝 tail.matchingIntegral)) := by
  constructor
  · exact extendedDuhamelTrace_integrable data
  · intro parameter
    let tail := toTerminalTailPrimitive data parameter
      (duhamelTrace_continuous parameter)
    exact ⟨tail.terminalPrimitive_tendsto_zero,
      tail.finiteBoundaryIdentity,
      tail.partialIntegral_tendsto⟩

end NuclearHeatDuhamelDominatedWeightedIntegralData

end
end P0EFTJanusProgramPNuclearHeatDuhamelDominatedTerminalTailPrimitive4D
end JanusFormal
