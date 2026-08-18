import Mathlib.Analysis.Calculus.MeanValue
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D

/-!
# Basepoint propagation of a counterterm-subtracted short-time remainder

An integrable remainder at one basepoint and a uniform quadratic bound on its
parameter derivative propagate short-time integrability to the whole real
parameter family.  The proof is the mean value theorem on the segment joining
the basepoint to the current parameter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D.NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
open P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Minimal input for propagating an integrable weighted remainder from one
basepoint using a uniform quadratic derivative estimate. -/
structure NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), weight time * time = 1
  counterterm : Real → Real → Real
  countertermDerivative : Real → Real → Real
  counterterm_hasDerivAt : ∀ parameter time,
    HasDerivAt (fun current => counterterm current time)
      (countertermDerivative parameter time) parameter
  integrand_aeStronglyMeasurable : ∀ parameter,
    AEStronglyMeasurable
      (fun time => weight time *
        (extendedHeatTrace nuclear parameter time - counterterm parameter time))
      (volume.restrict (Set.Ioo 0 cutoff))
  basepoint : Real
  basepoint_integrable :
    Integrable
      (fun time => weight time *
        (extendedHeatTrace nuclear basepoint time - counterterm basepoint time))
      (volume.restrict (Set.Ioo 0 cutoff))
  scale : Real
  derivative_norm_le :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), ∀ parameter,
      ‖weight time *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative parameter time)‖ ≤
        shortTimeQuadraticBound scale time

namespace NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData

/-- Weighted counterterm-subtracted heat remainder. -/
def weightedRemainder
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff)
    (parameter time : Real) : Real :=
  data.weight time *
    (extendedHeatTrace nuclear parameter time - data.counterterm parameter time)

/-- Parameter derivative of the weighted remainder. -/
def weightedRemainderDerivative
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff)
    (parameter time : Real) : Real :=
  data.weight time *
    (extendedHeatTraceDerivative nuclear parameter time -
      data.countertermDerivative parameter time)

theorem weightedRemainder_hasDerivAt
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff)
    (parameter time : Real) :
    HasDerivAt (fun current => data.weightedRemainder current time)
      (data.weightedRemainderDerivative parameter time) parameter := by
  simpa [weightedRemainder, weightedRemainderDerivative] using!
    (hasDerivAt_const parameter (data.weight time)).mul
      ((extendedHeatTrace_hasDerivAt nuclear parameter time).sub
        (data.counterterm_hasDerivAt parameter time))

/-- Mean-value propagation of the quadratic derivative estimate from the
basepoint to an arbitrary parameter. -/
theorem weightedRemainder_sub_basepoint_norm_le
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff)
    (parameter : Real) :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
      ‖data.weightedRemainder parameter time -
        data.weightedRemainder data.basepoint time‖ ≤
      shortTimeQuadraticBound data.scale time *
        ‖parameter - data.basepoint‖ := by
  filter_upwards [data.derivative_norm_le] with time hTime
  exact
    (convex_segment data.basepoint parameter).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun current => data.weightedRemainder current time)
      (f' := fun current => data.weightedRemainderDerivative current time)
      (fun current _ =>
        (data.weightedRemainder_hasDerivAt current time).hasDerivWithinAt)
      (fun current _ => by
        simpa [weightedRemainderDerivative] using hTime current)
      (left_mem_segment Real data.basepoint parameter)
      (right_mem_segment Real data.basepoint parameter)

/-- Integrable majorant transported from the basepoint. -/
def integrandMajorant
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff)
    (parameter : Real) : Real → Real :=
  (fun time => ‖data.weightedRemainder data.basepoint time‖) +
    fun time => shortTimeQuadraticBound data.scale time *
      ‖parameter - data.basepoint‖

theorem integrandMajorant_integrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff)
    (parameter : Real) :
    Integrable (data.integrandMajorant parameter)
      (volume.restrict (Set.Ioo 0 cutoff)) := by
  exact data.basepoint_integrable.norm.add
    ((integrableOn_shortTimeQuadraticBound data.scale cutoff).mul_const
      ‖parameter - data.basepoint‖)

theorem integrand_norm_le
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff)
    (parameter : Real) :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
      ‖data.weightedRemainder parameter time‖ ≤
        data.integrandMajorant parameter time := by
  filter_upwards [data.weightedRemainder_sub_basepoint_norm_le parameter]
      with time hDifference
  change ‖data.weightedRemainder parameter time‖ ≤
    ‖data.weightedRemainder data.basepoint time‖ +
      shortTimeQuadraticBound data.scale time *
        ‖parameter - data.basepoint‖
  calc
    ‖data.weightedRemainder parameter time‖ =
        ‖(data.weightedRemainder parameter time -
          data.weightedRemainder data.basepoint time) +
          data.weightedRemainder data.basepoint time‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖data.weightedRemainder parameter time -
          data.weightedRemainder data.basepoint time‖ +
        ‖data.weightedRemainder data.basepoint time‖ := norm_add_le _ _
    _ ≤ shortTimeQuadraticBound data.scale time *
          ‖parameter - data.basepoint‖ +
        ‖data.weightedRemainder data.basepoint time‖ :=
      add_le_add_left hDifference _
    _ = ‖data.weightedRemainder data.basepoint time‖ +
        shortTimeQuadraticBound data.scale time *
          ‖parameter - data.basepoint‖ := add_comm _ _

/-- Convert basepoint propagation data into the complete dominated
counterterm-subtracted short-time packet. -/
def toCountertermSubtractedShortTimeQuadratic
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff) :
    NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff where
  weight := data.weight
  weight_mul_time_eq_one := data.weight_mul_time_eq_one
  counterterm := data.counterterm
  countertermDerivative := data.countertermDerivative
  counterterm_hasDerivAt := data.counterterm_hasDerivAt
  parameterDomain := fun _ => Set.univ
  parameterDomain_mem_nhds := fun _ => Filter.univ_mem
  integrand_aeStronglyMeasurable := fun _ =>
    Filter.Eventually.of_forall data.integrand_aeStronglyMeasurable
  integrandMajorant := data.integrandMajorant
  integrandMajorant_integrable := data.integrandMajorant_integrable
  integrand_norm_le := by
    intro parameter
    simpa [weightedRemainder] using data.integrand_norm_le parameter
  scale := fun _ => data.scale
  derivative_norm_le := by
    intro parameter
    filter_upwards [data.derivative_norm_le] with time hTime
    intro current hCurrent
    exact hTime current

/-- Public basepoint-propagation checkpoint. -/
theorem nuclear_heat_duhamel_counterterm_subtracted_short_time_basepoint_quadratic_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real)
    (data :
      NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
        nuclear cutoff) :
    let shortTime := data.toCountertermSubtractedShortTimeQuadratic
    (∀ parameter,
      ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
        ‖data.weightedRemainder parameter time -
          data.weightedRemainder data.basepoint time‖ ≤
        shortTimeQuadraticBound data.scale time *
          ‖parameter - data.basepoint‖) ∧
    (∀ parameter, Integrable
      (fun time => shortTime.weight time *
        shortTime.subtractedHeatTrace parameter time)
      (volume.restrict (Set.Ioo 0 cutoff))) ∧
    (∀ parameter, Integrable
      (fun time => shortTime.weight time *
        shortTime.subtractedHeatTraceDerivative parameter time)
      (volume.restrict (Set.Ioo 0 cutoff))) ∧
    (∀ parameter, Integrable
      (shortTime.renormalizedDuhamelTrace parameter)
      (volume.restrict (Set.Ioo 0 cutoff))) ∧
    (∀ parameter, HasDerivAt
      (fun current =>
        ∫ time in Set.Ioo 0 cutoff,
          shortTime.weight time *
            shortTime.subtractedHeatTrace current time)
      (-∫ time in Set.Ioo 0 cutoff,
        shortTime.renormalizedDuhamelTrace parameter time) parameter) := by
  dsimp only
  rcases
      nuclear_heat_duhamel_counterterm_subtracted_short_time_quadratic_gate
        nuclear cutoff data.toCountertermSubtractedShortTimeQuadratic with
    ⟨hValue, hDerivative, hRenormalized, hVariation⟩
  exact
    ⟨data.weightedRemainder_sub_basepoint_norm_le,
      hValue, hDerivative, hRenormalized, hVariation⟩

end NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData

end
end P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
end JanusFormal
