import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartFamily4D

/-!
# Finite-part family from nuclear short- and long-time packets

At the canonical cutoff `1`, the counterterm-subtracted short-time packet and
an integrable dominated long-time packet already contain both finite-part
integrability obligations and their parameter variations.  The only extra
analytic datum is the finite part assigned to the short-time counterterm.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelFinitePartFamilyFrontend4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {Index : Type*}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Minimal data constructing the real finite-part family directly from the
nuclear heat packets. -/
structure NuclearHeatDuhamelFinitePartFamilyFrontendData
    (Index : Type*)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
    nuclear 1
  shortTime_counterterm_eq : ∀ parameter time,
    shortTime.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time
  longTime : NuclearHeatDuhamelWeightedIntegralData nuclear
    (Set.Ioi (1 : Real))
  longTime_integrable : ∀ parameter,
    Integrable
      (fun time ↦ longTime.weight time *
        extendedHeatTrace nuclear parameter time)
      (volume.restrict (Set.Ioi (1 : Real)))

namespace NuclearHeatDuhamelFinitePartFamilyFrontendData

theorem positiveTimeTraceExtension_eq_extendedHeatTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (parameter time : Real) :
    positiveTimeTraceExtension (nuclear.heatTrace parameter) time =
      extendedHeatTrace nuclear parameter time := by
  unfold positiveTimeTraceExtension extendedHeatTrace
  rfl

theorem shortTimeIntegrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear)
    (parameter : Real) :
    IntegrableOn
      (fun time =>
        (positiveTimeTraceExtension (nuclear.heatTrace parameter) time -
          counterterm data.finiteCounterterm.variation parameter time) / time)
      (Set.Ioc (0 : Real) 1) volume := by
  change Integrable _ (volume.restrict (Set.Ioc (0 : Real) 1))
  rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  apply (data.shortTime.integrand_integrable parameter).congr
  filter_upwards [data.shortTime.weight_mul_time_eq_one] with time hWeight
  rw [eq_inv_of_mul_eq_one_left hWeight,
    positiveTimeTraceExtension_eq_extendedHeatTrace parameter time,
    ← data.shortTime_counterterm_eq parameter time]
  simp only [NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData.subtractedHeatTrace,
    div_eq_mul_inv, mul_comm]

theorem longTimeIntegrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear)
    (parameter : Real) :
    IntegrableOn
      (fun time =>
        positiveTimeTraceExtension (nuclear.heatTrace parameter) time / time)
      (Set.Ioi (1 : Real)) volume := by
  apply (data.longTime_integrable parameter).congr
  filter_upwards [data.longTime.weight_mul_time_eq_one] with time hWeight
  rw [eq_inv_of_mul_eq_one_left hWeight,
    positiveTimeTraceExtension_eq_extendedHeatTrace parameter time]
  simp only [div_eq_mul_inv, mul_comm]

/-- The finite-part packet at one parameter, with no separately supplied
integrability proof. -/
def toRelativeHeatFinitePartData
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear)
    (parameter : Real) :
    RelativeHeatFinitePartData (nuclear.heatTrace parameter) where
  counterterm := counterterm data.finiteCounterterm.variation parameter
  countertermFinitePart := finitePartContribution data.finiteCounterterm parameter
  shortTimeIntegrable := data.shortTimeIntegrable parameter
  longTimeIntegrable := data.longTimeIntegrable parameter

theorem shortTimeContribution_eq
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear)
    (parameter : Real) :
    relativeHeatShortTimeFinitePart
        (data.toRelativeHeatFinitePartData parameter) =
      data.shortTime.toWeightedHeatTraceVariation.contribution parameter := by
  unfold relativeHeatShortTimeFinitePart
  unfold WeightedHeatTraceIntegralVariationData.contribution
  rw [integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [data.shortTime.weight_mul_time_eq_one] with time hWeight
  change
    (positiveTimeTraceExtension (nuclear.heatTrace parameter) time -
        (data.toRelativeHeatFinitePartData parameter).counterterm time) / time =
      data.shortTime.weight time *
        data.shortTime.subtractedHeatTrace parameter time
  simp only [toRelativeHeatFinitePartData]
  rw [eq_inv_of_mul_eq_one_left hWeight,
    positiveTimeTraceExtension_eq_extendedHeatTrace parameter time,
    ← data.shortTime_counterterm_eq parameter time]
  simp only [NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData.subtractedHeatTrace,
    div_eq_mul_inv, mul_comm]

theorem longTimeContribution_eq
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear)
    (parameter : Real) :
    relativeHeatLongTimeIntegral
        (data.toRelativeHeatFinitePartData parameter) =
      data.longTime.toWeightedHeatTraceVariation.contribution parameter := by
  unfold relativeHeatLongTimeIntegral
  unfold WeightedHeatTraceIntegralVariationData.contribution
  apply integral_congr_ae
  filter_upwards [data.longTime.weight_mul_time_eq_one] with time hWeight
  change
    positiveTimeTraceExtension (nuclear.heatTrace parameter) time / time =
      data.longTime.weight time * extendedHeatTrace nuclear parameter time
  rw [eq_inv_of_mul_eq_one_left hWeight,
    positiveTimeTraceExtension_eq_extendedHeatTrace parameter time]
  simp only [div_eq_mul_inv, mul_comm]

def logDerivative
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear)
    (parameter : Real) : Real :=
  -finitePartDerivative data.finiteCounterterm parameter +
    (∫ time in Set.Ioo (0 : Real) 1,
      data.shortTime.renormalizedDuhamelTrace parameter time) +
    (∫ time in Set.Ioi (1 : Real),
      extendedDuhamelTrace nuclear parameter time)

private theorem longTime_hasDerivAt
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        ∫ time in Set.Ioi (1 : Real),
          data.longTime.weight time * extendedHeatTrace nuclear current time)
      (-(∫ time in Set.Ioi (1 : Real),
        extendedDuhamelTrace nuclear parameter time)) parameter := by
  exact data.longTime.toDuhamelWeightedHeatTraceVariation.hasDerivAt_contribution
    parameter

/-- Canonical differentiable finite-part family generated by the two heat
regions and the finite counterterm. -/
def toRelativeHeatFinitePartFamilyData
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear) :
    RelativeHeatFinitePartFamilyData where
  heatTrace := nuclear.heatTrace
  finitePart := data.toRelativeHeatFinitePartData
  logDerivative := data.logDerivative
  hasDerivAt_logDeterminant := by
    intro parameter
    have hCounterterm :=
      finitePartContribution_hasDerivAt data.finiteCounterterm parameter
    have hShort := data.shortTime.hasDerivAt_integral parameter
    have hLong := data.longTime_hasDerivAt parameter
    have hTotal := ((hCounterterm.add hShort).add hLong).neg
    have hFunctions :
        (fun current =>
          relativeHeatFinitePartLogDeterminant
            (data.toRelativeHeatFinitePartData current)) =
        (fun current =>
          -(finitePartContribution data.finiteCounterterm current +
            data.shortTime.toWeightedHeatTraceVariation.contribution current +
            data.longTime.toWeightedHeatTraceVariation.contribution current)) := by
      funext current
      unfold relativeHeatFinitePartLogDeterminant
      rw [data.shortTimeContribution_eq current,
        data.longTimeContribution_eq current]
      rfl
    rw [hFunctions]
    refine hTotal.congr_deriv ?_
    unfold logDerivative
    ring

/-- Public constructor checkpoint. -/
theorem nuclear_heat_duhamel_finite_part_family_frontend_gate
    (Index : Type*)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear) :
    let family := data.toRelativeHeatFinitePartFamilyData
    (∀ parameter,
      family.finitePart parameter = data.toRelativeHeatFinitePartData parameter) ∧
    (∀ parameter,
      relativeHeatShortTimeFinitePart (family.finitePart parameter) =
        data.shortTime.toWeightedHeatTraceVariation.contribution parameter) ∧
    (∀ parameter,
      relativeHeatLongTimeIntegral (family.finitePart parameter) =
        data.longTime.toWeightedHeatTraceVariation.contribution parameter) ∧
    (∀ parameter,
      family.logDerivative parameter = data.logDerivative parameter) := by
  exact ⟨fun _ => rfl, data.shortTimeContribution_eq,
    data.longTimeContribution_eq, fun _ => rfl⟩

end NuclearHeatDuhamelFinitePartFamilyFrontendData

end
end P0EFTJanusProgramPNuclearHeatDuhamelFinitePartFamilyFrontend4D
end JanusFormal
