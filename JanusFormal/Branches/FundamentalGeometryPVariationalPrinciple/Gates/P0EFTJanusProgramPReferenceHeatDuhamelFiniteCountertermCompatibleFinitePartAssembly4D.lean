import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D

/-!
# Compatible finite-part and nuclear Duhamel assembly

Scalar equality of the heat traces and counterterms identifies the abstract
finite-part contributions with the weighted nuclear packets.  The logarithmic
weight is recovered almost everywhere from `w(t) * t = 1`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssembly4D

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
open P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {Index : Type*}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Exact scalar compatibility between a finite-part family and nuclear
short- and long-time packets at the canonical cutoff `1`. -/
structure ReferenceHeatDuhamelFiniteCountertermCompatibilityData
    (Index : Type*)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
    nuclear 1
  longTime : NuclearHeatDuhamelWeightedIntegralData nuclear
    (Set.Ioi (1 : Real))
  familyHeatTrace_eq : ∀ parameter time,
    family.finitePartFamily.heatTrace parameter time =
      nuclear.heatTrace parameter time
  familyCounterterm_eq : ∀ parameter time,
    (family.finitePartFamily.finitePart parameter).counterterm time =
      counterterm finiteCounterterm.variation parameter time
  rawCountertermFinitePart_eq : ∀ parameter,
    (family.finitePartFamily.finitePart parameter).countertermFinitePart =
      finitePartContribution finiteCounterterm parameter
  shortTime_counterterm_eq : ∀ parameter time,
    shortTime.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time

namespace ReferenceHeatDuhamelFiniteCountertermCompatibilityData

/-- Equality on positive heat time extends to equality of the two real-time
zero extensions. -/
theorem extendedHeatTrace_eq_positiveTimeTraceExtension
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceHeatDuhamelFiniteCountertermCompatibilityData
      Index family nuclear)
    (parameter time : Real) :
    extendedHeatTrace nuclear parameter time =
      positiveTimeTraceExtension
        (family.finitePartFamily.heatTrace parameter) time := by
  by_cases hTime : 0 < time
  · simp [extendedHeatTrace, positiveTimeTraceExtension, hTime,
      data.familyHeatTrace_eq]
  · simp [extendedHeatTrace, positiveTimeTraceExtension, hTime]

/-- The open short-time nuclear integral is the finite-part packet's
half-open short-time integral. -/
theorem shortTimeContribution_eq
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceHeatDuhamelFiniteCountertermCompatibilityData
      Index family nuclear)
    (parameter : Real) :
    relativeHeatShortTimeFinitePart
        (family.finitePartFamily.finitePart parameter) =
      data.shortTime.toWeightedHeatTraceVariation.contribution parameter := by
  unfold relativeHeatShortTimeFinitePart
  unfold WeightedHeatTraceIntegralVariationData.contribution
  rw [integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [data.shortTime.weight_mul_time_eq_one] with time hWeight
  change
    (positiveTimeTraceExtension
          (family.finitePartFamily.heatTrace parameter) time -
        (family.finitePartFamily.finitePart parameter).counterterm time) /
        time =
      data.shortTime.weight time *
        (extendedHeatTrace nuclear parameter time -
          data.shortTime.counterterm parameter time)
  rw [eq_inv_of_mul_eq_one_left hWeight,
    data.extendedHeatTrace_eq_positiveTimeTraceExtension parameter time,
    data.shortTime_counterterm_eq parameter time,
    ← data.familyCounterterm_eq parameter time]
  simp only [div_eq_mul_inv, mul_comm]

/-- The long-time nuclear packet is the finite-part packet's logarithmic
long-time integral. -/
theorem longTimeContribution_eq
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceHeatDuhamelFiniteCountertermCompatibilityData
      Index family nuclear)
    (parameter : Real) :
    relativeHeatLongTimeIntegral
        (family.finitePartFamily.finitePart parameter) =
      data.longTime.toWeightedHeatTraceVariation.contribution parameter := by
  unfold relativeHeatLongTimeIntegral
  unfold WeightedHeatTraceIntegralVariationData.contribution
  apply integral_congr_ae
  filter_upwards [data.longTime.weight_mul_time_eq_one] with time hWeight
  change
    positiveTimeTraceExtension
        (family.finitePartFamily.heatTrace parameter) time / time =
      data.longTime.weight time *
        extendedHeatTrace nuclear parameter time
  rw [eq_inv_of_mul_eq_one_left hWeight,
    data.extendedHeatTrace_eq_positiveTimeTraceExtension parameter time]
  simp only [div_eq_mul_inv, mul_comm]

end ReferenceHeatDuhamelFiniteCountertermCompatibilityData

/-- Terminal analytic data added to the exact scalar compatibility packet. -/
structure ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData
    (Index : Type*)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    extends ReferenceHeatDuhamelFiniteCountertermCompatibilityData
      Index family nuclear where
  logarithmicTrace : Real → Real
  duhamel_integral_identity : ∀ parameter,
    -finitePartDerivative finiteCounterterm parameter +
        (∫ time in Set.Ioo (0 : Real) 1,
          shortTime.renormalizedDuhamelTrace parameter time) +
        (∫ time in Set.Ioi (1 : Real),
          extendedDuhamelTrace nuclear parameter time) =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData

/-- Convert exact scalar compatibility into the canonical finite-counterterm
assembly. -/
def toReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData
      Index family nuclear) :
    ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear 1 (Set.Ioi (1 : Real)) where
  finiteCounterterm := data.finiteCounterterm
  shortTime := data.shortTime
  shortTime_counterterm_eq := data.shortTime_counterterm_eq
  longTime := data.longTime
  countertermFinitePart_eq := data.rawCountertermFinitePart_eq
  shortTimeContribution_eq :=
    data.toReferenceHeatDuhamelFiniteCountertermCompatibilityData.shortTimeContribution_eq
  longTimeContribution_eq :=
    data.toReferenceHeatDuhamelFiniteCountertermCompatibilityData.longTimeContribution_eq
  logarithmicTrace := data.logarithmicTrace
  duhamel_integral_identity := data.duhamel_integral_identity
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Public compatibility-to-assembly checkpoint. -/
theorem reference_heat_duhamel_finite_counterterm_compatible_finite_part_assembly_gate
    (Index : Type*)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData
      Index family nuclear) :
    (∀ parameter,
      (family.finitePartFamily.finitePart parameter).countertermFinitePart =
        finitePartContribution data.finiteCounterterm parameter) ∧
    (∀ parameter,
      relativeHeatShortTimeFinitePart
          (family.finitePartFamily.finitePart parameter) =
        data.shortTime.toWeightedHeatTraceVariation.contribution parameter) ∧
    (∀ parameter,
      relativeHeatLongTimeIntegral
          (family.finitePartFamily.finitePart parameter) =
        data.longTime.toWeightedHeatTraceVariation.contribution parameter) ∧
    (∀ parameter,
      HasDerivAt
        (fun current ↦
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        (data.logarithmicTrace parameter) parameter) ∧
    (∀ parameter time,
      data.shortTime.renormalizedDuhamelTrace parameter time =
        extendedDuhamelTrace nuclear parameter time +
          data.shortTime.weight time *
            countertermDerivative data.finiteCounterterm.variation
              parameter time) ∧
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        -finitePartDerivative data.finiteCounterterm parameter +
          (∫ time in Set.Ioo (0 : Real) 1,
            data.shortTime.renormalizedDuhamelTrace parameter time) +
          (∫ time in Set.Ioi (1 : Real),
            extendedDuhamelTrace nuclear parameter time)) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) := by
  let compatibility :=
    data.toReferenceHeatDuhamelFiniteCountertermCompatibilityData
  let assembly :=
    data.toReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
  rcases
      P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D.ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData.reference_heat_duhamel_finite_counterterm_subtracted_finite_part_assembly_gate
        Index family nuclear 1 (Set.Ioi (1 : Real)) assembly with
    ⟨hDerivative, hRenormalized, hNamed, hConnection⟩
  exact ⟨data.rawCountertermFinitePart_eq,
    compatibility.shortTimeContribution_eq,
    compatibility.longTimeContribution_eq,
    hDerivative, hRenormalized, hNamed, hConnection⟩

end ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData

end
end P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssembly4D
end JanusFormal
