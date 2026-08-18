import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelCountertermSubtractedFinitePartAssembly4D

/-!
# Assemble a finite UV counterterm with a subtracted Duhamel variation

The finite-part contribution and its derivative are now supplied directly by
the same finite counterterm whose density is subtracted at short heat time.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPReferenceHeatDuhamelCountertermSubtractedFinitePartAssembly4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {Index : Type*}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- A finite counterterm whose density is exactly the density subtracted from
the short-time heat trace. -/
structure ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
    (Index : Type*)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) (longTimeRegion : Set Real) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
    nuclear cutoff
  shortTime_counterterm_eq : ∀ parameter time,
    shortTime.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time
  longTime : NuclearHeatDuhamelWeightedIntegralData nuclear longTimeRegion
  countertermFinitePart_eq : ∀ parameter,
    (family.finitePartFamily.finitePart parameter).countertermFinitePart =
      finitePartContribution finiteCounterterm parameter
  shortTimeContribution_eq : ∀ parameter,
    relativeHeatShortTimeFinitePart
        (family.finitePartFamily.finitePart parameter) =
      shortTime.toWeightedHeatTraceVariation.contribution parameter
  longTimeContribution_eq : ∀ parameter,
    relativeHeatLongTimeIntegral
        (family.finitePartFamily.finitePart parameter) =
      longTime.toWeightedHeatTraceVariation.contribution parameter
  logarithmicTrace : Real → Real
  duhamel_integral_identity : ∀ parameter,
    -finitePartDerivative finiteCounterterm parameter +
        (∫ time in Set.Ioo 0 cutoff,
          shortTime.renormalizedDuhamelTrace parameter time) +
        (∫ time in longTimeRegion,
          extendedDuhamelTrace nuclear parameter time) =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData

/-- Equality of the short-time counterterm densities forces equality of their
declared parameter derivatives. -/
theorem shortTime_countertermDerivative_eq
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear cutoff longTimeRegion)
    (parameter time : Real) :
    data.shortTime.countertermDerivative parameter time =
      countertermDerivative data.finiteCounterterm.variation parameter time := by
  have hShort := data.shortTime.counterterm_hasDerivAt parameter time
  have hFinite := counterterm_hasDerivAt
    data.finiteCounterterm.variation parameter time
  have hFunctions :
      (fun current ↦ data.shortTime.counterterm current time) =
        (fun current ↦
          counterterm data.finiteCounterterm.variation current time) := by
    funext current
    exact data.shortTime_counterterm_eq current time
  rw [hFunctions] at hShort
  exact hShort.unique hFinite

/-- The short-time renormalized Duhamel trace uses the derivative of the same
finite counterterm whose density is subtracted. -/
theorem renormalizedDuhamelTrace_eq
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear cutoff longTimeRegion)
    (parameter time : Real) :
    data.shortTime.renormalizedDuhamelTrace parameter time =
      extendedDuhamelTrace nuclear parameter time + data.shortTime.weight time *
        countertermDerivative data.finiteCounterterm.variation parameter time := by
  unfold NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData.renormalizedDuhamelTrace
  rw [data.shortTime_countertermDerivative_eq parameter time]

/-- The three exact raw compatibility equations determine the canonical
finite-part logarithm, including its global heat/zeta minus sign. -/
theorem logDeterminant_eq
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear cutoff longTimeRegion)
    (parameter : Real) :
    relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      -(finitePartContribution data.finiteCounterterm parameter +
        data.shortTime.toWeightedHeatTraceVariation.contribution parameter +
          data.longTime.toWeightedHeatTraceVariation.contribution parameter) := by
  unfold relativeHeatFinitePartLogDeterminant
  rw [data.countertermFinitePart_eq parameter,
    data.shortTimeContribution_eq parameter,
    data.longTimeContribution_eq parameter]

/-- Forget that the integrated UV contribution was computed coefficientwise
from the density subtracted at short time. -/
def toReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear cutoff longTimeRegion) :
    ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData
      family nuclear cutoff longTimeRegion where
  countertermFinitePart := finitePartContribution data.finiteCounterterm
  countertermFinitePartDerivative := finitePartDerivative data.finiteCounterterm
  hasDerivAt_countertermFinitePart := fun parameter =>
    finitePartContribution_hasDerivAt data.finiteCounterterm parameter
  shortTime := data.shortTime
  longTime := data.longTime
  logDeterminant_eq := data.logDeterminant_eq
  logarithmicTrace := data.logarithmicTrace
  duhamel_integral_identity := data.duhamel_integral_identity
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The assembled finite-part logarithm has the integrated logarithmic trace
as derivative. -/
theorem hasDerivAt_finitePartLog
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear cutoff longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current ↦
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart current))
      (data.logarithmicTrace parameter) parameter :=
  data.toReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData.hasDerivAt_finitePartLog
    parameter

/-- The named finite-part derivative is the canonically signed Duhamel
expression computed from the finite counterterm. -/
theorem namedLogDerivative_eq_duhamel
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear cutoff longTimeRegion)
    (parameter : Real) :
    family.finitePartFamily.logDerivative parameter =
      -finitePartDerivative data.finiteCounterterm parameter +
        (∫ time in Set.Ioo 0 cutoff,
          data.shortTime.renormalizedDuhamelTrace parameter time) +
        (∫ time in longTimeRegion,
          extendedDuhamelTrace nuclear parameter time) :=
  data.toReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData.namedLogDerivative_eq_duhamel
    parameter

/-- The associated zeta connection coefficient is the negative logarithmic
trace. -/
theorem connectionCoefficient_eq_neg_trace
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear cutoff longTimeRegion)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.logarithmicTrace parameter : Complex) :=
  data.toReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData.connectionCoefficient_eq_neg_trace
    parameter

/-- Public finite-counterterm, UV-subtracted assembly checkpoint. -/
theorem reference_heat_duhamel_finite_counterterm_subtracted_finite_part_assembly_gate
    (Index : Type*)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) (longTimeRegion : Set Real)
    (data : ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      Index family nuclear cutoff longTimeRegion) :
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
            countertermDerivative data.finiteCounterterm.variation parameter time) ∧
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        -finitePartDerivative data.finiteCounterterm parameter +
          (∫ time in Set.Ioo 0 cutoff,
            data.shortTime.renormalizedDuhamelTrace parameter time) +
          (∫ time in longTimeRegion,
            extendedDuhamelTrace nuclear parameter time)) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) :=
  ⟨data.hasDerivAt_finitePartLog, data.renormalizedDuhamelTrace_eq,
    data.namedLogDerivative_eq_duhamel,
    data.connectionCoefficient_eq_neg_trace⟩

end ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData

end
end P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D
end JanusFormal
