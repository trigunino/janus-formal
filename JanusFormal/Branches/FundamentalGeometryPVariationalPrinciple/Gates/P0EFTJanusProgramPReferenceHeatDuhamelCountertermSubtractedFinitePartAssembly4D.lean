import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNegatedDuhamelWeightedHeatTraceVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelFinitePartAssembly4D

/-!
# Assemble a UV-subtracted reference finite-part variation

The heat counterterm and both heat integrals retain their raw signs.  The
global heat/zeta minus sign is applied only when converting them to determinant
contributions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceHeatDuhamelCountertermSubtractedFinitePartAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPReferenceHeatDuhamelFinitePartAssembly4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Reference finite-part data with a genuinely UV-subtracted short-time
integral and an unsubtracted nuclear long-time integral. -/
structure ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) (longTimeRegion : Set Real) where
  countertermFinitePart : Real → Real
  countertermFinitePartDerivative : Real → Real
  hasDerivAt_countertermFinitePart : ∀ parameter,
    HasDerivAt countertermFinitePart
      (countertermFinitePartDerivative parameter)
      parameter
  shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
    nuclear cutoff
  longTime : NuclearHeatDuhamelWeightedIntegralData nuclear longTimeRegion
  logDeterminant_eq : ∀ parameter,
    relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      -(countertermFinitePart parameter +
        shortTime.toWeightedHeatTraceVariation.contribution parameter +
          longTime.toWeightedHeatTraceVariation.contribution parameter)
  logarithmicTrace : Real → Real
  duhamel_integral_identity : ∀ parameter,
    -countertermFinitePartDerivative parameter +
        (∫ time in Set.Ioo 0 cutoff,
          shortTime.renormalizedDuhamelTrace parameter time) +
        (∫ time in longTimeRegion,
          extendedDuhamelTrace nuclear parameter time) =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData

/-- Forget the nuclear construction details after recording the subtracted
short-time and ordinary long-time Duhamel interfaces. -/
def toReferenceHeatDuhamelFinitePartAssemblyData
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData
      family nuclear cutoff longTimeRegion) :
    ReferenceHeatDuhamelFinitePartAssemblyData family (Set.Ioo 0 cutoff)
      longTimeRegion where
  countertermContribution := fun parameter => -data.countertermFinitePart parameter
  countertermDerivative := fun parameter =>
    -data.countertermFinitePartDerivative parameter
  hasDerivAt_counterterm := fun parameter =>
    (data.hasDerivAt_countertermFinitePart parameter).neg
  shortTime := data.shortTime.toDuhamelWeightedHeatTraceVariation.negated
  longTime := data.longTime.toDuhamelWeightedHeatTraceVariation.negated
  logDeterminant_eq := by
    intro parameter
    rw [data.logDeterminant_eq parameter,
      (data.shortTime.toDuhamelWeightedHeatTraceVariation.negated_contribution_eq_neg_contribution
        parameter),
      (data.longTime.toDuhamelWeightedHeatTraceVariation.negated_contribution_eq_neg_contribution
        parameter)]
    simp only [NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData.toDuhamelWeightedHeatTraceVariation,
      NuclearHeatDuhamelWeightedIntegralData.toDuhamelWeightedHeatTraceVariation]
    ring
  logarithmicTrace := data.logarithmicTrace
  duhamel_integral_identity := by
    intro parameter
    change -data.countertermFinitePartDerivative parameter -
        (∫ time in Set.Ioo 0 cutoff,
          -data.shortTime.renormalizedDuhamelTrace parameter time) -
        (∫ time in longTimeRegion,
          -extendedDuhamelTrace nuclear parameter time) =
      data.logarithmicTrace parameter
    rw [integral_neg, integral_neg]
    simpa only [sub_neg_eq_add] using
      data.duhamel_integral_identity parameter
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The UV-subtracted finite-part logarithm has the integrated logarithmic
trace as derivative. -/
theorem hasDerivAt_finitePartLog
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData
      family nuclear cutoff longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart current))
      (data.logarithmicTrace parameter) parameter :=
  data.toReferenceHeatDuhamelFinitePartAssemblyData.hasDerivAt_finitePartLog
    parameter

/-- The named finite-part derivative is the canonically signed Duhamel
expression. -/
theorem namedLogDerivative_eq_duhamel
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData
      family nuclear cutoff longTimeRegion)
    (parameter : Real) :
    family.finitePartFamily.logDerivative parameter =
      -data.countertermFinitePartDerivative parameter +
        (∫ time in Set.Ioo 0 cutoff,
          data.shortTime.renormalizedDuhamelTrace parameter time) +
        (∫ time in longTimeRegion,
          extendedDuhamelTrace nuclear parameter time) := by
  calc
    family.finitePartFamily.logDerivative parameter =
        data.logarithmicTrace parameter :=
      (family.finitePartFamily.hasDerivAt_logDeterminant parameter).unique
        (data.hasDerivAt_finitePartLog parameter)
    _ = _ := (data.duhamel_integral_identity parameter).symm

/-- The associated zeta connection coefficient is the negative logarithmic
trace. -/
theorem connectionCoefficient_eq_neg_trace
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real} {longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData
      family nuclear cutoff longTimeRegion)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.logarithmicTrace parameter : Complex) :=
  data.toReferenceHeatDuhamelFinitePartAssemblyData.connectionCoefficient_eq_neg_trace
    parameter

/-- Public UV-subtracted finite-part assembly checkpoint. -/
theorem reference_heat_duhamel_counterterm_subtracted_finite_part_assembly_gate
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) (longTimeRegion : Set Real)
    (data : ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData
      family nuclear cutoff longTimeRegion) :
    (∀ parameter,
      HasDerivAt
        (fun current =>
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        (data.logarithmicTrace parameter) parameter) ∧
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        -data.countertermFinitePartDerivative parameter +
          (∫ time in Set.Ioo 0 cutoff,
            data.shortTime.renormalizedDuhamelTrace parameter time) +
          (∫ time in longTimeRegion,
            extendedDuhamelTrace nuclear parameter time)) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) :=
  ⟨data.hasDerivAt_finitePartLog, data.namedLogDerivative_eq_duhamel,
    data.connectionCoefficient_eq_neg_trace⟩

end ReferenceHeatDuhamelCountertermSubtractedFinitePartAssemblyData

end
end P0EFTJanusProgramPReferenceHeatDuhamelCountertermSubtractedFinitePartAssembly4D
end JanusFormal
