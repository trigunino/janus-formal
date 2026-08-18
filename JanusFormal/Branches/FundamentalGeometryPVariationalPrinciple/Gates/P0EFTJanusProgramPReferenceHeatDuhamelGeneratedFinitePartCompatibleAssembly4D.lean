import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelFinitePartFamilyFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssembly4D

/-!
# Reference assembly with a generated finite-part family

The nuclear short- and long-time packets first generate the real finite-part
family.  A genuine Mellin continuation family then supplies only the remaining
complex analytic data.  Consequently the heat trace, counterterm and both
integral compatibility equations no longer occur as inputs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceHeatDuhamelGeneratedFinitePartCompatibleAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssembly4D
open P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssembly4D.ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {Index : Type*}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Minimal complex terminal data over the generated real finite-part family.
The continuation, its parameter derivative, the integrated Duhamel identity
and the reality condition remain genuine analytic inputs. -/
structure ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData
    (Index : Type*)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finitePart : NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear
  continuation : ∀ parameter,
    RelativeHeatMellinZetaContinuationData
      (finitePart.toRelativeHeatFinitePartData parameter)
  parameterDerivative : Real → Complex
  hasDerivAt_zetaPrime : ∀ parameter,
    HasDerivAt
      (fun current ↦ (continuation current).derivativeAtZero)
      (parameterDerivative parameter) parameter
  logarithmicTrace : Real → Real
  duhamel_integral_identity : ∀ parameter,
    -finitePartDerivative finitePart.finiteCounterterm parameter +
        (∫ time in Set.Ioo (0 : Real) 1,
          finitePart.shortTime.renormalizedDuhamelTrace parameter time) +
        (∫ time in Set.Ioi (1 : Real),
          extendedDuhamelTrace nuclear parameter time) =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (continuation parameter).derivativeAtZero.im = 0

namespace ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData

/-- The connection real-part identity follows from differentiating the
pointwise finite-part identity carried by the Mellin continuations. -/
theorem connection_realPart
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData
      Index nuclear)
    (parameter : Real) :
    data.finitePart.logDerivative parameter =
      -(data.parameterDerivative parameter).re := by
  have hFinite :=
    data.finitePart.toRelativeHeatFinitePartFamilyData.hasDerivAt_logDeterminant
      parameter
  change HasDerivAt
    (fun current ↦
      relativeHeatFinitePartLogDeterminant
        (data.finitePart.toRelativeHeatFinitePartData current))
    (data.finitePart.logDerivative parameter) parameter at hFinite
  have hZetaRe :
      HasDerivAt
        (fun current : Real ↦
          -(data.continuation current).derivativeAtZero.re)
        (-(data.parameterDerivative parameter).re) parameter := by
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt parameter
      (data.hasDerivAt_zetaPrime parameter)).neg
  have hFunctions :
      (fun current ↦
        relativeHeatFinitePartLogDeterminant
          (data.finitePart.toRelativeHeatFinitePartData current)) =
      (fun current : Real ↦
        -(data.continuation current).derivativeAtZero.re) := by
    funext current
    exact (data.continuation current).finitePart_realPart
  rw [hFunctions] at hFinite
  exact hFinite.unique hZetaRe

/-- Mellin zeta family on the finite-part family generated from the heat
packets. -/
def toRelativeHeatMellinZetaFamilyData
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData
      Index nuclear) :
    RelativeHeatMellinZetaFamilyData where
  finitePartFamily := data.finitePart.toRelativeHeatFinitePartFamilyData
  continuation := data.continuation
  parameterDerivative := data.parameterDerivative
  hasDerivAt_zetaPrime := data.hasDerivAt_zetaPrime
  connection_realPart := data.connection_realPart

/-- All scalar compatibility fields of the older assembly are generated
definitionally or by the two contribution theorems of the finite-part
frontend. -/
def toCompatibleFinitePartAssemblyData
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData
      Index nuclear) :
    ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData
      Index data.toRelativeHeatMellinZetaFamilyData nuclear where
  finiteCounterterm := data.finitePart.finiteCounterterm
  shortTime := data.finitePart.shortTime
  longTime := data.finitePart.longTime
  familyHeatTrace_eq := by
    intro parameter time
    rfl
  familyCounterterm_eq := by
    intro parameter time
    rfl
  rawCountertermFinitePart_eq := by
    intro parameter
    rfl
  shortTime_counterterm_eq := data.finitePart.shortTime_counterterm_eq
  logarithmicTrace := data.logarithmicTrace
  duhamel_integral_identity := data.duhamel_integral_identity
  zetaPrimeAtZero_real := by
    intro parameter
    exact data.zetaPrimeAtZero_real parameter

/-- Public terminal: only the genuine Mellin-family data and integrated
Duhamel identity remain above the generated short/long finite part. -/
theorem reference_heat_duhamel_generated_finite_part_compatible_assembly_gate
    (Index : Type*)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData
      Index nuclear) :
    let family := data.toRelativeHeatMellinZetaFamilyData
    (∀ parameter,
      relativeHeatShortTimeFinitePart
          (family.finitePartFamily.finitePart parameter) =
        data.finitePart.shortTime.toWeightedHeatTraceVariation.contribution
          parameter) ∧
    (∀ parameter,
      relativeHeatLongTimeIntegral
          (family.finitePartFamily.finitePart parameter) =
        data.finitePart.longTime.toWeightedHeatTraceVariation.contribution
          parameter) ∧
    (∀ parameter,
      HasDerivAt
        (fun current ↦
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        (data.logarithmicTrace parameter) parameter) ∧
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        -finitePartDerivative data.finitePart.finiteCounterterm parameter +
          (∫ time in Set.Ioo (0 : Real) 1,
            data.finitePart.shortTime.renormalizedDuhamelTrace parameter time) +
          (∫ time in Set.Ioi (1 : Real),
            extendedDuhamelTrace nuclear parameter time)) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) := by
  let family := data.toRelativeHeatMellinZetaFamilyData
  let assembly := data.toCompatibleFinitePartAssemblyData
  rcases
      reference_heat_duhamel_finite_counterterm_compatible_finite_part_assembly_gate
        Index family nuclear assembly with
    ⟨_hCounterterm, hShort, hLong, hDerivative, _hRenormalized,
      hNamed, hConnection⟩
  exact ⟨hShort, hLong, hDerivative, hNamed, hConnection⟩

end ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData

end
end P0EFTJanusProgramPReferenceHeatDuhamelGeneratedFinitePartCompatibleAssembly4D
end JanusFormal
