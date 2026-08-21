import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatCanonicalDuhamelTraceVariationFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D

/-!
# Isospectral canonical Duhamel trace variation

Unitary conjugation makes the scalar heat trace parameter-independent.  If the
Duhamel insertion has zero intrinsic trace, this constant derivative is exactly
the canonical Duhamel derivative required by the nuclear frontend.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatUnitaryConjugatedCanonicalDuhamelFrontend4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatCanonicalDuhamelTraceVariationFrontend4D
open P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Unitary heat transport and a traceless Duhamel insertion close the minimal
canonical trace-variation frontend. -/
def nuclearHeatCanonicalDuhamelTraceVariationFrontendData_of_unitaryConjugated
    (heatFamily : UnitaryConjugatedNuclearTraceFamilyData.{u, v}
      (Parameter := Real) (Time := HeatTime) (E := E))
    (duhamelOperator : Real → HeatTime → E →L[Real] E)
    (duhamelTraceClass : ∀ parameter time,
      IntrinsicNuclearTraceData.{u, v} (duhamelOperator parameter time))
    (duhamelTrace_zero : ∀ parameter time,
      intrinsicNuclearTrace (duhamelTraceClass parameter time) = 0) :
    NuclearHeatCanonicalDuhamelTraceVariationFrontendData.{u, v}
      (E := E) where
  heatOperator := heatFamily.movingOperator
  duhamelOperator := duhamelOperator
  heatTraceClass := heatFamily.movingTraceClass
  duhamelTraceClass := duhamelTraceClass
  trace_hasDerivAt := by
    intro parameter time
    have hTraceFunction :
        (fun current : Real =>
          intrinsicNuclearTrace (heatFamily.movingTraceClass current time)) =
          fun _ => heatFamily.baseTrace time := by
      funext current
      exact heatFamily.movingTrace_eq_baseTrace current time
    rw [hTraceFunction, duhamelTrace_zero parameter time, mul_zero]
    exact hasDerivAt_const parameter (heatFamily.baseTrace time)

end
end P0EFTJanusProgramPNuclearHeatUnitaryConjugatedCanonicalDuhamelFrontend4D
end JanusFormal
