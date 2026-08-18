import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
# Constant relative heat Mellin--zeta families

A single finite-part packet and its Mellin continuation define an isospectral
parameter family.  Its named logarithmic derivative and zeta connection both
vanish.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConstantRelativeHeatMellinZetaFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-- A finite-part heat packet viewed as a constant real family. -/
def constantRelativeHeatFinitePartFamily
    {heatTrace : HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace) :
    RelativeHeatFinitePartFamilyData where
  heatTrace := fun _ => heatTrace
  finitePart := fun _ => finitePart
  logDerivative := fun _ => 0
  hasDerivAt_logDeterminant := by
    intro parameter
    exact hasDerivAt_const parameter _

/-- A fixed Mellin continuation viewed as a constant zeta family. -/
def constantRelativeHeatMellinZetaFamily
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) :
    RelativeHeatMellinZetaFamilyData where
  finitePartFamily := constantRelativeHeatFinitePartFamily finitePart
  continuation := fun _ => continuation
  parameterDerivative := fun _ => 0
  hasDerivAt_zetaPrime := by
    intro parameter
    exact hasDerivAt_const parameter _
  connection_realPart := by
    intro parameter
    simp [constantRelativeHeatFinitePartFamily]

theorem constantRelativeHeatMellinZetaFamily_zetaPrimeAtZero
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (parameter : Real) :
    (constantRelativeHeatMellinZetaFamily continuation).zetaPrimeAtZero
        parameter =
      continuation.derivativeAtZero :=
  rfl

theorem constantRelativeHeatMellinZetaFamily_connection_eq_zero
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (parameter : Real) :
    relativeZetaConnectionCoefficient
        (constantRelativeHeatMellinZetaFamily continuation).toZetaFamily
        parameter = 0 :=
  rfl

/-- Public isospectral Mellin--zeta family checkpoint. -/
theorem constant_relative_heat_mellin_zeta_family_gate
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) :
    (∀ parameter,
      (constantRelativeHeatMellinZetaFamily continuation).finitePartFamily.finitePart
          parameter = finitePart) ∧
    (∀ parameter,
      (constantRelativeHeatMellinZetaFamily continuation).finitePartFamily.logDerivative
          parameter = 0) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          (constantRelativeHeatMellinZetaFamily continuation).toZetaFamily
          parameter = 0) := by
  exact ⟨fun _ => rfl, fun _ => rfl,
    constantRelativeHeatMellinZetaFamily_connection_eq_zero continuation⟩

end
end P0EFTJanusProgramPConstantRelativeHeatMellinZetaFamily4D
end JanusFormal
