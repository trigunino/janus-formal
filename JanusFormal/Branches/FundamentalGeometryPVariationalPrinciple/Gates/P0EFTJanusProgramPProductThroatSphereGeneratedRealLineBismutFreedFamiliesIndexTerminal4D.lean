import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereGeneratedFinitePartMellinZetaDuhamelTerminal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedRealLineFamiliesIndexTerminal4D

/-!
# Concrete real-line BF terminal for the generated reduced sphere

The generated spherical Mellin--Duhamel terminal has zero logarithmic
derivative and zero zeta connection.  The sole remaining operator input is a
differentiable relative intrinsic trace one-form whose scalar restriction is
zero.  The geometric BF one-form and local families-index two-form are then
chosen canonically to be zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereGeneratedRealLineBismutFreedFamiliesIndexTerminal4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
open P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatSphereGeneratedFinitePartMellinZetaDuhamelTerminal4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPRealLineIntrinsicTraceOneFormRestriction4D
open P0EFTJanusProgramPReferenceHeatDuhamelGeneratedFinitePartCompatibleAssembly4D
open P0EFTJanusProgramPRelativeBismutFreedRealLineFamiliesIndexTerminal4D
open P0EFTJanusProgramPRelativeBismutFreedRealLineUnitOneFormTerminal4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The exact irreducible operator datum left by the scalar spherical
terminal.  Vanishing of its scalar restriction is the only compatibility
hypothesis. -/
structure ProductThroatSphereGeneratedRealLineBismutFreedOperatorData
    (actual reference : Real → E →L[Real] E) where
  operator : DifferentiableRelativeIntrinsicTraceOneFormData.{0, u, v}
    actual reference
  scalarTrace_eq_zero : ∀ parameter,
    (toScalarRelativeIntrinsicTrace operator.trace).trace parameter = 0

/-- Canonical zero geometric BF one-form with its actual zero derivative. -/
def zeroDifferentiableGeometricBismutFreedOneForm :
    DifferentiableLinearGeometricBismutFreedOneFormData Real where
  geometry := ⟨fun _ ↦ 0⟩
  derivative := fun _ ↦ 0
  hasFDerivAt_oneForm := by
    intro parameter
    exact hasFDerivAt_const 0 parameter

/-- Canonical zero local families-index two-form on the real line. -/
def zeroLocalFamiliesIndexTwoForm : LocalFamiliesIndexTwoFormData Real where
  twoForm := fun _ ↦ 0
  antisymm := by
    intro base first second
    simp

namespace ProductThroatSphereGeneratedRealLineBismutFreedOperatorData

theorem directionalTrace_unit_eq_zero
    {actual reference : Real → E →L[Real] E}
    (operatorData :
      ProductThroatSphereGeneratedRealLineBismutFreedOperatorData.{u, v}
        actual reference)
    (parameter : Real) :
    operatorData.operator.trace.directionalTrace parameter 1 = 0 := by
  rw [← toScalarRelativeIntrinsicTrace_trace_eq_directionalTrace]
  exact operatorData.scalarTrace_eq_zero parameter

/-- Unit-one-form terminal obtained without a separately supplied geometric
comparison. -/
def toUnitOneFormTerminal
    {actual reference : Real → E →L[Real] E}
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (sphereNuclear :
      ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (operatorData :
      ProductThroatSphereGeneratedRealLineBismutFreedOperatorData.{u, v}
        actual reference) :
    RelativeBismutFreedRealLineUnitOneFormTerminalData.{u, v}
      actual reference where
  operator := operatorData.operator
  geometric := zeroDifferentiableGeometricBismutFreedOneForm
  oneForm_agreement_unit := by
    intro parameter
    change (0 : Complex) =
      ((operatorData.operator.trace.bismutFreedRealOneForm
        parameter 1 : Real) : Complex)
    rw [operatorData.operator.trace.bismutFreedRealOneForm_apply]
    change (0 : Complex) =
      ((-operatorData.operator.trace.directionalTrace parameter 1 : Real) :
        Complex)
    rw [operatorData.directionalTrace_unit_eq_zero parameter]
    norm_num
  zetaFamily :=
    (reducedSphereGeneratedCompatibleAssembly sphereData nuclear sphereNuclear).toRelativeHeatMellinZetaFamilyData
  finitePartLogDerivative_eq_trace := by
    have hSphere :=
      product_throat_sphere_generated_finite_part_mellin_zeta_duhamel_terminal_gate
        sphereData nuclear sphereNuclear
    intro parameter
    exact (hSphere.2.1 parameter).trans
      (operatorData.scalarTrace_eq_zero parameter).symm
  zetaPrimeAtZero_real := by
    intro parameter
    exact
      (reducedSphereGeneratedCompatibleAssembly sphereData nuclear sphereNuclear).zetaPrimeAtZero_real
        parameter

/-- Families-index terminal with the canonical zero local index form. -/
def toFamiliesIndexTerminal
    {actual reference : Real → E →L[Real] E}
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (sphereNuclear :
      ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (operatorData :
      ProductThroatSphereGeneratedRealLineBismutFreedOperatorData.{u, v}
        actual reference) :
    RelativeBismutFreedRealLineFamiliesIndexTerminalData.{u, v}
      actual reference where
  bismutFreed := operatorData.toUnitOneFormTerminal
    sphereData nuclear sphereNuclear
  localIndex := zeroLocalFamiliesIndexTwoForm

/-- Public concrete BF/families-index checkpoint. -/
theorem product_throat_sphere_generated_real_line_bismut_freed_families_index_terminal_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (sphereNuclear :
      ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (actual reference : Real → E →L[Real] E)
    (operatorData :
      ProductThroatSphereGeneratedRealLineBismutFreedOperatorData.{u, v}
        actual reference) :
    let unit := operatorData.toUnitOneFormTerminal
      sphereData nuclear sphereNuclear
    let families := operatorData.toFamiliesIndexTerminal
      sphereData nuclear sphereNuclear
    (∀ parameter,
      relativeZetaConnectionCoefficient unit.zetaFamily.toZetaFamily
        parameter = 0) ∧
    (∀ parameter direction,
      unit.geometric.geometry.oneForm parameter direction = 0) ∧
    (∀ parameter direction,
      unit.geometric.geometry.oneForm parameter direction =
        ((operatorData.operator.trace.bismutFreedRealOneForm
          parameter direction : Real) : Complex)) ∧
    (∀ base first second,
      unit.geometric.curvature base first second = 0) ∧
    (∀ base first second,
      families.localIndex.twoForm base first second = 0) ∧
    Nonempty
      (P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D.DifferentialFamiliesIndexComparisonData.{0, u, v}
        actual reference) := by
  dsimp only
  let unit := operatorData.toUnitOneFormTerminal
    sphereData nuclear sphereNuclear
  let families := operatorData.toFamiliesIndexTerminal
    sphereData nuclear sphereNuclear
  have hSphere :=
    product_throat_sphere_generated_finite_part_mellin_zeta_duhamel_terminal_gate
      sphereData nuclear sphereNuclear
  rcases
      unit.relative_bismut_freed_real_line_unit_one_form_terminal_gate
        actual reference with
    ⟨hOneForm, _hGeometricConnection, _hDerivative, _hOperatorCurvature⟩
  rcases
      families.relative_bismut_freed_real_line_families_index_terminal_gate
        actual reference with
    ⟨hCurvature, hLocalIndex, _hAgreement, hComparison⟩
  exact ⟨hSphere.2.2.1,
    fun _ _ ↦ rfl,
    hOneForm,
    hCurvature,
    hLocalIndex,
    hComparison⟩

end ProductThroatSphereGeneratedRealLineBismutFreedOperatorData

end
end P0EFTJanusProgramPProductThroatSphereGeneratedRealLineBismutFreedFamiliesIndexTerminal4D
end JanusFormal
