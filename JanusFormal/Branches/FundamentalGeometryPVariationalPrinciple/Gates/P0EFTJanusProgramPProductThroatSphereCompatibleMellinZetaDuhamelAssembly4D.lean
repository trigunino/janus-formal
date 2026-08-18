import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConstantRelativeHeatMellinZetaFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D

/-!
# Compatible reduced-sphere Mellin--Duhamel assembly

An arbitrary Mellin--zeta family whose finite-part family is the constant
reduced-sphere family inherits the concrete short- and long-time nuclear
Duhamel assembly.  The only remaining zeta input is reality of the derivative
at zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereCompatibleMellinZetaDuhamelAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPConstantRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
open P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Compatibility data for an arbitrary Mellin--zeta family with the fixed
reduced-sphere finite-part family. -/
structure ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
    (sphereData : ProductThroatSpectralData)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  sphereNuclear :
    ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear
  finitePartFamily_eq :
    family.finitePartFamily =
      constantRelativeHeatFinitePartFamily
        (reducedSphereMellinFinitePartData sphereData)
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData

/-- The short-time renormalized Duhamel integral vanishes. -/
theorem shortTimeDuhamelIntegral_eq_zero
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear)
    (parameter : Real) :
    (∫ time in Set.Ioo (0 : Real) 1,
      data.sphereNuclear.toCountertermSubtractedShortTimeQuadratic.renormalizedDuhamelTrace
        parameter time) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
  unfold NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData.renormalizedDuhamelTrace
  rw [P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.extendedDuhamelTrace_eq_zero
    data.sphereNuclear parameter time hTime.1]
  change 0 + time⁻¹ * 0 = 0
  ring

/-- The long-time Duhamel integral vanishes. -/
theorem longTimeDuhamelIntegral_eq_zero
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear)
    (parameter : Real) :
    (∫ time in Set.Ioi (1 : Real),
      extendedDuhamelTrace nuclear parameter time) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact
    P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.extendedDuhamelTrace_eq_zero
      data.sphereNuclear parameter time
        ((by norm_num : (0 : Real) < 1).trans hTime)

/-- Assemble the concrete finite counterterm with the spherical short- and
long-time nuclear packets. -/
def toFinitePartAssembly
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear) :
    ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      ReducedSphereCountertermProfile family nuclear 1
        (Set.Ioi (1 : Real)) where
  finiteCounterterm := reducedSphereMellinFiniteCountertermVariation sphereData
  shortTime := data.sphereNuclear.toCountertermSubtractedShortTimeQuadratic
  shortTime_counterterm_eq := by
    intro parameter time
    calc
      data.sphereNuclear.toCountertermSubtractedShortTimeQuadratic.counterterm
          parameter time =
          counterterm (reducedSphereCountertermVariation sphereData)
            parameter time :=
        data.sphereNuclear.counterterm_eq_finiteCounterterm parameter time
      _ = reducedSphereCounterterm sphereData time :=
        reducedSphereCountertermVariation_counterterm_eq
          sphereData parameter time
      _ = counterterm
          (reducedSphereMellinFiniteCountertermVariation sphereData).variation
          parameter time :=
        (reducedSphereMellinFiniteCountertermVariation_counterterm_eq
          sphereData parameter time).symm
  longTime :=
    P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.toLongTimeWeightedIntegral
      data.sphereNuclear
  countertermFinitePart_eq := by
    intro parameter
    rw [data.finitePartFamily_eq]
    change reducedSphereMellinCountertermFinitePart sphereData =
      finitePartContribution
        (reducedSphereMellinFiniteCountertermVariation sphereData) parameter
    exact
      (reducedSphereMellinFiniteCountertermVariation_contribution_eq
        sphereData parameter).symm
  shortTimeContribution_eq := by
    intro parameter
    rw [data.finitePartFamily_eq]
    change relativeHeatShortTimeFinitePart
        (reducedSphereMellinFinitePartData sphereData) = _
    rw [reducedSphereMellinFinitePartData_shortTime_eq_raw]
    exact
      (P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D.ProductThroatSphereNuclearShortTimeQuadraticData.contribution_eq
        data.sphereNuclear parameter).symm
  longTimeContribution_eq := by
    intro parameter
    rw [data.finitePartFamily_eq]
    change relativeHeatLongTimeIntegral
        (reducedSphereMellinFinitePartData sphereData) = _
    rw [reducedSphereMellinFinitePartData_longTime_eq_raw]
    exact
      (P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.contribution_eq
        data.sphereNuclear parameter).symm
  logarithmicTrace := fun _ => 0
  duhamel_integral_identity := by
    intro parameter
    rw [reducedSphereMellinFiniteCountertermVariation_derivative_eq_zero,
      data.shortTimeDuhamelIntegral_eq_zero parameter,
      data.longTimeDuhamelIntegral_eq_zero parameter]
    norm_num
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The named finite-part logarithmic derivative vanishes. -/
theorem logDerivative_eq_zero
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear)
    (parameter : Real) :
    family.finitePartFamily.logDerivative parameter = 0 := by
  rw [data.finitePartFamily_eq]
  rfl

/-- The reduced-sphere finite-part logarithm is constant in the parameter. -/
theorem hasDerivAt_logDeterminant_zero
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart current))
      0 parameter := by
  rw [data.finitePartFamily_eq]
  exact hasDerivAt_const parameter
    (relativeHeatFinitePartLogDeterminant
      (reducedSphereMellinFinitePartData sphereData))

/-- The named logarithmic derivative is the assembled, canonically signed
Duhamel expression. -/
theorem namedLogDerivative_eq_duhamel
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear)
    (parameter : Real) :
    family.finitePartFamily.logDerivative parameter =
      -finitePartDerivative data.toFinitePartAssembly.finiteCounterterm
          parameter +
        (∫ time in Set.Ioo (0 : Real) 1,
          data.toFinitePartAssembly.shortTime.renormalizedDuhamelTrace
            parameter time) +
        (∫ time in Set.Ioi (1 : Real),
          extendedDuhamelTrace nuclear parameter time) :=
  data.toFinitePartAssembly.namedLogDerivative_eq_duhamel parameter

/-- Reality of the zeta derivative removes the residual phase derivative, so
the zeta connection coefficient vanishes. -/
theorem connectionCoefficient_eq_zero
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter = 0 := by
  have hTrace :=
    data.toFinitePartAssembly.connectionCoefficient_eq_neg_trace parameter
  change relativeZetaConnectionCoefficient family.toZetaFamily parameter =
    -(0 : Complex) at hTrace
  simpa using hTrace

/-- Every compatible Mellin determinant has the normalized reduced-sphere
finite-part magnitude. -/
theorem norm_mellinZetaDeterminant
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear)
    (parameter : Real) :
    ‖relativeHeatMellinZetaFamilyDeterminant family parameter‖ =
      relativeHeatFinitePartDeterminant
        (reducedSphereMellinFinitePartData sphereData) := by
  rw [norm_relativeHeatMellinZetaFamilyDeterminant,
    data.finitePartFamily_eq]
  rfl

/-- Public generic reduced-sphere terminal checkpoint. -/
theorem product_throat_sphere_compatible_mellin_zeta_duhamel_assembly_gate
    (sphereData : ProductThroatSpectralData)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData
      sphereData family nuclear) :
    let assembly := data.toFinitePartAssembly
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter = 0) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        0 parameter) ∧
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        -finitePartDerivative assembly.finiteCounterterm parameter +
          (∫ time in Set.Ioo (0 : Real) 1,
            assembly.shortTime.renormalizedDuhamelTrace parameter time) +
          (∫ time in Set.Ioi (1 : Real),
            extendedDuhamelTrace nuclear parameter time)) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter = 0) ∧
    (∀ parameter,
      ‖relativeHeatMellinZetaFamilyDeterminant family parameter‖ =
        relativeHeatFinitePartDeterminant
          (reducedSphereMellinFinitePartData sphereData)) := by
  dsimp only
  exact ⟨data.logDerivative_eq_zero,
    data.hasDerivAt_logDeterminant_zero,
    data.namedLogDerivative_eq_duhamel,
    data.connectionCoefficient_eq_zero,
    data.norm_mellinZetaDeterminant⟩

end ProductThroatSphereCompatibleMellinZetaDuhamelAssemblyData

end
end P0EFTJanusProgramPProductThroatSphereCompatibleMellinZetaDuhamelAssembly4D
end JanusFormal
