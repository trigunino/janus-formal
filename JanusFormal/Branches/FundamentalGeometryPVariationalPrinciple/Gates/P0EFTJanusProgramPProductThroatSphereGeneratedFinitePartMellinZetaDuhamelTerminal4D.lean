import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelGeneratedFinitePartCompatibleAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereIsospectralMellinZetaDuhamelAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D

/-!
# Generated finite-part terminal for the isospectral reduced sphere

This is the end-to-end specialization of the generated finite-part frontend.
The spherical nuclear short and long packets construct the finite-part family;
the already proved reduced-sphere Mellin continuation supplies the remaining
complex analytic data.  No finite-part family or scalar compatibility equation
is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereGeneratedFinitePartMellinZetaDuhamelTerminal4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
open P0EFTJanusProgramPProductThroatSphereIsospectralMellinZetaDuhamelAssembly4D
open P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
open P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPReferenceHeatDuhamelGeneratedFinitePartCompatibleAssembly4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Spherical short and long packets viewed by the generated finite-part
frontend. -/
def reducedSphereGeneratedFinitePartFrontend
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    NuclearHeatDuhamelFinitePartFamilyFrontendData
      ReducedSphereCountertermProfile nuclear where
  finiteCounterterm := reducedSphereMellinFiniteCountertermVariation sphereData
  shortTime := data.toCountertermSubtractedShortTimeQuadratic
  shortTime_counterterm_eq := by
    intro parameter time
    simpa [reducedSphereMellinFiniteCountertermVariation] using
      data.counterterm_eq_finiteCounterterm parameter time
  longTime :=
    P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.toLongTimeWeightedIntegral
      data
  longTime_integrable :=
    P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.weightedHeatTrace_longTimeIntegrable
      data

theorem reducedSphereGeneratedFinitePartLogDeterminant_eq
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter : Real) :
    relativeHeatFinitePartLogDeterminant
        (reducedSphereGeneratedFinitePartFrontend sphereData nuclear data
          |>.toRelativeHeatFinitePartData parameter) =
      relativeHeatFinitePartLogDeterminant
        (reducedSphereMellinFinitePartData sphereData) := by
  let frontend :=
    reducedSphereGeneratedFinitePartFrontend sphereData nuclear data
  unfold relativeHeatFinitePartLogDeterminant
  rw [frontend.shortTimeContribution_eq parameter,
    frontend.longTimeContribution_eq parameter]
  change
    -(finitePartContribution
          (reducedSphereMellinFiniteCountertermVariation sphereData) parameter +
        data.toCountertermSubtractedShortTimeQuadratic.toWeightedHeatTraceVariation.contribution
          parameter +
        (P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.toLongTimeWeightedIntegral
          data).toWeightedHeatTraceVariation.contribution parameter) =
      -(reducedSphereMellinCountertermFinitePart sphereData +
        relativeHeatShortTimeFinitePart
          (reducedSphereMellinFinitePartData sphereData) +
        relativeHeatLongTimeIntegral
          (reducedSphereMellinFinitePartData sphereData))
  rw [
    P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D.ProductThroatSphereNuclearShortTimeQuadraticData.contribution_eq
      data parameter,
    P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.contribution_eq
      data parameter,
    reducedSphereMellinFinitePartData_shortTime_eq_raw,
    reducedSphereMellinFinitePartData_longTime_eq_raw,
    reducedSphereMellinFiniteCountertermVariation_contribution_eq]

/-- The concrete sphere continuation, retargeted to the finite-part packet
generated from the nuclear heat family. -/
def reducedSphereGeneratedMellinContinuation
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter : Real) :
    RelativeHeatMellinZetaContinuationData
      (reducedSphereGeneratedFinitePartFrontend sphereData nuclear data
        |>.toRelativeHeatFinitePartData parameter) where
  convergenceAbscissa :=
    (reducedSphereMellinZetaContinuationData sphereData).convergenceAbscissa
  zeta := (reducedSphereMellinZetaContinuationData sphereData).zeta
  derivativeAtZero :=
    (reducedSphereMellinZetaContinuationData sphereData).derivativeAtZero
  mellin_integrable := by
    intro spectral hSpectral
    have hHeatTrace : nuclear.heatTrace parameter =
        dimensionlessReducedSphereHeatTrace sphereData := by
      funext time
      exact data.heatTrace_eq parameter time
    rw [hHeatTrace]
    exact (reducedSphereMellinZetaContinuationData sphereData).mellin_integrable
      spectral hSpectral
  zeta_eq_mellin := by
    intro spectral hSpectral
    have hHeatTrace : nuclear.heatTrace parameter =
        dimensionlessReducedSphereHeatTrace sphereData := by
      funext time
      exact data.heatTrace_eq parameter time
    rw [hHeatTrace]
    exact (reducedSphereMellinZetaContinuationData sphereData).zeta_eq_mellin
      spectral hSpectral
  hasDerivAt_zero :=
    (reducedSphereMellinZetaContinuationData sphereData).hasDerivAt_zero
  finitePart_realPart := by
    rw [reducedSphereGeneratedFinitePartLogDeterminant_eq
      sphereData nuclear data parameter]
    exact (reducedSphereMellinZetaContinuationData sphereData).finitePart_realPart

/-- The fully generated isospectral assembly data. -/
def reducedSphereGeneratedCompatibleAssembly
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData
      ReducedSphereCountertermProfile nuclear where
  finitePart := reducedSphereGeneratedFinitePartFrontend sphereData nuclear data
  continuation := reducedSphereGeneratedMellinContinuation sphereData nuclear data
  parameterDerivative := fun _ ↦ 0
  hasDerivAt_zetaPrime := by
    intro parameter
    change HasDerivAt
      (fun _ : Real ↦
        (reducedSphereMellinZetaContinuationData sphereData).derivativeAtZero)
      0 parameter
    exact hasDerivAt_const parameter _
  logarithmicTrace := fun _ ↦ 0
  duhamel_integral_identity := by
    intro parameter
    change
      -finitePartDerivative
          (reducedSphereMellinFiniteCountertermVariation sphereData) parameter +
          (∫ time in Set.Ioo (0 : Real) 1,
            data.toCountertermSubtractedShortTimeQuadratic.renormalizedDuhamelTrace
              parameter time) +
          (∫ time in Set.Ioi (1 : Real),
            extendedDuhamelTrace nuclear parameter time) = 0
    rw [reducedSphereMellinFiniteCountertermVariation_derivative_eq_zero,
      shortTimeDuhamelIntegral_eq_zero data,
      longTimeDuhamelIntegral_eq_zero data]
    ring
  zetaPrimeAtZero_real := by
    intro parameter
    exact reducedSphereMellinZetaContinuationData_derivativeAtZero_im sphereData

/-- End-to-end checkpoint parallel to the older concrete terminal, but with
the finite-part family and all scalar compatibilities generated internally. -/
theorem product_throat_sphere_generated_finite_part_mellin_zeta_duhamel_terminal_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    let generated :=
      reducedSphereGeneratedCompatibleAssembly sphereData nuclear data
    let family := generated.toRelativeHeatMellinZetaFamilyData
    (∀ parameter,
      HasDerivAt
        (fun current ↦
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        0 parameter) ∧
    (∀ parameter, family.finitePartFamily.logDerivative parameter = 0) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter = 0) ∧
    (∀ parameter,
      relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
        relativeHeatFinitePartLogDeterminant
          (reducedSphereMellinFinitePartData sphereData)) ∧
    (∀ parameter,
      ‖relativeHeatMellinZetaFamilyDeterminant family parameter‖ =
        relativeHeatFinitePartDeterminant
          (reducedSphereMellinFinitePartData sphereData)) := by
  dsimp only
  let generated :=
    reducedSphereGeneratedCompatibleAssembly sphereData nuclear data
  let family := generated.toRelativeHeatMellinZetaFamilyData
  rcases
      generated.reference_heat_duhamel_generated_finite_part_compatible_assembly_gate
        ReducedSphereCountertermProfile nuclear with
    ⟨_hShort, _hLong, hDerivative, hNamed, hConnection⟩
  have hLogDet := reducedSphereGeneratedFinitePartLogDeterminant_eq
    sphereData nuclear data
  have hLogarithmicTrace : ∀ parameter,
      generated.logarithmicTrace parameter = 0 := by
    intro parameter
    rfl
  refine ⟨?_, ?_, ?_, hLogDet, ?_⟩
  · intro parameter
    simpa [hLogarithmicTrace parameter] using hDerivative parameter
  · intro parameter
    calc
      family.finitePartFamily.logDerivative parameter =
          -finitePartDerivative generated.finitePart.finiteCounterterm parameter +
            (∫ time in Set.Ioo (0 : Real) 1,
              generated.finitePart.shortTime.renormalizedDuhamelTrace
                parameter time) +
            (∫ time in Set.Ioi (1 : Real),
              extendedDuhamelTrace nuclear parameter time) := hNamed parameter
      _ = generated.logarithmicTrace parameter :=
        generated.duhamel_integral_identity parameter
      _ = 0 := hLogarithmicTrace parameter
  · intro parameter
    calc
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
          -(generated.logarithmicTrace parameter : Complex) :=
        hConnection parameter
      _ = 0 := by rw [hLogarithmicTrace parameter]; simp
  · intro parameter
    rw [norm_relativeHeatMellinZetaFamilyDeterminant]
    unfold relativeHeatFinitePartDeterminantFamily
      relativeHeatFinitePartDeterminant
    change
      Real.exp (relativeHeatFinitePartLogDeterminant
        (reducedSphereGeneratedFinitePartFrontend sphereData nuclear data
          |>.toRelativeHeatFinitePartData parameter)) =
        Real.exp (relativeHeatFinitePartLogDeterminant
          (reducedSphereMellinFinitePartData sphereData))
    rw [hLogDet parameter]

end
end P0EFTJanusProgramPProductThroatSphereGeneratedFinitePartMellinZetaDuhamelTerminal4D
end JanusFormal
