import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConstantRelativeHeatMellinZetaFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D

/-!
# Terminal isospectral reduced-sphere Mellin--Duhamel assembly

Given a reduced-sphere Mellin continuation, the constant family, its finite
local counterterm, and the nuclear short- and long-time packets assemble
canonically.  Both Duhamel integrals vanish, so the determinant logarithm and
the zeta connection have zero parameter derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereIsospectralMellinZetaDuhamelAssembly4D

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
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

theorem extendedDuhamelTrace_eq_zero
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter time : Real) (hTime : 0 < time) :
    extendedDuhamelTrace nuclear parameter time = 0 :=
  P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.extendedDuhamelTrace_eq_zero
    data parameter time hTime

theorem shortTimeRenormalizedDuhamelTrace_eq_zero
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter time : Real) (hTime : 0 < time) :
    data.toCountertermSubtractedShortTimeQuadratic.renormalizedDuhamelTrace
        parameter time = 0 := by
  unfold NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData.renormalizedDuhamelTrace
  rw [extendedDuhamelTrace_eq_zero data parameter time hTime]
  simp [ProductThroatSphereNuclearShortTimeQuadraticData.toCountertermSubtractedShortTimeQuadratic]

theorem shortTimeDuhamelIntegral_eq_zero
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter : Real) :
    (∫ time in Set.Ioo (0 : Real) 1,
      data.toCountertermSubtractedShortTimeQuadratic.renormalizedDuhamelTrace
        parameter time) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
  exact shortTimeRenormalizedDuhamelTrace_eq_zero data parameter time hTime.1

theorem longTimeDuhamelIntegral_eq_zero
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter : Real) :
    (∫ time in Set.Ioi (1 : Real),
      extendedDuhamelTrace nuclear parameter time) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact extendedDuhamelTrace_eq_zero data parameter time
    ((by norm_num : (0 : Real) < 1).trans hTime)

/-- The counterterm derivative and both Duhamel integrals vanish separately. -/
theorem product_throat_sphere_isospectral_duhamel_vanishing_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    (∀ parameter,
      finitePartDerivative (reducedSphereMellinFiniteCountertermVariation sphereData)
        parameter = 0) ∧
    (∀ parameter,
      (∫ time in Set.Ioo (0 : Real) 1,
        data.toCountertermSubtractedShortTimeQuadratic.renormalizedDuhamelTrace
          parameter time) = 0) ∧
    (∀ parameter,
      (∫ time in Set.Ioi (1 : Real),
        extendedDuhamelTrace nuclear parameter time) = 0) :=
  ⟨reducedSphereMellinFiniteCountertermVariation_derivative_eq_zero
      sphereData,
    shortTimeDuhamelIntegral_eq_zero data,
    longTimeDuhamelIntegral_eq_zero data⟩

/-- Phase-independent terminal checkpoint.  A constant imaginary part of the
zeta derivative does not affect the parameter connection. -/
theorem product_throat_sphere_isospectral_mellin_zeta_phase_independent_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (continuation : RelativeHeatMellinZetaContinuationData
      (reducedSphereMellinFinitePartData sphereData)) :
    ((∀ parameter,
      finitePartDerivative (reducedSphereMellinFiniteCountertermVariation sphereData)
        parameter = 0) ∧
    (∀ parameter,
      (∫ time in Set.Ioo (0 : Real) 1,
        data.toCountertermSubtractedShortTimeQuadratic.renormalizedDuhamelTrace
          parameter time) = 0) ∧
    (∀ parameter,
      (∫ time in Set.Ioi (1 : Real),
        extendedDuhamelTrace nuclear parameter time) = 0)) ∧
    (∀ parameter, HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
          ((constantRelativeHeatMellinZetaFamily continuation).finitePartFamily.finitePart
            current))
      0 parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          (constantRelativeHeatMellinZetaFamily continuation).toZetaFamily
          parameter = 0) ∧
    ((∀ spectral : Complex,
      continuation.convergenceAbscissa < spectral.re →
        continuation.zeta spectral =
          relativeHeatMellinZetaCandidate
            (dimensionlessReducedSphereHeatTrace sphereData) spectral) ∧
      relativeHeatMellinZetaDeterminant continuation ≠ 0 ∧
      ‖relativeHeatMellinZetaDeterminant continuation‖ =
        relativeHeatFinitePartDeterminant
          (reducedSphereMellinFinitePartData sphereData)) := by
  refine ⟨product_throat_sphere_isospectral_duhamel_vanishing_gate
      sphereData nuclear data, ?_,
    constantRelativeHeatMellinZetaFamily_connection_eq_zero continuation, ?_⟩
  · exact (constantRelativeHeatMellinZetaFamily continuation).finitePartFamily.hasDerivAt_logDeterminant
  · exact relative_heat_mellin_zeta_continuation_gate continuation

/-- The concrete isospectral reduced-sphere assembly. -/
def toFinitePartAssembly
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (continuation : RelativeHeatMellinZetaContinuationData
      (reducedSphereMellinFinitePartData sphereData))
    (derivativeAtZero_real : continuation.derivativeAtZero.im = 0) :
    ReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssemblyData
      ReducedSphereCountertermProfile
      (constantRelativeHeatMellinZetaFamily continuation)
      nuclear 1 (Set.Ioi (1 : Real)) where
  finiteCounterterm := reducedSphereMellinFiniteCountertermVariation sphereData
  shortTime := data.toCountertermSubtractedShortTimeQuadratic
  shortTime_counterterm_eq := by
    intro parameter time
    calc
      data.toCountertermSubtractedShortTimeQuadratic.counterterm parameter time =
          counterterm (reducedSphereCountertermVariation sphereData)
            parameter time :=
        data.counterterm_eq_finiteCounterterm parameter time
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
      data
  countertermFinitePart_eq := by
    intro parameter
    change (reducedSphereMellinFinitePartData sphereData).countertermFinitePart =
      finitePartContribution
        (reducedSphereMellinFiniteCountertermVariation sphereData) parameter
    exact
      (reducedSphereMellinFiniteCountertermVariation_contribution_eq
        sphereData parameter).symm
  shortTimeContribution_eq := by
    intro parameter
    change relativeHeatShortTimeFinitePart
        (reducedSphereMellinFinitePartData sphereData) = _
    rw [reducedSphereMellinFinitePartData_shortTime_eq_raw]
    exact (data.contribution_eq parameter).symm
  longTimeContribution_eq := by
    intro parameter
    change relativeHeatLongTimeIntegral
        (reducedSphereMellinFinitePartData sphereData) = _
    rw [reducedSphereMellinFinitePartData_longTime_eq_raw]
    exact
      (P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D.ProductThroatSphereNuclearShortTimeQuadraticData.contribution_eq
        data parameter).symm
  logarithmicTrace := fun _ => 0
  duhamel_integral_identity := by
    intro parameter
    rw [reducedSphereMellinFiniteCountertermVariation_derivative_eq_zero,
      shortTimeDuhamelIntegral_eq_zero data,
      longTimeDuhamelIntegral_eq_zero data]
    ring
  zetaPrimeAtZero_real := by
    intro parameter
    exact derivativeAtZero_real

/-- Public terminal isospectral reduced-sphere checkpoint. -/
theorem product_throat_sphere_isospectral_mellin_zeta_duhamel_assembly_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (continuation : RelativeHeatMellinZetaContinuationData
      (reducedSphereMellinFinitePartData sphereData))
    (derivativeAtZero_real : continuation.derivativeAtZero.im = 0) :
    let family := constantRelativeHeatMellinZetaFamily continuation
    let assembly := toFinitePartAssembly sphereData nuclear data continuation
      derivativeAtZero_real
    (∀ parameter, HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart current))
      0 parameter) ∧
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter = 0) ∧
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
  let assembly := toFinitePartAssembly sphereData nuclear data continuation
    derivativeAtZero_real
  refine ⟨assembly.hasDerivAt_finitePartLog,
    fun _ => rfl,
    assembly.namedLogDerivative_eq_duhamel,
    constantRelativeHeatMellinZetaFamily_connection_eq_zero continuation, ?_⟩
  intro parameter
  rw [norm_relativeHeatMellinZetaFamilyDeterminant]
  rfl

end
end P0EFTJanusProgramPProductThroatSphereIsospectralMellinZetaDuhamelAssembly4D
end JanusFormal
