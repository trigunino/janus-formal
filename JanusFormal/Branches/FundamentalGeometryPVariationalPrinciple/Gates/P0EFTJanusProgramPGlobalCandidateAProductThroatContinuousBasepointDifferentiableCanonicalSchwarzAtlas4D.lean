import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAProductThroatSpectralIdentification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlas4D

/-!
# Candidate-A continuous-basepoint ProductThroat atlas

This frontend fixes every abstract product spectrum in the analytic atlas to
the D10 product spectrum already carried by the Candidate-A configuration.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAProductThroatContinuousBasepointDifferentiableCanonicalSchwarzAtlas4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAProductThroatSpectralIdentification4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlas4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Candidate-A spectral identification attached to the strongest generated
base/local analytic atlas. -/
structure GlobalCandidateAProductThroatContinuousBasepointDifferentiableCanonicalSchwarzAtlasData
    (period : Real) (hPeriod : period ≠ 0)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (CountertermIndex Chart : Type*) (fold : Fold) where
  atlas :
    ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlasData.{u, v}
      (E := E) CountertermIndex Chart fold
  spectralIdentification :
    GlobalCandidateAProductThroatSpectralIdentificationData period hPeriod
      configuration atlas.baseProductData atlas.localProductData

namespace GlobalCandidateAProductThroatContinuousBasepointDifferentiableCanonicalSchwarzAtlasData

/-- Exact heat-operator and nuclear-trace identification for the base and all
local references. -/
theorem global_candidate_A_product_throat_heat_operator_identification_gate
    {period : Real} {hPeriod : period ≠ 0}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {CountertermIndex Chart : Type*} {fold : Fold}
    (data :
      GlobalCandidateAProductThroatContinuousBasepointDifferentiableCanonicalSchwarzAtlasData
        (E := E) period hPeriod configuration CountertermIndex Chart fold) :
    (∀ parameter time,
      isometricEquivalenceConjugatedOperator
          data.atlas.base.finitePart.realHeatTraceIdentification.operatorIdentification.coordinates
          (data.atlas.baseNuclear.heatOperator parameter time) =
          productThroatHeatOperatorReal data.atlas.baseProductData time fold
            data.atlas.baseTwist ∧
      intrinsicNuclearTrace
          (data.atlas.base.finitePart.realHeatTraceIdentification.operatorIdentification.productHeatTraceClass
            parameter time) =
        data.atlas.baseNuclear.heatTrace parameter time) ∧
    (∀ chart parameter time,
      isometricEquivalenceConjugatedOperator
          (data.atlas.localAssembly chart).finitePart.realHeatTraceIdentification.operatorIdentification.coordinates
          ((data.atlas.localNuclear chart).heatOperator parameter time) =
          productThroatHeatOperatorReal (data.atlas.localProductData chart) time
            fold (data.atlas.localTwist chart) ∧
      intrinsicNuclearTrace
          ((data.atlas.localAssembly chart).finitePart.realHeatTraceIdentification.operatorIdentification.productHeatTraceClass
            parameter time) =
        (data.atlas.localNuclear chart).heatTrace parameter time) := by
  exact
    ⟨fun parameter time =>
        data.atlas.base.heat_operator_identification_gate parameter time,
      fun chart parameter time =>
        (data.atlas.localAssembly chart).heat_operator_identification_gate
          parameter time⟩

/-- Exact real trace normalization for the base and every local reference. -/
theorem global_candidate_A_product_throat_real_heat_trace_gate
    {period : Real} {hPeriod : period ≠ 0}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {CountertermIndex Chart : Type*} {fold : Fold}
    (data :
      GlobalCandidateAProductThroatContinuousBasepointDifferentiableCanonicalSchwarzAtlasData
        (E := E) period hPeriod configuration CountertermIndex Chart fold) :
    (∀ parameter time,
      data.atlas.baseNuclear.heatTrace parameter time =
        2 * productThroatNuclearHeatTrace data.atlas.baseProductData time fold
          data.atlas.baseTwist) ∧
    (∀ chart parameter time,
      (data.atlas.localNuclear chart).heatTrace parameter time =
        2 * productThroatNuclearHeatTrace
          (data.atlas.localProductData chart) time fold
            (data.atlas.localTwist chart)) :=
  ⟨data.atlas.base.finitePart.realHeatTraceIdentification.heatTrace_eq_realProductTrace,
    fun chart =>
      (data.atlas.localAssembly chart).finitePart.realHeatTraceIdentification.heatTrace_eq_realProductTrace⟩

/-- Public Candidate-A identification and analytic regularity checkpoint. -/
theorem global_candidate_A_product_throat_continuous_basepoint_differentiable_canonical_schwarz_atlas_gate
    {period : Real} {hPeriod : period ≠ 0}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {CountertermIndex Chart : Type*} {fold : Fold}
    (data :
      GlobalCandidateAProductThroatContinuousBasepointDifferentiableCanonicalSchwarzAtlasData
        (E := E) period hPeriod configuration CountertermIndex Chart fold) :
    (data.atlas.baseProductData =
      globalCandidateAProductThroatSpectralData period hPeriod configuration) ∧
    (∀ chart, data.atlas.localProductData chart =
      globalCandidateAProductThroatSpectralData period hPeriod configuration) ∧
    Differentiable Real
      (fun parameter =>
        (data.atlas.base.continuation parameter).derivativeAtZero) ∧
    (∀ chart, Differentiable Real
      (fun parameter =>
        ((data.atlas.localAssembly chart).continuation parameter).derivativeAtZero)) ∧
    (∀ parameter,
      (data.atlas.base.continuation parameter).derivativeAtZero.im = 0) ∧
    (∀ chart parameter,
      ((data.atlas.localAssembly chart).continuation parameter).derivativeAtZero.im =
        0) := by
  exact
    ⟨data.spectralIdentification.base_eq,
      data.spectralIdentification.local_eq,
      data.atlas.base.zetaPrime_differentiable,
      fun chart => (data.atlas.localAssembly chart).zetaPrime_differentiable,
      data.atlas.product_throat_reference_heat_duhamel_continuous_basepoint_differentiable_canonical_schwarz_atlas_gate.2.2.2.2.1,
      data.atlas.product_throat_reference_heat_duhamel_continuous_basepoint_differentiable_canonical_schwarz_atlas_gate.2.2.2.2.2⟩

end GlobalCandidateAProductThroatContinuousBasepointDifferentiableCanonicalSchwarzAtlasData

end
end P0EFTJanusProgramPGlobalCandidateAProductThroatContinuousBasepointDifferentiableCanonicalSchwarzAtlas4D
end JanusFormal
