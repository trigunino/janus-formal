import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

/-!
# Candidate-A product-throat spectral identification

This gate identifies the product spectrum used by a reference atlas with the
D10 spectral completion already stored in the Candidate-A configuration.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAProductThroatSpectralIdentification4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The unique product-throat spectral datum already carried by a Candidate-A
configuration. -/
def globalCandidateAProductThroatSpectralData
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    ProductThroatSpectralData :=
  d10SpectralData period hPeriod configuration.physical.d10Completion

@[simp] theorem globalCandidateAProductThroatSpectralData_sphereRadius
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    (globalCandidateAProductThroatSpectralData period hPeriod configuration).sphereRadius =
      configuration.physical.d10Completion.sphereRadius :=
  rfl

@[simp] theorem globalCandidateAProductThroatSpectralData_circlePeriod
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    (globalCandidateAProductThroatSpectralData period hPeriod configuration).circlePeriod =
      |period| :=
  rfl

@[simp] theorem globalCandidateAProductThroatSpectralData_monopoleCharge
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    (globalCandidateAProductThroatSpectralData period hPeriod configuration).monopoleCharge =
      configuration.physical.d10Completion.monopoleCharge :=
  rfl

/-- Exact identification required when a base reference and its local
spectral-cut references use the Candidate-A product spectrum. -/
structure GlobalCandidateAProductThroatSpectralIdentificationData
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    {Index : Type*}
    (baseProductData : ProductThroatSpectralData)
    (localProductData : Index → ProductThroatSpectralData) : Prop where
  base_eq :
    baseProductData =
      globalCandidateAProductThroatSpectralData period hPeriod configuration
  local_eq : ∀ index,
    localProductData index =
      globalCandidateAProductThroatSpectralData period hPeriod configuration

namespace GlobalCandidateAProductThroatSpectralIdentificationData

/-- Public checkpoint exposing all geometric parameters fixed by the exact
Candidate-A identification. -/
theorem global_candidate_A_product_throat_spectral_identification_gate
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {Index : Type*}
    {baseProductData : ProductThroatSpectralData}
    {localProductData : Index → ProductThroatSpectralData}
    (identification :
      GlobalCandidateAProductThroatSpectralIdentificationData period hPeriod
        configuration baseProductData localProductData) :
    baseProductData.sphereRadius =
        configuration.physical.d10Completion.sphereRadius ∧
    baseProductData.circlePeriod = |period| ∧
    baseProductData.monopoleCharge =
        configuration.physical.d10Completion.monopoleCharge ∧
    ∀ index,
      (localProductData index).sphereRadius =
          configuration.physical.d10Completion.sphereRadius ∧
      (localProductData index).circlePeriod = |period| ∧
      (localProductData index).monopoleCharge =
        configuration.physical.d10Completion.monopoleCharge := by
  rw [identification.base_eq]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  intro index
  rw [identification.local_eq index]
  exact ⟨rfl, rfl, rfl⟩

end GlobalCandidateAProductThroatSpectralIdentificationData

end
end P0EFTJanusProgramPGlobalCandidateAProductThroatSpectralIdentification4D
end JanusFormal
