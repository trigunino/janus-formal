import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusConnectionCorrectedActualJetBridge

namespace JanusFormal
namespace P0EFTJanusFixedNormalTrivializationFamily

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusAdaptedOrthogonalSplitting
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusConnectionCorrectedActualJetBridge

universe u v w x

variable {Base : Type w} {Tangent : Type u} {Ambient : Type v} {Normal : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Ambient]
variable [FiniteDimensional ℝ Normal]

/-- A family of corrected local jets whose varying normal spaces have been
identified with one fixed normal model.  Smoothness is stated only for the
transported fixed-model coefficients, which is the form needed by the existing
Riesz pipeline. -/
structure FixedNormalTrivializedActualJetFamilyData where
  derivative : Base → Tangent →ₗᵢ[ℝ] Ambient
  correctedJet :
    ∀ base, ConnectionCorrectedActualJanusLocalJetData (derivative base)
  normalTrivialization :
    ∀ base, NormalSpace (derivative base) ≃ₗᵢ[ℝ] Normal
  tangentialQuadratic : Base → ContinuousTangentialQuadratic Tangent
  normalQuadratic : Base → ContinuousSecondFundamentalForm
    (Tangent := Tangent) (Normal := Normal)
  connectionValue : Base → ContinuousConnectionValue Tangent
  connectionDerivative : Base → ContinuousConnectionDerivative Tangent
  physicalNormal : Base → Normal
  tangentialQuadratic_apply :
    ∀ base, tangentialQuadratic base = (correctedJet base).sourceConnection
  normalQuadratic_apply :
    ∀ base first second,
      normalQuadratic base first second =
        normalTrivialization base ((correctedJet base).normalQuadratic first second)
  connectionValue_apply :
    ∀ base, connectionValue base = (correctedJet base).connectionValue
  connectionDerivative_apply :
    ∀ base, connectionDerivative base = (correctedJet base).connectionDerivative
  physicalNormal_apply :
    ∀ base,
      physicalNormal base =
        normalTrivialization base ((correctedJet base).physicalNormal)
  tangentialQuadratic_contDiff : ContDiff ℝ ∞ tangentialQuadratic
  normalQuadratic_contDiff : ContDiff ℝ ∞ normalQuadratic
  connectionValue_contDiff : ContDiff ℝ ∞ connectionValue
  connectionDerivative_contDiff : ContDiff ℝ ∞ connectionDerivative
  physicalNormal_contDiff : ContDiff ℝ ∞ physicalNormal

/-- The fixed-model coefficients define the actual local Janus interface. -/
def FixedNormalTrivializedActualJetFamilyData.localJet
    (data : FixedNormalTrivializedActualJetFamilyData
      (Base := Base) (Tangent := Tangent)
      (Ambient := Ambient) (Normal := Normal))
    (base : Base) :
    ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal) where
  tangentialQuadratic := data.tangentialQuadratic base
  normalQuadratic := data.normalQuadratic base
  connectionValue := data.connectionValue base
  connectionDerivative := data.connectionDerivative base
  physicalNormal := data.physicalNormal base
  tangentialQuadratic_symmetric := by
    intro first second
    rw [data.tangentialQuadratic_apply base]
    exact (data.correctedJet base).sourceConnection_symmetric first second
  normalQuadratic_symmetric := by
    intro first second
    rw [data.normalQuadratic_apply base first second,
      data.normalQuadratic_apply base second first]
    exact congrArg (data.normalTrivialization base)
      ((data.correctedJet base).normalQuadratic_symmetric
        (data.derivative base) first second)

/-- Package the transported family into the fixed-model smooth family interface. -/
def FixedNormalTrivializedActualJetFamilyData.toActualJanusLocalJetFamilyData
    (data : FixedNormalTrivializedActualJetFamilyData
      (Base := Base) (Tangent := Tangent)
      (Ambient := Ambient) (Normal := Normal)) :
    ActualJanusLocalJetFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal) where
  localJet := data.localJet
  tangentialQuadratic_contDiff := data.tangentialQuadratic_contDiff
  normalQuadratic_contDiff := data.normalQuadratic_contDiff
  connectionValue_contDiff := data.connectionValue_contDiff
  connectionDerivative_contDiff := data.connectionDerivative_contDiff
  physicalNormal_contDiff := data.physicalNormal_contDiff

@[simp]
theorem FixedNormalTrivializedActualJetFamilyData.localJet_normalQuadratic
    (data : FixedNormalTrivializedActualJetFamilyData
      (Base := Base) (Tangent := Tangent)
      (Ambient := Ambient) (Normal := Normal))
    (base : Base) :
    (data.localJet base).normalQuadratic = data.normalQuadratic base := by
  rfl

@[simp]
theorem FixedNormalTrivializedActualJetFamilyData.localJet_physicalNormal
    (data : FixedNormalTrivializedActualJetFamilyData
      (Base := Base) (Tangent := Tangent)
      (Ambient := Ambient) (Normal := Normal))
    (base : Base) :
    (data.localJet base).physicalNormal = data.physicalNormal base := by
  rfl

theorem FixedNormalTrivializedActualJetFamilyData.reducedJet_contDiff
    (data : FixedNormalTrivializedActualJetFamilyData
      (Base := Base) (Tangent := Tangent)
      (Ambient := Ambient) (Normal := Normal)) :
    ContDiff ℝ ∞ data.toActualJanusLocalJetFamilyData.reducedJet :=
  data.toActualJanusLocalJetFamilyData.reducedJet_contDiff

/-- Pointwise compatibility with the geometric second fundamental form after
transport to the fixed normal model. -/
theorem FixedNormalTrivializedActualJetFamilyData.normalQuadratic_eq_transport_secondFundamental
    (data : FixedNormalTrivializedActualJetFamilyData
      (Base := Base) (Tangent := Tangent)
      (Ambient := Ambient) (Normal := Normal))
    (base : Base) (first second : Tangent) :
    data.normalQuadratic base first second =
      data.normalTrivialization base
        (P0EFTJanusSecondFundamentalFormJet.secondFundamentalForm
          (data.derivative base)
          (data.correctedJet base).toConnectionCorrectedSecondJet
          first second) := by
  rw [data.normalQuadratic_apply base first second]
  exact congrArg (data.normalTrivialization base)
    ((data.correctedJet base).normalQuadratic_eq_secondFundamentalForm
      (data.derivative base) first second)

/-- Status ledger for the varying-normal-space stage. -/
structure FixedNormalTrivializationFamilyStatus where
  varyingNormalSpacesIdentifiedWithFixedModel : Prop
  correctedJetsTransported : Prop
  transportedCoefficientsSmooth : Prop
  fixedModelActualJetFamilyConstructed : Prop
  reducedJetFamilySmooth : Prop
  trivializationConstructedFromProjectedSeedAtlas : Prop
  transitionCompatibilityProved : Prop

def fixedNormalTrivializationFamilyClosed
    (s : FixedNormalTrivializationFamilyStatus) : Prop :=
  s.varyingNormalSpacesIdentifiedWithFixedModel ∧
  s.correctedJetsTransported ∧
  s.transportedCoefficientsSmooth ∧
  s.fixedModelActualJetFamilyConstructed ∧
  s.reducedJetFamilySmooth ∧
  s.trivializationConstructedFromProjectedSeedAtlas ∧
  s.transitionCompatibilityProved

theorem missing_projected_seed_trivialization_blocks_closure
    (s : FixedNormalTrivializationFamilyStatus)
    (hMissing : Not s.trivializationConstructedFromProjectedSeedAtlas) :
    Not (fixedNormalTrivializationFamilyClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

end

end P0EFTJanusFixedNormalTrivializationFamily
end JanusFormal
