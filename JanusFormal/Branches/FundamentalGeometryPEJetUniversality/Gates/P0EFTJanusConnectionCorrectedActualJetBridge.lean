import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondFundamentalFormJet
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusActualStructuredJetExtraction

namespace JanusFormal
namespace P0EFTJanusConnectionCorrectedActualJetBridge

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusAdaptedOrthogonalSplitting
open P0EFTJanusSecondFundamentalFormJet
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusActualStructuredJetExtraction

universe u v

variable {Tangent : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Ambient]

abbrev ContinuousAmbientQuadratic :=
  Tangent →L[ℝ] Tangent →L[ℝ] Ambient

/-- A continuous realization of the pointwise connection-corrected immersion
second jet.  The normal coefficient is kept as a continuous bilinear map and
is required to agree pointwise with the orthogonal projection of
`D²i + Γᴹ(di,di) - di(ΓΣ)`.

This is the exact bridge between the algebraic `ConnectionCorrectedSecondJet`
and the continuous coefficient interface consumed by the Riesz pipeline. -/
structure ConnectionCorrectedActualJanusLocalJetData
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) where
  rawSecond : ContinuousAmbientQuadratic
    (Tangent := Tangent) (Ambient := Ambient)
  ambientConnection : ContinuousAmbientQuadratic
    (Tangent := Tangent) (Ambient := Ambient)
  sourceConnection : ContinuousTangentialQuadratic Tangent
  normalQuadratic : ContinuousSecondFundamentalForm
    (Tangent := Tangent) (Normal := NormalSpace derivative)
  connectionValue : ContinuousConnectionValue Tangent
  connectionDerivative : ContinuousConnectionDerivative Tangent
  physicalNormal : NormalSpace derivative
  normalQuadratic_apply :
    ∀ first second : Tangent,
      normalQuadratic first second =
        normalProjection derivative
          (rawSecond first second + ambientConnection first second -
            derivative (sourceConnection first second))
  rawSecond_symmetric :
    ∀ first second : Tangent,
      rawSecond first second = rawSecond second first
  ambientConnection_symmetric :
    ∀ first second : Tangent,
      ambientConnection first second = ambientConnection second first
  sourceConnection_symmetric :
    ∀ first second : Tangent,
      sourceConnection first second = sourceConnection second first

/-- Forget continuity while retaining the existing algebraic corrected jet. -/
def ConnectionCorrectedActualJanusLocalJetData.toConnectionCorrectedSecondJet
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ConnectionCorrectedActualJanusLocalJetData derivative) :
    ConnectionCorrectedSecondJet Tangent Ambient where
  rawSecond first second := data.rawSecond first second
  ambientConnection first second := data.ambientConnection first second
  sourceConnection first second := data.sourceConnection first second

@[simp]
theorem ConnectionCorrectedActualJanusLocalJetData.covariantSecondDerivative_apply
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ConnectionCorrectedActualJanusLocalJetData derivative)
    (first second : Tangent) :
    covariantSecondDerivative derivative data.toConnectionCorrectedSecondJet
        first second =
      data.rawSecond first second + data.ambientConnection first second -
        derivative (data.sourceConnection first second) := by
  rfl

theorem ConnectionCorrectedActualJanusLocalJetData.normalQuadratic_eq_secondFundamentalForm
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ConnectionCorrectedActualJanusLocalJetData derivative) :
    ∀ first second : Tangent,
      data.normalQuadratic first second =
        secondFundamentalForm derivative
          data.toConnectionCorrectedSecondJet first second := by
  intro first second
  rw [data.normalQuadratic_apply first second]
  rfl

theorem ConnectionCorrectedActualJanusLocalJetData.normalQuadratic_symmetric
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ConnectionCorrectedActualJanusLocalJetData derivative) :
    ∀ first second : Tangent,
      data.normalQuadratic first second =
        data.normalQuadratic second first := by
  intro first second
  rw [data.normalQuadratic_apply first second,
    data.normalQuadratic_apply second first]
  apply congrArg (normalProjection derivative)
  rw [data.rawSecond_symmetric first second,
    data.ambientConnection_symmetric first second,
    data.sourceConnection_symmetric first second]

/-- Package the corrected geometric jet as the actual local coefficient
interface already connected to the smooth reduced/Riesz pipeline. -/
def ConnectionCorrectedActualJanusLocalJetData.toActualJanusLocalJetData
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ConnectionCorrectedActualJanusLocalJetData derivative) :
    ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := NormalSpace derivative) where
  tangentialQuadratic := data.sourceConnection
  normalQuadratic := data.normalQuadratic
  connectionValue := data.connectionValue
  connectionDerivative := data.connectionDerivative
  physicalNormal := data.physicalNormal
  tangentialQuadratic_symmetric := data.sourceConnection_symmetric
  normalQuadratic_symmetric := data.normalQuadratic_symmetric

@[simp]
theorem ConnectionCorrectedActualJanusLocalJetData.toActual_normalQuadratic
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ConnectionCorrectedActualJanusLocalJetData derivative) :
    data.toActualJanusLocalJetData.normalQuadratic = data.normalQuadratic := by
  rfl

@[simp]
theorem ConnectionCorrectedActualJanusLocalJetData.toActual_reduced_secondFundamental
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ConnectionCorrectedActualJanusLocalJetData derivative) :
    data.toActualJanusLocalJetData.toReducedJet.1 = data.normalQuadratic := by
  rfl

@[simp]
theorem ConnectionCorrectedActualJanusLocalJetData.toActual_reduced_curvature_apply
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ConnectionCorrectedActualJanusLocalJetData derivative)
    (first second : Tangent) :
    data.toActualJanusLocalJetData.toReducedJet.2 first second =
      data.connectionDerivative first second -
        data.connectionDerivative second first := by
  simp

/-- Status ledger for the bridge.  The remaining hard boundary is a smooth
family with varying immersion derivative, hence varying normal space. -/
structure ConnectionCorrectedActualJetBridgeStatus where
  continuousCorrectedJetPackaged : Prop
  algebraicCorrectedJetRecovered : Prop
  normalProjectionIdentified : Prop
  torsionFreeSymmetryTransferred : Prop
  actualCoefficientInterfaceProduced : Prop
  reducedJetProduced : Prop
  varyingNormalBundleFamilyConstructed : Prop

def connectionCorrectedActualJetBridgeClosed
    (s : ConnectionCorrectedActualJetBridgeStatus) : Prop :=
  s.continuousCorrectedJetPackaged ∧
  s.algebraicCorrectedJetRecovered ∧
  s.normalProjectionIdentified ∧
  s.torsionFreeSymmetryTransferred ∧
  s.actualCoefficientInterfaceProduced ∧
  s.reducedJetProduced ∧
  s.varyingNormalBundleFamilyConstructed

theorem missing_varying_normal_family_blocks_bridge
    (s : ConnectionCorrectedActualJetBridgeStatus)
    (hMissing : Not s.varyingNormalBundleFamilyConstructed) :
    Not (connectionCorrectedActualJetBridgeClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end

end P0EFTJanusConnectionCorrectedActualJetBridge
end JanusFormal
