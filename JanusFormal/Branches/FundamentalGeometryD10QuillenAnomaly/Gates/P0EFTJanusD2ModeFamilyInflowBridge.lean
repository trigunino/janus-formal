import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusGlobalSeparatedDiracModel
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusAnomalyTransgressionInflow

namespace JanusFormal
namespace P0EFTJanusD2ModeFamilyInflowBridge

set_option autoImplicit false

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusAnomalyTransgressionInflow

/-- Additive anomaly phase carried by the normal-root part of a D2 mode. -/
def modeAnomalyPhase (mode : ProductDiracMode) : ZMod 4 :=
  normalRootPhase mode.rootChoice

theorem pt_mode_anomaly_phases_cancel (mode : ProductDiracMode) :
    modeAnomalyPhase mode + modeAnomalyPhase (ptMode mode) = 0 := by
  cases mode with
  | mk level circle choice =>
      cases choice <;>
        simp [modeAnomalyPhase, ptMode, normalRootPhase, oppositeRoot] <;>
        native_decide

/-- Relative anomaly class of one explicit D2 boundary mode with opposite inflow. -/
def modeRelativeAnomaly (mode : ProductDiracMode) :
    RelativeAnomalyClass (ZMod 4) :=
  oppositeInflow (modeAnomalyPhase mode)

@[simp] theorem d2_mode_opposite_inflow_cancels (mode : ProductDiracMode) :
    anomalyCancelled (modeRelativeAnomaly mode) := by
  exact opposite_inflow_cancels _

structure D2ModeFamilyAnomalyStatus where
  globalSeparatedModeFamilyConstructed : Prop
  ptActionOnModesConstructed : Prop
  ptSquaredSpectrumInvarianceProved : Prop
  modeAnomalyPhaseIdentified : Prop
  ptPhaseCancellationProved : Prop
  bulkClassConstructed : Prop
  boundaryBulkTransgressionMatched : Prop
  etaHolonomyRepresentativeMatched : Prop

def d2ModeFamilyAnomalyClosed (s : D2ModeFamilyAnomalyStatus) : Prop :=
  s.globalSeparatedModeFamilyConstructed ∧ s.ptActionOnModesConstructed ∧
  s.ptSquaredSpectrumInvarianceProved ∧ s.modeAnomalyPhaseIdentified ∧
  s.ptPhaseCancellationProved ∧ s.bulkClassConstructed ∧
  s.boundaryBulkTransgressionMatched ∧ s.etaHolonomyRepresentativeMatched

end P0EFTJanusD2ModeFamilyInflowBridge
end JanusFormal
