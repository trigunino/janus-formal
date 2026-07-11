import Mathlib
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusCircleHolonomyEta

namespace JanusFormal
namespace P0EFTJanusEtaLargeGaugeAnomaly

set_option autoImplicit false

open P0EFTJanusCircleHolonomyEta

/-- A unit large-gauge shift changes eta by minus twice the Dirac index. -/
theorem eta_unit_large_gauge_shift
    (diracIndex : ℤ) (holonomy : ℝ) :
    zeroModeEta diracIndex (holonomy + 1) =
      zeroModeEta diracIndex holonomy - 2 * (diracIndex : ℝ) := by
  unfold zeroModeEta
  ring

/-- The residual sign of the exponentiated half-eta phase is the index parity. -/
def largeGaugeAnomalyParity (diracIndex : ℤ) : ZMod 2 :=
  diracIndex

/-- Primitive positive index has nontrivial large-gauge parity. -/
@[simp] theorem primitive_positive_anomaly_is_nontrivial :
    largeGaugeAnomalyParity 1 = 1 := by
  rfl

/-- Primitive negative index has the same nontrivial mod-two anomaly. -/
@[simp] theorem primitive_negative_anomaly_is_nontrivial :
    largeGaugeAnomalyParity (-1) = 1 := by
  native_decide

/-- A PT pair cancels the global mod-two anomaly. -/
theorem pt_pair_large_gauge_anomaly_cancels
    (diracIndex : ℤ) :
    largeGaugeAnomalyParity diracIndex +
      largeGaugeAnomalyParity (-diracIndex) = 0 := by
  change ((diracIndex : ZMod 2) + ((-diracIndex : ℤ) : ZMod 2)) = 0
  push_cast
  ring

/--
A single primitive fold therefore requires a half-level counterterm or a bulk
inflow phase, while the PT pair can be gauge invariant without breaking the
combined reflection symmetry.
-/
structure EtaGaugeAnomalyClosureStatus where
  etaJumpDerivedAnalytically : Prop
  exponentiatedEtaPhaseDefined : Prop
  primitiveFoldSignAnomalyDerived : Prop
  countertermQuantizationDerived : Prop
  ptPairedCancellationDerived : Prop
  bulkInflowMatched : Prop
  globalGaugeInvarianceProved : Prop


def etaGaugeAnomalyClosure
    (s : EtaGaugeAnomalyClosureStatus) : Prop :=
  s.etaJumpDerivedAnalytically /\
  s.exponentiatedEtaPhaseDefined /\
  s.primitiveFoldSignAnomalyDerived /\
  s.countertermQuantizationDerived /\
  s.ptPairedCancellationDerived /\
  s.bulkInflowMatched /\
  s.globalGaugeInvarianceProved

end P0EFTJanusEtaLargeGaugeAnomaly
end JanusFormal
