import Mathlib

namespace JanusFormal
namespace P0EFTJanusIndexParityAnomaly

set_option autoImplicit false

/-- Doubled induced Chern--Simons level in the unit-charge convention. -/
def doubledInducedLevel (diracIndex : ℤ) : ℤ := diracIndex

/-- PT reverses the signed Dirac index. -/
def ptIndex (diracIndex : ℤ) : ℤ := -diracIndex

@[simp] theorem pt_index_is_involutive (diracIndex : ℤ) :
    ptIndex (ptIndex diracIndex) = diracIndex := by
  simp [ptIndex]

/-- PT-paired induced levels cancel. -/
theorem pt_paired_levels_cancel (diracIndex : ℤ) :
    doubledInducedLevel diracIndex +
      doubledInducedLevel (ptIndex diracIndex) = 0 := by
  simp [doubledInducedLevel, ptIndex]

/-- Primitive positive monopole gives the doubled half-level `+1`. -/
@[simp] theorem primitive_plus_fold_level :
    doubledInducedLevel 1 = 1 := by
  rfl

/-- Primitive negative monopole gives the doubled half-level `-1`. -/
@[simp] theorem primitive_minus_fold_level :
    doubledInducedLevel (-1) = -1 := by
  rfl

/-- Each primitive fold is odd in the doubled-level convention. -/
theorem primitive_fold_levels_are_odd :
    ((doubledInducedLevel 1) % 2 = 1) /\
      ((doubledInducedLevel (-1)) % 2 = 1) := by
  norm_num [doubledInducedLevel]

/-- The two primitive folds have zero total doubled level. -/
theorem primitive_pt_pair_has_zero_total_level :
    doubledInducedLevel 1 + doubledInducedLevel (-1) = 0 := by
  norm_num [doubledInducedLevel]

/--
The primitive monopole therefore supplies one chiral zero mode and one
half-integral parity-anomaly shift per fold, while the PT pair is anomaly neutral
in total.  A complete theorem must derive the regulator choice and global Pin
eta phase, not only the doubled-level arithmetic.
-/
structure IndexAnomalyClosureStatus where
  primitiveMonopoleIndexProved : Prop
  oneChiralZeroModePerFoldProved : Prop
  fermionDeterminantRegularized : Prop
  halfLevelShiftDerived : Prop
  ptOppositeRegulatorsDerived : Prop
  pairedGaugeInvarianceProved : Prop
  pairedPTInvarianceProved : Prop
  globalEtaPhaseMatched : Prop


def indexAnomalyClosure (s : IndexAnomalyClosureStatus) : Prop :=
  s.primitiveMonopoleIndexProved /\
  s.oneChiralZeroModePerFoldProved /\
  s.fermionDeterminantRegularized /\
  s.halfLevelShiftDerived /\
  s.ptOppositeRegulatorsDerived /\
  s.pairedGaugeInvarianceProved /\
  s.pairedPTInvarianceProved /\
  s.globalEtaPhaseMatched

end P0EFTJanusIndexParityAnomaly
end JanusFormal
