import Mathlib

namespace JanusFormal
namespace P0EFTJanusIntrinsicSpinVsQuarterTwist

set_option autoImplicit false

/-- Intrinsic circle spin phases: periodic or antiperiodic. -/
abbrev IntrinsicSpinPhase := ZMod 2

/-- Fourth-root phase notation used by the twisted sectors. -/
abbrev FourthRootPhase := ZMod 4

/-- Embed an intrinsic spin sign into fourth-root notation. -/
def embedSpinPhase (phase : IntrinsicSpinPhase) : FourthRootPhase :=
  2 * (phase.val : FourthRootPhase)

/-- The intrinsic spin image consists exactly of phases `0` and `2`. -/
theorem intrinsic_spin_image_iff :
    ∀ phase : FourthRootPhase,
      (∃ spin : IntrinsicSpinPhase,
        embedSpinPhase spin = phase) ↔
      phase = 0 \/ phase = 2 := by
  native_decide

/-- Periodic spin embeds as phase zero. -/
@[simp] theorem periodic_spin_phase :
    embedSpinPhase 0 = 0 := by
  native_decide

/-- Antiperiodic spin embeds as a half-turn. -/
@[simp] theorem antiperiodic_spin_phase :
    embedSpinPhase 1 = 2 := by
  native_decide

/-- A positive quarter phase is not an intrinsic spin structure. -/
theorem quarter_phase_not_intrinsic_spin :
    Not (∃ spin : IntrinsicSpinPhase,
      embedSpinPhase spin = 1) := by
  native_decide

/-- A negative quarter phase is not an intrinsic spin structure either. -/
theorem three_quarter_phase_not_intrinsic_spin :
    Not (∃ spin : IntrinsicSpinPhase,
      embedSpinPhase spin = 3) := by
  native_decide

/-- Intrinsic spin phase plus a separate flat twist. -/
def twistedCirclePhase
    (spin : IntrinsicSpinPhase)
    (flatTwist : FourthRootPhase) : FourthRootPhase :=
  embedSpinPhase spin + flatTwist

/-- Periodic spin plus a quarter flat line yields the quarter phase. -/
@[simp] theorem periodic_spin_plus_quarter_twist :
    twistedCirclePhase 0 1 = 1 := by
  native_decide

/-- Antiperiodic spin plus a quarter flat line yields the conjugate quarter phase. -/
@[simp] theorem antiperiodic_spin_plus_quarter_twist :
    twistedCirclePhase 1 1 = 3 := by
  native_decide

/--
Thus the two intrinsic spin structures on the throat circle account only for
periodic/antiperiodic signs.  The `+/- i` phases used in the Dirac-Z4 sector
must be supplied by a separate flat line—naturally a square root of the
one-sided normal orientation line if that bundle is constructed.
-/
structure IntrinsicSpinQuarterPhysicalStatus where
  throatOrientableProved : Prop
  throatSpinStructuresClassified : Prop
  twoCircleSpinStructuresDerived : Prop
  intrinsicPhasesIdentifiedWithZeroAndTwo : Prop
  normalOrInternalFlatLineConstructed : Prop
  quarterTwistDerived : Prop
  tensorProductSpinorBundleConstructed : Prop
  globalBoundaryConditionsMatched : Prop


def intrinsicSpinQuarterPhysicalClosed
    (s : IntrinsicSpinQuarterPhysicalStatus) : Prop :=
  s.throatOrientableProved /\
  s.throatSpinStructuresClassified /\
  s.twoCircleSpinStructuresDerived /\
  s.intrinsicPhasesIdentifiedWithZeroAndTwo /\
  s.normalOrInternalFlatLineConstructed /\
  s.quarterTwistDerived /\
  s.tensorProductSpinorBundleConstructed /\
  s.globalBoundaryConditionsMatched

end P0EFTJanusIntrinsicSpinVsQuarterTwist
end JanusFormal
