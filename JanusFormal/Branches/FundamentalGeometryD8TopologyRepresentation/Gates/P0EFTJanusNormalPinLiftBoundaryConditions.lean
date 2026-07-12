import Mathlib
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalLineClutching
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusNormalOrientationZ4Lift

namespace JanusFormal
namespace P0EFTJanusNormalPinLiftBoundaryConditions

set_option autoImplicit false

open P0EFTJanusNormalLineClutching
open P0EFTJanusNormalOrientationZ4Lift

/-- The two complex square roots of the real normal transition `-1`. -/
inductive NormalRootChoice where
  | positiveQuarter
  | negativeQuarter
  deriving DecidableEq, Repr

/-- Complex multiplier carried by one loop around the throat circle. -/
def normalRootMultiplier : NormalRootChoice → ℂ
  | NormalRootChoice.positiveQuarter => Complex.I
  | NormalRootChoice.negativeQuarter => -Complex.I

/-- Additive `ZMod 4` code of the same root. -/
def normalRootPhase : NormalRootChoice → ZMod 4
  | NormalRootChoice.positiveQuarter => 1
  | NormalRootChoice.negativeQuarter => 3

/-- PT/conjugation exchanges the two roots. -/
def oppositeRoot : NormalRootChoice → NormalRootChoice
  | NormalRootChoice.positiveQuarter => NormalRootChoice.negativeQuarter
  | NormalRootChoice.negativeQuarter => NormalRootChoice.positiveQuarter

@[simp] theorem opposite_root_involutive
    (choice : NormalRootChoice) :
    oppositeRoot (oppositeRoot choice) = choice := by
  cases choice <;> rfl

/-- Each complex multiplier squares to the normal sign. -/
theorem normal_root_multiplier_square
    (choice : NormalRootChoice) :
    normalRootMultiplier choice * normalRootMultiplier choice = -1 := by
  cases choice <;>
    simp [normalRootMultiplier, Complex.I_mul_I]

/-- Four applications of either multiplier give the identity. -/
theorem normal_root_multiplier_fourth
    (choice : NormalRootChoice) :
    normalRootMultiplier choice * normalRootMultiplier choice *
        normalRootMultiplier choice * normalRootMultiplier choice = 1 := by
  calc
    normalRootMultiplier choice * normalRootMultiplier choice *
          normalRootMultiplier choice * normalRootMultiplier choice =
      (normalRootMultiplier choice * normalRootMultiplier choice) *
        (normalRootMultiplier choice * normalRootMultiplier choice) := by ring
    _ = (-1 : ℂ) * (-1 : ℂ) := by
      rw [normal_root_multiplier_square]
    _ = 1 := by ring

/-- The two roots are complex conjugates/opposites. -/
theorem opposite_root_multiplier
    (choice : NormalRootChoice) :
    normalRootMultiplier (oppositeRoot choice) =
      -normalRootMultiplier choice := by
  cases choice <;> simp [normalRootMultiplier, oppositeRoot]

/-- The additive phase is exactly one of the two normal square roots. -/
theorem normal_root_phase_is_square_root
    (choice : NormalRootChoice) :
    IsNormalSquareRoot (normalRootPhase choice) := by
  cases choice <;> native_decide

/-- Conversely, every additive normal square root is represented by one choice. -/
theorem every_normal_square_root_has_choice
    (phase : ZMod 4)
    (hRoot : IsNormalSquareRoot phase) :
    ∃ choice : NormalRootChoice,
      normalRootPhase choice = phase := by
  have hClassification :=
    (normal_square_root_iff_one_or_three phase).mp hRoot
  rcases hClassification with rfl | rfl
  · exact ⟨NormalRootChoice.positiveQuarter, rfl⟩
  · exact ⟨NormalRootChoice.negativeQuarter, rfl⟩

/-- A lifted spinor/Pinor section on the universal cover. -/
structure NormalRootLiftedSection
    (data : NormalClutchingData) where
  choice : NormalRootChoice
  toFun : ℝ → ℂ
  continuous_toFun : Continuous toFun
  oneLoopBoundary :
    ∀ u : ℝ,
      toFun (u + data.period) =
        normalRootMultiplier choice * toFun u

/-- Two loops give the antiperiodic/central-sign boundary condition. -/
theorem normal_root_lifted_two_loops
    (data : NormalClutchingData)
    (lifted : NormalRootLiftedSection data)
    (u : ℝ) :
    lifted.toFun (u + 2 * data.period) = -lifted.toFun u := by
  have hArgument :
      u + 2 * data.period =
        (u + data.period) + data.period := by ring
  rw [hArgument,
    lifted.oneLoopBoundary (u + data.period),
    lifted.oneLoopBoundary u]
  calc
    normalRootMultiplier lifted.choice *
        (normalRootMultiplier lifted.choice * lifted.toFun u) =
      (normalRootMultiplier lifted.choice *
          normalRootMultiplier lifted.choice) * lifted.toFun u := by ring
    _ = (-1 : ℂ) * lifted.toFun u := by
      rw [normal_root_multiplier_square]
    _ = -lifted.toFun u := by ring

/-- Four loops restore periodicity. -/
theorem normal_root_lifted_four_loops
    (data : NormalClutchingData)
    (lifted : NormalRootLiftedSection data)
    (u : ℝ) :
    lifted.toFun (u + 4 * data.period) = lifted.toFun u := by
  have hArgument :
      u + 4 * data.period =
        (u + 2 * data.period) + 2 * data.period := by ring
  rw [hArgument,
    normal_root_lifted_two_loops data lifted (u + 2 * data.period),
    normal_root_lifted_two_loops data lifted u]
  simp

/-- Integer numerator of the shifted Fourier/Kaluza--Klein modes. -/
def normalRootModeNumerator
    (choice : NormalRootChoice)
    (mode : ℤ) : ℤ :=
  match choice with
  | NormalRootChoice.positiveQuarter => 4 * mode + 1
  | NormalRootChoice.negativeQuarter => 4 * mode - 1

/-- The mode numerator realizes the same `ZMod 4` phase. -/
theorem normal_root_mode_phase
    (choice : NormalRootChoice)
    (mode : ℤ) :
    (normalRootModeNumerator choice mode : ZMod 4) =
      normalRootPhase choice := by
  cases choice
  · change ((4 * mode + 1 : ℤ) : ZMod 4) = 1
    push_cast
    have hFour : (4 : ZMod 4) = 0 := by norm_num
    rw [hFour, zero_mul, zero_add]
  · change ((4 * mode - 1 : ℤ) : ZMod 4) = 3
    push_cast
    have hFour : (4 : ZMod 4) = 0 := by norm_num
    rw [hFour, zero_mul, zero_sub]
    native_decide

/-- Quarter-twisted sectors have no zero momentum numerator. -/
theorem normal_root_mode_numerator_nonzero
    (choice : NormalRootChoice)
    (mode : ℤ) :
    normalRootModeNumerator choice mode ≠ 0 := by
  cases choice
  · intro hZero
    change 4 * mode + 1 = 0 at hZero
    omega
  · intro hZero
    change 4 * mode - 1 = 0 at hZero
    omega

/-- PT maps the positive-quarter mode tower to the negative-quarter tower. -/
theorem pt_pairs_mode_numerators
    (mode : ℤ) :
    normalRootModeNumerator
        NormalRootChoice.negativeQuarter (-mode) =
      -normalRootModeNumerator
        NormalRootChoice.positiveQuarter mode := by
  unfold normalRootModeNumerator
  ring

/-- Momentum formula generated by the boundary condition. -/
noncomputable def normalRootMomentum
    (data : NormalClutchingData)
    (choice : NormalRootChoice)
    (mode : ℤ) : ℝ :=
  Real.pi * (normalRootModeNumerator choice mode : ℝ) /
    (2 * data.period)

/-- Positive-quarter momenta are `2*pi*(m+1/4)/T`. -/
theorem positive_quarter_momentum_formula
    (data : NormalClutchingData)
    (mode : ℤ) :
    normalRootMomentum data
        NormalRootChoice.positiveQuarter mode =
      2 * Real.pi * ((mode : ℝ) + 1 / 4) /
        data.period := by
  have hPeriod : data.period ≠ 0 :=
    ne_of_gt data.periodPositive
  unfold normalRootMomentum normalRootModeNumerator
  push_cast
  field_simp [hPeriod]
  ring

/-- Negative-quarter momenta are `2*pi*(m-1/4)/T`. -/
theorem negative_quarter_momentum_formula
    (data : NormalClutchingData)
    (mode : ℤ) :
    normalRootMomentum data
        NormalRootChoice.negativeQuarter mode =
      2 * Real.pi * ((mode : ℝ) - 1 / 4) /
        data.period := by
  have hPeriod : data.period ≠ 0 :=
    ne_of_gt data.periodPositive
  unfold normalRootMomentum normalRootModeNumerator
  push_cast
  field_simp [hPeriod]
  ring

/-- Full algebraic consequence of a normal-line square root. -/
theorem normal_root_boundary_condition_matrix
    (data : NormalClutchingData)
    (lifted : NormalRootLiftedSection data)
    (u : ℝ) :
    normalRootMultiplier lifted.choice *
        normalRootMultiplier lifted.choice = -1 /\
    lifted.toFun (u + 2 * data.period) = -lifted.toFun u /\
    lifted.toFun (u + 4 * data.period) = lifted.toFun u := by
  exact ⟨normal_root_multiplier_square lifted.choice,
    normal_root_lifted_two_loops data lifted u,
    normal_root_lifted_four_loops data lifted u⟩

/--
Physical promotion status. The clutching line fixes the orientation sign and a
square-root lift fixes the quarter boundary conditions automatically. What is
not automatic is the existence/choice of an ambient Pin structure or which
physical field bundle carries the square-root local system.
-/
structure NormalPinLiftPhysicalStatus where
  ambientPinBundleConstructed : Prop
  restrictionToThroatConstructed : Prop
  normalClutchingLineIdentified : Prop
  complexSquareRootLineConstructed : Prop
  squareRootTensorSquareIdentifiedWithNormalComplexification : Prop
  pinReflectionSquareComputed : Prop
  positiveAndNegativeRootsClassified : Prop
  ptExchangeOfRootsDerived : Prop
  liftedFieldBundleConstructed : Prop
  quarterBoundaryConditionsDerived : Prop
  shiftedMomentumSpectrumDerived : Prop
  rootChoiceOrPTPairSelected : Prop


def normalPinLiftPhysicalClosure
    (s : NormalPinLiftPhysicalStatus) : Prop :=
  s.ambientPinBundleConstructed /\
  s.restrictionToThroatConstructed /\
  s.normalClutchingLineIdentified /\
  s.complexSquareRootLineConstructed /\
  s.squareRootTensorSquareIdentifiedWithNormalComplexification /\
  s.pinReflectionSquareComputed /\
  s.positiveAndNegativeRootsClassified /\
  s.ptExchangeOfRootsDerived /\
  s.liftedFieldBundleConstructed /\
  s.quarterBoundaryConditionsDerived /\
  s.shiftedMomentumSpectrumDerived /\
  s.rootChoiceOrPTPairSelected

end P0EFTJanusNormalPinLiftBoundaryConditions
end JanusFormal
