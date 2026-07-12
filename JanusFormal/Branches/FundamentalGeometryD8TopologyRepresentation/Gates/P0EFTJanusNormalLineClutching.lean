import Mathlib

namespace JanusFormal
namespace P0EFTJanusNormalLineClutching

set_option autoImplicit false

open Set

/-- Positive period of the compact Janus throat direction. -/
structure NormalClutchingData where
  period : ℝ
  periodPositive : 0 < period

/-- One generator of the normal-line clutching action: translate and reverse. -/
def normalDeckGenerator
    (data : NormalClutchingData)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  (point.1 + data.period, -point.2)

/-- Two circuits restore the normal sign and translate by twice the period. -/
theorem normal_deck_generator_square
    (data : NormalClutchingData)
    (point : ℝ × ℝ) :
    normalDeckGenerator data (normalDeckGenerator data point) =
      (point.1 + 2 * data.period, point.2) := by
  rcases point with ⟨u, normal⟩
  simp [normalDeckGenerator]
  ring

/-- Universal-cover presentation of a section of the sign-clutched normal line. -/
structure NormalLiftedSection
    (data : NormalClutchingData) where
  toFun : ℝ → ℝ
  continuous_toFun : Continuous toFun
  oneLoopBoundary :
    ∀ u : ℝ,
      toFun (u + data.period) = -toFun u

/-- One circuit gives the anti-periodic real normal boundary condition. -/
theorem normal_section_one_loop
    (data : NormalClutchingData)
    (lifted : NormalLiftedSection data)
    (u : ℝ) :
    lifted.toFun (u + data.period) = -lifted.toFun u :=
  lifted.oneLoopBoundary u

/-- Two circuits restore the normal direction. -/
theorem normal_section_two_loops
    (data : NormalClutchingData)
    (lifted : NormalLiftedSection data)
    (u : ℝ) :
    lifted.toFun (u + 2 * data.period) = lifted.toFun u := by
  have hArgument :
      u + 2 * data.period =
        (u + data.period) + data.period := by
    ring
  rw [hArgument,
    normal_section_one_loop data lifted (u + data.period),
    normal_section_one_loop data lifted u]
  ring

/-- A continuous anti-periodic real function vanishes on one fundamental interval. -/
theorem continuous_antiperiodic_has_zero
    (data : NormalClutchingData)
    (f : ℝ → ℝ)
    (hContinuous : Continuous f)
    (hAntiperiodic :
      ∀ u : ℝ, f (u + data.period) = -f u) :
    ∃ c ∈ Icc 0 data.period, f c = 0 := by
  by_cases hAtZero : f 0 = 0
  · exact ⟨0, ⟨le_rfl, le_of_lt data.periodPositive⟩, hAtZero⟩
  have hEndpoint : f data.period = -f 0 := by
    simpa using hAntiperiodic 0
  rcases lt_or_gt_of_ne hAtZero with hNegative | hPositive
  · have hEndpointPositive : 0 < f data.period := by
      rw [hEndpoint]
      linarith
    have hMembership :
        (0 : ℝ) ∈ Icc (f 0) (f data.period) := by
      exact ⟨le_of_lt hNegative, le_of_lt hEndpointPositive⟩
    rcases intermediate_value_Icc
        (le_of_lt data.periodPositive)
        hContinuous.continuousOn hMembership with
      ⟨c, hInterval, hValue⟩
    exact ⟨c, hInterval, hValue⟩
  · have hEndpointNegative : f data.period < 0 := by
      rw [hEndpoint]
      linarith
    have hMembership :
        (0 : ℝ) ∈ Icc (f data.period) (f 0) := by
      exact ⟨le_of_lt hEndpointNegative, le_of_lt hPositive⟩
    rcases intermediate_value_Icc'
        (le_of_lt data.periodPositive)
        hContinuous.continuousOn hMembership with
      ⟨c, hInterval, hValue⟩
    exact ⟨c, hInterval, hValue⟩

/-- A global frame is a continuous anti-periodic lift that never vanishes. -/
structure NormalLiftedFrame
    (data : NormalClutchingData)
    extends NormalLiftedSection data where
  nowhereZero : ∀ u : ℝ, toFun u ≠ 0

/-- No global frame exists for the sign-clutched line. -/
theorem no_normal_lifted_frame
    (data : NormalClutchingData) :
    Not (Nonempty (NormalLiftedFrame data)) := by
  rintro ⟨frame⟩
  obtain ⟨c, _hInterval, hZero⟩ :=
    continuous_antiperiodic_has_zero
      data frame.toFun frame.continuous_toFun
      frame.oneLoopBoundary
  exact frame.nowhereZero c hZero

/-- Triviality criterion in the clutching presentation. -/
def NormalClutchingTrivial
    (data : NormalClutchingData) : Prop :=
  Nonempty (NormalLiftedFrame data)

/-- The Janus normal line is nontrivial in the clutching/frame sense. -/
theorem normal_clutching_nontrivial
    (data : NormalClutchingData) :
    Not (NormalClutchingTrivial data) :=
  no_normal_lifted_frame data

/-- First Stiefel--Whitney/orientation character of the normal line. -/
def normalW1Character (winding : ℤ) : ZMod 2 :=
  winding

@[simp] theorem normal_w1_generator_nonzero :
    normalW1Character 1 = 1 := by
  native_decide

@[simp] theorem normal_w1_double_loop_zero :
    normalW1Character 2 = 0 := by
  native_decide

/-- Frame data after pullback to the doubled circle. -/
structure DoubledNormalFrame
    (data : NormalClutchingData) where
  toFun : ℝ → ℝ
  continuous_toFun : Continuous toFun
  twoPeriodBoundary :
    ∀ u : ℝ,
      toFun (u + 2 * data.period) = toFun u
  nowhereZero : ∀ u : ℝ, toFun u ≠ 0

/-- The constant frame trivializes the doubled pullback. -/
def constantDoubledNormalFrame
    (data : NormalClutchingData) : DoubledNormalFrame data where
  toFun := fun _ => 1
  continuous_toFun := continuous_const
  twoPeriodBoundary := by
    intro u
    rfl
  nowhereZero := by
    intro u
    norm_num

/-- The pullback to the orientation double cover is trivial. -/
theorem doubled_normal_pullback_trivial
    (data : NormalClutchingData) :
    Nonempty (DoubledNormalFrame data) :=
  ⟨constantDoubledNormalFrame data⟩

/-- Complete algebraic normal-line matrix. -/
theorem normal_clutching_matrix
    (data : NormalClutchingData) :
    Not (NormalClutchingTrivial data) /\
      normalW1Character 1 = 1 /\
      normalW1Character 2 = 0 /\
      Nonempty (DoubledNormalFrame data) := by
  exact ⟨normal_clutching_nontrivial data,
    normal_w1_generator_nonzero,
    normal_w1_double_loop_zero,
    doubled_normal_pullback_trivial data⟩

/--
Geometric promotion status. The clutching/frame obstruction is proved above;
registering the quotient as a Mathlib vector bundle and identifying it with the
actual differential normal bundle remain separate global constructions.
-/
structure NormalLineGeometricClosureStatus where
  equatorialThroatEmbedded : Prop
  derivativeReflectionMinusOneOnNormal : Prop
  orbitQuotientConstructed : Prop
  localTrivializationsConstructed : Prop
  mathlibVectorBundleRegistered : Prop
  clutchingModelIdentifiedWithNormalBundle : Prop
  w1ComparisonWithCohomologyProved : Prop
  orientationCoverPullbackTrivialized : Prop


def normalLineGeometricClosure
    (s : NormalLineGeometricClosureStatus) : Prop :=
  s.equatorialThroatEmbedded /\
  s.derivativeReflectionMinusOneOnNormal /\
  s.orbitQuotientConstructed /\
  s.localTrivializationsConstructed /\
  s.mathlibVectorBundleRegistered /\
  s.clutchingModelIdentifiedWithNormalBundle /\
  s.w1ComparisonWithCohomologyProved /\
  s.orientationCoverPullbackTrivialized

end P0EFTJanusNormalLineClutching
end JanusFormal
