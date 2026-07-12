import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusPeriodCircleQuotient

namespace JanusFormal
namespace P0EFTJanusNormalLineClutching

set_option autoImplicit false

open Set
open P0EFTJanusPeriodCircleQuotient

/-- Sign representation of `ZMod 2` on a real line. -/
def z2Sign (phase : ZMod 2) : ℝ :=
  if phase = 0 then 1 else -1

@[simp] theorem z2_sign_zero : z2Sign 0 = 1 := by
  simp [z2Sign]

@[simp] theorem z2_sign_one : z2Sign 1 = -1 := by
  native_decide

/-- The sign representation is multiplicative with respect to addition of phases. -/
theorem z2_sign_add
    (first second : ZMod 2) :
    z2Sign (first + second) = z2Sign first * z2Sign second := by
  fin_cases first <;> fin_cases second <;>
    norm_num [z2Sign]

/-- Normal holonomy of an integer winding. -/
def normalSign (winding : ℤ) : ℝ :=
  z2Sign (winding : ZMod 2)

@[simp] theorem normal_sign_zero : normalSign 0 = 1 := by
  simp [normalSign]

@[simp] theorem normal_sign_one : normalSign 1 = -1 := by
  norm_num [normalSign]

@[simp] theorem normal_sign_two : normalSign 2 = 1 := by
  norm_num [normalSign]

/-- Normal signs multiply under concatenation of loops. -/
theorem normal_sign_add
    (first second : ℤ) :
    normalSign (first + second) =
      normalSign first * normalSign second := by
  unfold normalSign
  push_cast
  exact z2_sign_add _ _

/-- The concrete clutching datum for the Janus normal line. -/
structure NormalClutchingData where
  period : ℝ
  periodPositive : 0 < period

/-- Deck action on the universal-cover coordinates `(u,v)`. -/
def normalDeckAction
    (data : NormalClutchingData)
    (winding : ℤ)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  (point.1 + (winding : ℝ) * data.period,
    normalSign winding * point.2)

@[simp] theorem normal_deck_action_zero
    (data : NormalClutchingData)
    (point : ℝ × ℝ) :
    normalDeckAction data 0 point = point := by
  ext <;> simp [normalDeckAction]

/-- The integer deck transformations form an action. -/
theorem normal_deck_action_add
    (data : NormalClutchingData)
    (first second : ℤ)
    (point : ℝ × ℝ) :
    normalDeckAction data (first + second) point =
      normalDeckAction data first
        (normalDeckAction data second point) := by
  ext
  · simp [normalDeckAction]
    push_cast
    ring
  · simp [normalDeckAction, normal_sign_add]
    ring

/-- Orbit equivalence defining the total space of the clutching line. -/
def normalEquivalent
    (data : NormalClutchingData)
    (first second : ℝ × ℝ) : Prop :=
  ∃ winding : ℤ,
    second = normalDeckAction data winding first

/-- Orbit equivalence is reflexive. -/
theorem normal_equivalent_refl
    (data : NormalClutchingData)
    (point : ℝ × ℝ) :
    normalEquivalent data point point := by
  exact ⟨0, (normal_deck_action_zero data point).symm⟩

/-- Orbit equivalence is symmetric. -/
theorem normal_equivalent_symm
    (data : NormalClutchingData)
    {first second : ℝ × ℝ}
    (hEquivalent : normalEquivalent data first second) :
    normalEquivalent data second first := by
  rcases hEquivalent with ⟨winding, rfl⟩
  refine ⟨-winding, ?_⟩
  have hCompose := normal_deck_action_add
    data (-winding) winding first
  have hZero : (-winding) + winding = 0 := by ring
  rw [hZero, normal_deck_action_zero] at hCompose
  exact hCompose.symm

/-- Orbit equivalence is transitive. -/
theorem normal_equivalent_trans
    (data : NormalClutchingData)
    {first second third : ℝ × ℝ}
    (hFirst : normalEquivalent data first second)
    (hSecond : normalEquivalent data second third) :
    normalEquivalent data first third := by
  rcases hFirst with ⟨firstWinding, rfl⟩
  rcases hSecond with ⟨secondWinding, rfl⟩
  refine ⟨secondWinding + firstWinding, ?_⟩
  exact (normal_deck_action_add
    data secondWinding firstWinding first).symm

/-- Setoid for the total-space quotient. -/
def normalSetoid
    (data : NormalClutchingData) : Setoid (ℝ × ℝ) where
  r := normalEquivalent data
  iseqv :=
    { refl := normal_equivalent_refl data
      symm := normal_equivalent_symm data
      trans := normal_equivalent_trans data }

/-- Algebraic total space of the Janus normal line. -/
abbrev NormalLineTotalSpace
    (data : NormalClutchingData) :=
  Quotient (normalSetoid data)

/-- Class of a universal-cover normal vector. -/
def normalClass
    (data : NormalClutchingData)
    (u normal : ℝ) : NormalLineTotalSpace data :=
  Quotient.mk (normalSetoid data) (u, normal)

/-- Projection from the clutching total space to the period circle. -/
def normalProjection
    (data : NormalClutchingData) :
    NormalLineTotalSpace data → PeriodCircle data.period :=
  Quotient.lift
    (fun point => periodClass data.period point.1)
    (by
      intro first second hEquivalent
      rcases hEquivalent with ⟨winding, rfl⟩
      change
        periodClass data.period
            (first.1 + (winding : ℝ) * data.period) =
          periodClass data.period first.1
      exact
        (period_class_add_integer_period
          data.period first.1 winding).symm)

/-- The zero vector is compatible with the sign gluing. -/
def normalZeroSection
    (data : NormalClutchingData) :
    PeriodCircle data.period → NormalLineTotalSpace data :=
  Quotient.lift
    (fun u => normalClass data u 0)
    (by
      intro first second hEquivalent
      apply Quotient.sound
      rcases hEquivalent with ⟨winding, hSecond⟩
      subst second
      refine ⟨winding, ?_⟩
      ext <;> simp [normalDeckAction, normalClass])

/-- The algebraic zero section projects to the identity. -/
theorem normal_projection_zero_section
    (data : NormalClutchingData)
    (basePoint : PeriodCircle data.period) :
    normalProjection data (normalZeroSection data basePoint) = basePoint := by
  refine Quotient.inductionOn basePoint ?_
  intro u
  rfl

/-- Universal-cover presentation of a section of the clutching line. -/
structure NormalLiftedSection
    (data : NormalClutchingData) where
  toFun : ℝ → ℝ
  continuous_toFun : Continuous toFun
  equivariant :
    ∀ winding : ℤ, ∀ u : ℝ,
      toFun (u + (winding : ℝ) * data.period) =
        normalSign winding * toFun u

/-- A lifted section descends to the algebraic quotient. -/
def normalSection
    (data : NormalClutchingData)
    (section : NormalLiftedSection data) :
    PeriodCircle data.period → NormalLineTotalSpace data :=
  Quotient.lift
    (fun u => normalClass data u (section.toFun u))
    (by
      intro first second hEquivalent
      apply Quotient.sound
      rcases hEquivalent with ⟨winding, hSecond⟩
      subst second
      refine ⟨winding, ?_⟩
      ext
      · simp [normalDeckAction, normalClass]
      · simpa [normalDeckAction, normalClass] using
          (section.equivariant winding first).symm)

/-- Every descended lifted section is a right inverse of the projection. -/
theorem normal_projection_section
    (data : NormalClutchingData)
    (section : NormalLiftedSection data)
    (basePoint : PeriodCircle data.period) :
    normalProjection data (normalSection data section basePoint) = basePoint := by
  refine Quotient.inductionOn basePoint ?_
  intro u
  rfl

/-- One circuit makes every lifted normal section anti-periodic. -/
theorem normal_section_one_loop
    (data : NormalClutchingData)
    (section : NormalLiftedSection data)
    (u : ℝ) :
    section.toFun (u + data.period) = -section.toFun u := by
  simpa using section.equivariant 1 u

/-- Two circuits restore the normal direction. -/
theorem normal_section_two_loops
    (data : NormalClutchingData)
    (section : NormalLiftedSection data)
    (u : ℝ) :
    section.toFun (u + 2 * data.period) = section.toFun u := by
  have hArgument :
      u + 2 * data.period =
        (u + data.period) + data.period := by ring
  rw [hArgument,
    normal_section_one_loop data section (u + data.period),
    normal_section_one_loop data section u]
  ring

/-- A continuous anti-periodic real function has a zero on one fundamental interval. -/
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

/-- A global frame is a continuous equivariant lift that never vanishes. -/
structure NormalLiftedFrame
    (data : NormalClutchingData)
    extends NormalLiftedSection data where
  nowhereZero : ∀ u : ℝ, toFun u ≠ 0

/-- The Janus normal clutching line has no global frame. -/
theorem no_normal_lifted_frame
    (data : NormalClutchingData) :
    Not (Nonempty (NormalLiftedFrame data)) := by
  rintro ⟨frame⟩
  obtain ⟨c, _hInterval, hZero⟩ :=
    continuous_antiperiodic_has_zero
      data frame.toFun frame.continuous_toFun
      (normal_section_one_loop data frame.toNormalLiftedSection)
  exact frame.nowhereZero c hZero

/-- Triviality criterion for this rank-one clutching presentation. -/
def NormalClutchingTrivial
    (data : NormalClutchingData) : Prop :=
  Nonempty (NormalLiftedFrame data)

/-- The normal line is nontrivial in the clutching/frame sense. -/
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

/-- A frame on the pulled-back line over the doubled circle. -/
structure DoubledNormalFrame
    (data : NormalClutchingData) where
  toFun : ℝ → ℝ
  continuous_toFun : Continuous toFun
  twoPeriodEquivariant :
    ∀ winding : ℤ, ∀ u : ℝ,
      toFun (u + (winding : ℝ) * (2 * data.period)) = toFun u
  nowhereZero : ∀ u : ℝ, toFun u ≠ 0

/-- The constant frame trivializes the pullback to the orientation double cover. -/
def constantDoubledNormalFrame
    (data : NormalClutchingData) : DoubledNormalFrame data where
  toFun := fun _ => 1
  continuous_toFun := continuous_const
  twoPeriodEquivariant := by
    intro winding u
    rfl
  nowhereZero := by
    intro u
    norm_num

/-- The doubled pullback is trivial in the same frame sense. -/
theorem doubled_normal_pullback_trivial
    (data : NormalClutchingData) :
    Nonempty (DoubledNormalFrame data) :=
  ⟨constantDoubledNormalFrame data⟩

/--
Geometric promotion status: the quotient and frame obstruction are explicit.
The remaining library-level task is to equip the quotient with local
trivializations and register the resulting object as a Mathlib `VectorBundle`.
-/
structure NormalLineGeometricClosureStatus where
  equatorialThroatEmbedded : Prop
  derivativeReflectionMinusOneOnNormal : Prop
  orbitQuotientHomeomorphismConstructed : Prop
  localTrivializationsConstructed : Prop
  mathlibVectorBundleRegistered : Prop
  clutchingModelIdentifiedWithNormalBundle : Prop
  w1ComparisonWithSingularCohomologyProved : Prop
  orientationCoverPullbackTrivialized : Prop


def normalLineGeometricClosure
    (s : NormalLineGeometricClosureStatus) : Prop :=
  s.equatorialThroatEmbedded /\
  s.derivativeReflectionMinusOneOnNormal /\
  s.orbitQuotientHomeomorphismConstructed /\
  s.localTrivializationsConstructed /\
  s.mathlibVectorBundleRegistered /\
  s.clutchingModelIdentifiedWithNormalBundle /\
  s.w1ComparisonWithSingularCohomologyProved /\
  s.orientationCoverPullbackTrivialized

end P0EFTJanusNormalLineClutching
end JanusFormal
