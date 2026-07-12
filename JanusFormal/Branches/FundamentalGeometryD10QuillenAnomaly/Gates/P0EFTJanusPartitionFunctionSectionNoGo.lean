import Mathlib

namespace JanusFormal
namespace P0EFTJanusPartitionFunctionSectionNoGo

set_option autoImplicit false

/--
Additive logarithmic model of a section of an anomaly line/gerbe trivialization.
`sectionLog` is intrinsic only as a section; `trivializationLog` converts it to
a scalar effective action.
-/
structure TrivializedAnomalySection where
  sectionLog : ℝ
  trivializationLog : ℝ

/-- Scalar effective action in the chosen trivialization. -/
def scalarEffectiveAction
    (s : TrivializedAnomalySection) : ℝ :=
  s.sectionLog - s.trivializationLog

/-- Change of trivialization by a finite local counterterm. -/
def changeTrivialization
    (counterterm : ℝ)
    (s : TrivializedAnomalySection) : TrivializedAnomalySection :=
  { sectionLog := s.sectionLog
    trivializationLog := s.trivializationLog - counterterm }

/-- A change of trivialization shifts the scalar action by the counterterm. -/
theorem effective_action_under_trivialization_change
    (counterterm : ℝ)
    (s : TrivializedAnomalySection) :
    scalarEffectiveAction (changeTrivialization counterterm s) =
      scalarEffectiveAction s + counterterm := by
  unfold scalarEffectiveAction changeTrivialization
  ring

/-- Trivialization that realizes a chosen target scalar action. -/
def trivializationForTarget
    (sectionLog targetAction : ℝ) : TrivializedAnomalySection :=
  { sectionLog := sectionLog
    trivializationLog := sectionLog - targetAction }

/-- Every target action can be reproduced by a suitable trivialization. -/
theorem every_target_action_can_be_realized
    (sectionLog targetAction : ℝ) :
    scalarEffectiveAction
      (trivializationForTarget sectionLog targetAction) =
      targetAction := by
  unfold scalarEffectiveAction trivializationForTarget
  ring

/-- Two different scalar potentials can represent the same underlying section. -/
theorem same_section_supports_distinct_scalar_actions
    (sectionLog firstAction secondAction : ℝ)
    (hDifferent : firstAction ≠ secondAction) :
    ∃ first second : TrivializedAnomalySection,
      first.sectionLog = second.sectionLog /\
      scalarEffectiveAction first = firstAction /\
      scalarEffectiveAction second = secondAction /\
      scalarEffectiveAction first ≠
        scalarEffectiveAction second := by
  refine ⟨trivializationForTarget sectionLog firstAction,
    trivializationForTarget sectionLog secondAction,
    rfl, every_target_action_can_be_realized sectionLog firstAction,
    every_target_action_can_be_realized sectionLog secondAction, ?_⟩
  simpa [every_target_action_can_be_realized] using hDifferent

/-- Derivative bookkeeping for a modulus-dependent section and trivialization. -/
structure TrivializedSectionDerivative where
  sectionDerivative : ℝ
  trivializationDerivative : ℝ

/-- Scalar potential slope in the chosen trivialization. -/
def scalarPotentialDerivative
    (s : TrivializedSectionDerivative) : ℝ :=
  s.sectionDerivative - s.trivializationDerivative

/-- Any target slope can be fitted by the derivative of a finite trivialization. -/
def derivativeTrivializationForTarget
    (sectionDerivative targetDerivative : ℝ) :
    TrivializedSectionDerivative :=
  { sectionDerivative := sectionDerivative
    trivializationDerivative :=
      sectionDerivative - targetDerivative }

@[simp] theorem every_target_slope_can_be_realized
    (sectionDerivative targetDerivative : ℝ) :
    scalarPotentialDerivative
      (derivativeTrivializationForTarget
        sectionDerivative targetDerivative) =
      targetDerivative := by
  unfold scalarPotentialDerivative
    derivativeTrivializationForTarget
  ring

/-- A stationary point is not scheme-independent until the trivialization law is fixed. -/
theorem any_point_can_be_made_stationary_at_derivative_level
    (sectionDerivative : ℝ) :
    ∃ trivializationDerivative : ℝ,
      sectionDerivative - trivializationDerivative = 0 := by
  exact ⟨sectionDerivative, by ring⟩

/--
The partition function of an anomalous family is naturally a section, not a
number.  An anomaly cancellation/trivialization turns it into a scalar.  Finite
local counterterms are precisely changes of local trivialization, so the scalar
potential and its stationary point are not canonically fixed by the anomaly
object alone.
-/
structure ScalarPotentialPhysicalStatus where
  anomalyObjectConstructed : Prop
  partitionFunctionSectionConstructed : Prop
  gaugeEquivarianceProved : Prop
  anomalyCancellationProved : Prop
  globalTrivializationConstructed : Prop
  localityCompatibleTrivializationDerived : Prop
  finiteCountertermsClassified : Prop
  finitePartsFixedMicroscopically : Prop
  scalarEffectiveActionDefined : Prop
  stationaryPointSchemeIndependent : Prop


def scalarPotentialPhysicalClosure
    (s : ScalarPotentialPhysicalStatus) : Prop :=
  s.anomalyObjectConstructed /\
  s.partitionFunctionSectionConstructed /\
  s.gaugeEquivarianceProved /\
  s.anomalyCancellationProved /\
  s.globalTrivializationConstructed /\
  s.localityCompatibleTrivializationDerived /\
  s.finiteCountertermsClassified /\
  s.finitePartsFixedMicroscopically /\
  s.scalarEffectiveActionDefined /\
  s.stationaryPointSchemeIndependent

/-- Missing a locality-compatible trivialization blocks a canonical scalar potential. -/
theorem missing_local_trivialization_blocks_scalar_potential
    (s : ScalarPotentialPhysicalStatus)
    (hMissing : Not s.localityCompatibleTrivializationDerived) :
    Not (scalarPotentialPhysicalClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

/-- Missing finite counterterm data blocks scheme-independent stationarity. -/
theorem missing_finite_part_law_blocks_scheme_independent_vacuum
    (s : ScalarPotentialPhysicalStatus)
    (hMissing : Not s.finitePartsFixedMicroscopically) :
    Not (scalarPotentialPhysicalClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end P0EFTJanusPartitionFunctionSectionNoGo
end JanusFormal
