import Mathlib

namespace JanusFormal
namespace P0EFTJanusAnomalySelection

set_option autoImplicit false

/-- Minimal action data separating parity-odd anomaly from parity-even dynamics. -/
@[ext] structure AnomalyDecoratedAction where
  anomalyCoefficient : ℤ
  parityEvenCoupling : ℝ
  finiteEvenCounterterm : ℝ

/-- Anomaly-free action. -/
def AnomalyFree (action : AnomalyDecoratedAction) : Prop :=
  action.anomalyCoefficient = 0

/-- PT conjugation reverses the anomaly and preserves parity-even data. -/
def ptConjugate
    (action : AnomalyDecoratedAction) : AnomalyDecoratedAction :=
  { anomalyCoefficient := -action.anomalyCoefficient
    parityEvenCoupling := action.parityEvenCoupling
    finiteEvenCounterterm := action.finiteEvenCounterterm }

/-- Componentwise PT pair. -/
def ptPair
    (action : AnomalyDecoratedAction) : AnomalyDecoratedAction :=
  { anomalyCoefficient :=
      action.anomalyCoefficient +
        (ptConjugate action).anomalyCoefficient
    parityEvenCoupling :=
      action.parityEvenCoupling +
        (ptConjugate action).parityEvenCoupling
    finiteEvenCounterterm :=
      action.finiteEvenCounterterm +
        (ptConjugate action).finiteEvenCounterterm }

/-- PT pairing cancels the anomaly. -/
theorem pt_pair_anomaly_cancels
    (action : AnomalyDecoratedAction) :
    AnomalyFree (ptPair action) := by
  unfold AnomalyFree ptPair ptConjugate
  ring

/-- PT pairing doubles the parity-even coupling. -/
theorem pt_pair_even_coupling_doubles
    (action : AnomalyDecoratedAction) :
    (ptPair action).parityEvenCoupling =
      2 * action.parityEvenCoupling := by
  unfold ptPair ptConjugate
  ring

/-- PT pairing also doubles every finite parity-even counterterm. -/
theorem pt_pair_even_counterterm_doubles
    (action : AnomalyDecoratedAction) :
    (ptPair action).finiteEvenCounterterm =
      2 * action.finiteEvenCounterterm := by
  unfold ptPair ptConjugate
  ring

/-- Two distinct actions can both be anomaly-free. -/
theorem anomaly_cancellation_does_not_select_even_coupling :
    ∃ first second : AnomalyDecoratedAction,
      AnomalyFree first /\
      AnomalyFree second /\
      first.parityEvenCoupling ≠ second.parityEvenCoupling := by
  refine ⟨
    { anomalyCoefficient := 0
      parityEvenCoupling := 0
      finiteEvenCounterterm := 0 },
    { anomalyCoefficient := 0
      parityEvenCoupling := 1
      finiteEvenCounterterm := 0 },
    rfl, rfl, by norm_num⟩

/-- Finite parity-even counterterms preserve anomaly cancellation. -/
def addEvenCounterterm
    (action : AnomalyDecoratedAction)
    (counterterm : ℝ) : AnomalyDecoratedAction :=
  { anomalyCoefficient := action.anomalyCoefficient
    parityEvenCoupling := action.parityEvenCoupling
    finiteEvenCounterterm :=
      action.finiteEvenCounterterm + counterterm }

/-- Adding an even counterterm leaves the anomaly unchanged. -/
theorem add_even_counterterm_preserves_anomaly
    (action : AnomalyDecoratedAction)
    (counterterm : ℝ)
    (hFree : AnomalyFree action) :
    AnomalyFree (addEvenCounterterm action counterterm) := by
  exact hFree

/-- Anomaly phase of a determinant line, in fourth-root notation. -/
structure DeterminantPhaseLine where
  holonomy : ZMod 4

/-- Flat/anomaly-cancelled phase line. -/
def PhaseAnomalyCancelled
    (line : DeterminantPhaseLine) : Prop :=
  line.holonomy = 0

/-- Constant phase choice used to trivialize a flat line. -/
abbrev ConstantTrivializationPhase := ZMod 4

/-- A flat line still admits at least two distinct constant trivialization phases. -/
theorem anomaly_free_line_has_nonunique_constant_trivialization
    (line : DeterminantPhaseLine)
    (_hCancelled : PhaseAnomalyCancelled line) :
    ∃ first second : ConstantTrivializationPhase,
      first ≠ second := by
  exact ⟨0, 2, by native_decide⟩

/-- Doubled parity level for one regulated fold. -/
def doubledParityLevel
    (bareLevel multiplicity : ℤ) : ℤ :=
  2 * bareLevel + multiplicity

/-- With bare level `-2`, the minimal positive half-level condition selects multiplicity five. -/
theorem bare_minus_two_minimal_half_level_forces_five
    (multiplicity : ℤ)
    (hMinimal : doubledParityLevel (-2) multiplicity = 1) :
    multiplicity = 5 := by
  unfold doubledParityLevel at hMinimal
  linarith

/-- PT-conjugate folds at multiplicity five carry opposite half-levels. -/
theorem five_mode_pt_anomaly_matrix :
    doubledParityLevel (-2) 5 = 1 /\
      -doubledParityLevel (-2) 5 = -1 /\
      doubledParityLevel (-2) 5 +
        (-doubledParityLevel (-2) 5) = 0 := by
  norm_num [doubledParityLevel]

/--
P-B can select discrete field-content arithmetic only after the regulator/bare
level and a minimality condition are fixed.  It still does not select the
parity-even Hessian, determinant sign, finite counterterms or action
normalization.
-/
structure AnomalySelectionPhysicalStatus where
  determinantLineConstructed : Prop
  localAnomalyPolynomialComputed : Prop
  globalHolonomyComputed : Prop
  ptPairingDerived : Prop
  anomalyCancellationProved : Prop
  regulatorLevelDerivedMicroscopically : Prop
  discreteMultiplicitySelected : Prop
  trivializationOrPartitionSectionSelected : Prop
  parityEvenCouplingsDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop


def anomalySelectionPhysicalClosure
    (s : AnomalySelectionPhysicalStatus) : Prop :=
  s.determinantLineConstructed /\
  s.localAnomalyPolynomialComputed /\
  s.globalHolonomyComputed /\
  s.ptPairingDerived /\
  s.anomalyCancellationProved /\
  s.regulatorLevelDerivedMicroscopically /\
  s.discreteMultiplicitySelected /\
  s.trivializationOrPartitionSectionSelected /\
  s.parityEvenCouplingsDerived /\
  s.finiteCountertermsFixedMicroscopically

/-- Missing parity-even dynamics blocks a full action even after anomaly cancellation. -/
theorem anomaly_free_without_even_couplings_is_not_physical_closure
    (s : AnomalySelectionPhysicalStatus)
    (hMissing : Not s.parityEvenCouplingsDerived) :
    Not (anomalySelectionPhysicalClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end P0EFTJanusAnomalySelection
end JanusFormal
