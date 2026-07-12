import Mathlib

namespace JanusFormal
namespace P0EFTJanusQuillenFamilyCanonicity

set_option autoImplicit false

/-- Data needed before a family of elliptic operators has a Quillen/Bismut-Freed package. -/
structure EllipticFamilyInputStatus where
  parameterSpaceOrStackConstructed : Prop
  universalFamilyConstructed : Prop
  smoothFiberMetricsChosen : Prop
  bundleMetricsChosen : Prop
  compatibleConnectionsChosen : Prop
  familyOperatorConstructed : Prop
  ellipticityProved : Prop
  fredholmDomainsConstructed : Prop
  smoothFamilyDependenceProved : Prop

/-- The family itself is not determined by the abstract moduli stack. -/
def ellipticFamilyInputClosed
    (s : EllipticFamilyInputStatus) : Prop :=
  s.parameterSpaceOrStackConstructed /\
  s.universalFamilyConstructed /\
  s.smoothFiberMetricsChosen /\
  s.bundleMetricsChosen /\
  s.compatibleConnectionsChosen /\
  s.familyOperatorConstructed /\
  s.ellipticityProved /\
  s.fredholmDomainsConstructed /\
  s.smoothFamilyDependenceProved

/-- Geometric structures on a determinant line after the Fredholm family is fixed. -/
structure QuillenBismutFreedStatus where
  determinantLineConstructed : Prop
  quillenMetricConstructed : Prop
  bismutFreedConnectionConstructed : Prop
  localFamiliesIndexCurvatureProved : Prop
  holonomyFormulaProved : Prop
  gaugeEquivariantDescentProved : Prop


def quillenBismutFreedClosed
    (s : QuillenBismutFreedStatus) : Prop :=
  s.determinantLineConstructed /\
  s.quillenMetricConstructed /\
  s.bismutFreedConnectionConstructed /\
  s.localFamiliesIndexCurvatureProved /\
  s.holonomyFormulaProved /\
  s.gaugeEquivariantDescentProved

/-- Overall normalization and finite local terms remain external to the bare line bundle. -/
structure RenormalizedSectionChoices where
  actionNormalization : ℝ
  finiteLocalCounterterm : ℝ
  referenceScaleLog : ℝ

/-- Additive logarithmic renormalized action model. -/
def renormalizedActionValue
    (bareSectionLog : ℝ)
    (choices : RenormalizedSectionChoices) : ℝ :=
  choices.actionNormalization * bareSectionLog +
    choices.finiteLocalCounterterm +
    choices.referenceScaleLog

/-- Changing a finite counterterm changes the scalar action while leaving the family fixed. -/
theorem finite_counterterm_changes_action
    (bareSectionLog : ℝ)
    (choices : RenormalizedSectionChoices)
    (shift : ℝ) :
    renormalizedActionValue bareSectionLog
      { choices with
        finiteLocalCounterterm :=
          choices.finiteLocalCounterterm + shift } =
      renormalizedActionValue bareSectionLog choices + shift := by
  unfold renormalizedActionValue
  ring

/-- Changing the reference scale changes the scalar action while preserving the abstract line. -/
theorem reference_scale_changes_action
    (bareSectionLog : ℝ)
    (choices : RenormalizedSectionChoices)
    (shift : ℝ) :
    renormalizedActionValue bareSectionLog
      { choices with
        referenceScaleLog := choices.referenceScaleLog + shift } =
      renormalizedActionValue bareSectionLog choices + shift := by
  unfold renormalizedActionValue
  ring

/-- Same elliptic family admits different renormalized scalar actions. -/
theorem quillen_line_does_not_fix_renormalized_action :
    ∃ first second : RenormalizedSectionChoices,
      first ≠ second /\
      renormalizedActionValue 1 first ≠
        renormalizedActionValue 1 second := by
  refine ⟨
    { actionNormalization := 1
      finiteLocalCounterterm := 0
      referenceScaleLog := 0 },
    { actionNormalization := 1
      finiteLocalCounterterm := 1
      referenceScaleLog := 0 },
    ?_, ?_⟩
  · intro hEqual
    have hCounterterm := congrArg
      RenormalizedSectionChoices.finiteLocalCounterterm hEqual
    norm_num at hCounterterm
  · norm_num [renormalizedActionValue]

/--
The determinant line is canonical relative to the Fredholm family. The Quillen
metric and Bismut-Freed connection are canonical relative to the chosen
geometric family data. Neither statement makes the physical action,
normalization, reference scale or finite counterterms unique.
-/
structure QuillenPredictivityStatus where
  ellipticFamilyInputDerived : Prop
  quillenPackageConstructed : Prop
  anomalyCancellationDerived : Prop
  actionNormalizationDerived : Prop
  referenceScaleDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop
  partitionSectionTrivialized : Prop
  effectivePotentialDerived : Prop
  vacuumSchemeIndependent : Prop


def quillenPredictivityClosed
    (s : QuillenPredictivityStatus) : Prop :=
  s.ellipticFamilyInputDerived /\
  s.quillenPackageConstructed /\
  s.anomalyCancellationDerived /\
  s.actionNormalizationDerived /\
  s.referenceScaleDerived /\
  s.finiteCountertermsFixedMicroscopically /\
  s.partitionSectionTrivialized /\
  s.effectivePotentialDerived /\
  s.vacuumSchemeIndependent

/-- Constructing a Quillen package without fixing finite parts is not a predictive vacuum theorem. -/
theorem quillen_without_finite_parts_blocks_predictivity
    (s : QuillenPredictivityStatus)
    (hMissing : Not s.finiteCountertermsFixedMicroscopically) :
    Not (quillenPredictivityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

end P0EFTJanusQuillenFamilyCanonicity
end JanusFormal
