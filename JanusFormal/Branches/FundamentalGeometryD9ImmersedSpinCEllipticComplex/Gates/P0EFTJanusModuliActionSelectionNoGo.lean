import Mathlib

namespace JanusFormal
namespace P0EFTJanusModuliActionSelectionNoGo

set_option autoImplicit false

/-- Minimal configuration-and-symmetry skeleton. -/
structure ModuliSkeleton where
  fieldRank : ℕ
  gaugeRank : ℕ

/-- Quadratic action coefficient on a one-dimensional test field. -/
def quadraticAction
    (coefficient field : ℝ) : ℝ :=
  coefficient * field ^ 2 / 2

/-- Gradient/equation of motion. -/
def quadraticGradient
    (coefficient field : ℝ) : ℝ :=
  coefficient * field

/-- Hessian map. -/
def quadraticHessian
    (coefficient variation : ℝ) : ℝ :=
  coefficient * variation

/-- Two actions can live on exactly the same configuration skeleton. -/
def scalarSkeleton : ModuliSkeleton :=
  { fieldRank := 1
    gaugeRank := 0 }

/-- Unit and doubled actions have different Hessians. -/
theorem same_moduli_skeleton_supports_distinct_hessians :
    quadraticHessian 1 1 ≠ quadraticHessian 2 1 := by
  norm_num [quadraticHessian]

/-- Their critical point is nevertheless the same when coefficients are nonzero. -/
theorem nonzero_quadratic_actions_have_same_critical_locus
    (firstCoefficient secondCoefficient field : ℝ)
    (hFirst : firstCoefficient ≠ 0)
    (hSecond : secondCoefficient ≠ 0) :
    quadraticGradient firstCoefficient field = 0 ↔
      quadraticGradient secondCoefficient field = 0 := by
  unfold quadraticGradient
  constructor
  · intro hFirstCritical
    have hField : field = 0 :=
      (mul_eq_zero.mp hFirstCritical).resolve_left hFirst
    rw [hField]
    ring
  · intro hSecondCritical
    have hField : field = 0 :=
      (mul_eq_zero.mp hSecondCritical).resolve_left hSecond
    rw [hField]
    ring

/-- Scaling an action scales the Hessian without changing the object or gauge group. -/
theorem action_rescaling_changes_hessian
    (scale coefficient variation : ℝ) :
    quadraticHessian (scale * coefficient) variation =
      scale * quadraticHessian coefficient variation := by
  unfold quadraticHessian
  ring

/-- A finite local counterterm changes the Hessian additively. -/
theorem counterterm_changes_hessian
    (bareCoefficient counterterm variation : ℝ) :
    quadraticHessian (bareCoefficient + counterterm) variation =
      quadraticHessian bareCoefficient variation +
        quadraticHessian counterterm variation := by
  unfold quadraticHessian
  ring

/-- Action-decorated moduli problem. -/
structure ActionDecoratedModuliProblem where
  skeleton : ModuliSkeleton
  actionNormalization : ℝ
  finiteCounterterm : ℝ
  hessianCoefficient : ℝ
  hessianLaw :
    hessianCoefficient = actionNormalization + finiteCounterterm

/-- Same underlying moduli skeleton can carry different action decorations. -/
theorem same_skeleton_does_not_fix_action_decoration :
    ∃ first second : ActionDecoratedModuliProblem,
      first.skeleton = second.skeleton /\
      first.hessianCoefficient ≠ second.hessianCoefficient := by
  refine ⟨
    { skeleton := scalarSkeleton
      actionNormalization := 1
      finiteCounterterm := 0
      hessianCoefficient := 1
      hessianLaw := by norm_num },
    { skeleton := scalarSkeleton
      actionNormalization := 1
      finiteCounterterm := 1
      hessianCoefficient := 2
      hessianLaw := by norm_num },
    rfl, by norm_num⟩

/--
Therefore the configuration stack or moduli groupoid is not the terminal
fundamental object for quantum dynamics.  The minimum data are an
**action-decorated derived moduli problem**: objects and automorphisms, plus an
invariant action and a target-independent renormalization prescription.
-/
structure ActionSelectionPhysicalStatus where
  configurationGroupoidDerived : Prop
  invariantLocalActionDerived : Prop
  normalizationFixedMicroscopically : Prop
  allowedCountertermsClassified : Prop
  finiteCountertermsFixedMicroscopically : Prop
  hessianDerived : Prop
  sameActionUsedInAllSectors : Prop
  noTargetRadiusUsedInMatching : Prop
  renormalizedCriticalLocusDerived : Prop


def actionSelectionPhysicalClosure
    (s : ActionSelectionPhysicalStatus) : Prop :=
  s.configurationGroupoidDerived /\
  s.invariantLocalActionDerived /\
  s.normalizationFixedMicroscopically /\
  s.allowedCountertermsClassified /\
  s.finiteCountertermsFixedMicroscopically /\
  s.hessianDerived /\
  s.sameActionUsedInAllSectors /\
  s.noTargetRadiusUsedInMatching /\
  s.renormalizedCriticalLocusDerived

end P0EFTJanusModuliActionSelectionNoGo
end JanusFormal
