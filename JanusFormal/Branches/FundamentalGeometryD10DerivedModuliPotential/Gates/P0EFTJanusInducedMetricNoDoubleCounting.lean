import Mathlib

namespace JanusFormal
namespace P0EFTJanusInducedMetricNoDoubleCounting

set_option autoImplicit false

variable {ImmersionVariation MetricVariation : Type*}

/--
Compatible variation of an immersion together with the metric variation induced
by it.  The map `inducedMetricVariation` contains the first-variation formula.
-/
structure CompatibleImmersionMetricVariation
    (inducedMetricVariation : ImmersionVariation → MetricVariation) where
  immersionVariation : ImmersionVariation
  metricVariation : MetricVariation
  compatibility :
    metricVariation = inducedMetricVariation immersionVariation

/-- Construct compatible data from one immersion variation. -/
def compatibleFromImmersion
    (inducedMetricVariation : ImmersionVariation → MetricVariation)
    (variation : ImmersionVariation) :
    CompatibleImmersionMetricVariation inducedMetricVariation :=
  { immersionVariation := variation
    metricVariation := inducedMetricVariation variation
    compatibility := rfl }

/-- Forget the redundant induced metric component. -/
def forgetInducedMetric
    (inducedMetricVariation : ImmersionVariation → MetricVariation)
    (variation : CompatibleImmersionMetricVariation inducedMetricVariation) :
    ImmersionVariation :=
  variation.immersionVariation

/-- Compatible immersion-plus-metric variations contain exactly one immersion variation's data. -/
def compatibleVariationEquiv
    (inducedMetricVariation : ImmersionVariation → MetricVariation) :
    CompatibleImmersionMetricVariation inducedMetricVariation ≃
      ImmersionVariation where
  toFun := forgetInducedMetric inducedMetricVariation
  invFun := compatibleFromImmersion inducedMetricVariation
  left_inv := by
    intro variation
    cases variation with
    | mk immersion metric compatibility =>
        simp only [forgetInducedMetric, compatibleFromImmersion]
        subst metric
        rfl
  right_inv := by
    intro variation
    rfl

/-- Two compatible variations with the same immersion component are equal. -/
theorem compatible_variation_ext
    (inducedMetricVariation : ImmersionVariation → MetricVariation)
    (first second :
      CompatibleImmersionMetricVariation inducedMetricVariation)
    (hImmersion :
      first.immersionVariation = second.immersionVariation) :
    first = second := by
  apply (compatibleVariationEquiv inducedMetricVariation).injective
  exact hImmersion

/-- The metric component is fixed once the immersion variation is fixed. -/
theorem compatible_metric_is_not_independent
    (inducedMetricVariation : ImmersionVariation → MetricVariation)
    (variation :
      CompatibleImmersionMetricVariation inducedMetricVariation) :
    variation.metricVariation =
      inducedMetricVariation variation.immersionVariation :=
  variation.compatibility

/-- Independent immersion and metric variations before imposing a constraint. -/
abbrev IndependentImmersionMetricVariation :=
  ImmersionVariation × MetricVariation

/-- Constraint residual comparing an auxiliary metric variation with the induced one. -/
def inducedMetricConstraintResidual
    [Sub MetricVariation]
    (inducedMetricVariation : ImmersionVariation → MetricVariation)
    (variation : IndependentImmersionMetricVariation) : MetricVariation :=
  variation.2 - inducedMetricVariation variation.1

/-- Vanishing residual is precisely the compatibility equation. -/
theorem residual_zero_iff_compatibility
    [AddGroup MetricVariation]
    (inducedMetricVariation : ImmersionVariation → MetricVariation)
    (variation : IndependentImmersionMetricVariation) :
    inducedMetricConstraintResidual inducedMetricVariation variation = 0 ↔
      variation.2 = inducedMetricVariation variation.1 := by
  unfold inducedMetricConstraintResidual
  exact sub_eq_zero

/--
There are therefore three different theories, which must not be conflated:

1. **induced metric:** only the immersion is varied; the metric variation is
   determined and no independent Lichnerowicz block exists on the throat;
2. **auxiliary intrinsic metric:** immersion and metric are independent fields,
   but a constraint and its multiplier/ghost sector must be added;
3. **variable ambient metric:** the metric block belongs to the bulk and its
   boundary reduction must be derived.
-/
structure MetricFormulationStatus where
  inducedMetricFormulationSelected : Prop
  auxiliaryMetricFormulationSelected : Prop
  variableAmbientMetricFormulationSelected : Prop
  exactlyOneFormulationSelected : Prop
  inducedConstraintDerivedIfAuxiliary : Prop
  multiplierAndGhostSectorDerivedIfAuxiliary : Prop
  bulkBoundaryMapDerivedIfAmbientMetricVaries : Prop
  noMetricDoubleCountingProved : Prop


def metricFormulationClosed
    (s : MetricFormulationStatus) : Prop :=
  s.exactlyOneFormulationSelected /\
  s.inducedConstraintDerivedIfAuxiliary /\
  s.multiplierAndGhostSectorDerivedIfAuxiliary /\
  s.bulkBoundaryMapDerivedIfAmbientMetricVaries /\
  s.noMetricDoubleCountingProved

/-- Missing a formulation choice blocks a well-defined field space. -/
theorem missing_metric_formulation_blocks_closure
    (s : MetricFormulationStatus)
    (hMissing : Not s.exactlyOneFormulationSelected) :
    Not (metricFormulationClosed s) := by
  intro hClosed
  exact hMissing hClosed.1

end P0EFTJanusInducedMetricNoDoubleCounting
end JanusFormal
