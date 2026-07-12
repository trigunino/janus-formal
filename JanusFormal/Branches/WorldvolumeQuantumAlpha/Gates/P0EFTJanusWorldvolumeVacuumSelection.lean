import Mathlib

namespace JanusFormal
namespace P0EFTJanusWorldvolumeVacuumSelection

set_option autoImplicit false

/-- A positive condensate satisfying a world-volume vacuum predicate. -/
def PositiveVacuum (vacuum : ℝ → Prop) (scale : ℝ) : Prop :=
  0 < scale /\ vacuum scale

/--
An exact positive flat direction cannot select a unique condensate scale.  This
is the mathematical obstruction affecting an exactly scale-invariant
Bardeen--Moshe--Bander-like phase before a stable anomaly or boundary law lifts
the modulus.
-/
theorem exact_positive_flat_direction_blocks_unique_scale
    (vacuum : ℝ → Prop)
    (hFlat : ∀ scale : ℝ, 0 < scale → vacuum scale) :
    Not (∃! scale : ℝ, PositiveVacuum vacuum scale) := by
  intro hUnique
  rcases hUnique with ⟨scale₀, hScale₀, hOnly⟩
  have hOne : PositiveVacuum vacuum 1 := by
    exact ⟨by norm_num, hFlat 1 (by norm_num)⟩
  have hTwo : PositiveVacuum vacuum 2 := by
    exact ⟨by norm_num, hFlat 2 (by norm_num)⟩
  have hOneEq : (1 : ℝ) = scale₀ := hOnly 1 hOne
  have hTwoEq : (2 : ℝ) = scale₀ := hOnly 2 hTwo
  have hContradiction : (1 : ℝ) = 2 :=
    hOneEq.trans hTwoEq.symm
  norm_num at hContradiction

/-- The LL scale selected by a condensate. -/
def ScaleSelectedBy
    (vacuum : ℝ → Prop)
    (scaleMap : ℝ → ℝ)
    (length : ℝ) : Prop :=
  ∃ condensate, PositiveVacuum vacuum condensate /\
    scaleMap condensate = length

/-- A unique condensate always induces a unique selected length. -/
theorem unique_quantum_vacuum_induces_unique_length
    (vacuum : ℝ → Prop)
    (scaleMap : ℝ → ℝ)
    (hVacuum : ∃! condensate : ℝ, PositiveVacuum vacuum condensate) :
    ∃! length : ℝ, ScaleSelectedBy vacuum scaleMap length := by
  rcases hVacuum with ⟨condensate₀, hCondensate₀, hOnly⟩
  refine ⟨scaleMap condensate₀, ?_, ?_⟩
  · exact ⟨condensate₀, hCondensate₀, rfl⟩
  · intro length hLength
    rcases hLength with ⟨condensate, hCondensate, hMap⟩
    have hEq : condensate = condensate₀ := hOnly condensate hCondensate
    rw [← hMap, hEq]

/--
A usable quantum effective potential must do more than exhibit a massive phase:
it must select one stable, scheme-independent, positive condensate and map it
to the normalized LL charge operator.
-/
structure EffectiveVacuumClosureStatus where
  renormalizedEffectivePotentialDefined : Prop
  boundedBelow : Prop
  positiveStationaryPointExists : Prop
  hessianPositiveAtVacuum : Prop
  globalMinimumUnique : Prop
  gaugeAndSchemeIndependent : Prop
  condensateToChargeMapDerived : Prop
  noTargetScaleInserted : Prop


def effectiveVacuumClosure
    (s : EffectiveVacuumClosureStatus) : Prop :=
  s.renormalizedEffectivePotentialDefined /\
  s.boundedBelow /\
  s.positiveStationaryPointExists /\
  s.hessianPositiveAtVacuum /\
  s.globalMinimumUnique /\
  s.gaugeAndSchemeIndependent /\
  s.condensateToChargeMapDerived /\
  s.noTargetScaleInserted

end P0EFTJanusWorldvolumeVacuumSelection
end JanusFormal
