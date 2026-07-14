import Mathlib

namespace JanusFormal
namespace P0EFTJanusIsotropyStratification

set_option autoImplicit false

inductive FlipSymmetry where
  | identity
  | reflection
  deriving DecidableEq, Repr

def actOnBase : FlipSymmetry → Option Bool → Option Bool
  | .identity, base => base
  | .reflection, none => none
  | .reflection, some value => some (!value)

def actOnField : FlipSymmetry → ℝ → ℝ
  | .identity, value => value
  | .reflection, value => -value

def IsInIsotropy
    (symmetry : FlipSymmetry)
    (base : Option Bool) : Prop :=
  actOnBase symmetry base = base

def scalarFunctional (coefficient value : ℝ) : ℝ :=
  coefficient * value

def IsPointwiseInvariantFunctional
    (base : Option Bool)
    (coefficient : ℝ) : Prop :=
  ∀ symmetry,
    IsInIsotropy symmetry base →
      ∀ value,
        scalarFunctional coefficient (actOnField symmetry value) =
          scalarFunctional coefficient value

@[simp]
theorem reflection_fixes_fixed_background :
    IsInIsotropy FlipSymmetry.reflection none :=
  rfl

@[simp]
theorem reflection_does_not_fix_false_background :
    Not (IsInIsotropy FlipSymmetry.reflection (some false)) := by
  simp [IsInIsotropy, actOnBase]

@[simp]
theorem reflection_does_not_fix_true_background :
    Not (IsInIsotropy FlipSymmetry.reflection (some true)) := by
  simp [IsInIsotropy, actOnBase]

theorem fixed_background_invariant_iff_zero
    (coefficient : ℝ) :
    IsPointwiseInvariantFunctional none coefficient ↔ coefficient = 0 := by
  constructor
  · intro hInvariant
    have hAtOne :=
      hInvariant FlipSymmetry.reflection
        reflection_fixes_fixed_background 1
    dsimp [scalarFunctional, actOnField] at hAtOne
    linarith
  · intro hZero
    subst coefficient
    intro symmetry hIsotropy value
    simp [scalarFunctional]

theorem false_background_every_coefficient_invariant
    (coefficient : ℝ) :
    IsPointwiseInvariantFunctional (some false) coefficient := by
  intro symmetry hIsotropy value
  cases symmetry with
  | identity => rfl
  | reflection =>
      simp [IsInIsotropy, actOnBase] at hIsotropy

theorem true_background_every_coefficient_invariant
    (coefficient : ℝ) :
    IsPointwiseInvariantFunctional (some true) coefficient := by
  intro symmetry hIsotropy value
  cases symmetry with
  | identity => rfl
  | reflection =>
      simp [IsInIsotropy, actOnBase] at hIsotropy

theorem no_nonzero_invariant_on_fixed_stratum :
    Not (∃ coefficient : ℝ,
      coefficient ≠ 0 /\
        IsPointwiseInvariantFunctional none coefficient) := by
  rintro ⟨coefficient, hNonzero, hInvariant⟩
  exact hNonzero
    ((fixed_background_invariant_iff_zero coefficient).1 hInvariant)

theorem nonzero_invariant_exists_on_free_stratum :
    ∃ coefficient : ℝ,
      coefficient ≠ 0 /\
        IsPointwiseInvariantFunctional (some false) coefficient := by
  exact ⟨1, by norm_num,
    false_background_every_coefficient_invariant 1⟩

theorem isotropy_jump_changes_pairing_freedom :
    Not (∃ coefficient : ℝ,
      coefficient ≠ 0 /\
        IsPointwiseInvariantFunctional none coefficient) /\
      (∃ coefficient : ℝ,
        coefficient ≠ 0 /\
          IsPointwiseInvariantFunctional (some false) coefficient) := by
  exact ⟨no_nonzero_invariant_on_fixed_stratum,
    nonzero_invariant_exists_on_free_stratum⟩

def SameOrbit (first second : Option Bool) : Prop :=
  ∃ symmetry, actOnBase symmetry first = second

theorem moving_backgrounds_same_orbit :
    SameOrbit (some false) (some true) :=
  ⟨FlipSymmetry.reflection, rfl⟩

theorem fixed_and_moving_backgrounds_not_same_orbit :
    Not (SameOrbit none (some false)) := by
  rintro ⟨symmetry, hOrbit⟩
  cases symmetry <;> simp [actOnBase] at hOrbit

theorem orbit_stratification_and_invariant_jump :
    SameOrbit (some false) (some true) /\
      Not (SameOrbit none (some false)) /\
      Not (∃ coefficient : ℝ,
        coefficient ≠ 0 /\
          IsPointwiseInvariantFunctional none coefficient) /\
      (∃ coefficient : ℝ,
        coefficient ≠ 0 /\
          IsPointwiseInvariantFunctional (some false) coefficient) := by
  exact ⟨moving_backgrounds_same_orbit,
    fixed_and_moving_backgrounds_not_same_orbit,
    no_nonzero_invariant_on_fixed_stratum,
    nonzero_invariant_exists_on_free_stratum⟩

structure JanusIsotropyStratificationStatus where
  structuredJetGroupoidConstructed : Prop
  orbitTypesClassified : Prop
  stabilizersComputed : Prop
  invariantFiberRanksComputedOnEachStratum : Prop
  smoothExtensionAcrossStrataProved : Prop
  singularStrataIncludedInGlobalClassification : Prop

def janusIsotropyStratificationClosed
    (s : JanusIsotropyStratificationStatus) : Prop :=
  s.structuredJetGroupoidConstructed /\
  s.orbitTypesClassified /\
  s.stabilizersComputed /\
  s.invariantFiberRanksComputedOnEachStratum /\
  s.smoothExtensionAcrossStrataProved /\
  s.singularStrataIncludedInGlobalClassification

theorem missing_extension_across_strata_blocks_global_classification
    (s : JanusIsotropyStratificationStatus)
    (hMissing : Not s.smoothExtensionAcrossStrataProved) :
    Not (janusIsotropyStratificationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end P0EFTJanusIsotropyStratification
end JanusFormal
