import Mathlib

namespace JanusFormal
namespace P0EFTJanusCyclicHolonomyRepresentationAudit

set_option autoImplicit false

/-- Orientation character of the candidate mapping-torus loop. -/
def orientationCharacter (winding : ℤ) : ZMod 2 :=
  winding

/-- Positive and negative fourth-root lifts of the orientation character. -/
def positiveQuarterLift (winding : ℤ) : ZMod 4 :=
  winding


def negativeQuarterLift (winding : ℤ) : ZMod 4 :=
  -winding

@[simp] theorem orientation_character_generator :
    orientationCharacter 1 = 1 := by
  native_decide

@[simp] theorem orientation_character_double_loop :
    orientationCharacter 2 = 0 := by
  native_decide

@[simp] theorem positive_lift_generator :
    positiveQuarterLift 1 = 1 := by
  native_decide

@[simp] theorem negative_lift_generator :
    negativeQuarterLift 1 = 3 := by
  native_decide

@[simp] theorem positive_lift_two_loops :
    positiveQuarterLift 2 = 2 := by
  native_decide

@[simp] theorem negative_lift_two_loops :
    negativeQuarterLift 2 = 2 := by
  native_decide

@[simp] theorem positive_lift_four_loops :
    positiveQuarterLift 4 = 0 := by
  native_decide

@[simp] theorem negative_lift_four_loops :
    negativeQuarterLift 4 = 0 := by
  native_decide

/-- Four loops remain nontrivial as an integer winding even when the holonomy image closes. -/
theorem four_loops_are_not_null_in_the_cyclic_group :
    (4 : ℤ) ≠ 0 := by
  norm_num

/-- An orientation fourth-root at the generator is one of the two odd phases. -/
structure OrientationZ4GeneratorLift where
  phase : ZMod 4
  phaseIsQuarterOrThreeQuarter : phase = 1 \/ phase = 3

/-- The equation `2*phase=2` classifies the two orientation fourth-roots. -/
theorem phase_doubles_to_half_turn_iff
    (phase : ZMod 4) :
    phase + phase = 2 ↔ phase = 1 \/ phase = 3 := by
  fin_cases phase <;> native_decide

/-- The two odd phases are exactly the generator lifts of the orientation parity. -/
theorem orientation_generator_lifts_are_exactly_two :
    ∀ phase : ZMod 4,
      phase + phase = 2 → phase = 1 \/ phase = 3 := by
  intro phase hPhase
  exact (phase_doubles_to_half_turn_iff phase).mp hPhase

/-- Every allowed lift squares to the internal half-turn. -/
theorem orientation_lift_squares_to_half_turn
    (s : OrientationZ4GeneratorLift) :
    s.phase + s.phase = 2 := by
  exact (phase_doubles_to_half_turn_iff s.phase).mpr
    s.phaseIsQuarterOrThreeQuarter

/-- Every allowed lift has fourth power equal to the identity phase. -/
theorem orientation_lift_fourth_power_trivial
    (s : OrientationZ4GeneratorLift) :
    s.phase + s.phase + s.phase + s.phase = 0 := by
  have hSquare := orientation_lift_squares_to_half_turn s
  calc
    s.phase + s.phase + s.phase + s.phase =
        (s.phase + s.phase) + (s.phase + s.phase) := by
      abel
    _ = 2 + 2 := by rw [hSquare]
    _ = 0 := by native_decide

/-- Flat-sector bookkeeping over a cyclic fundamental group. -/
structure CyclicFlatSector where
  complexRank : ℕ
  generatorPhase : ZMod 4

/-- The same quarter holonomy exists at every externally chosen rank. -/
def quarterSectorOfRank (rank : ℕ) : CyclicFlatSector :=
  { complexRank := rank
    generatorPhase := 1 }

@[simp] theorem quarter_sector_rank
    (rank : ℕ) :
    (quarterSectorOfRank rank).complexRank = rank := by
  rfl

@[simp] theorem quarter_sector_phase
    (rank : ℕ) :
    (quarterSectorOfRank rank).generatorPhase = 1 := by
  rfl

/-- Identical cyclic holonomy is compatible with rank one and rank five. -/
theorem same_quarter_holonomy_allows_rank_one_and_five :
    (quarterSectorOfRank 1).generatorPhase =
        (quarterSectorOfRank 5).generatorPhase /\
    (quarterSectorOfRank 1).complexRank = 1 /\
    (quarterSectorOfRank 5).complexRank = 5 := by
  norm_num [quarterSectorOfRank]

/-- More generally, cyclic topology plus one generator phase does not select bundle rank. -/
theorem every_rank_supports_the_same_quarter_phase
    (rank : ℕ) :
    ∃ sector : CyclicFlatSector,
      sector.complexRank = rank /\
      sector.generatorPhase = 1 := by
  exact ⟨quarterSectorOfRank rank, rfl, rfl⟩

/--
The order four belongs to the image of the infinite cyclic loop under a chosen
holonomy representation. It does not turn the mapping-torus fundamental group
itself into `Z4`, and it does not determine a rank-five multiplet.
-/
structure CyclicRepresentationFrontierStatus where
  mappingTorusFiberBundleConstructed : Prop
  sphereFiberSimplyConnectedProved : Prop
  fundamentalGroupIdentifiedWithIntegers : Prop
  orientationCharacterIdentifiedWithParity : Prop
  twoOrientationZ4LiftsClassified : Prop
  pinLiftConventionFixed : Prop
  finiteDimensionalComplexIrreduciblesClassified : Prop
  irreducibleCyclicRepresentationsOneDimensionalProved : Prop
  rankFiveFlavorBundleDerivedIndependently : Prop
  internalNonabelianSymmetryDerivedIfNeeded : Prop


def cyclicRepresentationFrontierClosed
    (s : CyclicRepresentationFrontierStatus) : Prop :=
  s.mappingTorusFiberBundleConstructed /\
  s.sphereFiberSimplyConnectedProved /\
  s.fundamentalGroupIdentifiedWithIntegers /\
  s.orientationCharacterIdentifiedWithParity /\
  s.twoOrientationZ4LiftsClassified /\
  s.pinLiftConventionFixed /\
  s.finiteDimensionalComplexIrreduciblesClassified /\
  s.irreducibleCyclicRepresentationsOneDimensionalProved /\
  s.rankFiveFlavorBundleDerivedIndependently /\
  s.internalNonabelianSymmetryDerivedIfNeeded

end P0EFTJanusCyclicHolonomyRepresentationAudit
end JanusFormal
