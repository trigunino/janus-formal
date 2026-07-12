import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusNormalOrientationZ4Lift

namespace JanusFormal
namespace P0EFTJanusCyclicRepresentationMultiplicityNoGo

set_option autoImplicit false

open P0EFTJanusNormalOrientationZ4Lift

/-- Algebraic loop group of the simply-connected-fiber mapping-torus candidate. -/
abbrev CyclicLoopGroup := ℤ

/-- Every flat `Z4` character of a cyclic loop model is determined by one phase. -/
def z4Character
    (generatorPhase : ZMod 4)
    (winding : CyclicLoopGroup) : ZMod 4 :=
  (winding : ZMod 4) * generatorPhase

/-- Character law. -/
theorem z4_character_additive
    (generatorPhase : ZMod 4)
    (first second : CyclicLoopGroup) :
    z4Character generatorPhase (first + second) =
      z4Character generatorPhase first +
        z4Character generatorPhase second := by
  unfold z4Character
  push_cast
  ring

/-- The generator value recovers the chosen phase. -/
@[simp] theorem z4_character_on_generator
    (generatorPhase : ZMod 4) :
    z4Character generatorPhase 1 = generatorPhase := by
  simp [z4Character]

/-- Equal generator phases give equal characters. -/
theorem same_generator_phase_same_character
    (firstPhase secondPhase : ZMod 4)
    (hPhase : firstPhase = secondPhase) :
    ∀ winding,
      z4Character firstPhase winding =
        z4Character secondPhase winding := by
  intro winding
  rw [hPhase]

/-- Conversely, equality on all loops forces equality on the generator. -/
theorem same_character_forces_same_generator_phase
    (firstPhase secondPhase : ZMod 4)
    (hCharacters :
      ∀ winding,
        z4Character firstPhase winding =
          z4Character secondPhase winding) :
    firstPhase = secondPhase := by
  simpa using hCharacters 1

/-- Flat holonomy plus an independently chosen fiber multiplicity. -/
structure FlatZ4BundleModel where
  generatorPhase : ZMod 4
  fiberRank : ℕ

/-- Forgetting the field content retains only topological holonomy data. -/
def forgetFiberRank
    (s : FlatZ4BundleModel) : ZMod 4 :=
  s.generatorPhase

/-- The same topology/holonomy supports every nonnegative fiber rank. -/
def bundleOfRank
    (generatorPhase : ZMod 4)
    (fiberRank : ℕ) : FlatZ4BundleModel :=
  { generatorPhase := generatorPhase
    fiberRank := fiberRank }

@[simp] theorem bundle_of_rank_has_requested_holonomy
    (generatorPhase : ZMod 4)
    (fiberRank : ℕ) :
    forgetFiberRank (bundleOfRank generatorPhase fiberRank) =
      generatorPhase := by
  rfl

@[simp] theorem bundle_of_rank_has_requested_rank
    (generatorPhase : ZMod 4)
    (fiberRank : ℕ) :
    (bundleOfRank generatorPhase fiberRank).fiberRank = fiberRank := by
  rfl

/-- Rank one and rank five can carry exactly the same primitive quarter holonomy. -/
theorem same_quarter_holonomy_supports_rank_one_and_rank_five :
    forgetFiberRank (bundleOfRank 1 1) =
        forgetFiberRank (bundleOfRank 1 5) /\
      (bundleOfRank 1 1).fiberRank = 1 /\
      (bundleOfRank 1 5).fiberRank = 5 := by
  norm_num [forgetFiberRank, bundleOfRank]

/-- Holonomy equality does not imply rank equality. -/
theorem holonomy_does_not_determine_multiplicity :
    ∃ first second : FlatZ4BundleModel,
      forgetFiberRank first = forgetFiberRank second /\
      first.fiberRank ≠ second.fiberRank := by
  exact ⟨bundleOfRank 1 1, bundleOfRank 1 5,
    rfl, by norm_num⟩

/-- The orientation-compatible order-four phases are still only `1` and `3`. -/
theorem cyclic_orientation_lifts_are_two_characters :
    (IsNormalSquareRoot (1 : ZMod 4)) /\
      (IsNormalSquareRoot (3 : ZMod 4)) /\
      (1 : ZMod 4) ≠ 3 := by
  exact ⟨one_is_normal_square_root,
    three_is_normal_square_root,
    by native_decide⟩

/--
Thus a mapping torus with cyclic fundamental group can force a holonomy phase,
or at most a PT-conjugate pair of phases, but cannot by itself force the integer
five.  A rank-five sector must come from an additional vector bundle,
representation, index theorem, tensor bundle, gauge/ghost complex or bulk
reduction.
-/
structure CyclicRepresentationPhysicalStatus where
  actualFundamentalGroupProvedInfiniteCyclic : Prop
  flatBundlesClassifiedByRepresentations : Prop
  orderFourCharactersClassified : Prop
  finiteDimensionalUnitaryRepresentationsDecomposed : Prop
  multiplicityBundleDerivedFromGeometry : Prop
  rankFiveOrAlternativeWeightDerived : Prop
  noMultiplicityInsertedByHand : Prop


def cyclicRepresentationPhysicalClosure
    (s : CyclicRepresentationPhysicalStatus) : Prop :=
  s.actualFundamentalGroupProvedInfiniteCyclic /\
  s.flatBundlesClassifiedByRepresentations /\
  s.orderFourCharactersClassified /\
  s.finiteDimensionalUnitaryRepresentationsDecomposed /\
  s.multiplicityBundleDerivedFromGeometry /\
  s.rankFiveOrAlternativeWeightDerived /\
  s.noMultiplicityInsertedByHand

end P0EFTJanusCyclicRepresentationMultiplicityNoGo
end JanusFormal
