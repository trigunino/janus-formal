import JanusFormal.Foundations.ProgramMEnsembleFirstSeparation

/-!
# MF-ADV-005: two finite moments do not identify an ensemble law

The non-ergodic competitor mixes a total order with weight 1/6, the two-level
law with weight 2/3, and an antichain with weight 1/6.
-/

namespace JanusFormal.ProgramM

def minkowskiPairMoment : ℚ := 1 / 2
def minkowskiThreeChainMoment : ℚ := 1 / 6

def mixedPairMoment : ℚ := (1 / 6) * 1 + (2 / 3) * (1 / 2) + (1 / 6) * 0
def mixedThreeChainMoment : ℚ := (1 / 6) * 1 + (2 / 3) * 0 + (1 / 6) * 0

theorem mixed_pair_moment_matches_minkowski :
    mixedPairMoment = minkowskiPairMoment := by
  norm_num [mixedPairMoment, minkowskiPairMoment]

theorem mixed_three_chain_moment_matches_minkowski :
    mixedThreeChainMoment = minkowskiThreeChainMoment := by
  norm_num [mixedThreeChainMoment, minkowskiThreeChainMoment]

def firstTwoMomentSignature (mixedModel : Bool) : ℚ × ℚ :=
  if mixedModel then (mixedPairMoment, mixedThreeChainMoment)
  else (minkowskiPairMoment, minkowskiThreeChainMoment)

theorem target_and_mixture_have_same_firstTwoMomentSignature :
    firstTwoMomentSignature false = firstTwoMomentSignature true := by
  simp [firstTwoMomentSignature, mixed_pair_moment_matches_minkowski,
    mixed_three_chain_moment_matches_minkowski]

theorem firstTwoMomentSignature_not_injective :
    ¬ Function.Injective firstTwoMomentSignature := by
  intro hinjective
  have : false = true := hinjective target_and_mixture_have_same_firstTwoMomentSignature
  cases this

end JanusFormal.ProgramM
