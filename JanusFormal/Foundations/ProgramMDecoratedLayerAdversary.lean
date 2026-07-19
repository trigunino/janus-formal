import JanusFormal.Foundations.ProgramMTwinFractionDecay

/-!
# MF-ADV-008: decorated infinite-layer adversary
-/

namespace JanusFormal.ProgramM

def decoratedMicroEdgeProbability : ℚ := 1 / 5
def decoratedLevelSquareSum : ℚ := 5 / 9
def decoratedLevelCubeSum : ℚ := 20 / 51

def decoratedPairMoment : ℚ :=
  1 - (1 - decoratedMicroEdgeProbability / 2) * decoratedLevelSquareSum

def decoratedThreeChainMoment : ℚ :=
  1 - 3 * decoratedLevelSquareSum + 2 * decoratedLevelCubeSum +
    (3 * decoratedMicroEdgeProbability / 2) *
      (decoratedLevelSquareSum - decoratedLevelCubeSum)

theorem decorated_pair_moment_matches : decoratedPairMoment = 1 / 2 := by
  norm_num [decoratedPairMoment, decoratedMicroEdgeProbability,
    decoratedLevelSquareSum]

theorem decorated_three_chain_moment_matches :
    decoratedThreeChainMoment = 1 / 6 := by
  norm_num [decoratedThreeChainMoment, decoratedMicroEdgeProbability,
    decoratedLevelSquareSum, decoratedLevelCubeSum]

/-- One realized random bipartite micro-order.  Probability is not used in the
order axioms: every realized edge must simply point from lower to upper. -/
structure HeightTwoMicroRelation (α : Type*) where
  lower : α → Prop
  edge : α → α → Prop
  edge_direction : ∀ {x y}, edge x y → lower x ∧ ¬ lower y

def HeightTwoMicroRelation.rel {α : Type*}
    (micro : HeightTwoMicroRelation α) (x y : α) : Prop :=
  x = y ∨ micro.edge x y

theorem HeightTwoMicroRelation.refl {α : Type*}
    (micro : HeightTwoMicroRelation α) (x : α) : micro.rel x x :=
  Or.inl rfl

theorem HeightTwoMicroRelation.antisymm {α : Type*}
    (micro : HeightTwoMicroRelation α) {x y : α}
    (hxy : micro.rel x y) (hyx : micro.rel y x) : x = y := by
  rcases hxy with h | hxy
  · exact h
  rcases hyx with h | hyx
  · exact h.symm
  exact False.elim ((micro.edge_direction hyx).2 (micro.edge_direction hxy).1)

theorem HeightTwoMicroRelation.trans {α : Type*}
    (micro : HeightTwoMicroRelation α) {x y z : α}
    (hxy : micro.rel x y) (hyz : micro.rel y z) : micro.rel x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  exact False.elim ((micro.edge_direction hxy).2 (micro.edge_direction hyz).1)

end JanusFormal.ProgramM

