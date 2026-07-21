import JanusFormal.Foundations.ProgramMEnsembleMomentNoGo
import Mathlib.Tactic

/-!
# MF-ADV-006: six-level ergodic adversary

The numerical audit supplies positive weights.  This file makes the exact
moment equations explicit and proves the structural height obstruction.
-/

namespace JanusFormal.ProgramM

structure SixLevelMomentWeights where
  weight : Fin 6 → ℚ
  sum_one : ∑ i, weight i = 1
  square_sum : ∑ i, (weight i) ^ 2 = 1 / 2
  cube_sum : ∑ i, (weight i) ^ 3 = 1 / 3

def layeredPairMoment (weights : SixLevelMomentWeights) : ℚ :=
  1 - ∑ i, (weights.weight i) ^ 2

def layeredThreeChainMoment (weights : SixLevelMomentWeights) : ℚ :=
  1 - 3 * (∑ i, (weights.weight i) ^ 2) +
    2 * (∑ i, (weights.weight i) ^ 3)

theorem layered_pair_moment_matches (weights : SixLevelMomentWeights) :
    layeredPairMoment weights = 1 / 2 := by
  rw [layeredPairMoment, weights.square_sum]
  norm_num

theorem layered_three_chain_moment_matches (weights : SixLevelMomentWeights) :
    layeredThreeChainMoment weights = 1 / 6 := by
  rw [layeredThreeChainMoment, weights.square_sum, weights.cube_sum]
  norm_num

def sixLevelRel {n : ℕ} (level : Fin n → Fin 6) (x y : Fin n) : Prop :=
  x = y ∨ level x < level y

theorem sixLevelRel_refl {n : ℕ} (level : Fin n → Fin 6) (x : Fin n) :
    sixLevelRel level x x :=
  Or.inl rfl

theorem sixLevelRel_antisymm {n : ℕ} (level : Fin n → Fin 6) {x y : Fin n}
    (hxy : sixLevelRel level x y) (hyx : sixLevelRel level y x) : x = y := by
  rcases hxy with h | hxy
  · exact h
  rcases hyx with h | hyx
  · exact h.symm
  exact False.elim (LT.lt.false (LT.lt.trans hxy hyx))

theorem sixLevelRel_trans {n : ℕ} (level : Fin n → Fin 6) {x y z : Fin n}
    (hxy : sixLevelRel level x y) (hyz : sixLevelRel level y z) :
    sixLevelRel level x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  exact Or.inr (LT.lt.trans hxy hyz)

def sixLevelPoset {n : ℕ} (level : Fin n → Fin 6) : FinitePoset n where
  rel := sixLevelRel level
  refl := sixLevelRel_refl level
  antisymm := sixLevelRel_antisymm level
  trans := sixLevelRel_trans level

theorem sixLevelRel_strict {n : ℕ} (level : Fin n → Fin 6) {x y : Fin n}
    (hxy : sixLevelRel level x y) (hne : x ≠ y) : level x < level y := by
  rcases hxy with h | h
  · exact False.elim (hne h)
  · exact h

theorem sixLevelRel_no_strict_chain_of_seven {n : ℕ} (level : Fin n → Fin 6)
    (x0 x1 x2 x3 x4 x5 x6 : Fin n)
    (h01 : sixLevelRel level x0 x1) (h12 : sixLevelRel level x1 x2)
    (h23 : sixLevelRel level x2 x3) (h34 : sixLevelRel level x3 x4)
    (h45 : sixLevelRel level x4 x5) (h56 : sixLevelRel level x5 x6)
    (n01 : x0 ≠ x1) (n12 : x1 ≠ x2) (n23 : x2 ≠ x3)
    (n34 : x3 ≠ x4) (n45 : x4 ≠ x5) (n56 : x5 ≠ x6) : False := by
  have l01 := sixLevelRel_strict level h01 n01
  have l12 := sixLevelRel_strict level h12 n12
  have l23 := sixLevelRel_strict level h23 n23
  have l34 := sixLevelRel_strict level h34 n34
  have l45 := sixLevelRel_strict level h45 n45
  have l56 := sixLevelRel_strict level h56 n56
  omega

end JanusFormal.ProgramM
