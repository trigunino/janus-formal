import Mathlib
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalLineClutching

namespace JanusFormal
namespace P0EFTJanusNormalBundleOrientationCover

set_option autoImplicit false

open P0EFTJanusNormalLineClutching

/-- Sign representation defining the associated real normal line. -/
def normalSignRepresentation (winding : ℤ) : ℝˣ :=
  if Even winding then 1 else -1

@[simp] theorem normal_sign_even (winding : ℤ) (h : Even winding) :
    normalSignRepresentation winding = 1 := by
  simp [normalSignRepresentation, h]

theorem normal_sign_odd (winding : ℤ) (h : ¬ Even winding) :
    normalSignRepresentation winding = -1 := by
  simp [normalSignRepresentation, h]

/-- The orientation cover consists of even deck windings. -/
structure OrientationCoverWinding where
  winding : ℤ
  liesInKernel : Even winding

/-- Pullback of the normal orientation character to the orientation cover. -/
def pulledBackNormalW1 (winding : OrientationCoverWinding) : ZMod 2 :=
  normalW1Character winding.winding

@[simp] theorem pulled_back_normal_w1_vanishes
    (winding : OrientationCoverWinding) :
    pulledBackNormalW1 winding = 0 := by
  rcases winding.liesInKernel with ⟨k, hk⟩
  simp only [pulledBackNormalW1, normalW1Character, hk]
  push_cast
  have hTwo : (2 : ZMod 2) = 0 := by native_decide
  calc
    (k : ZMod 2) + k = 2 * (k : ZMod 2) := by ring
    _ = 0 := by rw [hTwo, zero_mul]

/-- The clutching character and the first Stiefel--Whitney representative agree. -/
theorem clutching_character_is_w1 (winding : ℤ) :
    normalW1Character winding = (winding : ZMod 2) := by
  rfl

/-- Two deck circuits act trivially on the associated real line. -/
theorem doubled_deck_action_trivial (winding : ℤ) :
    normalSignRepresentation (2 * winding) = 1 := by
  apply normal_sign_even
  exact ⟨winding, by omega⟩

/-- A point of the pulled-back normal line before quotienting by deck transformations. -/
@[ext] structure NormalBundleCoverPoint where
  baseCoordinate : ℝ
  fiberCoordinate : ℝ

/-- Integer deck action presenting the associated real normal line globally. -/
def normalBundleDeckAction (period : ℝ) (winding : ℤ)
    (point : NormalBundleCoverPoint) : NormalBundleCoverPoint :=
  { baseCoordinate := point.baseCoordinate + winding * period
    fiberCoordinate := (normalSignRepresentation winding : ℝ) *
      point.fiberCoordinate }

@[simp] theorem normal_bundle_deck_zero (period : ℝ)
    (point : NormalBundleCoverPoint) :
    normalBundleDeckAction period 0 point = point := by
  ext <;> simp [normalBundleDeckAction, normalSignRepresentation]

theorem normal_sign_add (first second : ℤ) :
    normalSignRepresentation (first + second) =
      normalSignRepresentation first * normalSignRepresentation second := by
  by_cases hFirst : Even first <;> by_cases hSecond : Even second <;>
    simp [normalSignRepresentation, hFirst, hSecond, Int.even_add]

theorem normal_bundle_deck_add (period : ℝ) (first second : ℤ)
    (point : NormalBundleCoverPoint) :
    normalBundleDeckAction period (first + second) point =
      normalBundleDeckAction period first
        (normalBundleDeckAction period second point) := by
  ext
  · simp [normalBundleDeckAction]
    ring
  · simp [normalBundleDeckAction, normal_sign_add]
    ring

/-- Global construction ledger, independent of the variational program. -/
structure NormalBundleGlobalStatus where
  quotientBaseConstructed : Prop
  signRepresentationConstructed : Prop
  associatedRealLineRegistered : Prop
  clutchingModelIdentified : Prop
  orientationCoverAsKernelConstructed : Prop
  pullbackBundleTrivialized : Prop
  w1ClutchingComparisonProved : Prop
  pulledBackW1VanishingProved : Prop

def normalBundleGlobalClosed (s : NormalBundleGlobalStatus) : Prop :=
  s.quotientBaseConstructed ∧ s.signRepresentationConstructed ∧
  s.associatedRealLineRegistered ∧ s.clutchingModelIdentified ∧
  s.orientationCoverAsKernelConstructed ∧ s.pullbackBundleTrivialized ∧
  s.w1ClutchingComparisonProved ∧ s.pulledBackW1VanishingProved

theorem missing_associated_line_blocks_global_normal_bundle
    (s : NormalBundleGlobalStatus)
    (h : Not s.associatedRealLineRegistered) :
    Not (normalBundleGlobalClosed s) := by
  intro hs
  exact h hs.2.2.1

end P0EFTJanusNormalBundleOrientationCover
end JanusFormal
