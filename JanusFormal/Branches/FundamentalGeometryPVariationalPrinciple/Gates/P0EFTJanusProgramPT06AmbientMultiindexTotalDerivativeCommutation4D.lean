import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientTotalDerivativeCommutation4D

/-!
# Permutation invariance of ambient multi-index total derivatives

Smooth fixed-ambient total derivatives commute, so their finite iterates
depend only on the multiset of spatial directions.  This identifies adding a
coordinate multi-index with applying the corresponding total derivative
before the canonical multi-index word.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AmbientMultiindexTotalDerivativeCommutation4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
open P0EFTJanusProgramPT06AmbientTotalDerivativeCommutation4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- A smooth iterated ambient total derivative depends only on its direction
multiset. -/
theorem programPT06AmbientIteratedTotalDerivative_eq_of_perm
    (order : Nat) {first second : List (Fin 3)}
    (directionsPerm : first.Perm second)
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : ContDiff Real ∞ localFunction) :
    programPT06AmbientIteratedTotalDerivative order first localFunction =
      programPT06AmbientIteratedTotalDerivative order second localFunction := by
  induction directionsPerm generalizing localFunction with
  | nil => rfl
  | cons direction directionsPerm induction =>
      exact induction _
        (programPT06AmbientLocalFunctionTotalDerivative_contDiff
          order direction localFunction hLocalFunction)
  | swap first second directions =>
      exact congrArg
        (programPT06AmbientIteratedTotalDerivative
          (Fiber := Fiber) (Target := Target) order directions)
        (programPT06AmbientLocalFunctionTotalDerivative_comm
          order first second localFunction
          (hLocalFunction.of_le
            (show (2 : ℕ∞) ≤ ∞ by
              exact WithTop.coe_le_coe.mpr le_top)))
  | trans firstPerm secondPerm firstInduction secondInduction =>
      exact (firstInduction localFunction hLocalFunction).trans
        (secondInduction localFunction hLocalFunction)

/-- The canonical word for `index + e_direction` is a permutation of the
word obtained by prepending `direction` to the canonical word for `index`. -/
theorem programPT06ThroatSpatialMultiIndexDirectionWord_add_coordinate_perm
    (index : ThroatSpatialMultiIndex) (direction : Fin 3) :
    (programPT06ThroatSpatialMultiIndexDirectionWord
        (index + throatSpatialCoordinateMultiIndex direction)).Perm
      (direction ::
        programPT06ThroatSpatialMultiIndexDirectionWord index) := by
  rw [← Multiset.coe_eq_coe]
  simp [programPT06ThroatSpatialMultiIndexDirectionWord,
    Finsupp.toMultiset_add, throatSpatialCoordinateMultiIndex, add_comm]
  simpa only [Multiset.cons_coe] using
    (congrArg (Multiset.cons direction)
      (Multiset.sort_eq (Finsupp.toMultiset index)
        (fun first second : Fin 3 => first ≤ second))).symm

/-- Adding one coordinate to a multi-index amounts to applying that ambient
total derivative before the canonical word for the original multi-index. -/
theorem programPT06AmbientMultiindexTotalDerivative_add_coordinate
    (order : Nat) (index : ThroatSpatialMultiIndex) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : ContDiff Real ∞ localFunction) :
    programPT06AmbientMultiindexTotalDerivative order
        (index + throatSpatialCoordinateMultiIndex direction) localFunction =
      programPT06AmbientMultiindexTotalDerivative order index
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) := by
  simpa only [programPT06AmbientMultiindexTotalDerivative,
    programPT06AmbientIteratedTotalDerivative_cons] using
    programPT06AmbientIteratedTotalDerivative_eq_of_perm
      (Fiber := Fiber) (Target := Target) order
      (programPT06ThroatSpatialMultiIndexDirectionWord_add_coordinate_perm
        index direction) localFunction hLocalFunction

end
end P0EFTJanusProgramPT06AmbientMultiindexTotalDerivativeCommutation4D
end JanusFormal
