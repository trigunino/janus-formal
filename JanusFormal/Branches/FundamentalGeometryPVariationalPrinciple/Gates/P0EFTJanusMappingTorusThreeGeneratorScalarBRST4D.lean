import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusExteriorScalarBRSTDerivation4D

/-!
# Three-generator scalar BRST closure on the D8 quotient

This gate extends the exterior-valued scalar calculation from two arbitrary
smooth diffeomorphism ghosts to all three odd coefficient generators.  The
square of their combined scalar action is the sum of the three pairwise Lie
bracket actions.  Consequently the nonlinear ghost rule cancels the scalar
BRST square exactly.

This is a genuine calculation in the three-generator exterior algebra.  It
does not construct antifields or the BV antibracket.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusThreeGeneratorScalarBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusExteriorScalarBRSTDerivation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Ghost := CInfinityDiffeomorphismGhost period hPeriod
private abbrev Scalar := CInfinityScalarField period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The odd ghost using every generator of `Fin 3`. -/
def threeGeneratorOddGhost
    (first second third : Ghost period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  oddPureGhost period hPeriod 0 first +
    oddPureGhost period hPeriod 1 second +
      oddPureGhost period hPeriod 2 third

/-- Scalar action carried by one odd exterior generator. -/
def oddPureScalarAction
    (i : Fin 3) (ghost : Ghost period hPeriod) :
    ExteriorScalarModule period hPeriod →ₗ[Real]
      ExteriorScalarModule period hPeriod :=
  exteriorGhostScalarAction period hPeriod
    (oddPureGhost period hPeriod i ghost)

@[simp]
theorem oddPureScalarAction_self
    (i : Fin 3) (ghost : Ghost period hPeriod)
    (scalar : Scalar period hPeriod) :
    oddPureScalarAction period hPeriod i ghost
        (oddPureScalarAction period hPeriod i ghost
          (exteriorScalarEmbed period hPeriod scalar)) = 0 := by
  simp [oddPureScalarAction, oddPureGhost, exteriorScalarEmbed]

/-- The two cross terms associated with a pair of odd pure ghosts combine to
the action of their Lie bracket. -/
theorem oddPureGhost_scalarAction_cross
    (i j : Fin 3)
    (first second : Ghost period hPeriod)
    (scalar : Scalar period hPeriod) :
    oddPureScalarAction period hPeriod i first
          (oddPureScalarAction period hPeriod j second
            (exteriorScalarEmbed period hPeriod scalar)) +
        oddPureScalarAction period hPeriod j second
          (oddPureScalarAction period hPeriod i first
            (exteriorScalarEmbed period hPeriod scalar)) =
      (oddGenerator i * oddGenerator j) ⊗ₜ[Real]
        cInfinityScalarLieDerivative period hPeriod
          (smoothGhostLieBracket period hPeriod first second) scalar := by
  simp only [oddPureScalarAction, oddPureGhost, exteriorScalarEmbed,
    exteriorGhostScalarAction_tmul, mul_one]
  rw [oddGenerator_anticommute j i, TensorProduct.neg_tmul,
    ← sub_eq_add_neg, ← TensorProduct.tmul_sub,
    ← cInfinityScalarLieDerivative_bracket period hPeriod first second scalar]

/-- Even bracket carried by a selected pair of odd generators. -/
def oddPairGhostBracket
    (i j : Fin 3) (first second : Ghost period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  exteriorGhostBracket period hPeriod
    (oddPureGhost period hPeriod i first)
    (oddPureGhost period hPeriod j second)

@[simp]
theorem oddPairGhostBracket_eq
    (i j : Fin 3) (first second : Ghost period hPeriod) :
    oddPairGhostBracket period hPeriod i j first second =
      (oddGenerator i * oddGenerator j) ⊗ₜ[Real]
        smoothGhostLieBracket period hPeriod first second := by
  rfl

theorem oddGenerator_commute_pair (i j k : Fin 3) :
    oddGenerator k * (oddGenerator i * oddGenerator j) =
      (oddGenerator i * oddGenerator j) * oddGenerator k := by
  calc
    oddGenerator k * (oddGenerator i * oddGenerator j) =
        (oddGenerator k * oddGenerator i) * oddGenerator j := by
      rw [mul_assoc]
    _ = (-(oddGenerator i * oddGenerator k)) * oddGenerator j := by
      rw [oddGenerator_anticommute]
    _ = -(oddGenerator i * (oddGenerator k * oddGenerator j)) := by
      rw [neg_mul, mul_assoc]
    _ = -(oddGenerator i * (-(oddGenerator j * oddGenerator k))) := by
      rw [oddGenerator_anticommute]
    _ = (oddGenerator i * oddGenerator j) * oddGenerator k := by
      rw [mul_neg, neg_neg, mul_assoc]

@[simp]
theorem oddPureGhost_oddPair_repeat_left_zero
    (i j : Fin 3) (first second : Ghost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod i first)
        (oddPairGhostBracket period hPeriod i j first second) = 0 := by
  simp only [oddPairGhostBracket, oddPureGhost,
    exteriorGhostBracket_tmul]
  rw [← mul_assoc, oddGenerator_sq]
  simp

@[simp]
theorem oddPureGhost_oddPair_repeat_right_zero
    (i j : Fin 3) (first second : Ghost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod j second)
        (oddPairGhostBracket period hPeriod i j first second) = 0 := by
  simp only [oddPairGhostBracket, oddPureGhost,
    exteriorGhostBracket_tmul]
  rw [← mul_assoc, oddGenerator_anticommute j i, neg_mul,
    mul_assoc, oddGenerator_sq]
  simp

/-- An even pair bracket and an odd pure ghost satisfy the even--odd Koszul
antisymmetry rule. -/
theorem oddPairGhostBracket_oddPure_swap
    (i j k : Fin 3)
    (first second third : Ghost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (oddPairGhostBracket period hPeriod i j first second)
        (oddPureGhost period hPeriod k third) =
      -exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod k third)
        (oddPairGhostBracket period hPeriod i j first second) := by
  simp only [oddPairGhostBracket, oddPureGhost,
    exteriorGhostBracket_tmul]
  rw [smoothGhostLieBracket_swap period hPeriod third
    (smoothGhostLieBracket period hPeriod first second)]
  simp only [TensorProduct.tmul_neg, neg_neg]
  rw [oddGenerator_commute_pair]

/-- Sum of the three independent even pairwise ghost brackets. -/
def threeGeneratorPairwiseBracket
    (first second third : Ghost period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  oddPairGhostBracket period hPeriod 0 1 first second +
    oddPairGhostBracket period hPeriod 0 2 first third +
    oddPairGhostBracket period hPeriod 1 2 second third

/-- The self-bracket of the full odd ghost is twice the sum over unordered
pairs. -/
theorem threeGeneratorOddGhost_self_bracket
    (first second third : Ghost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (threeGeneratorOddGhost period hPeriod first second third)
        (threeGeneratorOddGhost period hPeriod first second third) =
      (2 : Real) •
        threeGeneratorPairwiseBracket period hPeriod first second third := by
  let ghost0 := oddPureGhost period hPeriod 0 first
  let ghost1 := oddPureGhost period hPeriod 1 second
  let ghost2 := oddPureGhost period hPeriod 2 third
  change exteriorGhostBracket period hPeriod
      (ghost0 + ghost1 + ghost2) (ghost0 + ghost1 + ghost2) = _
  calc
    exteriorGhostBracket period hPeriod
        (ghost0 + ghost1 + ghost2) (ghost0 + ghost1 + ghost2) =
      exteriorGhostBracket period hPeriod ghost0 ghost0 +
        (exteriorGhostBracket period hPeriod ghost0 ghost1 +
          exteriorGhostBracket period hPeriod ghost1 ghost0) +
        (exteriorGhostBracket period hPeriod ghost0 ghost2 +
          exteriorGhostBracket period hPeriod ghost2 ghost0) +
        exteriorGhostBracket period hPeriod ghost1 ghost1 +
        (exteriorGhostBracket period hPeriod ghost1 ghost2 +
          exteriorGhostBracket period hPeriod ghost2 ghost1) +
        exteriorGhostBracket period hPeriod ghost2 ghost2 := by
          simp only [map_add, LinearMap.add_apply]
          module
    _ = _ := by
      dsimp only [ghost0, ghost1, ghost2]
      rw [exteriorGhostBracket_oddPure_self,
        exteriorGhostBracket_oddPure_swap period hPeriod 1 0 second first,
        exteriorGhostBracket_oddPure_swap period hPeriod 2 0 third first,
        exteriorGhostBracket_oddPure_self,
        exteriorGhostBracket_oddPure_swap period hPeriod 2 1 third second,
        exteriorGhostBracket_oddPure_self]
      simp only [oddPureGhost, exteriorGhostBracket_tmul]
      unfold threeGeneratorPairwiseBracket
      simp only [oddPairGhostBracket_eq]
      module

/-- Conventional nonlinear ghost rule for the complete three-component odd
ghost. -/
def threeGeneratorNonlinearGhostBRSTTerm
    (first second third : Ghost period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  (-((2 : Real)⁻¹)) •
    exteriorGhostBracket period hPeriod
      (threeGeneratorOddGhost period hPeriod first second third)
      (threeGeneratorOddGhost period hPeriod first second third)

theorem threeGeneratorNonlinearGhostBRSTTerm_eq
    (first second third : Ghost period hPeriod) :
    threeGeneratorNonlinearGhostBRSTTerm period hPeriod first second third =
      -threeGeneratorPairwiseBracket period hPeriod first second third := by
  rw [threeGeneratorNonlinearGhostBRSTTerm,
    threeGeneratorOddGhost_self_bracket, smul_smul]
  norm_num

/-- The cubic pure-ghost obstruction vanishes for the complete three-component
odd ghost, not merely for one selected ordered triple. -/
@[simp]
theorem threeGeneratorOddGhost_nested_jacobi_zero
    (first second third : Ghost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (threeGeneratorOddGhost period hPeriod first second third)
        (exteriorGhostBracket period hPeriod
          (threeGeneratorOddGhost period hPeriod first second third)
          (threeGeneratorOddGhost period hPeriod first second third)) = 0 := by
  rw [threeGeneratorOddGhost_self_bracket]
  simp only [map_smul, threeGeneratorOddGhost,
    threeGeneratorPairwiseBracket, map_add, LinearMap.add_apply]
  rw [oddPureGhost_oddPair_repeat_left_zero,
    oddPureGhost_oddPair_repeat_left_zero,
    oddPureGhost_oddPair_repeat_right_zero,
    oddPureGhost_oddPair_repeat_left_zero,
    oddPureGhost_oddPair_repeat_right_zero,
    oddPureGhost_oddPair_repeat_right_zero]
  simp only [zero_add, add_zero]
  have hJacobi := exteriorGhostBracket_oddPure_jacobi period hPeriod
    0 1 2 first second third
  change exteriorGhostBracket period hPeriod
      (oddPureGhost period hPeriod 0 first)
      (oddPairGhostBracket period hPeriod 1 2 second third) =
    exteriorGhostBracket period hPeriod
        (oddPairGhostBracket period hPeriod 0 1 first second)
        (oddPureGhost period hPeriod 2 third) -
      exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod 1 second)
        (oddPairGhostBracket period hPeriod 0 2 first third) at hJacobi
  rw [oddPairGhostBracket_oddPure_swap] at hJacobi
  rw [hJacobi]
  abel
  simp

/-- The square of the full three-generator scalar action is exactly the sum
of the three pairwise bracket actions. -/
theorem threeGeneratorOddGhost_scalarAction_sq
    (first second third : Ghost period hPeriod)
    (scalar : Scalar period hPeriod) :
    exteriorGhostScalarAction period hPeriod
        (threeGeneratorOddGhost period hPeriod first second third)
        (exteriorGhostScalarAction period hPeriod
          (threeGeneratorOddGhost period hPeriod first second third)
          (exteriorScalarEmbed period hPeriod scalar)) =
      (oddGenerator 0 * oddGenerator 1) ⊗ₜ[Real]
          cInfinityScalarLieDerivative period hPeriod
            (smoothGhostLieBracket period hPeriod first second) scalar +
        (oddGenerator 0 * oddGenerator 2) ⊗ₜ[Real]
          cInfinityScalarLieDerivative period hPeriod
            (smoothGhostLieBracket period hPeriod first third) scalar +
        (oddGenerator 1 * oddGenerator 2) ⊗ₜ[Real]
          cInfinityScalarLieDerivative period hPeriod
            (smoothGhostLieBracket period hPeriod second third) scalar := by
  let embedded := exteriorScalarEmbed period hPeriod scalar
  let action0 := oddPureScalarAction period hPeriod 0 first
  let action1 := oddPureScalarAction period hPeriod 1 second
  let action2 := oddPureScalarAction period hPeriod 2 third
  change (action0 + action1 + action2)
      ((action0 + action1 + action2) embedded) = _
  calc
    (action0 + action1 + action2)
        ((action0 + action1 + action2) embedded) =
      action0 (action0 embedded) +
        (action0 (action1 embedded) + action1 (action0 embedded)) +
        (action0 (action2 embedded) + action2 (action0 embedded)) +
        action1 (action1 embedded) +
        (action1 (action2 embedded) + action2 (action1 embedded)) +
        action2 (action2 embedded) := by
          simp only [LinearMap.add_apply, map_add]
          module
    _ = _ := by
      dsimp only [action0, action1, action2, embedded]
      rw [oddPureScalarAction_self,
        oddPureGhost_scalarAction_cross,
        oddPureGhost_scalarAction_cross,
        oddPureScalarAction_self,
        oddPureGhost_scalarAction_cross,
        oddPureScalarAction_self]
      module

/-- Scalar component of the BRST square for all three odd generators. -/
def threeGeneratorScalarBRSTSquare
    (first second third : Ghost period hPeriod)
    (scalar : Scalar period hPeriod) :
    ExteriorScalarModule period hPeriod :=
  -exteriorGhostScalarAction period hPeriod
      (threeGeneratorNonlinearGhostBRSTTerm period hPeriod
        first second third)
      (exteriorScalarEmbed period hPeriod scalar) -
    exteriorGhostScalarAction period hPeriod
      (threeGeneratorOddGhost period hPeriod first second third)
      (exteriorGhostScalarAction period hPeriod
        (threeGeneratorOddGhost period hPeriod first second third)
        (exteriorScalarEmbed period hPeriod scalar))

@[simp]
theorem threeGeneratorScalarBRSTSquare_zero
    (first second third : Ghost period hPeriod)
    (scalar : Scalar period hPeriod) :
    threeGeneratorScalarBRSTSquare period hPeriod
      first second third scalar = 0 := by
  rw [threeGeneratorScalarBRSTSquare,
    threeGeneratorNonlinearGhostBRSTTerm_eq,
    threeGeneratorOddGhost_scalarAction_sq]
  simp only [map_neg, LinearMap.neg_apply, neg_neg,
    threeGeneratorPairwiseBracket, map_add, LinearMap.add_apply,
    oddPairGhostBracket, oddPureGhost, exteriorGhostBracket_tmul,
    exteriorScalarEmbed, exteriorGhostScalarAction_tmul, mul_one]
  abel

theorem three_generator_scalar_brst4D_closure
    (first second third : Ghost period hPeriod)
    (scalar : Scalar period hPeriod) :
    threeGeneratorNonlinearGhostBRSTTerm period hPeriod first second third =
        -threeGeneratorPairwiseBracket period hPeriod first second third ∧
      exteriorGhostBracket period hPeriod
          (threeGeneratorOddGhost period hPeriod first second third)
          (exteriorGhostBracket period hPeriod
            (threeGeneratorOddGhost period hPeriod first second third)
            (threeGeneratorOddGhost period hPeriod first second third)) = 0 ∧
      threeGeneratorScalarBRSTSquare period hPeriod
        first second third scalar = 0 :=
  ⟨threeGeneratorNonlinearGhostBRSTTerm_eq period hPeriod first second third,
    threeGeneratorOddGhost_nested_jacobi_zero period hPeriod
      first second third,
    threeGeneratorScalarBRSTSquare_zero period hPeriod
      first second third scalar⟩

end

end P0EFTJanusMappingTorusThreeGeneratorScalarBRST4D
end JanusFormal
