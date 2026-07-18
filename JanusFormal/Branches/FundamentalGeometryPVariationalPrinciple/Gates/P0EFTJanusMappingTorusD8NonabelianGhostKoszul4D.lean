import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D

/-!
# Explicit `so(3)` Koszul differential for the D8 rotation ghosts

The Chevalley--Eilenberg rule on the three exterior generators is extended by
the Clifford-algebra recursion principle.  Its odd Leibniz rule and
nilpotence are then proved on the whole coefficient algebra.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostKoszul4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusThreeGeneratorScalarBRST4D
open P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
open P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Ghost := CInfinityDiffeomorphismGhost period hPeriod
private abbrev Coefficient := GhostCoefficientExterior

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem oddVector_eq_coordinates (vector : OddGeneratorSpace) :
    ExteriorAlgebra.ι Real vector =
      vector 0 • oddGenerator 0 + vector 1 • oddGenerator 1 +
        vector 2 • oddGenerator 2 := by
  have hVector : vector =
      vector 0 • oddBasisVector 0 + vector 1 • oddBasisVector 1 +
        vector 2 • oddBasisVector 2 := by
    funext index
    fin_cases index <;> simp [oddBasisVector]
  calc
    ExteriorAlgebra.ι Real vector = ExteriorAlgebra.ι Real
        (vector 0 • oddBasisVector 0 + vector 1 • oddBasisVector 1 +
          vector 2 • oddBasisVector 2) := congrArg _ hVector
    _ = _ := by simp [oddGenerator]

/-- The `so(3)` Chevalley--Eilenberg rule before extension to the exterior
algebra. -/
def spatialRotationGeneratorDifferential :
    OddGeneratorSpace →ₗ[Real] Coefficient where
  toFun vector :=
    vector 0 • (oddGenerator 1 * oddGenerator 2) -
      vector 1 • (oddGenerator 0 * oddGenerator 2) +
        vector 2 • (oddGenerator 0 * oddGenerator 1)
  map_add' first second := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' scalar vector := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul]
    module

@[simp]
private theorem spatialRotationGeneratorDifferential_apply
    (vector : OddGeneratorSpace) :
    spatialRotationGeneratorDifferential vector =
      vector 0 • (oddGenerator 1 * oddGenerator 2) -
        vector 1 • (oddGenerator 0 * oddGenerator 2) +
          vector 2 • (oddGenerator 0 * oddGenerator 1) :=
  rfl

private theorem oddGenerator_commutes_generatorDifferential
    (index : Fin 3) (vector : OddGeneratorSpace) :
    oddGenerator index * spatialRotationGeneratorDifferential vector =
      spatialRotationGeneratorDifferential vector * oddGenerator index := by
  simp only [spatialRotationGeneratorDifferential_apply, mul_add, add_mul,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  rw [oddGenerator_commute_pair 1 2 index,
    oddGenerator_commute_pair 0 2 index,
    oddGenerator_commute_pair 0 1 index]

private theorem generatorDifferential_commutes_vector
    (vector : OddGeneratorSpace) :
    spatialRotationGeneratorDifferential vector *
        ExteriorAlgebra.ι Real vector =
      ExteriorAlgebra.ι Real vector *
        spatialRotationGeneratorDifferential vector := by
  rw [oddVector_eq_coordinates]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [← oddGenerator_commutes_generatorDifferential 0 vector,
    ← oddGenerator_commutes_generatorDifferential 1 vector,
    ← oddGenerator_commutes_generatorDifferential 2 vector]

private theorem generatorDifferential_involute
    (vector : OddGeneratorSpace) :
    CliffordAlgebra.involute
        (spatialRotationGeneratorDifferential vector) =
      spatialRotationGeneratorDifferential vector := by
  simp [spatialRotationGeneratorDifferential,
    oddGenerator]

private theorem generatorDifferential_parity
    (vector : OddGeneratorSpace) :
    ghostCoefficientParity (spatialRotationGeneratorDifferential vector) =
      spatialRotationGeneratorDifferential vector :=
  generatorDifferential_involute vector

@[simp]
private theorem ghostCoefficientParity_oddGenerator (index : Fin 3) :
    ghostCoefficientParity (oddGenerator index) = -oddGenerator index := by
  simp [ghostCoefficientParity, oddGenerator]

private def spatialRotationKoszulStep :
    OddGeneratorSpace →ₗ[Real]
      (Coefficient × Coefficient) →ₗ[Real] Coefficient :=
  LinearMap.mk₂ Real
    (fun vector state =>
      spatialRotationGeneratorDifferential vector * state.1 -
        ExteriorAlgebra.ι Real vector * state.2)
    (by
      intro first second state
      simp only [map_add, add_mul]
      module)
    (by
      intro scalar vector state
      simp only [map_smul, smul_mul_assoc]
      module)
    (by
      intro vector first second
      simp only [Prod.fst_add, Prod.snd_add, mul_add]
      module)
    (by
      intro scalar vector state
      simp [smul_sub])

@[simp]
private theorem spatialRotationKoszulStep_apply
    (vector : OddGeneratorSpace) (state : Coefficient × Coefficient) :
    spatialRotationKoszulStep vector state =
      spatialRotationGeneratorDifferential vector * state.1 -
        ExteriorAlgebra.ι Real vector * state.2 :=
  rfl

private theorem spatialRotationKoszulStep_square
    (vector : OddGeneratorSpace) (coefficient differential : Coefficient) :
    spatialRotationKoszulStep vector
        (ExteriorAlgebra.ι Real vector * coefficient,
          spatialRotationKoszulStep vector (coefficient, differential)) =
      (0 : QuadraticForm Real OddGeneratorSpace) vector • differential := by
  simp only [spatialRotationKoszulStep_apply,
    QuadraticMap.zero_apply, zero_smul]
  change spatialRotationGeneratorDifferential vector *
        (ExteriorAlgebra.ι Real vector * coefficient) -
      ExteriorAlgebra.ι Real vector *
        (spatialRotationGeneratorDifferential vector * coefficient -
          ExteriorAlgebra.ι Real vector * differential) = 0
  rw [mul_sub,
    ← mul_assoc (spatialRotationGeneratorDifferential vector)
      (ExteriorAlgebra.ι Real vector) coefficient,
    ← mul_assoc (ExteriorAlgebra.ι Real vector)
      (spatialRotationGeneratorDifferential vector) coefficient,
    ← mul_assoc (ExteriorAlgebra.ι Real vector)
      (ExteriorAlgebra.ι Real vector) differential,
    generatorDifferential_commutes_vector,
    ExteriorAlgebra.ι_sq_zero]
  simp

/-- Explicit global coefficient differential extending the `so(3)` rule. -/
def spatialRotationKoszulDifferential : Coefficient →ₗ[Real] Coefficient :=
  CliffordAlgebra.foldr'
    (0 : QuadraticForm Real OddGeneratorSpace)
    spatialRotationKoszulStep spatialRotationKoszulStep_square 0

@[simp]
theorem spatialRotationKoszulDifferential_algebraMap (scalar : Real) :
    spatialRotationKoszulDifferential
        (algebraMap Real Coefficient scalar) = 0 := by
  rw [spatialRotationKoszulDifferential,
    CliffordAlgebra.foldr'_algebraMap]
  simp

@[simp]
theorem spatialRotationKoszulDifferential_one :
    spatialRotationKoszulDifferential (1 : Coefficient) = 0 := by
  simpa using spatialRotationKoszulDifferential_algebraMap (1 : Real)

theorem spatialRotationKoszulDifferential_ι_mul
    (vector : OddGeneratorSpace) (coefficient : Coefficient) :
    spatialRotationKoszulDifferential
        (ExteriorAlgebra.ι Real vector * coefficient) =
      spatialRotationGeneratorDifferential vector * coefficient -
        ExteriorAlgebra.ι Real vector *
          spatialRotationKoszulDifferential coefficient := by
  rw [spatialRotationKoszulDifferential,
    CliffordAlgebra.foldr'_ι_mul]
  rfl

@[simp]
theorem spatialRotationKoszulDifferential_ι
    (vector : OddGeneratorSpace) :
    spatialRotationKoszulDifferential (ExteriorAlgebra.ι Real vector) =
      spatialRotationGeneratorDifferential vector := by
  rw [← mul_one (ExteriorAlgebra.ι Real vector),
    spatialRotationKoszulDifferential_ι_mul]
  simp

@[simp]
theorem spatialRotationKoszulDifferential_oddGenerator
    (output : Fin 3) :
    spatialRotationKoszulDifferential (oddGenerator output) =
      (-((2 : Real)⁻¹)) •
        ∑ first : Fin 3, ∑ second : Fin 3,
          spatialRotationStructureConstant first second output •
            (oddGenerator first * oddGenerator second) := by
  have hExplicit : spatialRotationKoszulDifferential (oddGenerator output) =
      spatialRotationGeneratorDifferential (oddBasisVector output) := by
    exact spatialRotationKoszulDifferential_ι (oddBasisVector output)
  fin_cases output
  · rw [hExplicit]
    simp [spatialRotationGeneratorDifferential, oddBasisVector,
      spatialRotationStructureConstant, Fin.sum_univ_succ]
    rw [oddGenerator_anticommute 2 1]
    module
  · rw [hExplicit]
    simp [spatialRotationGeneratorDifferential, oddBasisVector,
      spatialRotationStructureConstant, Fin.sum_univ_succ]
    rw [oddGenerator_anticommute 2 0]
    module
  · rw [hExplicit]
    simp [spatialRotationGeneratorDifferential, oddBasisVector,
      spatialRotationStructureConstant, Fin.sum_univ_succ]
    rw [oddGenerator_anticommute 1 0]
    module

theorem spatialRotationKoszulDifferential_parity_odd
    (coefficient : Coefficient) :
    ghostCoefficientParity
        (spatialRotationKoszulDifferential coefficient) =
      -spatialRotationKoszulDifferential
        (ghostCoefficientParity coefficient) := by
  change CliffordAlgebra.involute
      (spatialRotationKoszulDifferential coefficient) =
    -spatialRotationKoszulDifferential
      (CliffordAlgebra.involute coefficient)
  induction coefficient using CliffordAlgebra.left_induction with
  | algebraMap scalar =>
      simp
  | add first second firstHypothesis secondHypothesis =>
      simp only [map_add, firstHypothesis, secondHypothesis, neg_add]
  | ι_mul coefficient vector hypothesis =>
      simp only [spatialRotationKoszulDifferential_ι_mul,
        map_sub, map_mul, generatorDifferential_involute,
        CliffordAlgebra.involute_ι, hypothesis, neg_mul, map_neg]
      simp

theorem spatialRotationKoszulDifferential_leibniz
    (first second : Coefficient) :
    spatialRotationKoszulDifferential (first * second) =
      spatialRotationKoszulDifferential first * second +
        ghostCoefficientParity first *
          spatialRotationKoszulDifferential second := by
  change spatialRotationKoszulDifferential (first * second) =
    spatialRotationKoszulDifferential first * second +
      CliffordAlgebra.involute first *
        spatialRotationKoszulDifferential second
  induction first using CliffordAlgebra.left_induction with
  | algebraMap scalar =>
      rw [← Algebra.smul_def, map_smul,
        spatialRotationKoszulDifferential_algebraMap]
      simp [Algebra.smul_def]
  | add first third firstHypothesis thirdHypothesis =>
      simp only [add_mul, map_add, firstHypothesis, thirdHypothesis]
      module
  | ι_mul coefficient vector hypothesis =>
      rw [mul_assoc (ExteriorAlgebra.ι Real vector) coefficient second,
        spatialRotationKoszulDifferential_ι_mul,
        hypothesis, spatialRotationKoszulDifferential_ι_mul,
        map_mul, CliffordAlgebra.involute_ι]
      noncomm_ring

@[simp]
private theorem spatialRotationKoszulDifferential_generator_zero :
    spatialRotationKoszulDifferential (oddGenerator 0) =
      oddGenerator 1 * oddGenerator 2 := by
  change spatialRotationKoszulDifferential
      (ExteriorAlgebra.ι Real (oddBasisVector 0)) = _
  rw [spatialRotationKoszulDifferential_ι]
  simp [spatialRotationGeneratorDifferential, oddBasisVector]

@[simp]
private theorem spatialRotationKoszulDifferential_generator_one :
    spatialRotationKoszulDifferential (oddGenerator 1) =
      -(oddGenerator 0 * oddGenerator 2) := by
  change spatialRotationKoszulDifferential
      (ExteriorAlgebra.ι Real (oddBasisVector 1)) = _
  rw [spatialRotationKoszulDifferential_ι]
  simp [spatialRotationGeneratorDifferential, oddBasisVector]

@[simp]
private theorem spatialRotationKoszulDifferential_generator_two :
    spatialRotationKoszulDifferential (oddGenerator 2) =
      oddGenerator 0 * oddGenerator 1 := by
  change spatialRotationKoszulDifferential
      (ExteriorAlgebra.ι Real (oddBasisVector 2)) = _
  rw [spatialRotationKoszulDifferential_ι]
  simp [spatialRotationGeneratorDifferential, oddBasisVector]

private theorem spatialRotationKoszulDifferential_pair_one_two :
    spatialRotationKoszulDifferential
        (oddGenerator 1 * oddGenerator 2) = 0 := by
  rw [spatialRotationKoszulDifferential_leibniz,
    spatialRotationKoszulDifferential_generator_one,
    spatialRotationKoszulDifferential_generator_two,
    ghostCoefficientParity_oddGenerator, neg_mul, neg_mul,
    mul_assoc (oddGenerator 0) (oddGenerator 2) (oddGenerator 2),
    oddGenerator_sq,
    oddGenerator_triple_swap 0 1 1,
    oddGenerator_sq]
  simp

private theorem spatialRotationKoszulDifferential_pair_zero_two :
    spatialRotationKoszulDifferential
        (oddGenerator 0 * oddGenerator 2) = 0 := by
  rw [spatialRotationKoszulDifferential_leibniz,
    spatialRotationKoszulDifferential_generator_zero,
    spatialRotationKoszulDifferential_generator_two,
    ghostCoefficientParity_oddGenerator,
    mul_assoc (oddGenerator 1) (oddGenerator 2) (oddGenerator 2),
    oddGenerator_sq, mul_zero, neg_mul,
    ← mul_assoc (oddGenerator 0) (oddGenerator 0) (oddGenerator 1),
    oddGenerator_sq, zero_mul]
  simp

private theorem spatialRotationKoszulDifferential_pair_zero_one :
    spatialRotationKoszulDifferential
        (oddGenerator 0 * oddGenerator 1) = 0 := by
  rw [spatialRotationKoszulDifferential_leibniz,
    spatialRotationKoszulDifferential_generator_zero,
    spatialRotationKoszulDifferential_generator_one,
    ghostCoefficientParity_oddGenerator,
    ← oddGenerator_commute_pair 1 2 1,
    ← mul_assoc (oddGenerator 1) (oddGenerator 1) (oddGenerator 2),
    oddGenerator_sq, zero_mul, neg_mul, mul_neg,
    ← mul_assoc (oddGenerator 0) (oddGenerator 0) (oddGenerator 2),
    oddGenerator_sq, zero_mul]
  simp

private theorem spatialRotationKoszulDifferential_generatorDifferential
    (vector : OddGeneratorSpace) :
    spatialRotationKoszulDifferential
        (spatialRotationGeneratorDifferential vector) = 0 := by
  simp [spatialRotationGeneratorDifferential,
    spatialRotationKoszulDifferential_pair_one_two,
    spatialRotationKoszulDifferential_pair_zero_two,
    spatialRotationKoszulDifferential_pair_zero_one]

theorem spatialRotationKoszulDifferential_square_zero
    (coefficient : Coefficient) :
    spatialRotationKoszulDifferential
        (spatialRotationKoszulDifferential coefficient) = 0 := by
  induction coefficient using CliffordAlgebra.left_induction with
  | algebraMap scalar => simp
  | add first second firstHypothesis secondHypothesis =>
      simp only [map_add, firstHypothesis, secondHypothesis, add_zero]
  | ι_mul coefficient vector hypothesis =>
      rw [spatialRotationKoszulDifferential_ι_mul, map_sub,
        spatialRotationKoszulDifferential_leibniz,
        spatialRotationKoszulDifferential_generatorDifferential,
        generatorDifferential_parity,
        spatialRotationKoszulDifferential_ι_mul, hypothesis]
      simp

private theorem realization_bracket_zero_one
    (realization : D8SpatialRotationGhostRealization period hPeriod) :
    smoothGhostLieBracket period hPeriod
        (realization.ghosts 0) (realization.ghosts 1) =
      -realization.ghosts 2 := by
  rw [realization.bracket_closure]
  simp [spatialRotationStructureConstant, Fin.sum_univ_succ]

private theorem realization_bracket_zero_two
    (realization : D8SpatialRotationGhostRealization period hPeriod) :
    smoothGhostLieBracket period hPeriod
        (realization.ghosts 0) (realization.ghosts 2) =
      realization.ghosts 1 := by
  rw [realization.bracket_closure]
  simp [spatialRotationStructureConstant, Fin.sum_univ_succ]

private theorem realization_bracket_one_two
    (realization : D8SpatialRotationGhostRealization period hPeriod) :
    smoothGhostLieBracket period hPeriod
        (realization.ghosts 1) (realization.ghosts 2) =
      -realization.ghosts 0 := by
  rw [realization.bracket_closure]
  simp [spatialRotationStructureConstant, Fin.sum_univ_succ]

theorem spatialRotationKoszulDifferential_nonlinear_ghost_rule
    (realization : D8SpatialRotationGhostRealization period hPeriod) :
    TensorProduct.map spatialRotationKoszulDifferential
        (LinearMap.id : Ghost period hPeriod →ₗ[Real] Ghost period hPeriod)
        (threeGeneratorOddGhost period hPeriod
          (realization.ghosts 0) (realization.ghosts 1)
          (realization.ghosts 2)) =
      threeGeneratorNonlinearGhostBRSTTerm period hPeriod
        (realization.ghosts 0) (realization.ghosts 1)
        (realization.ghosts 2) := by
  rw [threeGeneratorNonlinearGhostBRSTTerm_eq]
  simp only [threeGeneratorOddGhost, oddPureGhost, map_add,
    TensorProduct.map_tmul, LinearMap.id_apply,
    spatialRotationKoszulDifferential_generator_zero,
    spatialRotationKoszulDifferential_generator_one,
    spatialRotationKoszulDifferential_generator_two,
    threeGeneratorPairwiseBracket, oddPairGhostBracket_eq]
  rw [realization_bracket_zero_one period hPeriod,
    realization_bracket_zero_two period hPeriod,
    realization_bracket_one_two period hPeriod]
  simp only [TensorProduct.tmul_neg, TensorProduct.neg_tmul]
  abel

/-- Explicit coefficient-side Koszul data for every spatial-rotation
realization. -/
def spatialRotationKoszulCoefficientData
    (realization : D8SpatialRotationGhostRealization period hPeriod) :
    SpatialRotationKoszulCoefficientData period hPeriod realization where
  differential := spatialRotationKoszulDifferential
  parity_odd := spatialRotationKoszulDifferential_parity_odd
  leibniz := spatialRotationKoszulDifferential_leibniz
  square_zero := spatialRotationKoszulDifferential_square_zero
  generator_rule := spatialRotationKoszulDifferential_oddGenerator
  nonlinear_ghost_rule :=
    spatialRotationKoszulDifferential_nonlinear_ghost_rule
      period hPeriod realization

/-- Unconditional coefficient data for the explicit quotient `so(3)`
triple. -/
def unconditionalSpatialRotationKoszulCoefficientData :
    SpatialRotationKoszulCoefficientData period hPeriod
      (unconditionalD8SpatialRotationGhostRealization period hPeriod) :=
  spatialRotationKoszulCoefficientData period hPeriod
    (unconditionalD8SpatialRotationGhostRealization period hPeriod)

/-- The formerly conditional closed three-generator Koszul package. -/
def unconditionalClosedThreeGeneratorGhostKoszulData :
    ClosedThreeGeneratorGhostKoszulData period hPeriod :=
  closedThreeGeneratorGhostKoszulData period hPeriod
    (unconditionalD8SpatialRotationGhostRealization period hPeriod)
    (unconditionalSpatialRotationKoszulCoefficientData period hPeriod)

end

end P0EFTJanusMappingTorusD8NonabelianGhostKoszul4D
end JanusFormal
