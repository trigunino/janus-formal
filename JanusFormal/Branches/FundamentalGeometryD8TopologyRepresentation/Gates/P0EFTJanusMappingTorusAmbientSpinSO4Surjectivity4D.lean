import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.ProdL2
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinEvenReflectionLift

/-!
# Cartan--Dieudonne closure for the ambient Spin(4) projection

Mathlib's finite-dimensional Cartan--Dieudonne theorem factors every real
linear isometry into orthogonal hyperplane reflections.  This gate transports
that theorem through the canonical L2 realization of the ambient coordinate
space, removes zero normals, normalizes all genuine normals, and uses
determinant parity to group them in pairs.  The explicit Clifford construction
therefore gives an unconditional surjectivity theorem for `Spin(4) -> SO(4)`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinSurjectivityFrontier
open P0EFTJanusMappingTorusAmbientSpinEvenReflectionLift

private abbrev AmbientHilbert := WithLp 2 CoverCoordinates

private abbrev ambientHilbertCoordinatesEquiv :
    AmbientHilbert ≃ₗ[Real] CoverCoordinates :=
  WithLp.linearEquiv 2 Real CoverCoordinates

private theorem ambientQuadraticForm_ofLp_eq_norm_sq
    (vector : AmbientHilbert) :
    ambientCoverEuclideanQuadraticForm (WithLp.ofLp vector) =
      ‖vector‖ ^ 2 := by
  rw [ambientCoverEuclideanQuadraticForm_apply,
    WithLp.prod_norm_sq_eq_of_L2]
  simp

private theorem ambientQuadraticPolar_ofLp_eq_two_inner
    (first second : AmbientHilbert) :
    QuadraticMap.polar ambientCoverEuclideanQuadraticForm
        (WithLp.ofLp first) (WithLp.ofLp second) =
      2 * inner Real first second := by
  rw [ambientCoverEuclideanQuadraticForm,
    LinearMap.BilinMap.polar_toQuadraticMap]
  rw [WithLp.prod_inner_apply]
  change
    (inner Real first.fst second.fst + first.snd * second.snd) +
        (inner Real second.fst first.fst + second.snd * first.snd) =
      2 * (inner Real first.fst second.fst +
        inner Real first.snd second.snd)
  rw [real_inner_comm second.fst first.fst]
  simp
  ring

/-- Conjugation from the Hilbert realization back to the project's ambient
coordinate module. -/
private def ambientHilbertConjugation :
    (AmbientHilbert ≃ₗ[Real] AmbientHilbert) →*
      (CoverCoordinates ≃ₗ[Real] CoverCoordinates) where
  toFun isometry :=
    (ambientHilbertCoordinatesEquiv.symm.trans isometry).trans
      ambientHilbertCoordinatesEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro vector
    simp
  map_mul' first second := by
    apply LinearEquiv.ext
    intro vector
    rfl

/-- An ambient quadratic-form isometry becomes an ordinary real linear
isometry on the L2 realization. -/
private def ambientHilbertLinearIsometryEquiv
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) :
    AmbientHilbert ≃ₗᵢ[Real] AmbientHilbert where
  __ := ambientHilbertCoordinatesEquiv.trans
    (target.toLinearEquiv.trans ambientHilbertCoordinatesEquiv.symm)
  norm_map' vector := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [← ambientQuadraticForm_ofLp_eq_norm_sq,
      ← ambientQuadraticForm_ofLp_eq_norm_sq]
    change ambientCoverEuclideanQuadraticForm
        (target (WithLp.ofLp vector)) =
      ambientCoverEuclideanQuadraticForm (WithLp.ofLp vector)
    exact target.map_app (WithLp.ofLp vector)

private theorem ambientHilbertLinearIsometryEquiv_conjugates_to_target
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) :
    ambientHilbertConjugation
        (ambientHilbertLinearIsometryEquiv target).toLinearEquiv =
      target.toLinearEquiv := by
  apply LinearEquiv.ext
  intro vector
  simp [ambientHilbertConjugation,
    ambientHilbertLinearIsometryEquiv]

/-- Transport a Hilbert-space orthogonal map back to the project's ambient
quadratic coordinates. -/
private def ambientQuadraticIsometryOfHilbert
    (isometry : AmbientHilbert ≃ₗᵢ[Real] AmbientHilbert) :
    ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm where
  __ := ambientHilbertConjugation isometry.toLinearEquiv
  map_app' vector := by
    let pulledBack : AmbientHilbert := WithLp.toLp 2 vector
    change ambientCoverEuclideanQuadraticForm
        (WithLp.ofLp (isometry pulledBack)) =
      ambientCoverEuclideanQuadraticForm (WithLp.ofLp pulledBack)
    rw [ambientQuadraticForm_ofLp_eq_norm_sq,
      ambientQuadraticForm_ofLp_eq_norm_sq, isometry.norm_map]

/-- The ambient orthogonal group acts transitively on every nonempty level set
of the positive Euclidean quadratic form. -/
theorem exists_ambientOrthogonalIsometry_map_of_quadratic_eq
    (first second : CoverCoordinates)
    (hQuadratic : ambientCoverEuclideanQuadraticForm first =
      ambientCoverEuclideanQuadraticForm second) :
    ∃ isometry : ambientCoverEuclideanQuadraticForm.IsometryEquiv
        ambientCoverEuclideanQuadraticForm,
      isometry first = second := by
  let firstHilbert : AmbientHilbert := WithLp.toLp 2 first
  let secondHilbert : AmbientHilbert := WithLp.toLp 2 second
  have hNorm : ‖firstHilbert‖ = ‖secondHilbert‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [← ambientQuadraticForm_ofLp_eq_norm_sq,
      ← ambientQuadraticForm_ofLp_eq_norm_sq]
    exact hQuadratic
  let aligningIsometry : AmbientHilbert ≃ₗᵢ[Real] AmbientHilbert :=
    (Real ∙ (firstHilbert - secondHilbert)).orthogonal.reflection
  refine ⟨ambientQuadraticIsometryOfHilbert aligningIsometry, ?_⟩
  change WithLp.ofLp (aligningIsometry firstHilbert) = second
  have hAlign : aligningIsometry firstHilbert = secondHilbert := by
    exact Submodule.reflection_sub hNorm
  rw [hAlign]

private structure AmbientUnitVector where
  hilbertVector : AmbientHilbert
  norm_sq : ‖hilbertVector‖ ^ 2 = 1

private def AmbientUnitVector.vector
    (unitVector : AmbientUnitVector) : CoverCoordinates :=
  WithLp.ofLp unitVector.hilbertVector

private theorem AmbientUnitVector.unit
    (unitVector : AmbientUnitVector) :
    ambientCoverEuclideanQuadraticForm unitVector.vector = 1 :=
  (ambientQuadraticForm_ofLp_eq_norm_sq
    unitVector.hilbertVector).trans unitVector.norm_sq

private def AmbientUnitVector.reflectionEquiv
    (unitVector : AmbientUnitVector) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  ambientUnitReflection unitVector.vector unitVector.unit

private def AmbientUnitVector.toReflectionFactor
    (unitVector : AmbientUnitVector) : AmbientUnitReflectionFactor where
  vector := unitVector.vector
  unit := unitVector.unit

private theorem ambientHilbertUnitReflection_conjugates
    (vector : AmbientHilbert) (hNormSq : ‖vector‖ ^ 2 = 1) :
    ambientHilbertConjugation
        (((Real ∙ vector).orthogonal.reflection).toLinearEquiv) =
      ambientUnitReflection (WithLp.ofLp vector)
        ((ambientQuadraticForm_ofLp_eq_norm_sq vector).trans hNormSq) := by
  apply LinearEquiv.ext
  intro tangent
  let pulledBack : AmbientHilbert := WithLp.toLp 2 tangent
  change WithLp.ofLp
      ((Real ∙ vector).orthogonal.reflection pulledBack) =
    tangent -
      QuadraticMap.polar ambientCoverEuclideanQuadraticForm
        (WithLp.ofLp vector) tangent • WithLp.ofLp vector
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  have hPulledBack : WithLp.ofLp pulledBack = tangent := rfl
  have hNorm : ‖vector‖ = 1 := by
    nlinarith [norm_nonneg vector]
  rw [← hPulledBack,
    ambientQuadraticPolar_ofLp_eq_two_inner]
  simp only [hNorm, RCLike.ofReal_one, one_pow, div_one]
  change
    -(2 • inner Real vector pulledBack • WithLp.ofLp vector -
        WithLp.ofLp pulledBack) =
      WithLp.ofLp pulledBack -
        (2 * inner Real vector pulledBack) • WithLp.ofLp vector
  module

private def normalizedAmbientUnitVector
    (vector : AmbientHilbert) (hVector : vector ≠ 0) :
    AmbientUnitVector where
  hilbertVector := ‖vector‖⁻¹ • vector
  norm_sq := by
    have hNorm : ‖vector‖ ≠ 0 := norm_ne_zero_iff.mpr hVector
    rw [norm_smul]
    simp [hNorm]

private theorem normalizedAmbientUnitVector_reflection
    (vector : AmbientHilbert) (hVector : vector ≠ 0) :
    ambientHilbertConjugation
        (((Real ∙ vector).orthogonal.reflection).toLinearEquiv) =
      (normalizedAmbientUnitVector vector hVector).reflectionEquiv := by
  have hNorm : ‖vector‖ ≠ 0 := norm_ne_zero_iff.mpr hVector
  have hSpan :
      Real ∙ (‖vector‖⁻¹ • vector) = Real ∙ vector :=
    Submodule.span_singleton_smul_eq
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hNorm)) vector
  calc
    ambientHilbertConjugation
        (((Real ∙ vector).orthogonal.reflection).toLinearEquiv) =
        ambientHilbertConjugation
          (((Real ∙ (normalizedAmbientUnitVector vector hVector).hilbertVector).orthogonal.reflection).toLinearEquiv) := by
      exact congrArg
        (fun subspace : Submodule Real AmbientHilbert =>
          ambientHilbertConjugation
            (subspace.orthogonal.reflection.toLinearEquiv))
        hSpan.symm
    _ = (normalizedAmbientUnitVector vector hVector).reflectionEquiv :=
      ambientHilbertUnitReflection_conjugates
        (normalizedAmbientUnitVector vector hVector).hilbertVector
        (normalizedAmbientUnitVector vector hVector).norm_sq

private theorem ambientHilbertZeroReflection_conjugates :
    ambientHilbertConjugation
        (((Real ∙ (0 : AmbientHilbert)).orthogonal.reflection).toLinearEquiv) =
      1 := by
  have hReflection :
      (((Real ∙ (0 : AmbientHilbert)).orthogonal.reflection).toLinearEquiv) =
        1 := by
    apply LinearEquiv.ext
    intro vector
    exact Submodule.reflection_mem_subspace_eq_self (by simp)
  rw [hReflection]
  exact map_one ambientHilbertConjugation

/-- Remove zero Cartan--Dieudonne vectors and normalize all genuine
reflection normals. -/
private def ambientUnitFactors :
    List AmbientHilbert → List AmbientUnitVector
  | [] => []
  | vector :: rest =>
      if hVector : vector = 0 then
        ambientUnitFactors rest
      else
        normalizedAmbientUnitVector vector hVector :: ambientUnitFactors rest

private theorem ambientUnitFactors_reflectionProduct :
    ∀ vectors : List AmbientHilbert,
      ((ambientUnitFactors vectors).map
        AmbientUnitVector.reflectionEquiv).prod =
      (vectors.map fun vector =>
        ambientHilbertConjugation
          (((Real ∙ vector).orthogonal.reflection).toLinearEquiv)).prod
  | [] => by simp [ambientUnitFactors]
  | vector :: rest => by
      by_cases hVector : vector = 0
      · subst vector
        rw [ambientUnitFactors, dif_pos rfl]
        simp only [List.map_cons, List.prod_cons]
        rw [ambientHilbertZeroReflection_conjugates, one_mul,
          ambientUnitFactors_reflectionProduct rest]
      · simp [ambientUnitFactors, hVector,
          normalizedAmbientUnitVector_reflection vector hVector,
          ambientUnitFactors_reflectionProduct rest]

private theorem AmbientUnitVector.hilbertVector_ne_zero
    (unitVector : AmbientUnitVector) : unitVector.hilbertVector ≠ 0 := by
  intro hZero
  have hNormSq := unitVector.norm_sq
  rw [hZero] at hNormSq
  simp at hNormSq

private theorem AmbientUnitVector.sourceReflection
    (unitVector : AmbientUnitVector) :
    ambientHilbertConjugation
        (((Real ∙ unitVector.hilbertVector).orthogonal.reflection).toLinearEquiv) =
      unitVector.reflectionEquiv :=
  ambientHilbertUnitReflection_conjugates
    unitVector.hilbertVector unitVector.norm_sq

private theorem AmbientUnitVector.det_reflectionEquiv
    (unitVector : AmbientUnitVector) :
    LinearEquiv.det unitVector.reflectionEquiv = (-1 : Realˣ) := by
  rw [← unitVector.sourceReflection]
  change LinearEquiv.det
      ((ambientHilbertCoordinatesEquiv.symm.trans
        (((Real ∙ unitVector.hilbertVector).orthogonal.reflection).toLinearEquiv)).trans
          ambientHilbertCoordinatesEquiv) = _
  rw [LinearEquiv.det_conj,
    Submodule.linearEquiv_det_reflection,
    Submodule.orthogonal_orthogonal,
    finrank_span_singleton unitVector.hilbertVector_ne_zero]
  simp

private theorem ambientUnitReflectionProduct_det :
    ∀ unitVectors : List AmbientUnitVector,
      LinearEquiv.det
          ((unitVectors.map AmbientUnitVector.reflectionEquiv).prod) =
        (-1 : Realˣ) ^ unitVectors.length
  | [] => by simp
  | unitVector :: rest => by
      simp [unitVector.det_reflectionEquiv,
        ambientUnitReflectionProduct_det rest, pow_succ]

private def AmbientUnitVector.pair
    (first second : AmbientUnitVector) : AmbientUnitVectorPair where
  first := first.vector
  second := second.vector
  first_unit := first.unit
  second_unit := second.unit

private def pairAmbientUnitVectors :
    List AmbientUnitVector → List AmbientUnitVectorPair
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      first.pair second :: pairAmbientUnitVectors rest

private theorem pairAmbientUnitVectors_reflectionProduct :
    ∀ unitVectors : List AmbientUnitVector,
      Even unitVectors.length →
        ambientReflectionProductOfUnitPairs
            (pairAmbientUnitVectors unitVectors) =
          (unitVectors.map AmbientUnitVector.reflectionEquiv).prod
  | [], _ => by
      simp [pairAmbientUnitVectors, ambientReflectionProductOfUnitPairs]
  | [unitVector], hEven => by
      rcases hEven with ⟨half, hHalf⟩
      simp only [List.length_cons, List.length_nil] at hHalf
      omega
  | first :: second :: rest, hEven => by
      have hRestEven : Even rest.length := by
        rcases hEven with ⟨half, hHalf⟩
        refine ⟨half - 1, ?_⟩
        simp only [List.length_cons] at hHalf
        omega
      rw [pairAmbientUnitVectors,
        ambientReflectionProductOfUnitPairs]
      change
        (first.pair second).reflectionEquiv *
            ambientReflectionProductOfUnitPairs
              (pairAmbientUnitVectors rest) =
          first.reflectionEquiv *
            (second.reflectionEquiv *
              (rest.map AmbientUnitVector.reflectionEquiv).prod)
      rw [pairAmbientUnitVectors_reflectionProduct rest hRestEven]
      change
        (first.reflectionEquiv * second.reflectionEquiv) *
            (rest.map AmbientUnitVector.reflectionEquiv).prod =
          first.reflectionEquiv *
            (second.reflectionEquiv *
              (rest.map AmbientUnitVector.reflectionEquiv).prod)
      rw [mul_assoc]

private theorem linearIsometryListProd_toLinearEquiv
    (isometries : List (AmbientHilbert ≃ₗᵢ[Real] AmbientHilbert)) :
    isometries.prod.toLinearEquiv =
      (isometries.map fun isometry => isometry.toLinearEquiv).prod := by
  induction isometries with
  | nil => rfl
  | cons isometry rest inductionHypothesis =>
      change (isometry * rest.prod).toLinearEquiv =
        isometry.toLinearEquiv *
          (rest.map fun next => next.toLinearEquiv).prod
      rw [← inductionHypothesis]
      rfl

/-- Cartan--Dieudonné gives a finite unit-reflection factorization for every
ambient orthogonal isometry, with no determinant or orientation restriction. -/
theorem ambientO4HasUnitReflectionFactorization
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) :
    Nonempty (AmbientO4UnitReflectionFactorization target) := by
  obtain ⟨vectors, _, hReflections⟩ :=
    (ambientHilbertLinearIsometryEquiv target).reflections_generate_dim
  let unitVectors := ambientUnitFactors vectors
  have hHilbertProduct :
      (vectors.map fun vector =>
          ((Real ∙ vector).orthogonal.reflection).toLinearEquiv).prod =
        (ambientHilbertLinearIsometryEquiv target).toLinearEquiv := by
    have hReflectionsLinear := congrArg
      (fun isometry : AmbientHilbert ≃ₗᵢ[Real] AmbientHilbert =>
        isometry.toLinearEquiv) hReflections
    rw [linearIsometryListProd_toLinearEquiv] at hReflectionsLinear
    simpa only [List.map_map, Function.comp_def] using
      hReflectionsLinear.symm
  have hOrthogonalProduct :
      (vectors.map fun vector =>
          ambientHilbertConjugation
            (((Real ∙ vector).orthogonal.reflection).toLinearEquiv)).prod =
        target.toLinearEquiv := by
    calc
      _ = ambientHilbertConjugation
          ((vectors.map fun vector =>
            ((Real ∙ vector).orthogonal.reflection).toLinearEquiv).prod) := by
          simpa only [List.map_map, Function.comp_def] using
            (map_list_prod ambientHilbertConjugation
              (vectors.map fun vector =>
                ((Real ∙ vector).orthogonal.reflection).toLinearEquiv)).symm
      _ = target.toLinearEquiv := by
        rw [hHilbertProduct,
          ambientHilbertLinearIsometryEquiv_conjugates_to_target]
  have hUnitProduct :
      (unitVectors.map AmbientUnitVector.reflectionEquiv).prod =
        target.toLinearEquiv :=
    (ambientUnitFactors_reflectionProduct vectors).trans hOrthogonalProduct
  refine ⟨{
    factors := unitVectors.map AmbientUnitVector.toReflectionFactor
    factorization := ?_ }⟩
  rw [ambientReflectionProductOfUnitFactors, List.map_map]
  have hMap :
      unitVectors.map
          (AmbientUnitReflectionFactor.reflectionEquiv ∘
            AmbientUnitVector.toReflectionFactor) =
        unitVectors.map AmbientUnitVector.reflectionEquiv := by
    apply List.map_congr_left
    intro unitVector _
    apply LinearEquiv.ext
    intro tangent
    rfl
  rw [hMap]
  exact hUnitProduct

/-- Cartan--Dieudonne and determinant parity supply the exact finite input
required by the explicit even-reflection Clifford lift. -/
theorem ambientSO4HasEvenReflectionFactorizations :
    AmbientSO4HasEvenReflectionFactorizations := by
  intro target hDet
  obtain ⟨vectors, _, hReflections⟩ :=
    (ambientHilbertLinearIsometryEquiv target).reflections_generate_dim
  let unitVectors := ambientUnitFactors vectors
  have hHilbertProduct :
      (vectors.map fun vector =>
          ((Real ∙ vector).orthogonal.reflection).toLinearEquiv).prod =
        (ambientHilbertLinearIsometryEquiv target).toLinearEquiv := by
    have hReflectionsLinear := congrArg
      (fun isometry : AmbientHilbert ≃ₗᵢ[Real] AmbientHilbert =>
        isometry.toLinearEquiv) hReflections
    rw [linearIsometryListProd_toLinearEquiv] at hReflectionsLinear
    simpa only [List.map_map, Function.comp_def] using
      hReflectionsLinear.symm
  have hOrthogonalProduct :
      (vectors.map fun vector =>
          ambientHilbertConjugation
            (((Real ∙ vector).orthogonal.reflection).toLinearEquiv)).prod =
        target.toLinearEquiv := by
    calc
      _ = ambientHilbertConjugation
          ((vectors.map fun vector =>
            ((Real ∙ vector).orthogonal.reflection).toLinearEquiv).prod) := by
          simpa only [List.map_map, Function.comp_def] using
            (map_list_prod ambientHilbertConjugation
              (vectors.map fun vector =>
                ((Real ∙ vector).orthogonal.reflection).toLinearEquiv)).symm
      _ = target.toLinearEquiv := by
        rw [hHilbertProduct,
          ambientHilbertLinearIsometryEquiv_conjugates_to_target]
  have hUnitProduct :
      (unitVectors.map AmbientUnitVector.reflectionEquiv).prod =
        target.toLinearEquiv := by
    exact (ambientUnitFactors_reflectionProduct vectors).trans
      hOrthogonalProduct
  have hEven : Even unitVectors.length := by
    apply (neg_one_pow_eq_one_iff_even
      (by norm_num : (-1 : Realˣ) ≠ 1)).mp
    rw [← ambientUnitReflectionProduct_det, hUnitProduct, hDet]
  refine ⟨⟨pairAmbientUnitVectors unitVectors, ?_⟩⟩
  exact (pairAmbientUnitVectors_reflectionProduct unitVectors hEven).trans
    hUnitProduct

/-- The explicit Clifford projection `Spin(4) -> SO(4)` is surjective. -/
theorem ambientSpinSO4Surjective : AmbientSpinSO4Surjective :=
  ambientSpinSO4Surjective_of_evenReflectionFactorizations
    ambientSO4HasEvenReflectionFactorizations

/-- Pointwise lifting function obtained by classical choice from the proved
surjectivity theorem. -/
def ambientSpinSO4LiftingFunction : AmbientSpinSO4LiftingFunction :=
  ambientSpinSO4LiftingFunctionOfEvenReflectionFactorizations
    ambientSO4HasEvenReflectionFactorizations

end

end P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D
end JanusFormal
