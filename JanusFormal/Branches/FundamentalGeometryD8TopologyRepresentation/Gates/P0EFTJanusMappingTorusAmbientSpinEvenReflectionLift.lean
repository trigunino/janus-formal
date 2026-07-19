import Mathlib.LinearAlgebra.Reflection
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinSurjectivityFrontier

/-!
# Constructive even-reflection lifts into ambient Spin(4)

This gate constructs the part of the `Spin(4) → SO(4)` surjectivity argument
that is available from Mathlib's current Clifford API.  A pair of unit
vectors gives an explicit element of `spinGroup`; its Clifford action is the
product of the two corresponding orthogonal reflections.  Consequently any
finite even-reflection factorization of an ambient special orthogonal map
produces an actual Spin lift.

The remaining input is exactly the Cartan--Dieudonné factorization theorem,
including the determinant parity statement.  Mathlib currently has the
reflection construction but no such generation theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSpinEvenReflectionLift

set_option autoImplicit false

noncomputable section

open CliffordAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinProjection
open P0EFTJanusMappingTorusAmbientSpinSurjectivityFrontier

private abbrev AmbientCliffordAlgebra :=
  CliffordAlgebra ambientCoverEuclideanQuadraticForm

/-- Two unit ambient vectors, hence two consecutive Euclidean reflections. -/
structure AmbientUnitVectorPair where
  first : CoverCoordinates
  second : CoverCoordinates
  first_unit : ambientCoverEuclideanQuadraticForm first = 1
  second_unit : ambientCoverEuclideanQuadraticForm second = 1

/-- The ordinary reflection in the hyperplane orthogonal to a unit vector. -/
def ambientUnitReflection
    (vector : CoverCoordinates)
    (hUnit : ambientCoverEuclideanQuadraticForm vector = 1) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  Module.reflection
    (x := vector)
    (f := ambientCoverEuclideanQuadraticForm.polarBilin vector)
    (by
      simp [hUnit])

/-- One unit Euclidean reflection factor, without an orientation-parity
restriction.  This public wrapper lets the full orthogonal Cartan--Dieudonné
factorization be reused by the ambient Pin-minus projection. -/
structure AmbientUnitReflectionFactor where
  vector : CoverCoordinates
  unit : ambientCoverEuclideanQuadraticForm vector = 1

/-- Orthogonal reflection carried by one unit factor. -/
def AmbientUnitReflectionFactor.reflectionEquiv
    (factor : AmbientUnitReflectionFactor) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  ambientUnitReflection factor.vector factor.unit

/-- Ordered product of an arbitrary finite list of unit reflections. -/
def ambientReflectionProductOfUnitFactors
    (factors : List AmbientUnitReflectionFactor) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  (factors.map AmbientUnitReflectionFactor.reflectionEquiv).prod

/-- A Cartan--Dieudonné factorization of an arbitrary ambient orthogonal
isometry; unlike the Spin factorization below, its length need not be even. -/
structure AmbientO4UnitReflectionFactorization
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) where
  factors : List AmbientUnitReflectionFactor
  factorization :
    ambientReflectionProductOfUnitFactors factors = target.toLinearEquiv

private theorem ambientIotaUnit_mem_lipschitzGroup
    (vector : CoverCoordinates)
    (unit : AmbientCliffordAlgebraˣ)
    (hCoe : (unit : AmbientCliffordAlgebra) =
      CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector) :
    unit ∈ lipschitzGroup ambientCoverEuclideanQuadraticForm := by
  apply Subgroup.subset_closure
  change (unit : AmbientCliffordAlgebra) ∈
    Set.range (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm)
  exact ⟨vector, hCoe.symm⟩

private theorem ambientUnitVectorPair_mem_spinGroup
    (pair : AmbientUnitVectorPair) :
    CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
        CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second ∈
      spinGroup ambientCoverEuclideanQuadraticForm := by
  have hFirstQuadraticUnit :
      IsUnit (ambientCoverEuclideanQuadraticForm pair.first) := by
    rw [pair.first_unit]
    exact isUnit_one
  have hSecondQuadraticUnit :
      IsUnit (ambientCoverEuclideanQuadraticForm pair.second) := by
    rw [pair.second_unit]
    exact isUnit_one
  obtain ⟨firstUnit, hFirstCoe⟩ :=
    CliffordAlgebra.isUnit_ι_of_isUnit
      (Q := ambientCoverEuclideanQuadraticForm) hFirstQuadraticUnit
  obtain ⟨secondUnit, hSecondCoe⟩ :=
    CliffordAlgebra.isUnit_ι_of_isUnit
      (Q := ambientCoverEuclideanQuadraticForm) hSecondQuadraticUnit
  apply spinGroup.mem_iff.mpr
  constructor
  · apply pinGroup.mem_iff.mpr
    constructor
    · apply Submonoid.mem_map.mpr
      refine ⟨firstUnit * secondUnit, ?_, ?_⟩
      · exact mul_mem
          (ambientIotaUnit_mem_lipschitzGroup pair.first
            firstUnit hFirstCoe)
          (ambientIotaUnit_mem_lipschitzGroup pair.second
            secondUnit hSecondCoe)
      · simp only [Units.coeHom_apply, Units.val_mul, hFirstCoe, hSecondCoe]
    · apply Unitary.mem_iff.mpr
      constructor
      · calc
          star
                (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
                  CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second) *
              (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
                CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second) =
              CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second *
                (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
                  CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first) *
                CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second := by
            simp only [star_mul, CliffordAlgebra.star_ι]
            noncomm_ring
          _ = 1 := by
            simp only [CliffordAlgebra.ι_sq_scalar, pair.first_unit,
              pair.second_unit, map_one, mul_one]
      · calc
          (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
                CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second) *
              star
                (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
                  CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second) =
              CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
                (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second *
                  CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second) *
                CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first := by
            simp only [star_mul, CliffordAlgebra.star_ι]
            noncomm_ring
          _ = 1 := by
            simp only [CliffordAlgebra.ι_sq_scalar, pair.first_unit,
              pair.second_unit, map_one, mul_one]
  · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero
      ambientCoverEuclideanQuadraticForm pair.first pair.second

/-- Explicit Spin element represented by the Clifford product of two unit
vectors. -/
def AmbientUnitVectorPair.spinLift
    (pair : AmbientUnitVectorPair) : AmbientCoordinateSpinGroup :=
  ⟨CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
      CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second,
    ambientUnitVectorPair_mem_spinGroup pair⟩

@[simp] theorem AmbientUnitVectorPair.spinLift_coe
    (pair : AmbientUnitVectorPair) :
    (pair.spinLift : AmbientCliffordAlgebra) =
      CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
        CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second :=
  rfl

@[simp] theorem AmbientUnitVectorPair.spinLift_inv_coe
    (pair : AmbientUnitVectorPair) :
    (↑(pair.spinLift⁻¹) : AmbientCliffordAlgebra) =
      CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second *
        CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first := by
  change star
      (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
        CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second) = _
  simp only [star_mul, CliffordAlgebra.star_ι]
  noncomm_ring

/-- Untwisted Clifford conjugation by one unit vector.  It is the negative of
the corresponding hyperplane reflection. -/
def ambientUnitVectorConjugation
    (vector tangent : CoverCoordinates) : CoverCoordinates :=
  QuadraticMap.polar ambientCoverEuclideanQuadraticForm vector tangent • vector - tangent

theorem ambientUnitVectorConjugation_iota
    (vector : CoverCoordinates)
    (hUnit : ambientCoverEuclideanQuadraticForm vector = 1)
    (tangent : CoverCoordinates) :
    CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector =
      CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm
        (ambientUnitVectorConjugation vector tangent) := by
  rw [CliffordAlgebra.ι_mul_ι_mul_ι]
  simp [ambientUnitVectorConjugation, hUnit]

theorem ambientUnitVectorConjugation_eq_neg_reflection
    (vector : CoverCoordinates)
    (hUnit : ambientCoverEuclideanQuadraticForm vector = 1)
    (tangent : CoverCoordinates) :
    ambientUnitVectorConjugation vector tangent =
      -ambientUnitReflection vector hUnit tangent := by
  change QuadraticMap.polar ambientCoverEuclideanQuadraticForm vector tangent • vector - tangent =
    -(tangent -
      QuadraticMap.polar ambientCoverEuclideanQuadraticForm vector tangent • vector)
  exact (neg_sub tangent
    (QuadraticMap.polar ambientCoverEuclideanQuadraticForm vector tangent • vector)).symm

/-- The explicit Clifford pair acts as two consecutive reflections. -/
theorem AmbientUnitVectorPair.spinProjection_apply
    (pair : AmbientUnitVectorPair)
    (tangent : CoverCoordinates) :
    ambientSpinProjection pair.spinLift tangent =
      ambientUnitVectorConjugation pair.first
        (ambientUnitVectorConjugation pair.second tangent) := by
  apply ambientCliffordIota_injective
  rw [ambientSpinProjection_apply, ambientSpinVectorAction_spec]
  rw [pair.spinLift_coe, pair.spinLift_inv_coe]
  calc
    _ = CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
          (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second *
            CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
            CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.second) *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first := by
        noncomm_ring
    _ = CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm
            (ambientUnitVectorConjugation pair.second tangent) *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm pair.first := by
        rw [ambientUnitVectorConjugation_iota pair.second pair.second_unit tangent]
    _ = _ := ambientUnitVectorConjugation_iota pair.first pair.first_unit
      (ambientUnitVectorConjugation pair.second tangent)

/-- Independent reflection-side representative of a pair. -/
def AmbientUnitVectorPair.reflectionEquiv
    (pair : AmbientUnitVectorPair) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  ambientUnitReflection pair.first pair.first_unit *
    ambientUnitReflection pair.second pair.second_unit

@[simp] theorem AmbientUnitVectorPair.spinProjection
    (pair : AmbientUnitVectorPair) :
    ambientSpinProjection pair.spinLift = pair.reflectionEquiv := by
  apply LinearEquiv.ext
  intro tangent
  rw [pair.spinProjection_apply]
  change ambientUnitVectorConjugation pair.first
      (ambientUnitVectorConjugation pair.second tangent) =
    ambientUnitReflection pair.first pair.first_unit
      (ambientUnitReflection pair.second pair.second_unit tangent)
  rw [ambientUnitVectorConjugation_eq_neg_reflection pair.first
    pair.first_unit]
  rw [ambientUnitVectorConjugation_eq_neg_reflection pair.second
    pair.second_unit]
  simp

/-- Clifford product associated with a finite list of reflection pairs. -/
def ambientSpinLiftOfUnitPairs
    (pairs : List AmbientUnitVectorPair) : AmbientCoordinateSpinGroup :=
  (pairs.map AmbientUnitVectorPair.spinLift).prod

/-- The matching product in the ambient linear group. -/
def ambientReflectionProductOfUnitPairs
    (pairs : List AmbientUnitVectorPair) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  (pairs.map AmbientUnitVectorPair.reflectionEquiv).prod

theorem ambientSpinProjection_liftOfUnitPairs
    (pairs : List AmbientUnitVectorPair) :
    ambientSpinProjection (ambientSpinLiftOfUnitPairs pairs) =
      ambientReflectionProductOfUnitPairs pairs := by
  induction pairs with
  | nil => simp [ambientSpinLiftOfUnitPairs,
      ambientReflectionProductOfUnitPairs]
  | cons pair pairs inductionHypothesis =>
      have hTail :
          ambientSpinProjection
              (pairs.map AmbientUnitVectorPair.spinLift).prod =
            (pairs.map AmbientUnitVectorPair.reflectionEquiv).prod := by
        simpa only [ambientSpinLiftOfUnitPairs,
          ambientReflectionProductOfUnitPairs] using inductionHypothesis
      change ambientSpinProjection
          (pair.spinLift * (pairs.map AmbientUnitVectorPair.spinLift).prod) =
        pair.reflectionEquiv *
          (pairs.map AmbientUnitVectorPair.reflectionEquiv).prod
      rw [map_mul, pair.spinProjection, hTail]

/-- A Cartan--Dieudonné witness already grouped into pairs of unit
reflections. -/
structure AmbientSO4EvenReflectionFactorization
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) where
  pairs : List AmbientUnitVectorPair
  factorization :
    ambientReflectionProductOfUnitPairs pairs = target.toLinearEquiv

/-- The factorization has a concrete Clifford Spin lift. -/
def AmbientSO4EvenReflectionFactorization.toSpinLift
    {target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm}
    (factorization : AmbientSO4EvenReflectionFactorization target) :
    AmbientCoordinateSpinGroup :=
  ambientSpinLiftOfUnitPairs factorization.pairs

theorem AmbientSO4EvenReflectionFactorization.projects
    {target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm}
    (factorization : AmbientSO4EvenReflectionFactorization target) :
    ambientSpinProjection factorization.toSpinLift = target.toLinearEquiv :=
  (ambientSpinProjection_liftOfUnitPairs factorization.pairs).trans
    factorization.factorization

/-- Exact remaining finite-dimensional input: every determinant-one ambient
isometry admits an even unit-reflection factorization. -/
def AmbientSO4HasEvenReflectionFactorizations : Prop :=
  ∀ target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm,
    LinearEquiv.det target.toLinearEquiv = (1 : Realˣ) →
      Nonempty (AmbientSO4EvenReflectionFactorization target)

/-- Cartan--Dieudonné with determinant parity now suffices for the actual
Clifford projection's surjectivity. -/
theorem ambientSpinSO4Surjective_of_evenReflectionFactorizations
    (hFactorizations : AmbientSO4HasEvenReflectionFactorizations) :
    AmbientSpinSO4Surjective := by
  intro target hDet
  rcases hFactorizations target hDet with ⟨factorization⟩
  exact ⟨factorization.toSpinLift, factorization.projects⟩

/-- The same finite-dimensional theorem produces the explicit global
pointwise lifting function used by the atlas frontier. -/
def ambientSpinSO4LiftingFunctionOfEvenReflectionFactorizations
    (hFactorizations : AmbientSO4HasEvenReflectionFactorizations) :
    AmbientSpinSO4LiftingFunction :=
  ambientSpinSO4LiftingFunctionOfSurjective
    (ambientSpinSO4Surjective_of_evenReflectionFactorizations hFactorizations)

end

end P0EFTJanusMappingTorusAmbientSpinEvenReflectionLift
end JanusFormal
