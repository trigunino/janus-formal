import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusProjectionKernel4D

/-!
# Compact parameterization of the ambient Pin-minus group

Products of at most four unit normals form a compact subset of the concrete
Pin-minus group.  The remaining algebraic input is a Cartan--Dieudonne
factorization retaining its public length bound.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusCompactness4D

set_option autoImplicit false
noncomputable section

open Set
open CliffordAlgebra
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinEvenReflectionLift
open P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPointwiseTangentLift4D
open P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
open P0EFTJanusMappingTorusAmbientPinMinusProjectionContinuity4D
open P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusProjectionKernel4D

private abbrev AmbientPinMinusHilbert := WithLp 2 CoverCoordinates

private theorem ambientPinMinusQuadraticForm_ofLp_eq_norm_sq
    (vector : AmbientPinMinusHilbert) :
    ambientCoverEuclideanQuadraticForm (WithLp.ofLp vector) =
      ‖vector‖ ^ 2 := by
  rw [ambientCoverEuclideanQuadraticForm_apply,
    WithLp.prod_norm_sq_eq_of_L2]
  simp

/-- The compact unit sphere used to parameterize reflection lifts. -/
abbrev AmbientPinMinusUnitSphere :=
  Metric.sphere (0 : AmbientPinMinusHilbert) 1

private theorem ambientPinMinusUnitSphere_quadratic
    (point : AmbientPinMinusUnitSphere) :
    ambientCoverEuclideanQuadraticForm (WithLp.ofLp point.1) = 1 := by
  rw [ambientPinMinusQuadraticForm_ofLp_eq_norm_sq]
  have hNorm : ‖(point.1 : AmbientPinMinusHilbert)‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using point.property
  rw [hNorm]
  norm_num

/-- Continuous Pin-minus generator carried by a unit-sphere point. -/
def ambientPinMinusSphereGenerator
    (point : AmbientPinMinusUnitSphere) :
    AmbientCoordinatePinMinusGroup :=
  ambientPinMinusUnitNormalGenerator (WithLp.ofLp point.1)
    (ambientPinMinusUnitSphere_quadratic point)

theorem continuous_ambientPinMinusSphereGenerator :
    Continuous ambientPinMinusSphereGenerator := by
  apply continuous_induced_rng.mpr
  change Continuous (fun point : AmbientPinMinusUnitSphere =>
    CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
      (WithLp.ofLp point.1))
  have hOfLp : Continuous
      (fun vector : AmbientPinMinusHilbert => WithLp.ofLp vector) :=
    WithLp.prod_continuous_ofLp 2 (EuclideanSpace Real (Fin 3)) Real
  exact (LinearMap.continuous_of_finiteDimensional
    (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm)).comp
      (hOfLp.comp continuous_subtype_val)

/-- Ordered product of `n` unit-sphere generators. -/
def ambientPinMinusSphereProduct
    {n : Nat} (parameters : Fin n → AmbientPinMinusUnitSphere) :
    AmbientCoordinatePinMinusGroup :=
  (List.ofFn fun index =>
    ambientPinMinusSphereGenerator (parameters index)).prod

theorem continuous_ambientPinMinusSphereProduct
    (n : Nat) :
    Continuous
      (@ambientPinMinusSphereProduct n) := by
  have hContinuous := continuous_list_prod
    (List.ofFn fun index : Fin n => index)
    (fun index _ =>
      continuous_ambientPinMinusSphereGenerator.comp
        (continuous_apply index))
  convert hContinuous using 1
  funext parameters
  exact congrArg List.prod
    (List.ofFn_comp'
      (fun index : Fin n => index)
      (fun index =>
        ambientPinMinusSphereGenerator (parameters index)))

theorem isCompact_range_ambientPinMinusSphereProduct
    (n : Nat) :
    IsCompact
      (Set.range (@ambientPinMinusSphereProduct n)) :=
  isCompact_range (continuous_ambientPinMinusSphereProduct n)

/-- Union of all products containing at most four unit generators. -/
def ambientPinMinusProductsAtMostFour :
    Set AmbientCoordinatePinMinusGroup :=
  ⋃ n : Fin 5, Set.range (@ambientPinMinusSphereProduct n)

theorem isCompact_ambientPinMinusProductsAtMostFour :
    IsCompact ambientPinMinusProductsAtMostFour := by
  exact isCompact_iUnion fun n =>
    isCompact_range_ambientPinMinusSphereProduct n

/-- Compactness follows once every Pin-minus element has a product
parameterization of length at most four. -/
theorem isCompact_univ_of_sphereProduct_le_four
    (hParameterization :
      ∀ lift : AmbientCoordinatePinMinusGroup,
        ∃ n : Fin 5, ∃ parameters : Fin n → AmbientPinMinusUnitSphere,
          ambientPinMinusSphereProduct parameters = lift) :
    IsCompact
      (Set.univ : Set AmbientCoordinatePinMinusGroup) := by
  have hUniv : ambientPinMinusProductsAtMostFour =
      (Set.univ : Set AmbientCoordinatePinMinusGroup) := by
    apply Set.eq_univ_of_forall
    intro lift
    rcases hParameterization lift with ⟨n, parameters, hParameters⟩
    exact Set.mem_iUnion.mpr
      ⟨n, Set.mem_range.mpr ⟨parameters, hParameters⟩⟩
  rw [← hUniv]
  exact isCompact_ambientPinMinusProductsAtMostFour

/-- A unit reflection factor as a point of the compact Hilbert sphere. -/
def ambientUnitReflectionFactorSphere
    (factor : AmbientUnitReflectionFactor) :
    AmbientPinMinusUnitSphere := by
  refine ⟨WithLp.toLp 2 factor.vector, ?_⟩
  rw [mem_sphere_zero_iff_norm]
  have hNormSq :
      ‖WithLp.toLp 2 factor.vector‖ ^ 2 = 1 := by
    rw [← ambientPinMinusQuadraticForm_ofLp_eq_norm_sq]
    exact factor.unit
  nlinarith [norm_nonneg (WithLp.toLp 2 factor.vector)]

@[simp] theorem ambientPinMinusSphereGenerator_factorSphere
    (factor : AmbientUnitReflectionFactor) :
    ambientPinMinusSphereGenerator
        (ambientUnitReflectionFactorSphere factor) =
      ambientUnitReflectionFactorPinMinusLift factor := by
  apply Subtype.ext
  rfl

/-- Sphere parameters canonically extracted from a finite factor list. -/
def ambientUnitReflectionFactorsSphereParameters
    (factors : List AmbientUnitReflectionFactor) :
    Fin factors.length → AmbientPinMinusUnitSphere :=
  fun index => ambientUnitReflectionFactorSphere (factors.get index)

@[simp] theorem ambientPinMinusSphereProduct_factors
    (factors : List AmbientUnitReflectionFactor) :
    ambientPinMinusSphereProduct
        (ambientUnitReflectionFactorsSphereParameters factors) =
      ambientPinMinusLiftOfUnitFactors factors := by
  change
    (List.ofFn fun index : Fin factors.length =>
      ambientUnitReflectionFactorPinMinusLift (factors.get index)).prod =
    (factors.map ambientUnitReflectionFactorPinMinusLift).prod
  rw [List.ofFn_comp']
  simp

/-- Negating the first normal absorbs the nontrivial central kernel sign. -/
def ambientNegUnitReflectionFactor
    (factor : AmbientUnitReflectionFactor) :
    AmbientUnitReflectionFactor where
  vector := -factor.vector
  unit := by simpa using factor.unit

@[simp] theorem ambientPinMinusLift_negUnitReflectionFactor
    (factor : AmbientUnitReflectionFactor) :
    ambientUnitReflectionFactorPinMinusLift
        (ambientNegUnitReflectionFactor factor) =
      ambientPinMinusCentralSign *
        ambientUnitReflectionFactorPinMinusLift factor := by
  simpa [ambientNegUnitReflectionFactor,
    ambientUnitReflectionFactorPinMinusLift] using
      ambientPinMinusUnitNormalGenerator_neg factor.vector factor.unit
        (ambientNegUnitReflectionFactor factor).unit

theorem ambientPinMinusLiftOfUnitFactors_neg_head
    (factor : AmbientUnitReflectionFactor)
    (rest : List AmbientUnitReflectionFactor) :
    ambientPinMinusLiftOfUnitFactors
        (ambientNegUnitReflectionFactor factor :: rest) =
      ambientPinMinusCentralSign *
        ambientPinMinusLiftOfUnitFactors (factor :: rest) := by
  simp [ambientPinMinusLiftOfUnitFactors, mul_assoc]

private def ambientPinMinusReferenceFactor :
    AmbientUnitReflectionFactor where
  vector := ambientPinMinusReferenceVector
  unit := ambientPinMinusReferenceVector_positive_unit

private theorem ambientPinMinusReferenceFactor_lift :
    ambientUnitReflectionFactorPinMinusLift
        ambientPinMinusReferenceFactor =
      ambientPinMinusReferenceGenerator := by
  apply Subtype.ext
  rfl

private theorem ambientPinMinusReferenceFactors_product :
    ambientPinMinusLiftOfUnitFactors
        [ambientPinMinusReferenceFactor, ambientPinMinusReferenceFactor] =
      ambientPinMinusCentralSign := by
  simp [ambientPinMinusLiftOfUnitFactors,
    ambientPinMinusReferenceFactor_lift, ambientPinMinusCentralSign]

/-- Public bounded form of the factorization data needed for compactness. -/
structure AmbientO4UnitReflectionFactorizationLeFour
    (target : AmbientOrthogonalIsometry) where
  factors : List AmbientUnitReflectionFactor
  length_le_four : factors.length ≤ 4
  factorization :
    ambientReflectionProductOfUnitFactors factors = target.toLinearEquiv

/-- A length-bounded Cartan--Dieudonne factorization gives the required
compact sphere parameterization of every Pin-minus element. -/
theorem ambientPinMinus_sphereProduct_le_four_of_boundedCartanDieudonne
    (hCartan :
      ∀ target : AmbientOrthogonalIsometry,
        Nonempty (AmbientO4UnitReflectionFactorizationLeFour target)) :
    ∀ lift : AmbientCoordinatePinMinusGroup,
      ∃ n : Fin 5, ∃ parameters : Fin n → AmbientPinMinusUnitSphere,
        ambientPinMinusSphereProduct parameters = lift := by
  intro lift
  let target := ambientPinMinusOrthogonalProjection lift
  obtain ⟨factorization⟩ := hCartan target
  let factorLift :=
    ambientPinMinusLiftOfUnitFactors factorization.factors
  have hFactorProjection :
      ambientPinMinusProjection factorLift =
        ambientPinMinusProjection lift := by
    calc
      ambientPinMinusProjection factorLift =
          ambientReflectionProductOfUnitFactors factorization.factors :=
        ambientPinMinusProjection_liftOfUnitFactors factorization.factors
      _ = target.toLinearEquiv := factorization.factorization
      _ = ambientPinMinusProjection lift :=
        ambientPinMinusOrthogonalProjection_toLinearEquiv lift
  let residual := lift * factorLift⁻¹
  have hResidualProjection :
      ambientPinMinusProjection residual = 1 := by
    simp [residual, hFactorProjection]
  rcases (ambientPinMinusProjection_eq_one_iff residual).mp
      hResidualProjection with hResidualOne | hResidualSign
  · have hLift : factorLift = lift := by
      have hRight := congrArg
        (fun value : AmbientCoordinatePinMinusGroup =>
          value * factorLift) hResidualOne
      simpa [residual, mul_assoc] using hRight.symm
    let n : Fin 5 :=
      ⟨factorization.factors.length,
        Nat.lt_succ_of_le factorization.length_le_four⟩
    let parameters : Fin n → AmbientPinMinusUnitSphere :=
      ambientUnitReflectionFactorsSphereParameters factorization.factors
    refine ⟨n, parameters, ?_⟩
    simpa [parameters, factorLift] using hLift
  · cases hFactors : factorization.factors with
    | nil =>
        have hLiftSign : lift = ambientPinMinusCentralSign := by
          simpa [residual, factorLift, hFactors,
            ambientPinMinusLiftOfUnitFactors] using hResidualSign
        let referenceFactors :=
          [ambientPinMinusReferenceFactor, ambientPinMinusReferenceFactor]
        let n : Fin 5 := ⟨referenceFactors.length, by decide⟩
        let parameters : Fin n → AmbientPinMinusUnitSphere :=
          ambientUnitReflectionFactorsSphereParameters referenceFactors
        refine ⟨n, parameters, ?_⟩
        rw [show ambientPinMinusSphereProduct parameters =
            ambientPinMinusLiftOfUnitFactors referenceFactors by
          simpa [parameters]]
        exact ambientPinMinusReferenceFactors_product.trans hLiftSign.symm
    | cons factor rest =>
        have hLiftSign :
            ambientPinMinusCentralSign * factorLift = lift := by
          have hRight := congrArg
            (fun value : AmbientCoordinatePinMinusGroup =>
              value * factorLift) hResidualSign
          simpa [residual, mul_assoc] using hRight.symm
        let signedFactors :=
          ambientNegUnitReflectionFactor factor :: rest
        have hSignedLength :
            signedFactors.length ≤ 4 := by
          simpa [signedFactors, hFactors] using factorization.length_le_four
        let n : Fin 5 :=
          ⟨signedFactors.length, Nat.lt_succ_of_le hSignedLength⟩
        let parameters : Fin n → AmbientPinMinusUnitSphere :=
          ambientUnitReflectionFactorsSphereParameters signedFactors
        refine ⟨n, parameters, ?_⟩
        rw [show ambientPinMinusSphereProduct parameters =
            ambientPinMinusLiftOfUnitFactors signedFactors by
          simpa [parameters]]
        rw [ambientPinMinusLiftOfUnitFactors_neg_head]
        simpa [factorLift, signedFactors, hFactors] using hLiftSign

/-- Conditional compactness with the erased Cartan--Dieudonne bound exposed
as the sole remaining input. -/
theorem isCompact_univ_of_boundedCartanDieudonne
    (hCartan :
      ∀ target : AmbientOrthogonalIsometry,
        Nonempty (AmbientO4UnitReflectionFactorizationLeFour target)) :
    IsCompact
      (Set.univ : Set AmbientCoordinatePinMinusGroup) :=
  isCompact_univ_of_sphereProduct_le_four
    (ambientPinMinus_sphereProduct_le_four_of_boundedCartanDieudonne hCartan)

/-- The public D8 Cartan--Dieudonne theorem supplies the retained bound. -/
theorem ambientO4HasUnitReflectionFactorizationLeFour_compactness
    (target : AmbientOrthogonalIsometry) :
    Nonempty (AmbientO4UnitReflectionFactorizationLeFour target) := by
  rcases ambientO4HasUnitReflectionFactorizationLeFour target with
    ⟨factorization, hLength⟩
  exact ⟨{
    factors := factorization.factors
    length_le_four := hLength
    factorization := factorization.factorization }⟩

/-- The concrete ambient Pin-minus group is compact. -/
theorem isCompact_univ_ambientCoordinatePinMinusGroup :
    IsCompact
      (Set.univ : Set AmbientCoordinatePinMinusGroup) :=
  isCompact_univ_of_boundedCartanDieudonne
    ambientO4HasUnitReflectionFactorizationLeFour_compactness

end
end P0EFTJanusMappingTorusAmbientPinMinusCompactness4D
end JanusFormal
