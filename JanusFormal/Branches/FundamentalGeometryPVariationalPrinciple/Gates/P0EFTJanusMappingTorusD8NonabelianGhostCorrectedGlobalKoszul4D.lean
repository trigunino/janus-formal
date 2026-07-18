import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostKoszul4D

/-!
# Sign-corrected global Koszul differential for the D8 rotation ghosts

The historical candidate uses `D ⊗ id - action`.  The already proved scalar
closure instead fixes the coherent total differential to be
`D ⊗ id + action`.  This gate keeps the old API intact and packages the
corrected convention separately.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostCorrectedGlobalKoszul4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusExteriorScalarBRSTDerivation4D
open P0EFTJanusMappingTorusThreeGeneratorScalarBRST4D
open P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostKoszul4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Ghost := CInfinityDiffeomorphismGhost period hPeriod
private abbrev Scalar := CInfinityScalarField period hPeriod
private abbrev Coefficient := GhostCoefficientExterior
private abbrev Total := ThreeGeneratorExteriorScalarAlgebra period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem exterior_ι_supercommute
    (vector : OddGeneratorSpace) (coefficient : Coefficient) :
    ExteriorAlgebra.ι Real vector * coefficient =
      CliffordAlgebra.involute coefficient *
        ExteriorAlgebra.ι Real vector := by
  induction coefficient using CliffordAlgebra.left_induction with
  | algebraMap scalar =>
      simp [Algebra.commutes]
  | add first second firstHypothesis secondHypothesis =>
      simp only [mul_add, map_add, firstHypothesis, secondHypothesis,
        add_mul]
  | ι_mul coefficient secondVector hypothesis =>
      have hAnti :
          ExteriorAlgebra.ι Real vector *
              ExteriorAlgebra.ι Real secondVector =
            -(ExteriorAlgebra.ι Real secondVector *
              ExteriorAlgebra.ι Real vector) :=
        eq_neg_of_add_eq_zero_left
          (ExteriorAlgebra.ι_add_mul_swap
            (R := Real) vector secondVector)
      calc
        ExteriorAlgebra.ι Real vector *
            (ExteriorAlgebra.ι Real secondVector * coefficient) =
          (ExteriorAlgebra.ι Real vector *
              ExteriorAlgebra.ι Real secondVector) * coefficient := by
            rw [mul_assoc]
        _ = (-(ExteriorAlgebra.ι Real secondVector *
              ExteriorAlgebra.ι Real vector)) * coefficient := by
            rw [hAnti]
        _ = -(ExteriorAlgebra.ι Real secondVector *
              (ExteriorAlgebra.ι Real vector * coefficient)) := by
            simp only [neg_mul, mul_assoc]
        _ = -(ExteriorAlgebra.ι Real secondVector *
              (CliffordAlgebra.involute coefficient *
                ExteriorAlgebra.ι Real vector)) := by
            rw [hypothesis]
        _ = CliffordAlgebra.involute
              (ExteriorAlgebra.ι Real secondVector * coefficient) *
                ExteriorAlgebra.ι Real vector := by
            rw [map_mul, CliffordAlgebra.involute_ι]
            simp only [neg_mul, mul_assoc]

@[simp]
private theorem ghostCoefficientParity_oddGenerator_local
    (index : Fin 3) :
    ghostCoefficientParity (oddGenerator index) = -oddGenerator index := by
  simp [ghostCoefficientParity, oddGenerator]

private theorem oddGenerator_supercommute
    (index : Fin 3) (coefficient : Coefficient) :
    oddGenerator index * coefficient =
      ghostCoefficientParity coefficient * oddGenerator index :=
  exterior_ι_supercommute (oddBasisVector index) coefficient

private theorem cInfinityScalarLieDerivative_one
    (ghost : Ghost period hPeriod) :
    cInfinityScalarLieDerivative period hPeriod ghost
        (1 : Scalar period hPeriod) = 0 := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv coverModelWithCorners
      (fun _ : EffectiveQuotient period hPeriod => (1 : Real))
      point (ghost point) = 0
  rw [mvfderiv_const]
  rfl

/-- The sign-corrected total map. -/
def correctedCombinedLinear
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) :
    Total period hPeriod →ₗ[Real] Total period hPeriod :=
  TensorProduct.map data.coefficientDifferential
      (LinearMap.id : Scalar period hPeriod →ₗ[Real] Scalar period hPeriod) +
    exteriorGhostScalarAction period hPeriod
      (data.universalGhost period hPeriod)

theorem correctedCombinedLinear_eq_legacy_add_two_actions
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) :
    correctedCombinedLinear period hPeriod data =
      data.combinedLinear period hPeriod +
        (2 : Real) • exteriorGhostScalarAction period hPeriod
          (data.universalGhost period hPeriod) := by
  rw [two_smul]
  ext element
  simp [correctedCombinedLinear,
    ClosedThreeGeneratorGhostKoszulData.combinedLinear]

@[simp]
private theorem correctedCombinedLinear_tmul
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (coefficient : Coefficient) (scalar : Scalar period hPeriod) :
    correctedCombinedLinear period hPeriod data
        (coefficient ⊗ₜ[Real] scalar) =
      data.coefficientDifferential coefficient ⊗ₜ[Real] scalar +
        (oddGenerator 0 * coefficient) ⊗ₜ[Real]
            cInfinityScalarLieDerivative period hPeriod (data.ghosts 0) scalar +
        (oddGenerator 1 * coefficient) ⊗ₜ[Real]
            cInfinityScalarLieDerivative period hPeriod (data.ghosts 1) scalar +
        (oddGenerator 2 * coefficient) ⊗ₜ[Real]
            cInfinityScalarLieDerivative period hPeriod (data.ghosts 2) scalar := by
  simp [correctedCombinedLinear,
    ClosedThreeGeneratorGhostKoszulData.universalGhost,
    threeGeneratorOddGhost, oddPureGhost,
    exteriorGhostScalarAction_tmul]
  abel

private theorem correctedCombinedLinear_parity_tmul
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (coefficient : Coefficient) (scalar : Scalar period hPeriod) :
    threeGeneratorExteriorScalarParity period hPeriod
        (correctedCombinedLinear period hPeriod data
          (coefficient ⊗ₜ[Real] scalar)) =
      -correctedCombinedLinear period hPeriod data
        (ghostCoefficientParity coefficient ⊗ₜ[Real] scalar) := by
  rw [correctedCombinedLinear_tmul, map_add, map_add, map_add,
    threeGeneratorExteriorScalarParity_tmul,
    threeGeneratorExteriorScalarParity_tmul,
    threeGeneratorExteriorScalarParity_tmul,
    threeGeneratorExteriorScalarParity_tmul,
    data.coefficient_parity_odd,
    correctedCombinedLinear_tmul]
  simp only [map_mul, ghostCoefficientParity_oddGenerator_local,
    neg_mul, TensorProduct.neg_tmul, neg_add_rev]
  abel

theorem correctedCombinedLinear_parity_odd
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (element : Total period hPeriod) :
    threeGeneratorExteriorScalarParity period hPeriod
        (correctedCombinedLinear period hPeriod data element) =
      -correctedCombinedLinear period hPeriod data
        (threeGeneratorExteriorScalarParity period hPeriod element) := by
  induction element using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient scalar =>
      rw [threeGeneratorExteriorScalarParity_tmul]
      exact correctedCombinedLinear_parity_tmul
        period hPeriod data coefficient scalar
  | add first second firstHypothesis secondHypothesis =>
      simp only [map_add, firstHypothesis, secondHypothesis, neg_add]

private theorem correctedCombinedLinear_leibniz_tmul
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (firstCoefficient secondCoefficient : Coefficient)
    (firstScalar secondScalar : Scalar period hPeriod) :
    correctedCombinedLinear period hPeriod data
        ((firstCoefficient ⊗ₜ[Real] firstScalar) *
          (secondCoefficient ⊗ₜ[Real] secondScalar)) =
      correctedCombinedLinear period hPeriod data
          (firstCoefficient ⊗ₜ[Real] firstScalar) *
            (secondCoefficient ⊗ₜ[Real] secondScalar) +
        threeGeneratorExteriorScalarParity period hPeriod
            (firstCoefficient ⊗ₜ[Real] firstScalar) *
          correctedCombinedLinear period hPeriod data
            (secondCoefficient ⊗ₜ[Real] secondScalar) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    correctedCombinedLinear_tmul,
    data.coefficient_leibniz,
    cInfinityScalarLieDerivative_mul,
    cInfinityScalarLieDerivative_mul,
    cInfinityScalarLieDerivative_mul,
    correctedCombinedLinear_tmul,
    correctedCombinedLinear_tmul,
    threeGeneratorExteriorScalarParity_tmul]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
    add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul]
  rw [← mul_assoc (ghostCoefficientParity firstCoefficient)
      (oddGenerator 0) secondCoefficient,
    ← mul_assoc (ghostCoefficientParity firstCoefficient)
      (oddGenerator 1) secondCoefficient,
    ← mul_assoc (ghostCoefficientParity firstCoefficient)
      (oddGenerator 2) secondCoefficient,
    ← oddGenerator_supercommute 0 firstCoefficient,
    ← oddGenerator_supercommute 1 firstCoefficient,
    ← oddGenerator_supercommute 2 firstCoefficient]
  simp only [mul_assoc]
  module

theorem correctedCombinedLinear_leibniz
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (first second : Total period hPeriod) :
    correctedCombinedLinear period hPeriod data (first * second) =
      correctedCombinedLinear period hPeriod data first * second +
        threeGeneratorExteriorScalarParity period hPeriod first *
          correctedCombinedLinear period hPeriod data second := by
  induction first using TensorProduct.induction_on with
  | zero => simp
  | tmul firstCoefficient firstScalar =>
      induction second using TensorProduct.induction_on with
      | zero => simp
      | tmul secondCoefficient secondScalar =>
          exact correctedCombinedLinear_leibniz_tmul period hPeriod data
            firstCoefficient secondCoefficient firstScalar secondScalar
      | add second third secondHypothesis thirdHypothesis =>
          simp only [mul_add, map_add, secondHypothesis, thirdHypothesis]
          module
  | add first third firstHypothesis thirdHypothesis =>
      simp only [add_mul, map_add, firstHypothesis, thirdHypothesis]
      module

private theorem tensorDifferential_action_embed
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (ghost : ExteriorDiffeomorphismGhostModule period hPeriod)
    (scalar : Scalar period hPeriod) :
    TensorProduct.map data.coefficientDifferential
        (LinearMap.id : Scalar period hPeriod →ₗ[Real] Scalar period hPeriod)
        (exteriorGhostScalarAction period hPeriod ghost
          ((1 : Coefficient) ⊗ₜ[Real] scalar)) =
      exteriorGhostScalarAction period hPeriod
        (TensorProduct.map data.coefficientDifferential
          (LinearMap.id : Ghost period hPeriod →ₗ[Real] Ghost period hPeriod)
          ghost)
        ((1 : Coefficient) ⊗ₜ[Real] scalar) := by
  induction ghost using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient vector =>
      simp [exteriorGhostScalarAction_tmul]
  | add first second firstHypothesis secondHypothesis =>
      simp only [map_add, LinearMap.add_apply, firstHypothesis,
        secondHypothesis]

private theorem correctedCombinedLinear_square_on_coefficients
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (coefficient : Coefficient) :
    correctedCombinedLinear period hPeriod data
        (correctedCombinedLinear period hPeriod data
          (coefficient ⊗ₜ[Real] (1 : Scalar period hPeriod))) = 0 := by
  simp [correctedCombinedLinear_tmul,
    cInfinityScalarLieDerivative_one period hPeriod,
    data.coefficient_square_zero]

private theorem coefficientDifferential_one
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) :
    data.coefficientDifferential (1 : Coefficient) = 0 := by
  have h := data.coefficient_leibniz (1 : Coefficient) (1 : Coefficient)
  simp only [one_mul, mul_one, map_one] at h
  have hZero := congrArg
    (fun value => value - data.coefficientDifferential (1 : Coefficient)) h
  simpa only [sub_self, add_sub_cancel_right] using hZero.symm

private theorem correctedCombinedLinear_on_scalar
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (scalar : Scalar period hPeriod) :
    correctedCombinedLinear period hPeriod data
        ((1 : Coefficient) ⊗ₜ[Real] scalar) =
      exteriorGhostScalarAction period hPeriod
        (data.universalGhost period hPeriod)
        ((1 : Coefficient) ⊗ₜ[Real] scalar) := by
  simp [correctedCombinedLinear,
    coefficientDifferential_one period hPeriod data]

private theorem correctedCombinedLinear_square_on_scalars
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (scalar : Scalar period hPeriod) :
    correctedCombinedLinear period hPeriod data
        (correctedCombinedLinear period hPeriod data
          ((1 : Coefficient) ⊗ₜ[Real] scalar)) = 0 := by
  rw [correctedCombinedLinear_on_scalar]
  change (TensorProduct.map data.coefficientDifferential
        (LinearMap.id : Scalar period hPeriod →ₗ[Real] Scalar period hPeriod) +
      exteriorGhostScalarAction period hPeriod
        (data.universalGhost period hPeriod))
      (exteriorGhostScalarAction period hPeriod
        (data.universalGhost period hPeriod)
        ((1 : Coefficient) ⊗ₜ[Real] scalar)) = 0
  rw [LinearMap.add_apply,
    tensorDifferential_action_embed period hPeriod data]
  change exteriorGhostScalarAction period hPeriod
        (TensorProduct.map data.coefficientDifferential
          (LinearMap.id : Ghost period hPeriod →ₗ[Real] Ghost period hPeriod)
          (threeGeneratorOddGhost period hPeriod
            (data.ghosts 0) (data.ghosts 1) (data.ghosts 2)))
        ((1 : Coefficient) ⊗ₜ[Real] scalar) +
      exteriorGhostScalarAction period hPeriod
        (threeGeneratorOddGhost period hPeriod
          (data.ghosts 0) (data.ghosts 1) (data.ghosts 2))
        (exteriorGhostScalarAction period hPeriod
          (threeGeneratorOddGhost period hPeriod
            (data.ghosts 0) (data.ghosts 1) (data.ghosts 2))
          ((1 : Coefficient) ⊗ₜ[Real] scalar)) = 0
  rw [data.nonlinear_ghost_rule]
  have hClosure := threeGeneratorScalarBRSTSquare_zero period hPeriod
    (data.ghosts 0) (data.ghosts 1) (data.ghosts 2) scalar
  unfold threeGeneratorScalarBRSTSquare at hClosure
  apply neg_eq_zero.mp
  rw [neg_add]
  simpa only [sub_eq_add_neg, exteriorScalarEmbed] using hClosure

private theorem legacyCombinedLinear_on_scalar
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (scalar : Scalar period hPeriod) :
    data.combinedLinear period hPeriod
        ((1 : Coefficient) ⊗ₜ[Real] scalar) =
      -exteriorGhostScalarAction period hPeriod
        (data.universalGhost period hPeriod)
        ((1 : Coefficient) ⊗ₜ[Real] scalar) := by
  simp [ClosedThreeGeneratorGhostKoszulData.combinedLinear,
    coefficientDifferential_one period hPeriod data]

/-- Exact sign obstruction for the historical `D ⊗ id - action` candidate:
its square on embedded scalars is twice the iterated ghost action, rather than
the zero forced by the scalar closure convention. -/
theorem legacyCombinedLinear_square_on_scalar_eq_two_actions
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod)
    (scalar : Scalar period hPeriod) :
    data.combinedLinear period hPeriod
        (data.combinedLinear period hPeriod
          ((1 : Coefficient) ⊗ₜ[Real] scalar)) =
      (2 : Real) • exteriorGhostScalarAction period hPeriod
        (data.universalGhost period hPeriod)
        (exteriorGhostScalarAction period hPeriod
          (data.universalGhost period hPeriod)
          ((1 : Coefficient) ⊗ₜ[Real] scalar)) := by
  rw [legacyCombinedLinear_on_scalar, map_neg]
  change -((TensorProduct.map data.coefficientDifferential
          (LinearMap.id : Scalar period hPeriod →ₗ[Real] Scalar period hPeriod) -
        exteriorGhostScalarAction period hPeriod
          (data.universalGhost period hPeriod))
      (exteriorGhostScalarAction period hPeriod
        (data.universalGhost period hPeriod)
        ((1 : Coefficient) ⊗ₜ[Real] scalar))) = _
  rw [LinearMap.sub_apply,
    tensorDifferential_action_embed period hPeriod data]
  change -(exteriorGhostScalarAction period hPeriod
        (TensorProduct.map data.coefficientDifferential
          (LinearMap.id : Ghost period hPeriod →ₗ[Real] Ghost period hPeriod)
          (threeGeneratorOddGhost period hPeriod
            (data.ghosts 0) (data.ghosts 1) (data.ghosts 2)))
        ((1 : Coefficient) ⊗ₜ[Real] scalar) -
      exteriorGhostScalarAction period hPeriod
        (threeGeneratorOddGhost period hPeriod
          (data.ghosts 0) (data.ghosts 1) (data.ghosts 2))
        (exteriorGhostScalarAction period hPeriod
          (threeGeneratorOddGhost period hPeriod
            (data.ghosts 0) (data.ghosts 1) (data.ghosts 2))
          ((1 : Coefficient) ⊗ₜ[Real] scalar))) = _
  rw [data.nonlinear_ghost_rule]
  have hClosure := threeGeneratorScalarBRSTSquare_zero period hPeriod
    (data.ghosts 0) (data.ghosts 1) (data.ghosts 2) scalar
  unfold threeGeneratorScalarBRSTSquare at hClosure
  have hPositive :
      exteriorGhostScalarAction period hPeriod
            (threeGeneratorNonlinearGhostBRSTTerm period hPeriod
              (data.ghosts 0) (data.ghosts 1) (data.ghosts 2))
            ((1 : Coefficient) ⊗ₜ[Real] scalar) +
          exteriorGhostScalarAction period hPeriod
            (threeGeneratorOddGhost period hPeriod
              (data.ghosts 0) (data.ghosts 1) (data.ghosts 2))
            (exteriorGhostScalarAction period hPeriod
              (threeGeneratorOddGhost period hPeriod
                (data.ghosts 0) (data.ghosts 1) (data.ghosts 2))
              ((1 : Coefficient) ⊗ₜ[Real] scalar)) = 0 := by
    apply neg_eq_zero.mp
    rw [neg_add]
    simpa only [sub_eq_add_neg, exteriorScalarEmbed] using hClosure
  have hFirst := eq_neg_of_add_eq_zero_left hPositive
  rw [hFirst, two_smul]
  abel

/-- Corrected extension contract, parallel to the historical minus-sign API. -/
structure CorrectedThreeGeneratorGlobalKoszulExtension
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) where
  parity_odd : ∀ element,
    threeGeneratorExteriorScalarParity period hPeriod
        (correctedCombinedLinear period hPeriod data element) =
      -correctedCombinedLinear period hPeriod data
        (threeGeneratorExteriorScalarParity period hPeriod element)
  leibniz : ∀ first second,
    correctedCombinedLinear period hPeriod data (first * second) =
      correctedCombinedLinear period hPeriod data first * second +
        threeGeneratorExteriorScalarParity period hPeriod first *
          correctedCombinedLinear period hPeriod data second
  square_on_coefficients : ∀ coefficient : Coefficient,
    correctedCombinedLinear period hPeriod data
        (correctedCombinedLinear period hPeriod data
          (coefficient ⊗ₜ[Real] (1 : Scalar period hPeriod))) = 0
  square_on_scalars : ∀ scalar : Scalar period hPeriod,
    correctedCombinedLinear period hPeriod data
        (correctedCombinedLinear period hPeriod data
          ((1 : Coefficient) ⊗ₜ[Real] scalar)) = 0

/-- Every closed three-generator package satisfies the corrected contract. -/
def correctedThreeGeneratorGlobalKoszulExtension
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) :
    CorrectedThreeGeneratorGlobalKoszulExtension period hPeriod data where
  parity_odd := correctedCombinedLinear_parity_odd period hPeriod data
  leibniz := correctedCombinedLinear_leibniz period hPeriod data
  square_on_coefficients :=
    correctedCombinedLinear_square_on_coefficients period hPeriod data
  square_on_scalars :=
    correctedCombinedLinear_square_on_scalars period hPeriod data

theorem CorrectedThreeGeneratorGlobalKoszulExtension.square_mul
    {data : ClosedThreeGeneratorGhostKoszulData period hPeriod}
    (extension :
      CorrectedThreeGeneratorGlobalKoszulExtension period hPeriod data)
    (first second : Total period hPeriod) :
    correctedCombinedLinear period hPeriod data
        (correctedCombinedLinear period hPeriod data (first * second)) =
      correctedCombinedLinear period hPeriod data
          (correctedCombinedLinear period hPeriod data first) * second +
        first * correctedCombinedLinear period hPeriod data
          (correctedCombinedLinear period hPeriod data second) := by
  have hCross :
      threeGeneratorExteriorScalarParity period hPeriod
            (correctedCombinedLinear period hPeriod data first) *
          correctedCombinedLinear period hPeriod data second +
        correctedCombinedLinear period hPeriod data
              (threeGeneratorExteriorScalarParity period hPeriod first) *
          correctedCombinedLinear period hPeriod data second = 0 := by
    rw [extension.parity_odd, ← add_mul]
    simp
  calc
    correctedCombinedLinear period hPeriod data
        (correctedCombinedLinear period hPeriod data (first * second)) =
        correctedCombinedLinear period hPeriod data
          (correctedCombinedLinear period hPeriod data first * second +
            threeGeneratorExteriorScalarParity period hPeriod first *
              correctedCombinedLinear period hPeriod data second) := by
          rw [extension.leibniz]
    _ = correctedCombinedLinear period hPeriod data
          (correctedCombinedLinear period hPeriod data first * second) +
        correctedCombinedLinear period hPeriod data
          (threeGeneratorExteriorScalarParity period hPeriod first *
            correctedCombinedLinear period hPeriod data second) := by
          rw [map_add]
    _ =
        (correctedCombinedLinear period hPeriod data
              (correctedCombinedLinear period hPeriod data first) * second +
          threeGeneratorExteriorScalarParity period hPeriod
              (correctedCombinedLinear period hPeriod data first) *
            correctedCombinedLinear period hPeriod data second) +
        (correctedCombinedLinear period hPeriod data
              (threeGeneratorExteriorScalarParity period hPeriod first) *
            correctedCombinedLinear period hPeriod data second +
          threeGeneratorExteriorScalarParity period hPeriod
              (threeGeneratorExteriorScalarParity period hPeriod first) *
            correctedCombinedLinear period hPeriod data
              (correctedCombinedLinear period hPeriod data second)) := by
          rw [extension.leibniz, extension.leibniz]
    _ = correctedCombinedLinear period hPeriod data
          (correctedCombinedLinear period hPeriod data first) * second +
        first * correctedCombinedLinear period hPeriod data
          (correctedCombinedLinear period hPeriod data second) := by
          rw [threeGeneratorExteriorScalarParity_involutive]
          calc
            _ = correctedCombinedLinear period hPeriod data
                    (correctedCombinedLinear period hPeriod data first) * second +
                ((threeGeneratorExteriorScalarParity period hPeriod
                        (correctedCombinedLinear period hPeriod data first) *
                      correctedCombinedLinear period hPeriod data second +
                    correctedCombinedLinear period hPeriod data
                        (threeGeneratorExteriorScalarParity period hPeriod first) *
                      correctedCombinedLinear period hPeriod data second) +
                  first * correctedCombinedLinear period hPeriod data
                    (correctedCombinedLinear period hPeriod data second)) := by
                abel
            _ = _ := by rw [hCross, zero_add]

theorem CorrectedThreeGeneratorGlobalKoszulExtension.square_zero
    {data : ClosedThreeGeneratorGhostKoszulData period hPeriod}
    (extension :
      CorrectedThreeGeneratorGlobalKoszulExtension period hPeriod data)
    (element : Total period hPeriod) :
    correctedCombinedLinear period hPeriod data
        (correctedCombinedLinear period hPeriod data element) = 0 := by
  induction element using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient scalar =>
      have hFactorization :
          coefficient ⊗ₜ[Real] scalar =
            (coefficient ⊗ₜ[Real] (1 : Scalar period hPeriod)) *
              ((1 : Coefficient) ⊗ₜ[Real] scalar) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hFactorization, extension.square_mul,
        extension.square_on_coefficients, extension.square_on_scalars,
        zero_mul, mul_zero, add_zero]
  | add first second firstHypothesis secondHypothesis =>
      rw [map_add, map_add, firstHypothesis, secondHypothesis, add_zero]

def CorrectedThreeGeneratorGlobalKoszulExtension.toGlobalDifferential
    {data : ClosedThreeGeneratorGhostKoszulData period hPeriod}
    (extension :
      CorrectedThreeGeneratorGlobalKoszulExtension period hPeriod data) :
    Z2GradedDifferential (Total period hPeriod) where
  parity := threeGeneratorExteriorScalarParity period hPeriod
  parity_involutive :=
    threeGeneratorExteriorScalarParity_involutive period hPeriod
  toLinearMap := correctedCombinedLinear period hPeriod data
  parity_odd := extension.parity_odd
  leibniz := extension.leibniz
  square_zero := extension.square_zero period hPeriod

/-- Fully unconditional corrected global differential for the D8 rotations. -/
def unconditionalCorrectedThreeGeneratorGlobalKoszulExtension :
    CorrectedThreeGeneratorGlobalKoszulExtension period hPeriod
      (unconditionalClosedThreeGeneratorGhostKoszulData period hPeriod) :=
  correctedThreeGeneratorGlobalKoszulExtension period hPeriod
    (unconditionalClosedThreeGeneratorGhostKoszulData period hPeriod)

/-- The final square-zero global BRST differential with the coherent sign. -/
def unconditionalCorrectedGlobalKoszulDifferential :
    Z2GradedDifferential (Total period hPeriod) :=
  (unconditionalCorrectedThreeGeneratorGlobalKoszulExtension period hPeriod)
    |>.toGlobalDifferential period hPeriod

end

end P0EFTJanusMappingTorusD8NonabelianGhostCorrectedGlobalKoszul4D
end JanusFormal
