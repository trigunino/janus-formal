import Mathlib.RingTheory.TensorProduct.Maps
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusThreeGeneratorScalarBRST4D

/-!
# Global three-generator Koszul BRST interface on D8 scalars

This gate isolates a finite, closed three-ghost subalgebra and its
structure-constant Chevalley--Eilenberg differential.  From the corresponding
global Koszul extension laws it constructs an actual square-zero odd graded
differential on
`ExteriorAlgebra Real (Fin 3 → Real) ⊗ C∞(D8)`.

The construction is not the zero differential: its coefficient rule is the
usual quadratic structure-constant rule and its matter term is the concrete
D8 Lie-derivative action of all three ghosts.  The extension contract records
exactly the two generator-square checks and the global Koszul rule still
needed to instantiate this differential for a chosen closed D8 ghost triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusExteriorScalarBRSTDerivation4D
open P0EFTJanusMappingTorusThreeGeneratorScalarBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Ghost := CInfinityDiffeomorphismGhost period hPeriod
private abbrev Scalar := CInfinityScalarField period hPeriod
private abbrev Coefficient := GhostCoefficientExterior

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The full exterior-valued smooth scalar algebra. -/
abbrev ThreeGeneratorExteriorScalarAlgebra :=
  Coefficient ⊗[Real] Scalar period hPeriod

/-- Standard grade involution on the three-generator exterior algebra. -/
def ghostCoefficientParity : Coefficient →ₐ[Real] Coefficient :=
  (CliffordAlgebra.involute
    (Q := (0 : QuadraticForm Real OddGeneratorSpace)))

/-- Grade involution extended trivially over smooth D8 scalars. -/
def threeGeneratorExteriorScalarParity :
    ThreeGeneratorExteriorScalarAlgebra period hPeriod →ₐ[Real]
      ThreeGeneratorExteriorScalarAlgebra period hPeriod :=
  Algebra.TensorProduct.map ghostCoefficientParity
    (AlgHom.id Real (Scalar period hPeriod))

@[simp]
theorem threeGeneratorExteriorScalarParity_tmul
    (coefficient : Coefficient)
    (scalar : Scalar period hPeriod) :
    threeGeneratorExteriorScalarParity period hPeriod
        (coefficient ⊗ₜ[Real] scalar) =
      ghostCoefficientParity coefficient ⊗ₜ[Real] scalar := by
  simp [threeGeneratorExteriorScalarParity]

theorem threeGeneratorExteriorScalarParity_involutive
    (element : ThreeGeneratorExteriorScalarAlgebra period hPeriod) :
    threeGeneratorExteriorScalarParity period hPeriod
        (threeGeneratorExteriorScalarParity period hPeriod element) = element := by
  induction element using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient scalar =>
      rw [threeGeneratorExteriorScalarParity_tmul,
        threeGeneratorExteriorScalarParity_tmul]
      exact congrArg (fun value => value ⊗ₜ[Real] scalar)
        (CliffordAlgebra.involute_involutive coefficient)
  | add first second firstHypothesis secondHypothesis =>
      simp [map_add, firstHypothesis, secondHypothesis]

/-- A closed three-dimensional D8 ghost family together with a genuine
coefficient CE differential.  The last field ties its quadratic generator
rule to the already proved nonlinear three-ghost term. -/
structure ClosedThreeGeneratorGhostKoszulData where
  ghosts : Fin 3 → Ghost period hPeriod
  structureConstant : Fin 3 → Fin 3 → Fin 3 → Real
  bracket_closure : ∀ i j,
    smoothGhostLieBracket period hPeriod (ghosts i) (ghosts j) =
      ∑ k : Fin 3, structureConstant i j k • ghosts k
  coefficientDifferential : Coefficient →ₗ[Real] Coefficient
  coefficient_parity_odd : ∀ coefficient,
    ghostCoefficientParity (coefficientDifferential coefficient) =
      -coefficientDifferential (ghostCoefficientParity coefficient)
  coefficient_leibniz : ∀ first second,
    coefficientDifferential (first * second) =
      coefficientDifferential first * second +
        ghostCoefficientParity first * coefficientDifferential second
  coefficient_square_zero : ∀ coefficient,
    coefficientDifferential (coefficientDifferential coefficient) = 0
  generator_rule : ∀ k : Fin 3,
    coefficientDifferential (oddGenerator k) =
      (-((2 : Real)⁻¹)) •
        ∑ i : Fin 3, ∑ j : Fin 3,
          structureConstant i j k • (oddGenerator i * oddGenerator j)
  nonlinear_ghost_rule :
    TensorProduct.map coefficientDifferential
        (LinearMap.id : Ghost period hPeriod →ₗ[Real] Ghost period hPeriod)
        (threeGeneratorOddGhost period hPeriod (ghosts 0) (ghosts 1) (ghosts 2)) =
      threeGeneratorNonlinearGhostBRSTTerm period hPeriod
        (ghosts 0) (ghosts 1) (ghosts 2)

/-- The coefficient differential as an actual square-zero graded
differential, before coupling it to matter. -/
def ClosedThreeGeneratorGhostKoszulData.coefficientBRSTDifferential
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) :
    Z2GradedDifferential Coefficient where
  parity := ghostCoefficientParity
  parity_involutive := by
    intro coefficient
    exact CliffordAlgebra.involute_involutive coefficient
  toLinearMap := data.coefficientDifferential
  parity_odd := data.coefficient_parity_odd
  leibniz := data.coefficient_leibniz
  square_zero := data.coefficient_square_zero

/-- Concrete universal odd ghost attached to the closed triple. -/
def ClosedThreeGeneratorGhostKoszulData.universalGhost
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  threeGeneratorOddGhost period hPeriod
    (data.ghosts 0) (data.ghosts 1) (data.ghosts 2)

/-- Candidate full BRST map: coefficient CE differential minus the concrete
three-ghost D8 scalar action. -/
def ClosedThreeGeneratorGhostKoszulData.combinedLinear
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) :
    ThreeGeneratorExteriorScalarAlgebra period hPeriod →ₗ[Real]
      ThreeGeneratorExteriorScalarAlgebra period hPeriod :=
  TensorProduct.map data.coefficientDifferential
      (LinearMap.id : Scalar period hPeriod →ₗ[Real] Scalar period hPeriod) -
    exteriorGhostScalarAction period hPeriod data.universalGhost

/-- Exact global extension obligations.  They concern the fixed, nonzero
candidate above: oddness, the Koszul Leibniz identity, and square-zero on the
two algebra-generating embedded factors. -/
structure ThreeGeneratorGlobalKoszulExtension
    (data : ClosedThreeGeneratorGhostKoszulData period hPeriod) where
  parity_odd : ∀ element,
    threeGeneratorExteriorScalarParity period hPeriod
        (data.combinedLinear period hPeriod element) =
      -data.combinedLinear period hPeriod
        (threeGeneratorExteriorScalarParity period hPeriod element)
  leibniz : ∀ first second,
    data.combinedLinear period hPeriod (first * second) =
      data.combinedLinear period hPeriod first * second +
        threeGeneratorExteriorScalarParity period hPeriod first *
          data.combinedLinear period hPeriod second
  square_on_coefficients : ∀ coefficient : Coefficient,
    data.combinedLinear period hPeriod
        (data.combinedLinear period hPeriod
          (coefficient ⊗ₜ[Real] (1 : Scalar period hPeriod))) = 0
  square_on_scalars : ∀ scalar : Scalar period hPeriod,
    data.combinedLinear period hPeriod
        (data.combinedLinear period hPeriod
          ((1 : Coefficient) ⊗ₜ[Real] scalar)) = 0

/-- The square of an odd Koszul derivation is an ordinary derivation. -/
theorem ThreeGeneratorGlobalKoszulExtension.combinedSquare_mul
    {data : ClosedThreeGeneratorGhostKoszulData period hPeriod}
    (extension : ThreeGeneratorGlobalKoszulExtension period hPeriod data)
    (first second : ThreeGeneratorExteriorScalarAlgebra period hPeriod) :
    data.combinedLinear period hPeriod
        (data.combinedLinear period hPeriod (first * second)) =
      data.combinedLinear period hPeriod
          (data.combinedLinear period hPeriod first) * second +
        first * data.combinedLinear period hPeriod
          (data.combinedLinear period hPeriod second) := by
  have hCross :
      threeGeneratorExteriorScalarParity period hPeriod
            (data.combinedLinear period hPeriod first) *
          data.combinedLinear period hPeriod second +
        data.combinedLinear period hPeriod
              (threeGeneratorExteriorScalarParity period hPeriod first) *
          data.combinedLinear period hPeriod second = 0 := by
    rw [extension.parity_odd, ← add_mul]
    simp
  calc
    data.combinedLinear period hPeriod
        (data.combinedLinear period hPeriod (first * second)) =
        data.combinedLinear period hPeriod
          (data.combinedLinear period hPeriod first * second +
            threeGeneratorExteriorScalarParity period hPeriod first *
              data.combinedLinear period hPeriod second) := by
          rw [extension.leibniz]
    _ = data.combinedLinear period hPeriod
          (data.combinedLinear period hPeriod first * second) +
        data.combinedLinear period hPeriod
          (threeGeneratorExteriorScalarParity period hPeriod first *
            data.combinedLinear period hPeriod second) := by
          rw [map_add]
    _ =
        (data.combinedLinear period hPeriod
              (data.combinedLinear period hPeriod first) * second +
          threeGeneratorExteriorScalarParity period hPeriod
              (data.combinedLinear period hPeriod first) *
            data.combinedLinear period hPeriod second) +
        (data.combinedLinear period hPeriod
              (threeGeneratorExteriorScalarParity period hPeriod first) *
            data.combinedLinear period hPeriod second +
          threeGeneratorExteriorScalarParity period hPeriod
              (threeGeneratorExteriorScalarParity period hPeriod first) *
            data.combinedLinear period hPeriod
              (data.combinedLinear period hPeriod second)) := by
          rw [extension.leibniz, extension.leibniz]
    _ = data.combinedLinear period hPeriod
          (data.combinedLinear period hPeriod first) * second +
        first * data.combinedLinear period hPeriod
          (data.combinedLinear period hPeriod second) := by
          rw [threeGeneratorExteriorScalarParity_involutive]
          calc
            _ = data.combinedLinear period hPeriod
                    (data.combinedLinear period hPeriod first) * second +
                ((threeGeneratorExteriorScalarParity period hPeriod
                        (data.combinedLinear period hPeriod first) *
                      data.combinedLinear period hPeriod second +
                    data.combinedLinear period hPeriod
                        (threeGeneratorExteriorScalarParity period hPeriod first) *
                      data.combinedLinear period hPeriod second) +
                  first * data.combinedLinear period hPeriod
                    (data.combinedLinear period hPeriod second)) := by
                abel
            _ = _ := by rw [hCross, zero_add]

/-- The two embedded factors generate the tensor-product algebra, so the two
generator-square checks imply global nilpotence. -/
theorem ThreeGeneratorGlobalKoszulExtension.combinedSquare_zero
    {data : ClosedThreeGeneratorGhostKoszulData period hPeriod}
    (extension : ThreeGeneratorGlobalKoszulExtension period hPeriod data)
    (element : ThreeGeneratorExteriorScalarAlgebra period hPeriod) :
    data.combinedLinear period hPeriod
        (data.combinedLinear period hPeriod element) = 0 := by
  induction element using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient scalar =>
      have hFactorization :
          coefficient ⊗ₜ[Real] scalar =
            (coefficient ⊗ₜ[Real] (1 : Scalar period hPeriod)) *
              ((1 : Coefficient) ⊗ₜ[Real] scalar) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hFactorization, extension.combinedSquare_mul,
        extension.square_on_coefficients, extension.square_on_scalars,
        zero_mul, mul_zero, add_zero]
  | add first second firstHypothesis secondHypothesis =>
      rw [map_add, map_add, firstHypothesis, secondHypothesis, add_zero]

/-- Actual global square-zero odd graded differential obtained from the
finite closed-ghost Koszul extension data. -/
def ThreeGeneratorGlobalKoszulExtension.toGlobalDifferential
    {data : ClosedThreeGeneratorGhostKoszulData period hPeriod}
    (extension : ThreeGeneratorGlobalKoszulExtension period hPeriod data) :
    Z2GradedDifferential
      (ThreeGeneratorExteriorScalarAlgebra period hPeriod) where
  parity := threeGeneratorExteriorScalarParity period hPeriod
  parity_involutive :=
    threeGeneratorExteriorScalarParity_involutive period hPeriod
  toLinearMap := data.combinedLinear period hPeriod
  parity_odd := extension.parity_odd
  leibniz := extension.leibniz
  square_zero := extension.combinedSquare_zero period hPeriod

theorem three_generator_global_koszul_brst4D_closure
    {data : ClosedThreeGeneratorGhostKoszulData period hPeriod}
    (extension : ThreeGeneratorGlobalKoszulExtension period hPeriod data) :
    ∀ element : ThreeGeneratorExteriorScalarAlgebra period hPeriod,
      (extension.toGlobalDifferential period hPeriod).toLinearMap
          ((extension.toGlobalDifferential period hPeriod).toLinearMap element) = 0 :=
  extension.combinedSquare_zero period hPeriod

end

end P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D
end JanusFormal
