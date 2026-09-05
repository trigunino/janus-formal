import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D

/-! # Exact derivative of inversion in the finite C² matrix algebra -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix (dimension : Nat) :=
  C2FiniteMatrix period hPeriod dimension

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Matrix form of `δ(A⁻¹) = -A⁻¹ δA A⁻¹` in the completed
C² coefficient algebra. -/
def c2FiniteMatrixInverseDerivative
    (dimension : Nat) (matrix : C2Matrix period hPeriod dimension) :
    C2Matrix period hPeriod dimension →L[Real]
      C2Matrix period hPeriod dimension :=
  -((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension
        (c2FiniteMatrixInverse period hPeriod dimension matrix)).comp
    ((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension).flip
        (c2FiniteMatrixInverse period hPeriod dimension matrix)))

@[simp]
theorem c2FiniteMatrixInverseDerivative_apply
    (dimension : Nat) (matrix direction : C2Matrix period hPeriod dimension) :
    c2FiniteMatrixInverseDerivative period hPeriod dimension matrix direction =
      -c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        (c2FiniteMatrixInverse period hPeriod dimension matrix)
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension direction
          (c2FiniteMatrixInverse period hPeriod dimension matrix)) :=
  rfl

theorem c2FiniteMatrixInverse_hasFDerivAt
    (dimension : Nat) (matrix : C2Matrix period hPeriod dimension)
    (hMatrix : matrix ∈
      c2FiniteMatrixUnitSet period hPeriod dimension) :
    HasFDerivAt (c2FiniteMatrixInverse period hPeriod dimension)
      (c2FiniteMatrixInverseDerivative period hPeriod dimension matrix)
      matrix := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  let inverse := c2FiniteMatrixInverse period hPeriod dimension
  let identity := c2FiniteMatrixIdentity period hPeriod dimension
  let inverseAt := inverse matrix
  let derivative := fderiv Real inverse matrix
  have hOpen := c2FiniteMatrixUnitSet_isOpen period hPeriod dimension
  have hInverse : HasFDerivAt inverse derivative matrix :=
    (((c2FiniteMatrixInverse_contDiffOn period hPeriod dimension).contDiffAt
      (hOpen.mem_nhds hMatrix)).differentiableAt (by simp)).hasFDerivAt
  have hProduct : HasFDerivAt
      (fun current => product current (inverse current))
      ((product matrix).comp derivative + product.flip inverseAt) matrix := by
    exact product.hasFDerivAt.clm_apply hInverse
  have hEventually :
      (fun current => product current (inverse current)) =ᶠ[nhds matrix]
        fun _ => identity := by
    filter_upwards [hOpen.mem_nhds hMatrix] with current hCurrent
    exact c2FiniteMatrixProduct_inverse_right period hPeriod dimension
      current hCurrent
  have hConstant : HasFDerivAt (fun _ : C2Matrix period hPeriod dimension =>
      identity) ((product matrix).comp derivative + product.flip inverseAt)
      matrix :=
    hProduct.congr_of_eventuallyEq hEventually.symm
  have hZero : HasFDerivAt (fun _ : C2Matrix period hPeriod dimension =>
      identity)
      (0 : C2Matrix period hPeriod dimension →L[Real]
        C2Matrix period hPeriod dimension) matrix :=
    hasFDerivAt_const (x := matrix) (c := identity)
  have hDerivativeEquation :
      (product matrix).comp derivative + product.flip inverseAt = 0 :=
    hConstant.unique hZero
  apply hInverse.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  have hEquation := congrArg
    (fun linear : C2Matrix period hPeriod dimension →L[Real]
        C2Matrix period hPeriod dimension => linear direction)
    hDerivativeEquation
  change product matrix (derivative direction) +
      product direction inverseAt = 0 at hEquation
  have hSolve : product matrix (derivative direction) =
      -product direction inverseAt :=
    add_eq_zero_iff_eq_neg.mp hEquation
  have hApplied := congrArg (fun value => product inverseAt value) hSolve
  change derivative direction =
    c2FiniteMatrixInverseDerivative period hPeriod dimension matrix direction
  rw [c2FiniteMatrixInverseDerivative_apply]
  change derivative direction = -product inverseAt (product direction inverseAt)
  rw [← c2FiniteMatrixProduct_assoc period hPeriod dimension] at hApplied
  rw [c2FiniteMatrixProduct_inverse_left period hPeriod dimension matrix hMatrix,
    c2FiniteMatrixProduct_identity_left] at hApplied
  simpa using hApplied

/-- Gate marker: the smooth inverse used by the paired relative metric has
the exact noncommutative inverse derivative on its authentic open unit set. -/
theorem canonical_physical_c2_finite_matrix_inverse_derivative_gate
    (dimension : Nat) (matrix : C2Matrix period hPeriod dimension)
    (hMatrix : matrix ∈
      c2FiniteMatrixUnitSet period hPeriod dimension) :
    HasFDerivAt (c2FiniteMatrixInverse period hPeriod dimension)
        (c2FiniteMatrixInverseDerivative period hPeriod dimension matrix)
        matrix ∧
      ∀ direction,
        c2FiniteMatrixInverseDerivative period hPeriod dimension matrix
            direction =
          -c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) dimension
            (c2FiniteMatrixInverse period hPeriod dimension matrix)
            (c2FiniteMatrixProduct
              (period := period) (hPeriod := hPeriod) dimension direction
              (c2FiniteMatrixInverse period hPeriod dimension matrix)) :=
  ⟨c2FiniteMatrixInverse_hasFDerivAt period hPeriod dimension matrix hMatrix,
    c2FiniteMatrixInverseDerivative_apply period hPeriod dimension matrix⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
end JanusFormal
