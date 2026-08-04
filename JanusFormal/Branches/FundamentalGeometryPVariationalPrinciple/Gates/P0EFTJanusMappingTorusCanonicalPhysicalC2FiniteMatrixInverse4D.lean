import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Inversion in the finite C² matrix algebra

The invertible locus is pulled back from the open set of bounded linear
equivalences through left multiplication.  Operator inversion then gives a
smooth matrix inverse with exact two-sided identities.  No pointwise or
global-frame hypothesis is added.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Manifold ContDiff
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

/-- Constant identity matrix in the dense smooth coefficient algebra. -/
def smoothFiniteMatrixIdentity (dimension : Nat) :
    SmoothFiniteMatrix period hPeriod dimension :=
  fun row column =>
    constantSmoothField period hPeriod Real
      (if row = column then 1 else 0)

theorem smoothFiniteMatrixProduct_identity_left
    (dimension : Nat)
    (matrix : SmoothFiniteMatrix period hPeriod dimension) :
    smoothFiniteMatrixProduct period hPeriod dimension
        (smoothFiniteMatrixIdentity period hPeriod dimension) matrix =
      matrix := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp [smoothFiniteMatrixProduct, smoothFiniteMatrixIdentity,
    smoothScalarFieldMul_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    constantSmoothField]

theorem smoothFiniteMatrixProduct_identity_right
    (dimension : Nat)
    (matrix : SmoothFiniteMatrix period hPeriod dimension) :
    smoothFiniteMatrixProduct period hPeriod dimension matrix
        (smoothFiniteMatrixIdentity period hPeriod dimension) =
      matrix := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp [smoothFiniteMatrixProduct, smoothFiniteMatrixIdentity,
    smoothScalarFieldMul_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    constantSmoothField]

/-- Identity of the completed finite C² matrix algebra. -/
def c2FiniteMatrixIdentity (dimension : Nat) :
    C2FiniteMatrix period hPeriod dimension :=
  smoothFiniteMatrixToC2 period hPeriod dimension
    (smoothFiniteMatrixIdentity period hPeriod dimension)

theorem c2FiniteMatrixProduct_identity_left
    (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        (c2FiniteMatrixIdentity period hPeriod dimension) matrix =
      matrix := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  let lift := smoothFiniteMatrixToC2 period hPeriod dimension
  let identity := smoothFiniteMatrixIdentity period hPeriod dimension
  refine DenseRange.induction_on
    (smoothFiniteMatrixToC2_denseRange period hPeriod dimension) matrix
    (isClosed_eq (product (lift identity)).continuous continuous_id) ?_
  intro smoothMatrix
  change product (lift identity) (lift smoothMatrix) = lift smoothMatrix
  rw [c2FiniteMatrixProduct_smooth,
    smoothFiniteMatrixProduct_identity_left]

theorem c2FiniteMatrixProduct_identity_right
    (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension matrix
        (c2FiniteMatrixIdentity period hPeriod dimension) =
      matrix := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  let lift := smoothFiniteMatrixToC2 period hPeriod dimension
  let identity := smoothFiniteMatrixIdentity period hPeriod dimension
  refine DenseRange.induction_on
    (smoothFiniteMatrixToC2_denseRange period hPeriod dimension) matrix
    (isClosed_eq
      (product.continuous.clm_apply continuous_const) continuous_id) ?_
  intro smoothMatrix
  change product (lift smoothMatrix) (lift identity) = lift smoothMatrix
  rw [c2FiniteMatrixProduct_smooth,
    smoothFiniteMatrixProduct_identity_right]

/-- Matrices whose left-multiplication operator is a bounded equivalence. -/
def c2FiniteMatrixUnitSet (dimension : Nat) :
    Set (C2FiniteMatrix period hPeriod dimension) :=
  c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension ⁻¹'
    Set.range ((↑) :
      (C2FiniteMatrix period hPeriod dimension ≃L[Real]
          C2FiniteMatrix period hPeriod dimension) →
        C2FiniteMatrix period hPeriod dimension →L[Real]
          C2FiniteMatrix period hPeriod dimension)

theorem c2FiniteMatrixUnitSet_isOpen (dimension : Nat) :
    IsOpen (c2FiniteMatrixUnitSet period hPeriod dimension) := by
  change IsOpen
    (c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension ⁻¹'
      Set.range ((↑) :
        (C2FiniteMatrix period hPeriod dimension ≃L[Real]
            C2FiniteMatrix period hPeriod dimension) →
          C2FiniteMatrix period hPeriod dimension →L[Real]
            C2FiniteMatrix period hPeriod dimension))
  exact ContinuousLinearEquiv.isOpen.preimage
    (c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension).continuous

theorem c2FiniteMatrixIdentity_mem_unitSet (dimension : Nat) :
    c2FiniteMatrixIdentity period hPeriod dimension ∈
      c2FiniteMatrixUnitSet period hPeriod dimension := by
  refine ⟨ContinuousLinearEquiv.refl Real
      (C2FiniteMatrix period hPeriod dimension), ?_⟩
  apply ContinuousLinearMap.ext
  intro matrix
  exact (c2FiniteMatrixProduct_identity_left
    period hPeriod dimension matrix).symm

/-- Smooth inverse obtained from the inverse of left multiplication. -/
def c2FiniteMatrixInverse (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension) :
    C2FiniteMatrix period hPeriod dimension :=
  (c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension matrix).inverse
    (c2FiniteMatrixIdentity period hPeriod dimension)

theorem c2FiniteMatrixProduct_inverse_right
    (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension)
    (hMatrix : matrix ∈ c2FiniteMatrixUnitSet period hPeriod dimension) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension matrix
        (c2FiniteMatrixInverse period hPeriod dimension matrix) =
      c2FiniteMatrixIdentity period hPeriod dimension := by
  change (c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension matrix).IsInvertible
    at hMatrix
  exact hMatrix.self_apply_inverse
    (c2FiniteMatrixIdentity period hPeriod dimension)

theorem c2FiniteMatrixProduct_inverse_left
    (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension)
    (hMatrix : matrix ∈ c2FiniteMatrixUnitSet period hPeriod dimension) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        (c2FiniteMatrixInverse period hPeriod dimension matrix) matrix =
      c2FiniteMatrixIdentity period hPeriod dimension := by
  change (c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension matrix).IsInvertible
    at hMatrix
  apply hMatrix.injective
  rw [← c2FiniteMatrixProduct_assoc,
    c2FiniteMatrixProduct_inverse_right period hPeriod dimension matrix hMatrix,
    c2FiniteMatrixProduct_identity_left,
    c2FiniteMatrixProduct_identity_right]

theorem c2FiniteMatrixInverse_contDiffOn (dimension : Nat) :
    ContDiffOn Real ∞ (c2FiniteMatrixInverse period hPeriod dimension)
      (c2FiniteMatrixUnitSet period hPeriod dimension) := by
  intro matrix hMatrix
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension
  let identity := c2FiniteMatrixIdentity period hPeriod dimension
  change ContDiffWithinAt Real ∞
    (fun current : C2FiniteMatrix period hPeriod dimension =>
      (product current).inverse identity)
    (c2FiniteMatrixUnitSet period hPeriod dimension) matrix
  change (product matrix).IsInvertible at hMatrix
  have hInverse := hMatrix.contDiffAt_map_inverse (n := ∞)
  have hProduct : ContDiffAt Real ∞ product matrix :=
    product.contDiff.contDiffAt
  have hOperator := hInverse.comp matrix hProduct
  exact (hOperator.clm_apply contDiffAt_const).contDiffWithinAt

/-- Summary gate: the full finite C² algebra has an open smooth unit group. -/
theorem canonical_physical_c2_finite_matrix_inverse_gate
    (dimension : Nat) :
    IsOpen (c2FiniteMatrixUnitSet period hPeriod dimension) ∧
      c2FiniteMatrixIdentity period hPeriod dimension ∈
        c2FiniteMatrixUnitSet period hPeriod dimension ∧
      ContDiffOn Real ∞ (c2FiniteMatrixInverse period hPeriod dimension)
        (c2FiniteMatrixUnitSet period hPeriod dimension) ∧
      (∀ matrix,
        matrix ∈ c2FiniteMatrixUnitSet period hPeriod dimension →
          c2FiniteMatrixProduct
              (period := period) (hPeriod := hPeriod) dimension matrix
              (c2FiniteMatrixInverse period hPeriod dimension matrix) =
            c2FiniteMatrixIdentity period hPeriod dimension ∧
          c2FiniteMatrixProduct
              (period := period) (hPeriod := hPeriod) dimension
              (c2FiniteMatrixInverse period hPeriod dimension matrix) matrix =
            c2FiniteMatrixIdentity period hPeriod dimension) := by
  exact ⟨c2FiniteMatrixUnitSet_isOpen period hPeriod dimension,
    c2FiniteMatrixIdentity_mem_unitSet period hPeriod dimension,
    c2FiniteMatrixInverse_contDiffOn period hPeriod dimension,
    fun matrix hMatrix =>
      ⟨c2FiniteMatrixProduct_inverse_right
          period hPeriod dimension matrix hMatrix,
        c2FiniteMatrixProduct_inverse_left
          period hPeriod dimension matrix hMatrix⟩⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
end JanusFormal
