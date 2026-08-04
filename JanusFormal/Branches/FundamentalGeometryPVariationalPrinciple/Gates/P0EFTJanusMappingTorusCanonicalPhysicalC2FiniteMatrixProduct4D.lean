import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D

/-!
# Finite matrix algebra on the uniform C²-jet core

The bounded scalar Leibniz product is assembled entrywise into arbitrary
finite matrix multiplication.  Smooth matrices remain dense, multiplication
agrees exactly with pointwise smooth multiplication, and squaring is smooth
with the Sylvester derivative.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Manifold ContDiff
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

/-- Finite matrices with entries in the uniform C²-jet core. -/
abbrev C2FiniteMatrix (dimension : Nat) :=
  Fin dimension → Fin dimension → C2Scalar period hPeriod

abbrev SmoothFiniteMatrix (dimension : Nat) :=
  Fin dimension → Fin dimension →
    SmoothQuotientField period hPeriod Real

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

private def finiteMatrixProductBilinear
    (dimension : Nat)
    {Scalar : Type*} [AddCommMonoid Scalar] [Module Real Scalar]
    (product : Scalar →ₗ[Real] Scalar →ₗ[Real] Scalar) :
    (Fin dimension → Fin dimension → Scalar) →ₗ[Real]
      (Fin dimension → Fin dimension → Scalar) →ₗ[Real]
        (Fin dimension → Fin dimension → Scalar) :=
  LinearMap.mk₂ Real
    (fun first second row column => ∑ middle : Fin dimension,
      product (first row middle) (second middle column))
    (by
      intro first second third
      funext row column
      simp only [Pi.add_apply, map_add, LinearMap.add_apply,
        Finset.sum_add_distrib])
    (by
      intro scalar first second
      funext row column
      simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply,
        Finset.smul_sum])
    (by
      intro first second third
      funext row column
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib])
    (by
      intro scalar first second
      funext row column
      simp only [Pi.smul_apply, map_smul, Finset.smul_sum])

def c2FiniteMatrixProductBilinear (dimension : Nat) :
    C2FiniteMatrix period hPeriod dimension →ₗ[Real]
      C2FiniteMatrix period hPeriod dimension →ₗ[Real]
        C2FiniteMatrix period hPeriod dimension :=
  finiteMatrixProductBilinear dimension
    (LinearMap.mk₂ Real
      (fun first second =>
        canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod first second)
      (fun first second third => by
        exact (canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod).map_add₂ first second third)
      (fun scalar first second => by
        exact (canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod).map_smul₂ scalar first second)
      (fun first second third => by
        exact (canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod first).map_add second third)
      (fun scalar first second => by
        exact (canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod first).map_smul scalar second))

/-- Bounded finite matrix multiplication on the C² core. -/
def c2FiniteMatrixProduct (dimension : Nat) :
    C2FiniteMatrix period hPeriod dimension →L[Real]
      C2FiniteMatrix period hPeriod dimension →L[Real]
        C2FiniteMatrix period hPeriod dimension := by
  exact @LinearMap.mkContinuous₂ Real Real Real
    (C2FiniteMatrix period hPeriod dimension)
    (C2FiniteMatrix period hPeriod dimension)
    (C2FiniteMatrix period hPeriod dimension)
    _ _ _ _ _ _ _ _ _
    (RingHom.id Real) (RingHom.id Real) _
    (c2FiniteMatrixProductBilinear
      (period := period) (hPeriod := hPeriod) dimension)
    (4 * (dimension : Real))
    (by
      intro first second
      change ‖(fun row column => ∑ middle : Fin dimension,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (first row middle) (second middle column))‖ ≤
        (4 * (dimension : Real)) * ‖first‖ * ‖second‖
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro row
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro column
      calc
        ‖∑ middle : Fin dimension,
            canonicalPhysicalScalarC2JetCoreProduct period hPeriod
              (first row middle) (second middle column)‖ ≤
            ∑ middle : Fin dimension,
              ‖canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                (first row middle) (second middle column)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _middle : Fin dimension,
            4 * ‖first‖ * ‖second‖ := by
          apply Finset.sum_le_sum
          intro middle _
          calc
            ‖canonicalPhysicalScalarC2JetCoreProduct period hPeriod
                (first row middle) (second middle column)‖ ≤
                4 * ‖first row middle‖ * ‖second middle column‖ := by
              exact canonicalPhysicalScalarC2JetCoreProduct_norm_le
                period hPeriod (first row middle) (second middle column)
            _ ≤ 4 * ‖first‖ * ‖second‖ := by
              gcongr
              · exact (norm_le_pi_norm (first row) middle).trans
                  (norm_le_pi_norm first row)
              · exact (norm_le_pi_norm (second middle) column).trans
                  (norm_le_pi_norm second middle)
        _ = (4 * (dimension : Real)) * ‖first‖ * ‖second‖ := by
          simp
          ring)

@[simp]
theorem c2FiniteMatrixProduct_apply
    (dimension : Nat)
    (first second : C2FiniteMatrix period hPeriod dimension)
    (row column : Fin dimension) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        first second row column =
      ∑ middle : Fin dimension,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (first row middle) (second middle column) := by
  simp [c2FiniteMatrixProduct, c2FiniteMatrixProductBilinear,
    finiteMatrixProductBilinear]

/-- Coordinatewise exact smooth lift. -/
def smoothFiniteMatrixToC2 (dimension : Nat) :
    SmoothFiniteMatrix period hPeriod dimension →ₗ[Real]
      C2FiniteMatrix period hPeriod dimension where
  toFun matrix row column :=
    smoothToCanonicalPhysicalScalarC2JetCore
      period hPeriod (matrix row column)
  map_add' first second := by
    funext row column
    exact (smoothToCanonicalPhysicalScalarC2JetCore
      period hPeriod).map_add (first row column) (second row column)
  map_smul' scalar matrix := by
    funext row column
    exact (smoothToCanonicalPhysicalScalarC2JetCore
      period hPeriod).map_smul scalar (matrix row column)

def smoothFiniteMatrixProduct (dimension : Nat)
    (first second : SmoothFiniteMatrix period hPeriod dimension) :
    SmoothFiniteMatrix period hPeriod dimension :=
  fun row column => ∑ middle : Fin dimension,
    smoothScalarFieldMul period hPeriod
      (first row middle) (second middle column)

theorem c2FiniteMatrixProduct_smooth
    (dimension : Nat)
    (first second : SmoothFiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        (smoothFiniteMatrixToC2 period hPeriod dimension first)
        (smoothFiniteMatrixToC2 period hPeriod dimension second) =
      smoothFiniteMatrixToC2 period hPeriod dimension
        (smoothFiniteMatrixProduct period hPeriod dimension first second) := by
  funext row column
  rw [c2FiniteMatrixProduct_apply]
  change (∑ middle : Fin dimension,
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (first row middle))
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (second middle column))) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (∑ middle : Fin dimension, smoothScalarFieldMul period hPeriod
        (first row middle) (second middle column))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro middle _
  exact canonicalPhysicalScalarC2JetCoreProduct_smooth
    period hPeriod (first row middle) (second middle column)

theorem smoothFiniteMatrixToC2_denseRange (dimension : Nat) :
    DenseRange (smoothFiniteMatrixToC2 period hPeriod dimension) := by
  exact DenseRange.piMap fun _ : Fin dimension =>
    DenseRange.piMap fun _ : Fin dimension =>
      smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod

theorem c2ScalarProduct_assoc
    (first second third : C2Scalar period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod first second) third =
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod first
        (canonicalPhysicalScalarC2JetCoreProduct
          period hPeriod second third) := by
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  let lift := smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
  have hDense : DenseRange lift :=
    smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod
  refine DenseRange.induction_on hDense first
    (isClosed_eq
      ((product.flip third).comp (product.flip second)).continuous
      (product.flip (product second third)).continuous) ?_
  intro smoothFirst
  refine DenseRange.induction_on hDense second
    (isClosed_eq
      ((product.flip third).comp (product (lift smoothFirst))).continuous
      ((product (lift smoothFirst)).comp (product.flip third)).continuous) ?_
  intro smoothSecond
  refine DenseRange.induction_on hDense third
    (isClosed_eq
      (product (product (lift smoothFirst) (lift smoothSecond))).continuous
      ((product (lift smoothFirst)).comp
        (product (lift smoothSecond))).continuous) ?_
  intro smoothThird
  change product (product (lift smoothFirst) (lift smoothSecond))
      (lift smoothThird) =
    product (lift smoothFirst)
      (product (lift smoothSecond) (lift smoothThird))
  simp only [product, lift,
    canonicalPhysicalScalarC2JetCoreProduct_smooth]
  exact congrArg
    (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
    (smoothScalarFieldMul_assoc period hPeriod
      smoothFirst smoothSecond smoothThird)

theorem c2ScalarProduct_sum_left
    {Index : Type*} (indices : Finset Index)
    (fields : Index → C2Scalar period hPeriod)
    (second : C2Scalar period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (∑ index ∈ indices, fields index) second =
      ∑ index ∈ indices,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (fields index) second := by
  change (canonicalPhysicalScalarC2JetCoreProduct
      period hPeriod).flip second (∑ index ∈ indices, fields index) = _
  exact map_sum
    ((canonicalPhysicalScalarC2JetCoreProduct period hPeriod).flip second)
      fields indices

theorem c2ScalarProduct_sum_right
    {Index : Type*} (indices : Finset Index)
    (first : C2Scalar period hPeriod)
    (fields : Index → C2Scalar period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod first
        (∑ index ∈ indices, fields index) =
      ∑ index ∈ indices,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          first (fields index) := by
  exact map_sum
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod first)
      fields indices

theorem c2FiniteMatrixProduct_assoc
    (dimension : Nat)
    (first second third : C2FiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension first second) third =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension first
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension second third) := by
  funext row column
  simp only [c2FiniteMatrixProduct_apply]
  simp_rw [c2ScalarProduct_sum_left, c2ScalarProduct_sum_right]
  conv_lhs => rw [Finset.sum_comm]
  simp only [c2ScalarProduct_assoc]

/-- Matrix square on the C² Banach algebra. -/
def c2FiniteMatrixSquare (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension) :
    C2FiniteMatrix period hPeriod dimension :=
  c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension matrix matrix

/-- Sylvester derivative of matrix squaring. -/
def c2FiniteMatrixSylvester (dimension : Nat)
    (root : C2FiniteMatrix period hPeriod dimension) :
    C2FiniteMatrix period hPeriod dimension →L[Real]
      C2FiniteMatrix period hPeriod dimension := by
  let product : C2FiniteMatrix period hPeriod dimension →L[Real]
      C2FiniteMatrix period hPeriod dimension →L[Real]
        C2FiniteMatrix period hPeriod dimension :=
    c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension
  let flipped : C2FiniteMatrix period hPeriod dimension →L[Real]
      C2FiniteMatrix period hPeriod dimension →L[Real]
        C2FiniteMatrix period hPeriod dimension :=
    @ContinuousLinearMap.flip Real Real Real
      (C2FiniteMatrix period hPeriod dimension)
      (C2FiniteMatrix period hPeriod dimension)
      (C2FiniteMatrix period hPeriod dimension)
      _ _ _ _ _ _ _ _ _
      (RingHom.id Real) (RingHom.id Real) _ _ product
  exact product root + flipped root

theorem c2FiniteMatrixSquare_hasFDerivAt
    (dimension : Nat)
    (root : C2FiniteMatrix period hPeriod dimension) :
    HasFDerivAt (c2FiniteMatrixSquare period hPeriod dimension)
      (c2FiniteMatrixSylvester period hPeriod dimension root) root := by
  have hDerivative :=
    ((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension).hasFDerivAt
        (x := root)).clm_apply
      (hasFDerivAt_id root)
  simpa [c2FiniteMatrixSquare, c2FiniteMatrixSylvester] using hDerivative

theorem c2FiniteMatrixSquare_contDiff (dimension : Nat) :
    ContDiff Real ∞ (c2FiniteMatrixSquare period hPeriod dimension) :=
  (c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension).contDiff.clm_apply
      contDiff_id

/-- Coordinatewise bridge to the pre-existing strong matrix core. -/
def c2FiniteMatrixToStrongCore (dimension : Nat) :
    C2FiniteMatrix period hPeriod dimension →L[Real]
      StrongFiniteMatrix period hPeriod dimension :=
  ContinuousLinearMap.piMap fun _ : Fin dimension =>
    ContinuousLinearMap.piMap fun _ : Fin dimension =>
      canonicalPhysicalScalarC2JetCoreToStrongCore period hPeriod

@[simp]
theorem c2FiniteMatrixToStrongCore_smooth
    (dimension : Nat)
    (matrix : SmoothFiniteMatrix period hPeriod dimension) :
    c2FiniteMatrixToStrongCore period hPeriod dimension
        (smoothFiniteMatrixToC2 period hPeriod dimension matrix) =
      smoothFiniteMatrixToStrong period hPeriod dimension matrix := by
  funext row column
  exact canonicalPhysicalScalarC2JetCoreToStrongCore_smooth
    period hPeriod (matrix row column)

/-- Summary gate for finite C² coefficient matrices. -/
theorem canonical_physical_c2_finite_matrix_product_gate
    (dimension : Nat) :
    DenseRange (smoothFiniteMatrixToC2 period hPeriod dimension) ∧
      ContDiff Real ∞
        (c2FiniteMatrixSquare period hPeriod dimension) ∧
      (∀ first second : SmoothFiniteMatrix period hPeriod dimension,
        c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) dimension
            (smoothFiniteMatrixToC2 period hPeriod dimension first)
            (smoothFiniteMatrixToC2 period hPeriod dimension second) =
          smoothFiniteMatrixToC2 period hPeriod dimension
            (smoothFiniteMatrixProduct
              period hPeriod dimension first second)) := by
  exact ⟨smoothFiniteMatrixToC2_denseRange period hPeriod dimension,
    c2FiniteMatrixSquare_contDiff period hPeriod dimension,
    c2FiniteMatrixProduct_smooth period hPeriod dimension⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
end JanusFormal
