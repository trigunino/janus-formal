import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D

/-!
# C²-core inverse of the regular identity root

The Lorentz chart already makes the square of its selected root invertible in
the completed C² matrix algebra.  Hence the root itself is invertible.  This
gives a smooth C²-core inverse whose evaluation is the previously constructed
pointwise inverse-root matrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

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

/-- In any associative completed matrix algebra, invertibility of a square
implies invertibility of its root. -/
theorem c2FiniteMatrix_mem_unitSet_of_square_mem
    (matrix : C2Matrix period hPeriod)
    (hSquare : c2FiniteMatrixSquare period hPeriod 4 matrix ∈
      c2FiniteMatrixUnitSet period hPeriod 4) :
    matrix ∈ c2FiniteMatrixUnitSet period hPeriod 4 := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4
  change ∃ equivalence : C2Matrix period hPeriod ≃L[Real]
      C2Matrix period hPeriod,
    (equivalence : C2Matrix period hPeriod →L[Real]
      C2Matrix period hPeriod) =
      product (c2FiniteMatrixSquare period hPeriod 4 matrix) at hSquare
  rcases hSquare with ⟨squareEquivalence, hSquareEquivalence⟩
  have hSquareBijective : Function.Bijective
      (product (c2FiniteMatrixSquare period hPeriod 4 matrix)) := by
    rw [← hSquareEquivalence]
    exact squareEquivalence.bijective
  have hMatrixBijective : Function.Bijective (product matrix) := by
    constructor
    · intro first second hEqual
      apply hSquareBijective.1
      change product (product matrix matrix) first =
        product (product matrix matrix) second
      rw [c2FiniteMatrixProduct_assoc, c2FiniteMatrixProduct_assoc]
      exact congrArg (product matrix) hEqual
    · intro target
      rcases hSquareBijective.2 target with ⟨source, hSource⟩
      refine ⟨product matrix source, ?_⟩
      calc
        product matrix (product matrix source) =
            product (product matrix matrix) source :=
          (c2FiniteMatrixProduct_assoc period hPeriod 4
            matrix matrix source).symm
        _ = product (c2FiniteMatrixSquare period hPeriod 4 matrix) source := rfl
        _ = target := hSource
  let inverseRoot : C2Matrix period hPeriod →L[Real]
      C2Matrix period hPeriod :=
    (product matrix).comp squareEquivalence.symm.toContinuousLinearMap
  have hInverseRight : Function.RightInverse inverseRoot (product matrix) := by
    intro target
    change product matrix
        (product matrix (squareEquivalence.symm target)) = target
    calc
      product matrix (product matrix (squareEquivalence.symm target)) =
          product (product matrix matrix) (squareEquivalence.symm target) :=
        (c2FiniteMatrixProduct_assoc period hPeriod 4 matrix matrix
          (squareEquivalence.symm target)).symm
      _ = product (c2FiniteMatrixSquare period hPeriod 4 matrix)
          (squareEquivalence.symm target) := rfl
      _ = squareEquivalence (squareEquivalence.symm target) := by
        exact DFunLike.congr_fun hSquareEquivalence.symm
          (squareEquivalence.symm target)
      _ = target := squareEquivalence.apply_symm_apply target
  have hInverseLeft : Function.LeftInverse inverseRoot (product matrix) := by
    intro source
    apply hMatrixBijective.1
    exact hInverseRight (product matrix source)
  let equivalence := ContinuousLinearEquiv.equivOfInverse
    (product matrix) inverseRoot hInverseLeft hInverseRight
  change ∃ current : C2Matrix period hPeriod ≃L[Real]
      C2Matrix period hPeriod,
    (current : C2Matrix period hPeriod →L[Real]
      C2Matrix period hPeriod) = product matrix
  exact ⟨equivalence, rfl⟩

/-- Root perturbations for which both the local root and the affine target are
available in the completed C² matrix algebra. -/
def c2IdentityRootInvertiblePerturbationDomain :
    Set (C2Matrix period hPeriod) :=
  c2IdentityRootPerturbationDomain period hPeriod ∩
    (fun variation =>
      c2FiniteMatrixIdentity period hPeriod 4 + variation) ⁻¹'
      c2FiniteMatrixUnitSet period hPeriod 4

theorem c2IdentityRootInvertiblePerturbationDomain_isOpen :
    IsOpen (c2IdentityRootInvertiblePerturbationDomain
      period hPeriod) := by
  exact (c2IdentityRootPerturbationDomain_isOpen period hPeriod).inter
    ((c2FiniteMatrixUnitSet_isOpen period hPeriod 4).preimage
      (continuous_const.add continuous_id))

theorem zero_mem_c2IdentityRootInvertiblePerturbationDomain :
    (0 : C2Matrix period hPeriod) ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod := by
  constructor
  · exact zero_mem_c2IdentityRootPerturbationDomain period hPeriod
  · simpa using c2FiniteMatrixIdentity_mem_unitSet period hPeriod 4

/-- The selected identity root is a unit whenever its affine target is. -/
theorem c2IdentityRootBranch_mem_unitSet
    {variation : C2Matrix period hPeriod}
    (hVariation : variation ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod) :
    c2IdentityRootBranch period hPeriod variation ∈
      c2FiniteMatrixUnitSet period hPeriod 4 := by
  apply c2FiniteMatrix_mem_unitSet_of_square_mem period hPeriod
  rw [c2IdentityRootBranch_square period hPeriod hVariation.1]
  exact hVariation.2

/-- Inverse of the selected root in the completed C² matrix algebra. -/
def regularGeneralMetricC2IdentityRootInverseC2Matrix
    (variation : C2Matrix period hPeriod) : C2Matrix period hPeriod :=
  c2FiniteMatrixInverse period hPeriod 4
    (c2IdentityRootBranch period hPeriod variation)

/-- The C² inverse root depends C²-smoothly on the chart parameter. -/
theorem regularGeneralMetricC2IdentityRootInverseC2Matrix_contDiffOn :
    ContDiffOn Real 2
      (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod)
      (c2IdentityRootInvertiblePerturbationDomain
        period hPeriod) := by
  have hRoot : ContDiffOn Real 2
      (c2IdentityRootBranch period hPeriod)
      (c2IdentityRootInvertiblePerturbationDomain period hPeriod) :=
    (c2IdentityRootBranch_contDiffOn period hPeriod).mono
      (fun _ hVariation => hVariation.1)
  have hInverse := (c2FiniteMatrixInverse_contDiffOn
    period hPeriod 4).of_le
      (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
        exact WithTop.coe_le_coe.mpr le_top)
  exact hInverse.comp hRoot
    (fun _ hVariation =>
      c2IdentityRootBranch_mem_unitSet
        period hPeriod hVariation)

theorem regularGeneralMetricC2IdentityRoot_mul_inverseC2Matrix
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (c2IdentityRootBranch period hPeriod variation)
        (regularGeneralMetricC2IdentityRootInverseC2Matrix
          period hPeriod variation) =
      c2FiniteMatrixIdentity period hPeriod 4 :=
  c2FiniteMatrixProduct_inverse_right period hPeriod 4 _
    (c2IdentityRootBranch_mem_unitSet period hPeriod hVariation)

theorem regularGeneralMetricC2IdentityRootInverseC2Matrix_mul
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (regularGeneralMetricC2IdentityRootInverseC2Matrix
          period hPeriod variation)
        (c2IdentityRootBranch period hPeriod variation) =
      c2FiniteMatrixIdentity period hPeriod 4 :=
  c2FiniteMatrixProduct_inverse_left period hPeriod 4 _
    (c2IdentityRootBranch_mem_unitSet period hPeriod hVariation)

/-- Every genuine regular Lorentz-chart variation lies in the matrix domain
used by the inverse-root branch. -/
theorem regularGeneralMetricC2VariationMatrix_mem_invertibleRootDomain
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularGeneralMetricC2VariationMatrix period hPeriod metric tensor ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod := by
  constructor
  · exact hVariation.2.1
  · have hUnit := hVariation.1.1
    change c2FiniteMatrixIdentity period hPeriod 4 +
        regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor ∈
      c2FiniteMatrixUnitSet period hPeriod 4 at hUnit
    exact hUnit

/-- Evaluating the C²-core inverse gives the genuine pointwise inverse root. -/
theorem regularGeneralMetricC2IdentityRootInverseC2Matrix_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor)) point =
      regularGeneralMetricC2IdentityRootInverseMatrixAt
        period hPeriod metric tensor point := by
  have hMatrix :=
    regularGeneralMetricC2VariationMatrix_mem_invertibleRootDomain
      period hPeriod metric tensor hVariation
  have hRight := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point)
    (regularGeneralMetricC2IdentityRoot_mul_inverseC2Matrix
      period hPeriod
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor) hMatrix)
  simp only [c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_identity] at hRight
  change regularGeneralMetricC2IdentityRootMatrixAt
      period hPeriod metric tensor point *
      c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor)) point = 1 at hRight
  exact (Matrix.inv_eq_right_inv hRight).symm

/-- Gate marker: the chart root now has a smooth inverse in the same completed
C² matrix algebra, compatible with the intrinsic pointwise inverse. -/
theorem regular_general_metric_c2_identity_root_inverse_core_gate
    : IsOpen (c2IdentityRootInvertiblePerturbationDomain
        period hPeriod) ∧
      (0 : C2Matrix period hPeriod) ∈
        c2IdentityRootInvertiblePerturbationDomain period hPeriod ∧
      ContDiffOn Real 2
        (regularGeneralMetricC2IdentityRootInverseC2Matrix
          period hPeriod)
        (c2IdentityRootInvertiblePerturbationDomain
          period hPeriod) ∧
      ∀ (metric : RegularGeneralLorentzMetric period hPeriod)
        (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
        (_hVariation : regularGeneralMetricSmoothC2Variation
          period hPeriod metric tensor ∈
            regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
        (point : EffectiveQuotient period hPeriod),
        c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
              (regularGeneralMetricC2VariationMatrix
                period hPeriod metric tensor)) point =
          regularGeneralMetricC2IdentityRootInverseMatrixAt
            period hPeriod metric tensor point := by
  exact ⟨
    c2IdentityRootInvertiblePerturbationDomain_isOpen period hPeriod,
    zero_mem_c2IdentityRootInvertiblePerturbationDomain period hPeriod,
    regularGeneralMetricC2IdentityRootInverseC2Matrix_contDiffOn
      period hPeriod,
    fun metric tensor _hVariation point =>
      regularGeneralMetricC2IdentityRootInverseC2Matrix_valueAt
        period hPeriod metric tensor _hVariation point⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
end JanusFormal
