import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixExact4D

/-!
# C² jet rigidity for the regular identity root

The value field of the completed root is already smooth.  Equality of the
completed squares and pointwise injectivity of the Sylvester operator force
the first and second jet components to be the genuine derivatives of that
smooth value field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev PhysicalIndex :=
  Fin (finiteSmoothTangentFrame period hPeriod).count

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev Matrix4 :=
  Matrix (Fin 4) (Fin 4) Real

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

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

private def c2ScalarFirstAtLinearMap
    (point : EffectiveQuotient period hPeriod)
    (index : PhysicalIndex period hPeriod) :
    C2Scalar period hPeriod →ₗ[Real] Real where
  toFun value := (value.1 point).2.1 index
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def c2ScalarSecondAtLinearMap
    (point : EffectiveQuotient period hPeriod)
    (outer inner : PhysicalIndex period hPeriod) :
    C2Scalar period hPeriod →ₗ[Real] Real where
  toFun value := (value.1 point).2.2 outer inner
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Matrix of first jet components in one physical tangent direction. -/
def c2FiniteMatrixFirstAt
    (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : PhysicalIndex period hPeriod) : Matrix4 :=
  fun row column =>
    c2ScalarFirstAtLinearMap period hPeriod point index (matrix row column)

/-- Matrix of ordered second jet components. -/
def c2FiniteMatrixSecondAt
    (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (outer inner : PhysicalIndex period hPeriod) : Matrix4 :=
  fun row column =>
    c2ScalarSecondAtLinearMap period hPeriod point outer inner
      (matrix row column)

theorem c2FiniteMatrixFirstAt_product
    (first second : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : PhysicalIndex period hPeriod) :
    c2FiniteMatrixFirstAt period hPeriod
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 first second) point index =
      c2FiniteMatrixValueAt period hPeriod 4 first point *
          c2FiniteMatrixFirstAt period hPeriod second point index +
        c2FiniteMatrixFirstAt period hPeriod first point index *
          c2FiniteMatrixValueAt period hPeriod 4 second point := by
  ext row column
  unfold c2FiniteMatrixFirstAt
  rw [c2FiniteMatrixProduct_apply]
  change c2ScalarFirstAtLinearMap period hPeriod point index
      (∑ middle : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (first row middle) (second middle column)) =
    (∑ middle : Fin 4,
      ((first row middle).1 point).1 *
        ((second middle column).1 point).2.1 index) +
      ∑ middle : Fin 4,
        ((first row middle).1 point).2.1 index *
          ((second middle column).1 point).1
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro middle _
  change
    (((canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (first row middle) (second middle column)).1 point).2.1 index) = _
  change
    (scalarFrameJet2Mul
      ((first row middle).1 point)
      ((second middle column).1 point)).2.1 index = _
  simp [scalarFrameJet2Mul]
  ring

theorem c2FiniteMatrixSecondAt_product
    (first second : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (outer inner : PhysicalIndex period hPeriod) :
    c2FiniteMatrixSecondAt period hPeriod
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 first second)
        point outer inner =
      c2FiniteMatrixValueAt period hPeriod 4 first point *
          c2FiniteMatrixSecondAt period hPeriod second point outer inner +
        c2FiniteMatrixFirstAt period hPeriod first point outer *
          c2FiniteMatrixFirstAt period hPeriod second point inner +
        c2FiniteMatrixFirstAt period hPeriod first point inner *
          c2FiniteMatrixFirstAt period hPeriod second point outer +
        c2FiniteMatrixSecondAt period hPeriod first point outer inner *
          c2FiniteMatrixValueAt period hPeriod 4 second point := by
  ext row column
  unfold c2FiniteMatrixSecondAt
  rw [c2FiniteMatrixProduct_apply]
  change c2ScalarSecondAtLinearMap period hPeriod point outer inner
      (∑ middle : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (first row middle) (second middle column)) = _
  rw [map_sum]
  simp only [Matrix.add_apply, Matrix.mul_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro middle _
  change
    (((canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (first row middle) (second middle column)).1 point).2.2 outer inner) =
      ((first row middle).1 point).1 *
            ((second middle column).1 point).2.2 outer inner +
          ((first row middle).1 point).2.1 outer *
            ((second middle column).1 point).2.1 inner +
          ((first row middle).1 point).2.1 inner *
            ((second middle column).1 point).2.1 outer +
          ((first row middle).1 point).2.2 outer inner *
            ((second middle column).1 point).1
  change
    (scalarFrameJet2Mul
      ((first row middle).1 point)
      ((second middle column).1 point)).2.2 outer inner =
      ((first row middle).1 point).1 *
          ((second middle column).1 point).2.2 outer inner +
        ((first row middle).1 point).2.1 outer *
          ((second middle column).1 point).2.1 inner +
        ((first row middle).1 point).2.1 inner *
          ((second middle column).1 point).2.1 outer +
        ((first row middle).1 point).2.2 outer inner *
          ((second middle column).1 point).1
  simp [scalarFrameJet2Mul]
  ring

/-- A completed C² matrix root is determined by its value field and square
whenever the pointwise Sylvester family is injective. -/
theorem c2FiniteMatrix_eq_of_valueAt_eq_of_square_eq
    (first second : C2Matrix period hPeriod)
    (hValue : ∀ point,
      c2FiniteMatrixValueAt period hPeriod 4 first point =
        c2FiniteMatrixValueAt period hPeriod 4 second point)
    (hSquare : c2FiniteMatrixSquare period hPeriod 4 first =
      c2FiniteMatrixSquare period hPeriod 4 second)
    (hSylvester : ∀ point, Function.Injective
      (canonicalSylvesterOperator
        (c2FiniteMatrixValueAt period hPeriod 4 first point))) :
    first = second := by
  have hFirst : ∀ point index,
      c2FiniteMatrixFirstAt period hPeriod first point index =
        c2FiniteMatrixFirstAt period hPeriod second point index := by
    intro point index
    apply hSylvester point
    have hJet := congrArg
      (fun matrix => c2FiniteMatrixFirstAt period hPeriod matrix point index)
      hSquare
    simp only [c2FiniteMatrixSquare,
      c2FiniteMatrixFirstAt_product] at hJet
    simpa [canonicalSylvesterOperator_apply, hValue point] using hJet
  have hSecond : ∀ point outer inner,
      c2FiniteMatrixSecondAt period hPeriod first point outer inner =
        c2FiniteMatrixSecondAt period hPeriod second point outer inner := by
    intro point outer inner
    apply hSylvester point
    rw [canonicalSylvesterOperator_apply, hValue point]
    have hJet := congrArg
      (fun matrix => c2FiniteMatrixSecondAt period hPeriod
        matrix point outer inner) hSquare
    simp only [c2FiniteMatrixSquare,
      c2FiniteMatrixSecondAt_product] at hJet
    rw [hValue point, hFirst point outer, hFirst point inner] at hJet
    let base := c2FiniteMatrixValueAt period hPeriod 4 second point
    let firstOuter :=
      c2FiniteMatrixFirstAt period hPeriod second point outer
    let firstInner :=
      c2FiniteMatrixFirstAt period hPeriod second point inner
    let secondFirst :=
      c2FiniteMatrixSecondAt period hPeriod first point outer inner
    let secondSecond :=
      c2FiniteMatrixSecondAt period hPeriod second point outer inner
    have hReordered :
        (base * secondFirst + secondFirst * base) +
            (firstOuter * firstInner + firstInner * firstOuter) =
          (base * secondSecond + secondSecond * base) +
            (firstOuter * firstInner + firstInner * firstOuter) := by
      calc
        _ = base * secondFirst + firstOuter * firstInner +
              firstInner * firstOuter + secondFirst * base := by abel
        _ = base * secondSecond + firstOuter * firstInner +
              firstInner * firstOuter + secondSecond * base := by
            simpa only [base, firstOuter, firstInner, secondFirst,
              secondSecond] using hJet
        _ = _ := by abel
    exact add_right_cancel hReordered
  funext row column
  apply Subtype.ext
  apply ContinuousMap.ext
  intro point
  apply Prod.ext
  · exact congrFun (congrFun (hValue point) row) column
  · apply Prod.ext
    · funext index
      exact congrFun (congrFun (hFirst point index) row) column
    · funext outer inner
      exact congrFun (congrFun (hSecond point outer inner) row) column

theorem c2FiniteMatrixValueAt_smoothMatrixFieldToC2
    (field : SmoothQuotientField period hPeriod Matrix4)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod field) point =
      field point := by
  ext row column
  rfl

/-- The genuine smooth value field has exactly the same completed square as
the selected C² identity root. -/
theorem regularGeneralMetricC2IdentityRootSmoothC2_square
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor) :
    c2FiniteMatrixSquare period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod
          (regularGeneralMetricC2IdentityRootMatrixField
            period hPeriod metric tensor hRoot)) =
      c2FiniteMatrixIdentity period hPeriod 4 +
        regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor := by
  unfold c2FiniteMatrixSquare smoothMatrixFieldToC2
  rw [c2FiniteMatrixProduct_smooth]
  funext row column
  change
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D.smoothFiniteMatrixProduct
          period hPeriod 4
          (smoothMatrixFieldCoefficients period hPeriod
            (regularGeneralMetricC2IdentityRootMatrixField
              period hPeriod metric tensor hRoot))
          (smoothMatrixFieldCoefficients period hPeriod
            (regularGeneralMetricC2IdentityRootMatrixField
              period hPeriod metric tensor hRoot)) row column) =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothFiniteMatrixIdentity period hPeriod 4 row column) +
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
            (RegularFrame period hPeriod metric) metric.metric tensor
              row column)
  rw [← (smoothToCanonicalPhysicalScalarC2JetCore
    period hPeriod).map_add]
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore
    period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hSquare :=
    regularGeneralMetricC2IdentityRootMatrixAt_square_matrix
      period hPeriod metric tensor hRoot point
  have hEntry := congrFun (congrFun hSquare row) column
  change
    (∑ middle : Fin 4,
      regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point row middle *
        regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point middle column) =
      (if row = column then 1 else 0) +
        smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (RegularFrame period hPeriod metric) metric.metric tensor
            row column point
  change
    (∑ middle : Fin 4,
      regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point row middle *
        regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point middle column) =
      (if row = column then 1 else 0) +
        smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (RegularFrame period hPeriod metric) metric.metric tensor
            row column point at hEntry
  exact hEntry

/-- The selected completed root is exactly the C² jet of its smooth value
field, not merely pointwise equal to it. -/
theorem regularGeneralMetricC2IdentityRoot_eq_smoothMatrixFieldToC2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor) :
    c2IdentityRootBranch period hPeriod
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor) =
      smoothMatrixFieldToC2 period hPeriod
        (regularGeneralMetricC2IdentityRootMatrixField
          period hPeriod metric tensor hRoot) := by
  apply c2FiniteMatrix_eq_of_valueAt_eq_of_square_eq period hPeriod
  · intro point
    rw [c2FiniteMatrixValueAt_smoothMatrixFieldToC2]
    rfl
  · exact (c2IdentityRootBranch_square period hPeriod hRoot).trans
      (regularGeneralMetricC2IdentityRootSmoothC2_square
        period hPeriod metric tensor hRoot).symm
  · intro point
    exact (regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective
      period hPeriod metric tensor hRoot point).1

/-- The smooth root and inverse-root fields multiply to the completed matrix
identity. -/
theorem regularGeneralMetricC2IdentityRootSmoothC2_mul_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (smoothMatrixFieldToC2 period hPeriod
          (regularGeneralMetricC2IdentityRootMatrixField period hPeriod metric
            tensor (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
              period hPeriod metric hVariation).1))
        (smoothMatrixFieldToC2 period hPeriod
          (regularGeneralMetricC2IdentityRootInverseMatrixField
            period hPeriod metric tensor hVariation)) =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  unfold smoothMatrixFieldToC2
  rw [c2FiniteMatrixProduct_smooth]
  funext row column
  change
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D.smoothFiniteMatrixProduct
          period hPeriod 4
          (smoothMatrixFieldCoefficients period hPeriod
            (regularGeneralMetricC2IdentityRootMatrixField period hPeriod
              metric tensor
                (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
                  period hPeriod metric hVariation).1))
          (smoothMatrixFieldCoefficients period hPeriod
            (regularGeneralMetricC2IdentityRootInverseMatrixField
              period hPeriod metric tensor hVariation)) row column) =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (smoothFiniteMatrixIdentity period hPeriod 4 row column)
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore
    period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hProduct :=
    regularGeneralMetricC2IdentityRootMatrixAt_mul_inverse
      period hPeriod metric tensor hVariation point
  have hEntry := congrFun (congrFun hProduct row) column
  change
    (∑ middle : Fin 4,
      regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point row middle *
        regularGeneralMetricC2IdentityRootInverseMatrixAt
          period hPeriod metric tensor point middle column) =
      (if row = column then 1 else 0)
  simpa [Matrix.mul_apply, Matrix.one_apply] using hEntry

/-- The algebraic C² inverse is exactly the C² jet of the genuine smooth
inverse-root field. -/
theorem regularGeneralMetricC2IdentityRootInverseC2Matrix_eq_smoothMatrixFieldToC2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor) =
      smoothMatrixFieldToC2 period hPeriod
        (regularGeneralMetricC2IdentityRootInverseMatrixField
          period hPeriod metric tensor hVariation) := by
  let variation := regularGeneralMetricC2VariationMatrix
    period hPeriod metric tensor
  let root := c2IdentityRootBranch period hPeriod variation
  let inverse := regularGeneralMetricC2IdentityRootInverseC2Matrix
    period hPeriod variation
  let smoothInverse := smoothMatrixFieldToC2 period hPeriod
    (regularGeneralMetricC2IdentityRootInverseMatrixField
      period hPeriod metric tensor hVariation)
  have hDomain :=
    regularGeneralMetricC2VariationMatrix_mem_invertibleRootDomain
      period hPeriod metric tensor hVariation
  have hRootSmooth :=
    regularGeneralMetricC2IdentityRoot_eq_smoothMatrixFieldToC2
      period hPeriod metric tensor
        (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
          period hPeriod metric hVariation).1
  have hRootMulSmoothInverse :
      c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 root smoothInverse =
        c2FiniteMatrixIdentity period hPeriod 4 := by
    dsimp only [root, variation]
    rw [hRootSmooth]
    exact regularGeneralMetricC2IdentityRootSmoothC2_mul_inverse
      period hPeriod metric tensor hVariation
  have hInverseMulRoot :
      c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 inverse root =
        c2FiniteMatrixIdentity period hPeriod 4 :=
    regularGeneralMetricC2IdentityRootInverseC2Matrix_mul
      period hPeriod variation hDomain
  change inverse = smoothInverse
  calc
    inverse = c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4 inverse
          (c2FiniteMatrixIdentity period hPeriod 4) :=
      (c2FiniteMatrixProduct_identity_right period hPeriod 4 inverse).symm
    _ = c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4 inverse
          (c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) 4 root smoothInverse) := by
      rw [hRootMulSmoothInverse]
    _ = c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
          (c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) 4 inverse root)
          smoothInverse :=
      (c2FiniteMatrixProduct_assoc period hPeriod 4
        inverse root smoothInverse).symm
    _ = c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
          (c2FiniteMatrixIdentity period hPeriod 4) smoothInverse := by
      rw [hInverseMulRoot]
    _ = smoothInverse :=
      c2FiniteMatrixProduct_identity_left period hPeriod 4 smoothInverse

/-- Gate marker: both the selected root and its inverse are reconstructed as
full genuine smooth C² jets. -/
theorem regular_general_metric_c2_identity_root_jet_rigidity_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    c2IdentityRootBranch period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod metric tensor) =
        smoothMatrixFieldToC2 period hPeriod
          (regularGeneralMetricC2IdentityRootMatrixField period hPeriod metric
            tensor (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
              period hPeriod metric hVariation).1) ∧
      regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor) =
        smoothMatrixFieldToC2 period hPeriod
          (regularGeneralMetricC2IdentityRootInverseMatrixField
            period hPeriod metric tensor hVariation) :=
  ⟨regularGeneralMetricC2IdentityRoot_eq_smoothMatrixFieldToC2
      period hPeriod metric tensor
        (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
          period hPeriod metric hVariation).1,
    regularGeneralMetricC2IdentityRootInverseC2Matrix_eq_smoothMatrixFieldToC2
      period hPeriod metric tensor hVariation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D
end JanusFormal
