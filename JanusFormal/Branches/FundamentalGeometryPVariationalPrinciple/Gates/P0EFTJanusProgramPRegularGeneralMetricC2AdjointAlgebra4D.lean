import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMetricInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D

/-!
# Metric adjoint on the regular-frame C² matrix algebra

This builds the bounded transpose and the adjoint `G⁻¹ Rᵀ G` associated with
the genuine regular-frame metric matrix.  The construction stays on the same
completed C² matrix core used by the identity root branch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2AdjointAlgebra4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D

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

/-- Bounded coordinate transpose on the completed C² matrix core. -/
def c2FiniteMatrixTranspose :
    C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod :=
  ContinuousLinearMap.pi fun row : Fin 4 =>
    ContinuousLinearMap.pi fun column : Fin 4 =>
      (ContinuousLinearMap.proj row :
        (Fin 4 → C2Scalar period hPeriod) →L[Real]
          C2Scalar period hPeriod).comp
        (ContinuousLinearMap.proj column :
          C2Matrix period hPeriod →L[Real]
            (Fin 4 → C2Scalar period hPeriod))

@[simp]
theorem c2FiniteMatrixTranspose_apply
    (matrix : C2Matrix period hPeriod)
    (row column : Fin 4) :
    c2FiniteMatrixTranspose period hPeriod matrix row column =
      matrix column row :=
  rfl

theorem c2FiniteMatrixTranspose_product
    (first second : C2Matrix period hPeriod) :
    c2FiniteMatrixTranspose period hPeriod
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 first second) =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (c2FiniteMatrixTranspose period hPeriod second)
        (c2FiniteMatrixTranspose period hPeriod first) := by
  funext row column
  simp only [c2FiniteMatrixTranspose_apply,
    c2FiniteMatrixProduct_apply]
  apply Finset.sum_congr rfl
  intro middle _
  exact c2ScalarProduct_comm period hPeriod _ _

@[simp]
theorem c2FiniteMatrixTranspose_identity :
    c2FiniteMatrixTranspose period hPeriod
        (c2FiniteMatrixIdentity period hPeriod 4) =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  funext row column
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (smoothFiniteMatrixIdentity period hPeriod 4 column row) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (smoothFiniteMatrixIdentity period hPeriod 4 row column)
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp [smoothFiniteMatrixIdentity,
    P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.constantSmoothField,
    eq_comm]

theorem c2FiniteMatrixTranspose_involutive
    (matrix : C2Matrix period hPeriod) :
    c2FiniteMatrixTranspose period hPeriod
        (c2FiniteMatrixTranspose period hPeriod matrix) = matrix := by
  rfl

theorem regularFrameMetricC2Matrix_transpose
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    c2FiniteMatrixTranspose period hPeriod
        (regularFrameMetricC2Matrix period hPeriod metric) =
      regularFrameMetricC2Matrix period hPeriod metric := by
  funext row column
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (regularFrameMetricMatrix period hPeriod metric column row) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (regularFrameMetricMatrix period hPeriod metric row column)
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact metric.metric.tensor.symmetric point _ _

theorem regularFrameMetricInverseC2Matrix_transpose
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    c2FiniteMatrixTranspose period hPeriod
        (regularFrameMetricInverseC2Matrix period hPeriod metric) =
      regularFrameMetricInverseC2Matrix period hPeriod metric := by
  funext row column
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod metric column row) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod metric row column)
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹
      column row =
    (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ row column
  have hMetric :
      (regularFrameMetricMatrixMap period hPeriod metric point).transpose =
        regularFrameMetricMatrixMap period hPeriod metric point := by
    ext first second
    exact metric.metric.tensor.symmetric point _ _
  have hInverse := Matrix.transpose_nonsing_inv
    (A := regularFrameMetricMatrixMap period hPeriod metric point)
  rw [hMetric] at hInverse
  exact congrFun (congrFun hInverse row) column

private def c2FiniteMatrixRightProduct
    (matrix : C2Matrix period hPeriod) :
    C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod :=
  (c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4).flip matrix

/-- Metric adjoint `G⁻¹ Rᵀ G` in the genuine stored regular frame. -/
def regularFrameMetricC2Adjoint
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod :=
  (c2FiniteMatrixRightProduct period hPeriod
      (regularFrameMetricC2Matrix period hPeriod metric)).comp
    ((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) 4
      (regularFrameMetricInverseC2Matrix period hPeriod metric)).comp
        (c2FiniteMatrixTranspose period hPeriod))

@[simp]
theorem regularFrameMetricC2Adjoint_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (matrix : C2Matrix period hPeriod) :
    regularFrameMetricC2Adjoint period hPeriod metric matrix =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4
          (regularFrameMetricInverseC2Matrix period hPeriod metric)
          (c2FiniteMatrixTranspose period hPeriod matrix))
        (regularFrameMetricC2Matrix period hPeriod metric) :=
  rfl

@[simp]
theorem regularFrameMetricC2Adjoint_identity
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    regularFrameMetricC2Adjoint period hPeriod metric
        (c2FiniteMatrixIdentity period hPeriod 4) =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  rw [regularFrameMetricC2Adjoint_apply,
    c2FiniteMatrixTranspose_identity,
    c2FiniteMatrixProduct_identity_right,
    regularFrameMetricInverseC2Matrix_mul_matrix]

theorem regularFrameMetricC2Adjoint_product
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : C2Matrix period hPeriod) :
    regularFrameMetricC2Adjoint period hPeriod metric
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 first second) =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (regularFrameMetricC2Adjoint period hPeriod metric second)
        (regularFrameMetricC2Adjoint period hPeriod metric first) := by
  rw [regularFrameMetricC2Adjoint_apply,
    c2FiniteMatrixTranspose_product,
    regularFrameMetricC2Adjoint_apply,
    regularFrameMetricC2Adjoint_apply]
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4
  let inverse := regularFrameMetricInverseC2Matrix period hPeriod metric
  let gram := regularFrameMetricC2Matrix period hPeriod metric
  let firstTranspose := c2FiniteMatrixTranspose period hPeriod first
  let secondTranspose := c2FiniteMatrixTranspose period hPeriod second
  change product (product inverse
      (product secondTranspose firstTranspose)) gram =
    product (product (product inverse secondTranspose) gram)
      (product (product inverse firstTranspose) gram)
  symm
  calc
    product (product (product inverse secondTranspose) gram)
        (product (product inverse firstTranspose) gram) =
      product (product inverse secondTranspose)
        (product gram (product (product inverse firstTranspose) gram)) :=
      c2FiniteMatrixProduct_assoc period hPeriod 4 _ _ _
    _ = product (product inverse secondTranspose)
        (product gram (product inverse (product firstTranspose gram))) := by
      rw [c2FiniteMatrixProduct_assoc period hPeriod 4
        inverse firstTranspose gram]
    _ = product (product inverse secondTranspose)
        (product (product gram inverse) (product firstTranspose gram)) := by
      rw [← c2FiniteMatrixProduct_assoc period hPeriod 4
        gram inverse (product firstTranspose gram)]
    _ = product (product inverse secondTranspose)
        (product (c2FiniteMatrixIdentity period hPeriod 4)
          (product firstTranspose gram)) := by
      rw [show product gram inverse =
          c2FiniteMatrixIdentity period hPeriod 4 from
        regularFrameMetricC2Matrix_mul_inverse period hPeriod metric]
    _ = product (product inverse secondTranspose)
        (product firstTranspose gram) := by
      rw [c2FiniteMatrixProduct_identity_left]
    _ = product inverse
        (product secondTranspose (product firstTranspose gram)) :=
      c2FiniteMatrixProduct_assoc period hPeriod 4 _ _ _
    _ = product inverse
        (product (product secondTranspose firstTranspose) gram) := by
      rw [c2FiniteMatrixProduct_assoc period hPeriod 4
        secondTranspose firstTranspose gram]
    _ = product (product inverse
        (product secondTranspose firstTranspose)) gram := by
      rw [c2FiniteMatrixProduct_assoc period hPeriod 4
        inverse (product secondTranspose firstTranspose) gram]

theorem regularFrameMetricC2Adjoint_square
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (matrix : C2Matrix period hPeriod) :
    regularFrameMetricC2Adjoint period hPeriod metric
        (c2FiniteMatrixSquare period hPeriod 4 matrix) =
      c2FiniteMatrixSquare period hPeriod 4
        (regularFrameMetricC2Adjoint period hPeriod metric matrix) := by
  exact regularFrameMetricC2Adjoint_product
    period hPeriod metric matrix matrix

theorem regularGeneralMetricTensorC2Matrix_transpose
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    c2FiniteMatrixTranspose period hPeriod
        (smoothGeneralMetricTensorToC2Matrix period hPeriod
          (RegularFrame period hPeriod metric) tensor) =
      smoothGeneralMetricTensorToC2Matrix period hPeriod
        (RegularFrame period hPeriod metric) tensor := by
  funext row column
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (generalMetricFrameCoefficient period hPeriod
        (RegularFrame period hPeriod metric) tensor column row) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (generalMetricFrameCoefficient period hPeriod
        (RegularFrame period hPeriod metric) tensor row column)
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact tensor.symmetric point _ _

/-- Lowering the first index of the relative variation recovers the original
covariant tensor matrix exactly: `G (g⁻¹h) = h`. -/
theorem regularFrameMetricC2Matrix_mul_variation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (regularFrameMetricC2Matrix period hPeriod metric)
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor) =
      smoothGeneralMetricTensorToC2Matrix period hPeriod
        (RegularFrame period hPeriod metric) tensor := by
  classical
  change c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) 4
      (smoothFiniteMatrixToC2 period hPeriod 4
        (regularFrameMetricMatrix period hPeriod metric))
      (smoothFiniteMatrixToC2 period hPeriod 4
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (RegularFrame period hPeriod metric) metric.metric tensor)) = _
  rw [c2FiniteMatrixProduct_smooth]
  funext row column
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (smoothFiniteMatrixProduct period hPeriod 4
        (regularFrameMetricMatrix period hPeriod metric)
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (RegularFrame period hPeriod metric) metric.metric tensor)
        row column) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (generalMetricFrameCoefficient period hPeriod
        (RegularFrame period hPeriod metric) tensor row column)
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  let frame := RegularFrame period hPeriod metric
  let raised := inverseMetricSharp period hPeriod metric.metric point
    (tensor.tensor point (metric.frame column point))
  have hCoefficient (middle : Fin 4) :
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
          metric.metric tensor middle column point =
        generalMetricFiniteFrameCoefficientAt period hPeriod frame
          metric.metric point middle raised := by
    rfl
  have hReconstruct := generalMetricFiniteFrameCoefficientAt_reconstructs
    period hPeriod frame metric.metric point raised
  have hRaised : raised = ∑ middle : Fin 4,
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
          metric.metric tensor middle column point •
        metric.frame middle point := by
    calc
      raised = ∑ middle : Fin 4,
          generalMetricFiniteFrameCoefficientAt period hPeriod frame
              metric.metric point middle raised • metric.frame middle point :=
        hReconstruct
      _ = _ := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [hCoefficient]
  have hPair :
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
            metric.metric tensor middle column point =
        metric.metric.tensor.tensor point (metric.frame row point) raised := by
    calc
      _ = ∑ middle : Fin 4,
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
              metric.metric tensor middle column point *
            regularFrameMetricMatrix period hPeriod metric row middle point := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [mul_comm]
      _ = metric.metric.tensor.tensor point (metric.frame row point)
          (∑ middle : Fin 4,
            smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
                metric.metric tensor middle column point •
              metric.frame middle point) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul, regularFrameMetricMatrix_apply]
      _ = _ := congrArg
        (fun vector => metric.metric.tensor.tensor point
          (metric.frame row point) vector) hRaised.symm
  have hFlat := congrArg
    (fun covector => covector (metric.frame row point))
    (metric_flat_inverseMetricSharp period hPeriod metric.metric point
      (tensor.tensor point (metric.frame column point)))
  have hPairRaised :
      metric.metric.tensor.tensor point (metric.frame row point) raised =
        tensor.tensor point (metric.frame row point)
          (metric.frame column point) := by
    calc
      metric.metric.tensor.tensor point (metric.frame row point) raised =
          metric.metric.tensor.tensor point raised (metric.frame row point) :=
        metric.metric.tensor.symmetric _ _ _
      _ = tensor.tensor point (metric.frame column point)
          (metric.frame row point) := by
        rw [← metric.metric.musical_eq_tensor point]
        exact hFlat
      _ = _ := tensor.symmetric _ _ _
  simpa only [smoothFiniteMatrixProduct,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, generalMetricFrameCoefficient_apply,
    regularGeneralLorentzMetricSmoothD8Frame_vectorAt] using
      hPair.trans hPairRaised

theorem regularGeneralMetricC2VariationMatrix_transpose_mul_metric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (c2FiniteMatrixTranspose period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor))
        (regularFrameMetricC2Matrix period hPeriod metric) =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (regularFrameMetricC2Matrix period hPeriod metric)
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor) := by
  let variation := regularGeneralMetricC2VariationMatrix
    period hPeriod metric tensor
  let gram := regularFrameMetricC2Matrix period hPeriod metric
  let covariant := smoothGeneralMetricTensorToC2Matrix period hPeriod
    (RegularFrame period hPeriod metric) tensor
  have hLowered :
      c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 gram variation =
        covariant :=
    regularFrameMetricC2Matrix_mul_variation
      period hPeriod metric tensor
  have hTransposeProduct :
      c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4
          (c2FiniteMatrixTranspose period hPeriod variation) gram =
        c2FiniteMatrixTranspose period hPeriod
          (c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) 4 gram variation) := by
    rw [c2FiniteMatrixTranspose_product,
      regularFrameMetricC2Matrix_transpose]
  have hTransposeLowered :
      c2FiniteMatrixTranspose period hPeriod
          (c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) 4 gram variation) =
        c2FiniteMatrixTranspose period hPeriod covariant :=
    congrArg (c2FiniteMatrixTranspose period hPeriod) hLowered
  have hCovariantSymmetric :
      c2FiniteMatrixTranspose period hPeriod covariant = covariant :=
    regularGeneralMetricTensorC2Matrix_transpose
      period hPeriod metric tensor
  exact hTransposeProduct.trans
    (hTransposeLowered.trans (hCovariantSymmetric.trans hLowered.symm))

theorem regularGeneralMetricC2VariationMatrix_selfAdjoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularFrameMetricC2Adjoint period hPeriod metric
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor) =
      regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor := by
  rw [regularFrameMetricC2Adjoint_apply,
    c2FiniteMatrixProduct_assoc,
    regularGeneralMetricC2VariationMatrix_transpose_mul_metric,
    ← c2FiniteMatrixProduct_assoc,
    regularFrameMetricInverseC2Matrix_mul_matrix,
    c2FiniteMatrixProduct_identity_left]

theorem regularGeneralMetricC2IdentityTarget_selfAdjoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularFrameMetricC2Adjoint period hPeriod metric
        (c2FiniteMatrixIdentity period hPeriod 4 +
          regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor) =
      c2FiniteMatrixIdentity period hPeriod 4 +
        regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor := by
  rw [map_add, regularFrameMetricC2Adjoint_identity,
    regularGeneralMetricC2VariationMatrix_selfAdjoint]

/-- Gate marker: the bounded metric adjoint fixes both the identity and the
exact affine target `I + g⁻¹h`. -/
theorem regular_general_metric_c2_adjoint_algebra_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Continuous (c2FiniteMatrixTranspose period hPeriod) ∧
      Continuous (regularFrameMetricC2Adjoint period hPeriod metric) ∧
      regularFrameMetricC2Adjoint period hPeriod metric
          (c2FiniteMatrixIdentity period hPeriod 4) =
        c2FiniteMatrixIdentity period hPeriod 4 ∧
      regularFrameMetricC2Adjoint period hPeriod metric
          (c2FiniteMatrixIdentity period hPeriod 4 +
            regularGeneralMetricC2VariationMatrix
              period hPeriod metric tensor) =
        c2FiniteMatrixIdentity period hPeriod 4 +
          regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor := by
  exact ⟨(c2FiniteMatrixTranspose period hPeriod).continuous,
    (regularFrameMetricC2Adjoint period hPeriod metric).continuous,
    regularFrameMetricC2Adjoint_identity period hPeriod metric,
    regularGeneralMetricC2IdentityTarget_selfAdjoint
      period hPeriod metric tensor⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2AdjointAlgebra4D
end JanusFormal
