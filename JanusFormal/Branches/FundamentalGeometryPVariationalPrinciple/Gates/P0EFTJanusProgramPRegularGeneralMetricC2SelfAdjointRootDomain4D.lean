import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2AdjointAlgebra4D
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Self-adjoint identity-root domain for regular general metrics

The square-chart source produced by the inverse-function theorem is arbitrary,
so it need not be invariant under the metric adjoint.  This file restricts the
zero-centred perturbation domain to the open locus where the adjoint root also
lies in that source.  Chart injectivity then selects the self-adjoint root.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricAffineLorentzRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2AdjointAlgebra4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

private abbrev IdentitySquareChart :=
  c2MatrixLocalSquareChart period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod)

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

/-- Open root domain restricted so that the metric-adjoint root remains in the
same square-chart source. -/
def regularGeneralMetricC2SelfAdjointRootDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (C2Matrix period hPeriod) :=
  c2IdentityRootPerturbationDomain period hPeriod ∩
    (fun variation =>
      regularFrameMetricC2Adjoint period hPeriod metric
        (c2IdentityRootBranch period hPeriod variation)) ⁻¹'
      (IdentitySquareChart period hPeriod).source

theorem regularGeneralMetricC2SelfAdjointRootDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2SelfAdjointRootDomain
      period hPeriod metric) := by
  have hContinuous : ContinuousOn
      (fun variation =>
        regularFrameMetricC2Adjoint period hPeriod metric
          (c2IdentityRootBranch period hPeriod variation))
      (c2IdentityRootPerturbationDomain period hPeriod) :=
    (regularFrameMetricC2Adjoint period hPeriod metric).continuous
      |>.comp_continuousOn
        (c2IdentityRootBranch_contDiffOn period hPeriod).continuousOn
  exact hContinuous.isOpen_inter_preimage
    (c2IdentityRootPerturbationDomain_isOpen period hPeriod)
    (IdentitySquareChart period hPeriod).open_source

theorem zero_mem_regularGeneralMetricC2SelfAdjointRootDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (0 : C2Matrix period hPeriod) ∈
      regularGeneralMetricC2SelfAdjointRootDomain period hPeriod metric := by
  constructor
  · exact zero_mem_c2IdentityRootPerturbationDomain period hPeriod
  · change regularFrameMetricC2Adjoint period hPeriod metric
        (c2IdentityRootBranch period hPeriod 0) ∈
      (IdentitySquareChart period hPeriod).source
    rw [c2IdentityRootBranch_zero,
      regularFrameMetricC2Adjoint_identity]
    simpa only [smoothMatrixFieldToC2_identityRoot] using
      smoothMatrixFieldToC2_mem_localSquareChart_source period hPeriod
        (c2IdentityRootField period hPeriod)
        (c2IdentityRootField_regular period hPeriod)

theorem c2IdentityRootBranch_mem_localSquareChart_source
    {variation : C2Matrix period hPeriod}
    (hVariation : variation ∈
      c2IdentityRootPerturbationDomain period hPeriod) :
    c2IdentityRootBranch period hPeriod variation ∈
      (IdentitySquareChart period hPeriod).source := by
  change (IdentitySquareChart period hPeriod).symm
      (c2FiniteMatrixSquare period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod
          (c2IdentityRootField period hPeriod)) + variation) ∈
    (IdentitySquareChart period hPeriod).source
  exact (IdentitySquareChart period hPeriod).map_target hVariation

/-- On the restricted open domain, chart uniqueness forces the selected root
to equal its metric adjoint. -/
theorem regularGeneralMetricC2IdentityRoot_adjoint_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor ∈
      regularGeneralMetricC2SelfAdjointRootDomain
        period hPeriod metric) :
    regularFrameMetricC2Adjoint period hPeriod metric
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor)) =
      c2IdentityRootBranch period hPeriod
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor) := by
  let variation := regularGeneralMetricC2VariationMatrix
    period hPeriod metric tensor
  let root := c2IdentityRootBranch period hPeriod variation
  apply (IdentitySquareChart period hPeriod).injOn
    hVariation.2
    (c2IdentityRootBranch_mem_localSquareChart_source
      period hPeriod hVariation.1)
  change c2FiniteMatrixSquare period hPeriod 4
      (regularFrameMetricC2Adjoint period hPeriod metric root) =
    c2FiniteMatrixSquare period hPeriod 4 root
  calc
    c2FiniteMatrixSquare period hPeriod 4
        (regularFrameMetricC2Adjoint period hPeriod metric root) =
      regularFrameMetricC2Adjoint period hPeriod metric
        (c2FiniteMatrixSquare period hPeriod 4 root) :=
      (regularFrameMetricC2Adjoint_square
        period hPeriod metric root).symm
    _ = regularFrameMetricC2Adjoint period hPeriod metric
        (c2FiniteMatrixIdentity period hPeriod 4 + variation) :=
      congrArg (regularFrameMetricC2Adjoint period hPeriod metric)
        (c2IdentityRootBranch_square period hPeriod hVariation.1)
    _ = c2FiniteMatrixIdentity period hPeriod 4 + variation :=
      regularGeneralMetricC2IdentityTarget_selfAdjoint
        period hPeriod metric tensor
    _ = c2FiniteMatrixSquare period hPeriod 4 root :=
      (c2IdentityRootBranch_square period hPeriod hVariation.1).symm

/-- Matrix self-adjointness in the equivalent commutation form `RᵀG = GR`. -/
theorem regularGeneralMetricC2IdentityRoot_transpose_mul_metric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor ∈
      regularGeneralMetricC2SelfAdjointRootDomain
        period hPeriod metric) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (c2FiniteMatrixTranspose period hPeriod
          (c2IdentityRootBranch period hPeriod
            (regularGeneralMetricC2VariationMatrix
              period hPeriod metric tensor)))
        (regularFrameMetricC2Matrix period hPeriod metric) =
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (regularFrameMetricC2Matrix period hPeriod metric)
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor)) := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4
  let gram := regularFrameMetricC2Matrix period hPeriod metric
  let inverse := regularFrameMetricInverseC2Matrix period hPeriod metric
  let root := c2IdentityRootBranch period hPeriod
    (regularGeneralMetricC2VariationMatrix period hPeriod metric tensor)
  let rootTranspose := c2FiniteMatrixTranspose period hPeriod root
  have hAdjoint := regularGeneralMetricC2IdentityRoot_adjoint_eq
    period hPeriod metric tensor hVariation
  have hLeft :
      product gram (product (product inverse rootTranspose) gram) =
        product gram root := by
    simpa [regularFrameMetricC2Adjoint_apply] using
      congrArg (fun matrix => product gram matrix) hAdjoint
  calc
    product rootTranspose gram =
        product (c2FiniteMatrixIdentity period hPeriod 4)
          (product rootTranspose gram) := by
      rw [c2FiniteMatrixProduct_identity_left]
    _ = product (product gram inverse)
        (product rootTranspose gram) := by
      rw [regularFrameMetricC2Matrix_mul_inverse]
    _ = product gram (product inverse
        (product rootTranspose gram)) :=
      c2FiniteMatrixProduct_assoc period hPeriod 4 _ _ _
    _ = product gram
        (product (product inverse rootTranspose) gram) := by
      rw [c2FiniteMatrixProduct_assoc period hPeriod 4
        inverse rootTranspose gram]
    _ = product gram root := hLeft

@[simp]
theorem c2FiniteMatrixValueAt_transpose
    (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (c2FiniteMatrixTranspose period hPeriod matrix) point =
      (c2FiniteMatrixValueAt period hPeriod 4 matrix point).transpose :=
  rfl

@[simp]
theorem regularFrameMetricC2Matrix_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularFrameMetricC2Matrix period hPeriod metric) point =
      regularFrameMetricMatrixMap period hPeriod metric point :=
  rfl

private def regularMetricBilinFormAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    LinearMap.BilinForm Real (TangentFiber period hPeriod point) :=
  (metric.metric.tensor.tensor point).toBilinForm

private theorem regularFrameMetricMatrixMap_eq_toMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameMetricMatrixMap period hPeriod metric point =
      LinearMap.BilinForm.toMatrix
        (regularMetricBasisAt period hPeriod metric point)
        (regularMetricBilinFormAt period hPeriod metric point) := by
  ext row column
  simp [regularFrameMetricMatrixMap, regularFrameMetricMatrix,
    regularMetricBasisAt, regularMetricBilinFormAt,
    RegularGeneralLorentzMetric.frame_eq_basisFun]

private theorem regularGeneralMetricC2IdentityRootMatrixAt_eq_toMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor point =
      LinearMap.toMatrix
        (regularMetricBasisAt period hPeriod metric point)
        (regularMetricBasisAt period hPeriod metric point)
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point).toLinearMap := by
  ext row column
  rw [LinearMap.toMatrix_apply]
  simp [regularMetricBasisAt,
    regularGeneralMetricC2IdentityRootAt_apply,
    Pi.basisFun_apply]

/-- The selected completed root is intrinsically self-adjoint for the genuine
regular Lorentz metric on the restricted open domain. -/
theorem regularGeneralMetricC2IdentityRoot_isSelfAdjoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor ∈
      regularGeneralMetricC2SelfAdjointRootDomain
        period hPeriod metric) :
    RegularGeneralMetricC2IdentityRootIsSelfAdjoint
      period hPeriod metric tensor := by
  intro point first second
  have hC2 := regularGeneralMetricC2IdentityRoot_transpose_mul_metric
    period hPeriod metric tensor hVariation
  have hPoint := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point) hC2
  simp only [c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_transpose,
    regularFrameMetricC2Matrix_valueAt] at hPoint
  change
    (regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor point).transpose *
        regularFrameMetricMatrixMap period hPeriod metric point =
      regularFrameMetricMatrixMap period hPeriod metric point *
        regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point at hPoint
  let basis := regularMetricBasisAt period hPeriod metric point
  let form := regularMetricBilinFormAt period hPeriod metric point
  let root := regularGeneralMetricC2IdentityRootAt
    period hPeriod metric tensor point
  let rootMatrix := regularGeneralMetricC2IdentityRootMatrixAt
    period hPeriod metric tensor point
  let gram := regularFrameMetricMatrixMap period hPeriod metric point
  have hGram : gram = LinearMap.BilinForm.toMatrix basis form :=
    regularFrameMetricMatrixMap_eq_toMatrix period hPeriod metric point
  have hForm : Matrix.toLinearMap₂ basis basis gram = form := by
    rw [hGram]
    simpa [LinearMap.BilinForm.toMatrix] using
      (Matrix.toLinearMap₂_toMatrix₂ basis basis form)
  have hRootMatrix :
      rootMatrix = LinearMap.toMatrix basis basis root.toLinearMap :=
    regularGeneralMetricC2IdentityRootMatrixAt_eq_toMatrix
      period hPeriod metric tensor point
  have hRoot : Matrix.toLin basis basis rootMatrix = root.toLinearMap := by
    rw [hRootMatrix, Matrix.toLin_toMatrix]
  have hPair :=
    (isAdjointPair_toLinearMap₂ basis basis gram gram
      rootMatrix rootMatrix).2 hPoint
  rw [hForm, hRoot] at hPair
  have hTensor :
      metric.metric.tensor.tensor point (root first) second =
        metric.metric.tensor.tensor point first (root second) := by
    simpa [form, regularMetricBilinFormAt] using hPair first second
  calc
    metric.metric.musical point (root first) second =
        metric.metric.tensor.tensor point (root first) second :=
      DFunLike.congr_fun
        (DFunLike.congr_fun
          (metric.metric.musical_eq_tensor point) (root first)) second
    _ = metric.metric.tensor.tensor point first (root second) := hTensor
    _ = metric.metric.musical point first (root second) :=
      (DFunLike.congr_fun
        (DFunLike.congr_fun
          (metric.metric.musical_eq_tensor point) first) (root second)).symm

/-- Root data with self-adjointness discharged by the restricted chart. -/
def regularGeneralMetricC2SelfAdjointIdentityAffineRootData
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor ∈
      regularGeneralMetricC2SelfAdjointRootDomain
        period hPeriod metric) :
    RegularGeneralMetricAffineRootData period hPeriod metric tensor :=
  regularGeneralMetricC2IdentityAffineRootData period hPeriod metric tensor
    hVariation.1
    (regularGeneralMetricC2IdentityRoot_isSelfAdjoint
      period hPeriod metric tensor hVariation)

/-- The self-adjoint C² root and the nondegenerate affine domain now produce
the genuine varied Lorentz metric without an external root hypothesis. -/
def regularGeneralMetricC2SelfAdjointAffineLorentzMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor ∈
      regularGeneralMetricC2SelfAdjointRootDomain
        period hPeriod metric)
    (hNondegenerate : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    SmoothGeneralLorentzMetric period hPeriod :=
  regularGeneralMetricC2IdentityAffineLorentzMetric
    period hPeriod metric tensor hVariation.1 hNondegenerate
      (regularGeneralMetricC2IdentityRoot_isSelfAdjoint
        period hPeriod metric tensor hVariation)

@[simp]
theorem regularGeneralMetricC2SelfAdjointAffineLorentzMetric_tensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor ∈
      regularGeneralMetricC2SelfAdjointRootDomain
        period hPeriod metric)
    (hNondegenerate : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    (regularGeneralMetricC2SelfAdjointAffineLorentzMetric period hPeriod
      metric tensor hVariation hNondegenerate).tensor =
        metric.metric.tensor + tensor :=
  rfl

/-- Gate marker: a genuine open zero-neighbourhood selects the self-adjoint
identity root and removes the last root hypothesis from Lorentz packaging. -/
theorem regular_general_metric_c2_self_adjoint_root_domain_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2SelfAdjointRootDomain
      period hPeriod metric) ∧
      (0 : C2Matrix period hPeriod) ∈
        regularGeneralMetricC2SelfAdjointRootDomain period hPeriod metric ∧
      ∀ tensor : SmoothSymmetricCovariantTwoTensor period hPeriod,
        regularGeneralMetricC2VariationMatrix period hPeriod metric tensor ∈
          regularGeneralMetricC2SelfAdjointRootDomain period hPeriod metric →
        RegularGeneralMetricC2IdentityRootIsSelfAdjoint
          period hPeriod metric tensor := by
  exact ⟨regularGeneralMetricC2SelfAdjointRootDomain_isOpen
      period hPeriod metric,
    zero_mem_regularGeneralMetricC2SelfAdjointRootDomain
      period hPeriod metric,
    fun tensor hVariation =>
      regularGeneralMetricC2IdentityRoot_isSelfAdjoint
        period hPeriod metric tensor hVariation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D
end JanusFormal
