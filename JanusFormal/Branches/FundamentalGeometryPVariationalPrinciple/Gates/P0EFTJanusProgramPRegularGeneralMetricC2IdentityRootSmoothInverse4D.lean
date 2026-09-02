import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D

/-!
# Smooth inverse of the completed identity root

On the regular Lorentz chart the completed root is pointwise invertible.  Its
already proved smooth matrix coefficients therefore have a smooth matrix
inverse.  Reconstructing in the genuine regular frame gives the inverse action
on smooth tangent sections, with exact two-sided pointwise identities.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricAffineLorentzRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothOperator4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateAGeometry4D.TangentFiber
    period hPeriod point

private abbrev SmoothTangentSection :=
  P0EFTJanusProgramPGlobalCandidateAGeometry4D.SmoothTangentSection
    period hPeriod

private abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

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

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup

local instance canonicalMatrixAddCommGroup : AddCommGroup Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toAddCommGroup

local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace

local instance canonicalMatrixTopologicalSpace : TopologicalSpace Matrix4 :=
  canonicalMatrixUniformSpace.toTopologicalSpace

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4

local instance canonicalMatrixModule : Module Real Matrix4 :=
  canonicalMatrixNormedSpace.toModule

local instance canonicalMatrixCompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

/-- The completed root is injective on every fiber of the Lorentz chart. -/
theorem regularGeneralMetricC2IdentityRootAt_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    Function.Injective
      (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point) := by
  intro first second hEqual
  apply regularGeneralMetricAffineRelativeEndomorphismAt_injective
    period hPeriod metric tensor
      (regularGeneralMetricC2LorentzChartDomain_mem_nondegenerate
        period hPeriod metric hVariation) point
  have hSquare := regularGeneralMetricC2IdentityRootAt_square
    period hPeriod metric tensor
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
        period hPeriod metric hVariation).1 point
  have hFirst := DFunLike.congr_fun hSquare first
  have hSecond := DFunLike.congr_fun hSquare second
  rw [← hFirst, ← hSecond]
  change regularGeneralMetricC2IdentityRootAt
      period hPeriod metric tensor point
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point first) =
    regularGeneralMetricC2IdentityRootAt
      period hPeriod metric tensor point
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point second)
  rw [hEqual]

/-- The matrix of the completed root is a unit at every point. -/
theorem regularGeneralMetricC2IdentityRootMatrixAt_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    IsUnit (regularGeneralMetricC2IdentityRootMatrixAt
      period hPeriod metric tensor point) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro first second hEqual
  apply (metric.frameEquiv point).injective
  apply regularGeneralMetricC2IdentityRootAt_injective
    period hPeriod metric tensor hVariation point
  rw [regularGeneralMetricC2IdentityRootAt_apply,
    regularGeneralMetricC2IdentityRootAt_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg (metric.frameEquiv point) hEqual

/-- Pointwise inverse matrix of the completed root. -/
def regularGeneralMetricC2IdentityRootInverseMatrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  (regularGeneralMetricC2IdentityRootMatrixAt
    period hPeriod metric tensor point)⁻¹

/-- The inverse root matrix is a genuine smooth spacetime field. -/
theorem regularGeneralMetricC2IdentityRootInverseMatrixAt_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Matrix4) ∞
      (regularGeneralMetricC2IdentityRootInverseMatrixAt
        period hPeriod metric tensor) := by
  intro point
  have hUnit := regularGeneralMetricC2IdentityRootMatrixAt_isUnit
    period hPeriod metric tensor hVariation point
  have hFormula :
      regularGeneralMetricC2IdentityRootInverseMatrixAt
          period hPeriod metric tensor =
        fun current => Ring.inverse
          (regularGeneralMetricC2IdentityRootMatrixAt
            period hPeriod metric tensor current) := by
    funext current
    exact Matrix.nonsing_inv_eq_ringInverse
      (A := regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor current)
  rw [hFormula]
  have hInverse : ContDiffAt Real ∞
      (Ring.inverse : Matrix4 → Matrix4) (hUnit.unit : Matrix4) :=
    contDiffAt_ringInverse Real hUnit.unit
  rw [hUnit.unit_spec] at hInverse
  exact hInverse.contMDiffAt.comp point
    (regularGeneralMetricC2IdentityRootMatrixAt_contMDiff
      period hPeriod metric tensor
        (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
          period hPeriod metric hVariation).1).contMDiffAt

/-- Bundled smooth inverse-root matrix field. -/
def regularGeneralMetricC2IdentityRootInverseMatrixField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    SmoothQuotientField period hPeriod Matrix4 where
  toFun := regularGeneralMetricC2IdentityRootInverseMatrixAt
    period hPeriod metric tensor
  contMDiff_toFun :=
    regularGeneralMetricC2IdentityRootInverseMatrixAt_contMDiff
      period hPeriod metric tensor hVariation

theorem regularGeneralMetricC2IdentityRootInverseMatrixAt_mul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootInverseMatrixAt
        period hPeriod metric tensor point *
      regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor point = 1 := by
  apply Matrix.nonsing_inv_mul
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (regularGeneralMetricC2IdentityRootMatrixAt_isUnit
      period hPeriod metric tensor hVariation point)

theorem regularGeneralMetricC2IdentityRootMatrixAt_mul_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor point *
      regularGeneralMetricC2IdentityRootInverseMatrixAt
        period hPeriod metric tensor point = 1 := by
  apply Matrix.mul_nonsing_inv
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (regularGeneralMetricC2IdentityRootMatrixAt_isUnit
      period hPeriod metric tensor hVariation point)

private def matrix4ContinuousLinearMap (matrix : Matrix4) :
    (Fin 4 → Real) →L[Real] (Fin 4 → Real) :=
  LinearMap.toContinuousLinearMap matrix.mulVecLin

/-- Intrinsic pointwise inverse root reconstructed in the regular frame. -/
def regularGeneralMetricC2IdentityRootInverseAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point :=
  (metric.frameEquiv point).toContinuousLinearMap.comp
    ((matrix4ContinuousLinearMap
      (regularGeneralMetricC2IdentityRootInverseMatrixAt
        period hPeriod metric tensor point)).comp
      (metric.frameEquiv point).symm.toContinuousLinearMap)

@[simp]
theorem regularGeneralMetricC2IdentityRootInverseAt_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point vector =
      metric.frameEquiv point
        (Matrix.mulVec
          (regularGeneralMetricC2IdentityRootInverseMatrixAt
            period hPeriod metric tensor point)
          ((metric.frameEquiv point).symm vector)) :=
  rfl

theorem regularGeneralMetricC2IdentityRootInverseAt_comp_root
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    (regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point).comp
      (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point) =
      ContinuousLinearMap.id Real (TangentFiber period hPeriod point) := by
  apply ContinuousLinearMap.ext
  intro vector
  change regularGeneralMetricC2IdentityRootInverseAt
      period hPeriod metric tensor point
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point vector) = vector
  rw [regularGeneralMetricC2IdentityRootInverseAt_apply,
    regularGeneralMetricC2IdentityRootAt_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [Matrix.mulVec_mulVec,
    regularGeneralMetricC2IdentityRootInverseMatrixAt_mul
      period hPeriod metric tensor hVariation point,
    Matrix.one_mulVec, ContinuousLinearEquiv.apply_symm_apply]

theorem regularGeneralMetricC2IdentityRootAt_comp_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point).comp
      (regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point) =
      ContinuousLinearMap.id Real (TangentFiber period hPeriod point) := by
  apply ContinuousLinearMap.ext
  intro vector
  change regularGeneralMetricC2IdentityRootAt
      period hPeriod metric tensor point
        (regularGeneralMetricC2IdentityRootInverseAt
          period hPeriod metric tensor point vector) = vector
  rw [regularGeneralMetricC2IdentityRootAt_apply,
    regularGeneralMetricC2IdentityRootInverseAt_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [Matrix.mulVec_mulVec,
    regularGeneralMetricC2IdentityRootMatrixAt_mul_inverse
      period hPeriod metric tensor hVariation point,
    Matrix.one_mulVec, ContinuousLinearEquiv.apply_symm_apply]

private def matrix4EntryContinuousLinearMap
    (row column : Fin 4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- One smooth coefficient of the inverse root matrix. -/
def regularGeneralMetricC2IdentityRootInverseMatrixCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (row column : Fin 4) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    regularGeneralMetricC2IdentityRootInverseMatrixField
      period hPeriod metric tensor hVariation point row column
  contMDiff_toFun := by
    change ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      ((matrix4EntryContinuousLinearMap row column) ∘
        (regularGeneralMetricC2IdentityRootInverseMatrixField
          period hPeriod metric tensor hVariation).toFun)
    exact (matrix4EntryContinuousLinearMap row column).contMDiff.comp
      (regularGeneralMetricC2IdentityRootInverseMatrixField
        period hPeriod metric tensor hVariation).contMDiff_toFun

@[simp]
theorem regularGeneralMetricC2IdentityRootInverseMatrixCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (row column : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootInverseMatrixCoefficient
        period hPeriod metric tensor hVariation row column point =
      regularGeneralMetricC2IdentityRootInverseMatrixAt
        period hPeriod metric tensor point row column :=
  rfl

/-- Smooth inverse-root action on genuine tangent sections. -/
def regularGeneralMetricC2IdentityRootInverseSmoothAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (vector : SmoothTangentSection period hPeriod) :
    SmoothTangentSection period hPeriod where
  toFun := fun point =>
    ∑ row : Fin 4,
      (∑ column : Fin 4,
        regularGeneralMetricC2IdentityRootInverseMatrixCoefficient
            period hPeriod metric tensor hVariation row column point *
          generalMetricFiniteFrameCoefficient period hPeriod
            (RegularFrame period hPeriod metric) metric.metric vector column
              point) •
        (RegularFrame period hPeriod metric).vectorAt point row
  contMDiff_toFun := by
    apply ContMDiff.sum_section
    intro row _
    have hCoefficient :
        ContMDiff coverModelWithCorners
          (modelWithCornersSelf Real Real) ∞
          (fun point =>
            ∑ column : Fin 4,
              regularGeneralMetricC2IdentityRootInverseMatrixCoefficient
                  period hPeriod metric tensor hVariation row column point *
                generalMetricFiniteFrameCoefficient period hPeriod
                  (RegularFrame period hPeriod metric) metric.metric vector
                    column point) := by
      apply ContMDiff.sum
      intro column _
      exact
        (regularGeneralMetricC2IdentityRootInverseMatrixCoefficient
          period hPeriod metric tensor hVariation row column).contMDiff_toFun.mul
        (generalMetricFiniteFrameCoefficient period hPeriod
          (RegularFrame period hPeriod metric) metric.metric vector
            column).contMDiff_toFun
    exact hCoefficient.smul_section
      ((RegularFrame period hPeriod metric).contMDiff_vector row)

@[simp]
theorem regularGeneralMetricC2IdentityRootInverseSmoothAction_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootInverseSmoothAction
        period hPeriod metric tensor hVariation vector point =
      regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point (vector point) := by
  rw [generalMetricFiniteFrameCoefficientAt_reconstructs
    period hPeriod (RegularFrame period hPeriod metric) metric.metric point
      (regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point (vector point))]
  change (∑ row : Fin 4,
      (∑ column : Fin 4,
        regularGeneralMetricC2IdentityRootInverseMatrixCoefficient
            period hPeriod metric tensor hVariation row column point *
          generalMetricFiniteFrameCoefficient period hPeriod
            (RegularFrame period hPeriod metric) metric.metric vector column
              point) •
        (RegularFrame period hPeriod metric).vectorAt point row) = _
  apply Finset.sum_congr rfl
  intro row _
  congr 1
  rw [regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate]
  simp only [regularGeneralMetricC2IdentityRootInverseMatrixCoefficient_apply,
    generalMetricFiniteFrameCoefficient_apply,
    regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate,
    regularGeneralMetricC2IdentityRootInverseAt_apply,
    ContinuousLinearEquiv.symm_apply_apply, Matrix.mulVec, dotProduct]

/-- Linear inverse-root operator on smooth tangent sections. -/
def regularGeneralMetricC2IdentityRootInverseOperator
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    SmoothTangentSection period hPeriod →ₗ[Real]
      SmoothTangentSection period hPeriod where
  toFun := regularGeneralMetricC2IdentityRootInverseSmoothAction
    period hPeriod metric tensor hVariation
  map_add' := by
    intro first second
    ext point
    change regularGeneralMetricC2IdentityRootInverseSmoothAction
        period hPeriod metric tensor hVariation (first + second) point =
      regularGeneralMetricC2IdentityRootInverseSmoothAction
          period hPeriod metric tensor hVariation first point +
        regularGeneralMetricC2IdentityRootInverseSmoothAction
          period hPeriod metric tensor hVariation second point
    rw [regularGeneralMetricC2IdentityRootInverseSmoothAction_apply,
      regularGeneralMetricC2IdentityRootInverseSmoothAction_apply,
      regularGeneralMetricC2IdentityRootInverseSmoothAction_apply]
    change regularGeneralMetricC2IdentityRootInverseAt
      period hPeriod metric tensor point (first point + second point) = _
    exact map_add
      (regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point) (first point) (second point)
  map_smul' := by
    intro scalar vector
    ext point
    change regularGeneralMetricC2IdentityRootInverseSmoothAction
        period hPeriod metric tensor hVariation (scalar • vector) point =
      scalar • regularGeneralMetricC2IdentityRootInverseSmoothAction
        period hPeriod metric tensor hVariation vector point
    rw [regularGeneralMetricC2IdentityRootInverseSmoothAction_apply,
      regularGeneralMetricC2IdentityRootInverseSmoothAction_apply]
    change regularGeneralMetricC2IdentityRootInverseAt
      period hPeriod metric tensor point (scalar • vector point) = _
    exact map_smul
      (regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point) scalar (vector point)

@[simp]
theorem regularGeneralMetricC2IdentityRootInverseOperator_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootInverseOperator
        period hPeriod metric tensor hVariation vector point =
      regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point (vector point) :=
  regularGeneralMetricC2IdentityRootInverseSmoothAction_apply
    period hPeriod metric tensor hVariation vector point

/-- Gate marker: the smooth completed root has an exact smooth inverse action. -/
theorem regular_general_metric_c2_identity_root_smooth_inverse_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    ContMDiff coverModelWithCorners
        (modelWithCornersSelf Real Matrix4) ∞
        (regularGeneralMetricC2IdentityRootInverseMatrixAt
          period hPeriod metric tensor) ∧
      (∀ point,
        (regularGeneralMetricC2IdentityRootInverseAt
            period hPeriod metric tensor point).comp
          (regularGeneralMetricC2IdentityRootAt
            period hPeriod metric tensor point) =
          ContinuousLinearMap.id Real (TangentFiber period hPeriod point) ∧
        (regularGeneralMetricC2IdentityRootAt
            period hPeriod metric tensor point).comp
          (regularGeneralMetricC2IdentityRootInverseAt
            period hPeriod metric tensor point) =
          ContinuousLinearMap.id Real (TangentFiber period hPeriod point)) ∧
      ∀ vector point,
        regularGeneralMetricC2IdentityRootInverseOperator
            period hPeriod metric tensor hVariation vector point =
          regularGeneralMetricC2IdentityRootInverseAt
            period hPeriod metric tensor point (vector point) := by
  exact ⟨regularGeneralMetricC2IdentityRootInverseMatrixAt_contMDiff
      period hPeriod metric tensor hVariation,
    fun point =>
      ⟨regularGeneralMetricC2IdentityRootInverseAt_comp_root
          period hPeriod metric tensor hVariation point,
        regularGeneralMetricC2IdentityRootAt_comp_inverse
          period hPeriod metric tensor hVariation point⟩,
    regularGeneralMetricC2IdentityRootInverseOperator_apply
      period hPeriod metric tensor hVariation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
end JanusFormal
