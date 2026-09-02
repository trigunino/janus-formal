import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D

/-!
# Smooth operator induced by the completed identity root

The smooth matrix lift is reconstructed in the genuine regular frame.  It
therefore acts linearly on global smooth tangent sections and agrees pointwise
with the intrinsic completed root.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothOperator4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

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
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

private def matrix4EntryContinuousLinearMap
    (row column : Fin 4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- One smooth coefficient of the completed root matrix. -/
def regularGeneralMetricC2IdentityRootMatrixCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (row column : Fin 4) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    regularGeneralMetricC2IdentityRootMatrixField
      period hPeriod metric tensor hRoot point row column
  contMDiff_toFun := by
    change ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      ((matrix4EntryContinuousLinearMap row column) ∘
        (regularGeneralMetricC2IdentityRootMatrixField
          period hPeriod metric tensor hRoot).toFun)
    exact (matrix4EntryContinuousLinearMap row column).contMDiff.comp
      (regularGeneralMetricC2IdentityRootMatrixField
        period hPeriod metric tensor hRoot).contMDiff_toFun

@[simp]
theorem regularGeneralMetricC2IdentityRootMatrixCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (row column : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootMatrixCoefficient
        period hPeriod metric tensor hRoot row column point =
      regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor point row column :=
  rfl

/-- Reconstruct the smooth matrix action in the genuine regular frame. -/
def regularGeneralMetricC2IdentityRootSmoothAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (vector : SmoothTangentSection period hPeriod) :
    SmoothTangentSection period hPeriod where
  toFun := fun point =>
    ∑ row : Fin 4,
      (∑ column : Fin 4,
        regularGeneralMetricC2IdentityRootMatrixCoefficient
            period hPeriod metric tensor hRoot row column point *
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
              regularGeneralMetricC2IdentityRootMatrixCoefficient
                  period hPeriod metric tensor hRoot row column point *
                generalMetricFiniteFrameCoefficient period hPeriod
                  (RegularFrame period hPeriod metric) metric.metric vector
                    column point) := by
      apply ContMDiff.sum
      intro column _
      exact
        (regularGeneralMetricC2IdentityRootMatrixCoefficient
          period hPeriod metric tensor hRoot row column).contMDiff_toFun.mul
        (generalMetricFiniteFrameCoefficient period hPeriod
          (RegularFrame period hPeriod metric) metric.metric vector
            column).contMDiff_toFun
    exact hCoefficient.smul_section
      ((RegularFrame period hPeriod metric).contMDiff_vector row)

@[simp]
theorem regularGeneralMetricC2IdentityRootSmoothAction_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootSmoothAction
        period hPeriod metric tensor hRoot vector point =
      regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point (vector point) := by
  rw [generalMetricFiniteFrameCoefficientAt_reconstructs
    period hPeriod (RegularFrame period hPeriod metric) metric.metric point
      (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point (vector point))]
  change (∑ row : Fin 4,
      (∑ column : Fin 4,
        regularGeneralMetricC2IdentityRootMatrixCoefficient
            period hPeriod metric tensor hRoot row column point *
          generalMetricFiniteFrameCoefficient period hPeriod
            (RegularFrame period hPeriod metric) metric.metric vector column
              point) •
        (RegularFrame period hPeriod metric).vectorAt point row) = _
  apply Finset.sum_congr rfl
  intro row _
  congr 1
  rw [regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate]
  simp only [regularGeneralMetricC2IdentityRootMatrixCoefficient_apply,
    generalMetricFiniteFrameCoefficient_apply,
    regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate,
    regularGeneralMetricC2IdentityRootAt_apply,
    ContinuousLinearEquiv.symm_apply_apply, Matrix.mulVec, dotProduct]

/-- Genuine linear action of the completed root on smooth tangent sections. -/
def regularGeneralMetricC2IdentityRootOperator
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor) :
    SmoothTangentSection period hPeriod →ₗ[Real]
      SmoothTangentSection period hPeriod where
  toFun := regularGeneralMetricC2IdentityRootSmoothAction
    period hPeriod metric tensor hRoot
  map_add' := by
    intro first second
    ext point
    change regularGeneralMetricC2IdentityRootSmoothAction
        period hPeriod metric tensor hRoot (first + second) point =
      regularGeneralMetricC2IdentityRootSmoothAction
          period hPeriod metric tensor hRoot first point +
        regularGeneralMetricC2IdentityRootSmoothAction
          period hPeriod metric tensor hRoot second point
    rw [regularGeneralMetricC2IdentityRootSmoothAction_apply,
      regularGeneralMetricC2IdentityRootSmoothAction_apply,
      regularGeneralMetricC2IdentityRootSmoothAction_apply]
    change regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point (first point + second point) = _
    exact map_add
      (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point) (first point) (second point)
  map_smul' := by
    intro scalar vector
    ext point
    change regularGeneralMetricC2IdentityRootSmoothAction
        period hPeriod metric tensor hRoot (scalar • vector) point =
      scalar • regularGeneralMetricC2IdentityRootSmoothAction
        period hPeriod metric tensor hRoot vector point
    rw [regularGeneralMetricC2IdentityRootSmoothAction_apply,
      regularGeneralMetricC2IdentityRootSmoothAction_apply]
    change regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point (scalar • vector point) = _
    exact map_smul
      (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point) scalar (vector point)

@[simp]
theorem regularGeneralMetricC2IdentityRootOperator_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootOperator
        period hPeriod metric tensor hRoot vector point =
      regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point (vector point) :=
  regularGeneralMetricC2IdentityRootSmoothAction_apply
    period hPeriod metric tensor hRoot vector point

/-- Applying the smooth root operator twice gives the affine relative action. -/
theorem regularGeneralMetricC2IdentityRootOperator_square_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (vector : SmoothTangentSection period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2IdentityRootOperator
          period hPeriod metric tensor hRoot
          (regularGeneralMetricC2IdentityRootOperator
            period hPeriod metric tensor hRoot vector) point =
      regularGeneralMetricAffineRelativeEndomorphismAt
        period hPeriod metric tensor point (vector point) := by
  rw [regularGeneralMetricC2IdentityRootOperator_apply,
    regularGeneralMetricC2IdentityRootOperator_apply]
  exact congrArg
    (fun operator => operator (vector point))
    (regularGeneralMetricC2IdentityRootAt_square
      period hPeriod metric tensor hRoot point)

/-- Gate marker: the completed root now has the exact global smooth action
required by `GlobalCandidateAGeometry`. -/
theorem regular_general_metric_c2_identity_root_smooth_operator_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor) :
    (∀ vector point,
      regularGeneralMetricC2IdentityRootOperator
          period hPeriod metric tensor hRoot vector point =
        regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point (vector point)) ∧
      ∀ point,
        (regularGeneralMetricC2IdentityRootAt
            period hPeriod metric tensor point).comp
          (regularGeneralMetricC2IdentityRootAt
            period hPeriod metric tensor point) =
        regularGeneralMetricAffineRelativeEndomorphismAt
          period hPeriod metric tensor point :=
  ⟨regularGeneralMetricC2IdentityRootOperator_apply
      period hPeriod metric tensor hRoot,
    regularGeneralMetricC2IdentityRootAt_square
      period hPeriod metric tensor hRoot⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothOperator4D
end JanusFormal
