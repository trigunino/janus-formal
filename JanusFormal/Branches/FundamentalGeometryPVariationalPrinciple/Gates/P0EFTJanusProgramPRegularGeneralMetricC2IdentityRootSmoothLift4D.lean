import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawSplitCharpolySmoothLocalRootBranch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D

/-!
# Smooth lift of the completed identity root

The completed Candidate-A root is a continuous matrix field whose square is a
smooth affine relative-metric target.  Pointwise Sylvester regularity and the
smooth finite-matrix local branch therefore upgrade it to a genuine `C∞`
matrix field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff Matrix.Norms.Frobenius RightActions Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusPositiveRawSplitCharpolySmoothLocalRootBranch4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

private def regularFrameIndex
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 4) : Fin (RegularFrame period hPeriod metric).count :=
  Fin.cast (by rfl) index

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

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix4) :=
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
    NormedSpace Real (Matrix4) :=
  NormedAlgebra.toNormedSpace Matrix4

local instance canonicalMatrixModule : Module Real Matrix4 :=
  canonicalMatrixNormedSpace.toModule

local instance canonicalMatrixCompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

private theorem c2FiniteMatrixValueAt_continuous
    (matrix : C2Matrix period hPeriod) :
    Continuous (c2FiniteMatrixValueAt period hPeriod 4 matrix) := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  change Continuous (fun point => (((matrix row column).1 point).1))
  exact continuous_fst.comp (matrix row column).1.continuous

private theorem c2FiniteMatrixValueAt_smoothMatrixFieldToC2
    (field : SmoothQuotientField period hPeriod Matrix4)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod field) point = field point := by
  ext row column
  rfl

/-- Smooth affine relative-metric matrix `I + g⁻¹h` in the regular frame. -/
def regularGeneralMetricAffineRelativeMatrixField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothQuotientField period hPeriod Matrix4 where
  toFun := fun point =>
    fun (row column : Fin 4) =>
      (if row = column then 1 else 0) +
        smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (RegularFrame period hPeriod metric) metric.metric tensor
            (regularFrameIndex period hPeriod metric row)
            (regularFrameIndex period hPeriod metric column) point
  contMDiff_toFun := by
    have hExpansion :
        ContMDiff coverModelWithCorners
          (modelWithCornersSelf Real Matrix4) ∞
          (fun point =>
            (1 : Matrix4) +
              ∑ row : Fin 4, ∑ column : Fin 4,
                smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
                    (RegularFrame period hPeriod metric) metric.metric tensor
                    (regularFrameIndex period hPeriod metric row)
                    (regularFrameIndex period hPeriod metric column) point •
                  Matrix.single row column (1 : Real)) := by
      apply contMDiff_const.add
      apply ContMDiff.sum
      intro row _
      apply ContMDiff.sum
      intro column _
      exact (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (RegularFrame period hPeriod metric) metric.metric tensor
          (regularFrameIndex period hPeriod metric row)
          (regularFrameIndex period hPeriod metric column)).contMDiff_toFun.smul
            contMDiff_const
    exact hExpansion.congr fun point => by
      let variation : Matrix4 := fun row column =>
        smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (RegularFrame period hPeriod metric) metric.metric tensor
            (regularFrameIndex period hPeriod metric row)
            (regularFrameIndex period hPeriod metric column) point
      have hMatrix : variation =
          ∑ row : Fin 4, ∑ column : Fin 4,
            smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
                (RegularFrame period hPeriod metric) metric.metric tensor
                (regularFrameIndex period hPeriod metric row)
                (regularFrameIndex period hPeriod metric column) point •
              Matrix.single row column (1 : Real) := by
        simpa [variation] using (Matrix.matrix_eq_sum_single
        (fun row column =>
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
            (RegularFrame period hPeriod metric) metric.metric tensor
              (regularFrameIndex period hPeriod metric row)
              (regularFrameIndex period hPeriod metric column) point))
      show (1 : Matrix4) + variation = _
      exact congrArg (fun matrix : Matrix4 => (1 : Matrix4) + matrix) hMatrix

theorem regularGeneralMetricC2IdentityRootMatrixAt_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Continuous (regularGeneralMetricC2IdentityRootMatrixAt
      period hPeriod metric tensor) :=
  c2FiniteMatrixValueAt_continuous period hPeriod
    (c2IdentityRootBranch period hPeriod
      (regularGeneralMetricC2VariationMatrix
        period hPeriod metric tensor))

theorem regularGeneralMetricC2IdentityRootMatrixAt_square_matrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (point : EffectiveQuotient period hPeriod) :
    canonicalMatrixSquare
        (regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point) =
      regularGeneralMetricAffineRelativeMatrixField
        period hPeriod metric tensor point := by
  have hC2 := c2IdentityRootBranch_square period hPeriod hRoot
  have hValue := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point) hC2
  rw [show c2FiniteMatrixSquare period hPeriod 4
      (c2IdentityRootBranch period hPeriod
        (regularGeneralMetricC2VariationMatrix
          period hPeriod metric tensor)) =
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor))
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor)) by rfl,
    c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_add,
    c2FiniteMatrixValueAt_identity] at hValue
  have hVariationValue :
      c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor) point =
        (fun row column =>
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
            (RegularFrame period hPeriod metric) metric.metric tensor
              row column point) := by
    calc
      _ = finiteFrameEndomorphismMatrixAt period hPeriod
          (RegularFrame period hPeriod metric) metric.metric point
          (raisedGeneralMetricTensorAt
            period hPeriod metric.metric tensor point) :=
        regularGeneralMetricC2VariationMatrix_valueAt
          period hPeriod metric tensor point
      _ = _ := (smoothGeneralMetricRelativeEndomorphismMatrix_apply
        period hPeriod (RegularFrame period hPeriod metric) metric.metric
          tensor point).symm
  calc
    canonicalMatrixSquare
        (regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point) =
        (1 : Matrix4) +
          c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2VariationMatrix
              period hPeriod metric tensor) point := by
      simpa [canonicalMatrixSquare,
        regularGeneralMetricC2IdentityRootMatrixAt] using hValue
    _ = regularGeneralMetricAffineRelativeMatrixField
          period hPeriod metric tensor point := by
      rw [hVariationValue]
      ext row column
      simp [regularGeneralMetricAffineRelativeMatrixField,
        Matrix.one_apply, regularFrameIndex, RegularFrame]

theorem regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor)
    (point : EffectiveQuotient period hPeriod) :
    Function.Bijective
      (canonicalSylvesterOperator
        (regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point)) := by
  let rootC2 := c2IdentityRootBranch period hPeriod
    (regularGeneralMetricC2VariationMatrix period hPeriod metric tensor)
  have hSource := c2IdentityRootBranch_mem_localSquareChart_source
    period hPeriod hRoot
  change rootC2 ∈
    (c2MatrixLocalSquareChart period hPeriod
      (c2IdentityRootField period hPeriod)
      (c2IdentityRootField_regular period hPeriod)).source at hSource
  rw [c2MatrixLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  rcases hSource.2 with ⟨equiv, hEquiv⟩
  have hGlobalSurjective : Function.Surjective
      (c2MatrixSylvesterFamily period hPeriod rootC2) := by
    rw [← hEquiv]
    exact equiv.surjective
  have hPointSurjective : Function.Surjective
      (canonicalSylvesterOperator
        (regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor point)) := by
    intro output
    let outputField : SmoothQuotientField period hPeriod Matrix4 :=
      constantSmoothField period hPeriod Matrix4 output
    let outputC2 : C2Matrix period hPeriod :=
      smoothMatrixFieldToC2 period hPeriod outputField
    rcases hGlobalSurjective outputC2 with ⟨input, hInput⟩
    refine ⟨c2FiniteMatrixValueAt period hPeriod 4 input point, ?_⟩
    change c2FiniteMatrixSylvester period hPeriod 4 rootC2 input =
      outputC2 at hInput
    change c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 rootC2 input +
        c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4 input rootC2 =
      outputC2 at hInput
    have hValue := congrArg
      (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point) hInput
    rw [c2FiniteMatrixValueAt_add,
      c2FiniteMatrixValueAt_product,
      c2FiniteMatrixValueAt_product] at hValue
    have hOutputValue :
        c2FiniteMatrixValueAt period hPeriod 4 outputC2 point = output := by
      exact c2FiniteMatrixValueAt_smoothMatrixFieldToC2
        period hPeriod outputField point
    simpa [canonicalSylvesterOperator_apply,
      regularGeneralMetricC2IdentityRootMatrixAt, rootC2,
      hOutputValue] using hValue
  exact ⟨LinearMap.injective_iff_surjective.mpr hPointSurjective,
    hPointSurjective⟩

/-- The evaluated completed root is a genuine smooth matrix field. -/
theorem regularGeneralMetricC2IdentityRootMatrixAt_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor) :
    ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Matrix4) ∞
      (regularGeneralMetricC2IdentityRootMatrixAt
        period hPeriod metric tensor) := by
  intro point
  let target := regularGeneralMetricAffineRelativeMatrixField
    period hPeriod metric tensor
  let rootLift := regularGeneralMetricC2IdentityRootMatrixAt
    period hPeriod metric tensor
  have hRegular : Function.Bijective
      (canonicalSylvesterOperator (rootLift point)) :=
    regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective
      period hPeriod metric tensor hRoot point
  have hBranch : ContDiffAt Real ∞
      (canonicalC2LocalRootBranchAt (rootLift point) hRegular)
      (target point) := by
    have hSquare := regularGeneralMetricC2IdentityRootMatrixAt_square_matrix
      period hPeriod metric tensor hRoot point
    simpa only [target, rootLift, hSquare] using
      canonicalC2LocalRootBranchAt_contDiffAt_infty
        (rootLift point) hRegular
  have hLocal : ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real Matrix4) ∞
      (canonicalC2LocalTargetLift target (rootLift point) hRegular) point :=
    hBranch.comp_contMDiffAt target.contMDiff_toFun.contMDiffAt
  exact hLocal.congr_of_eventuallyEq
    (continuousRegularRootLift_eventuallyEq_canonicalC2LocalTargetLift
      target rootLift point hRegular
      (regularGeneralMetricC2IdentityRootMatrixAt_continuous
        period hPeriod metric tensor).continuousAt
      (regularGeneralMetricC2IdentityRootMatrixAt_square_matrix
        period hPeriod metric tensor hRoot))

/-- The smooth matrix field packaged for downstream section reconstruction. -/
def regularGeneralMetricC2IdentityRootMatrixField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor) :
    SmoothQuotientField period hPeriod Matrix4 where
  toFun := regularGeneralMetricC2IdentityRootMatrixAt
    period hPeriod metric tensor
  contMDiff_toFun :=
    regularGeneralMetricC2IdentityRootMatrixAt_contMDiff
      period hPeriod metric tensor hRoot

/-- Gate marker for the completed-to-smooth identity-root lift. -/
theorem regular_general_metric_c2_identity_root_smooth_lift_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor) :
    ContMDiff coverModelWithCorners
        (modelWithCornersSelf Real Matrix4) ∞
        (regularGeneralMetricC2IdentityRootMatrixAt
          period hPeriod metric tensor) ∧
      ∀ point,
        canonicalMatrixSquare
            (regularGeneralMetricC2IdentityRootMatrixAt
              period hPeriod metric tensor point) =
          regularGeneralMetricAffineRelativeMatrixField
            period hPeriod metric tensor point :=
  ⟨regularGeneralMetricC2IdentityRootMatrixAt_contMDiff
      period hPeriod metric tensor hRoot,
    regularGeneralMetricC2IdentityRootMatrixAt_square_matrix
      period hPeriod metric tensor hRoot⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
end JanusFormal
