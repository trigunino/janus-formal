import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D

/-!
# Evaluation of the paired relative C² matrix

The abstract C² sandwich is evaluated on the minimal physical tangent and
identified with the exact fixed-plus-frame matrix of the varied relative
tensor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixEvaluation4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 4000000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

theorem regularGeneralMetricC2VariationMatrix_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2VariationMatrix period hPeriod metric
        (first + second) =
      regularGeneralMetricC2VariationMatrix period hPeriod metric first +
        regularGeneralMetricC2VariationMatrix period hPeriod metric second :=
  congrArg Subtype.val
    ((smoothToGeneralMetricRelativeC2Core period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric).map_add first second)

theorem regularGeneralMetricC2VariationMatrix_sub
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2VariationMatrix period hPeriod metric
        (first - second) =
      regularGeneralMetricC2VariationMatrix period hPeriod metric first -
        regularGeneralMetricC2VariationMatrix period hPeriod metric second :=
  congrArg Subtype.val
    ((smoothToGeneralMetricRelativeC2Core period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric).map_sub first second)

/-- The affine base displacement plus the cross projection is exactly the
full relative tensor of the two varied metrics. -/
theorem globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_relative
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) +
        (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
          configuration plusBase minusBase direction).2.2 =
      regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        ((minusBase.metric.tensor +
            direction.1.completeVariation.fullMetricPerturbation .minus) -
          (plusBase.metric.tensor +
            direction.1.completeVariation.fullMetricPerturbation .plus)) := by
  rw [globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_cross]
  calc
    _ = regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) +
        regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .minus -
            direction.1.completeVariation.fullMetricPerturbation .plus) := by
      exact congrArg
        (fun matrix =>
          regularGeneralMetricC2VariationMatrix period hPeriod plusBase
              (minusBase.metric.tensor - plusBase.metric.tensor) + matrix)
        (regularGeneralMetricC2VariationMatrix_sub period hPeriod plusBase _ _).symm
    _ = regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        ((minusBase.metric.tensor - plusBase.metric.tensor) +
          (direction.1.completeVariation.fullMetricPerturbation .minus -
            direction.1.completeVariation.fullMetricPerturbation .plus)) :=
      (regularGeneralMetricC2VariationMatrix_add period hPeriod plusBase _ _).symm
    _ = _ := by
      apply congrArg
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase)
      abel

/-- Pointwise evaluation of the projected C² core is the exact inverse-root
sandwich of the full varied relative tensor in the fixed plus frame. -/
theorem regularGeneralMetricC2PairedRelativeMatrix_projected_valueAt
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hPlus : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2PairedRelativeMatrix period hPeriod
          plusBase minusBase
          (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
            configuration plusBase minusBase direction)) point =
      regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus) point *
        (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
              ((minusBase.metric.tensor +
                  direction.1.completeVariation.fullMetricPerturbation .minus) -
                (plusBase.metric.tensor +
                  direction.1.completeVariation.fullMetricPerturbation .plus)))
            point *
          regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod
            plusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus)
            point) := by
  simp only [regularGeneralMetricC2PairedRelativeMatrix,
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_plus,
    c2FiniteMatrixValueAt_product]
  rw [regularGeneralMetricC2IdentityRootInverseC2Matrix_valueAt
      period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus) hPlus point,
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_relative]

/-- Gate marker: the C² relative core evaluates to the intended geometric
inverse-root sandwich for every admissible plus variation. -/
theorem regular_general_metric_c2_paired_relative_matrix_evaluation_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    ∀ (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration)
      (_hPlus : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus) ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
      (point : EffectiveQuotient period hPeriod),
      c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeMatrix period hPeriod
            plusBase minusBase
            (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period
              hPeriod configuration plusBase minusBase direction)) point =
        regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod
            plusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus) point *
          (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
                ((minusBase.metric.tensor +
                    direction.1.completeVariation.fullMetricPerturbation .minus) -
                  (plusBase.metric.tensor +
                    direction.1.completeVariation.fullMetricPerturbation .plus)))
              point *
            regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod
              plusBase
              (direction.1.completeVariation.fullMetricPerturbation .plus)
              point) :=
  fun direction _hPlus point =>
    regularGeneralMetricC2PairedRelativeMatrix_projected_valueAt
      period hPeriod configuration plusBase minusBase direction _hPlus point

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixEvaluation4D
end JanusFormal
