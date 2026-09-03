import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D

/-!
# Full C² exactness of the paired relative matrix

The inverse-root factors are genuine smooth C² jets by Gate 372.  Hence the
parametric sandwich is itself a smooth lift, and its pointwise transport
formula upgrades to equality in the complete C² matrix algebra.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixC2Exact4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixEvaluation4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D

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

/-- The parametric sandwich equals the genuine transported relative variation
as a full completed C² matrix; plus-chart admissibility is the only hypothesis. -/
theorem regularGeneralMetricC2PairedRelativeMatrix_projected_exact
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hPlus : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase) :
    regularGeneralMetricC2PairedRelativeMatrix period hPeriod
        plusBase minusBase
        (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
          configuration plusBase minusBase direction) =
      regularGeneralMetricC2VariationMatrix period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          hPlus)
        (regularGeneralMetricC2PairedRelativeTensor period hPeriod
          plusBase minusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          (direction.1.completeVariation.fullMetricPerturbation .minus)) := by
  let plusVariation :=
    direction.1.completeVariation.fullMetricPerturbation .plus
  let relativeTensor :=
    regularGeneralMetricC2PairedRelativeTensor period hPeriod
      plusBase minusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus)
      (direction.1.completeVariation.fullMetricPerturbation .minus)
  let inverseField :=
    regularGeneralMetricC2IdentityRootInverseMatrixField period hPeriod
      plusBase plusVariation hPlus
  have hInverse :=
    regularGeneralMetricC2IdentityRootInverseC2Matrix_eq_smoothMatrixFieldToC2
      period hPeriod plusBase plusVariation hPlus
  unfold regularGeneralMetricC2PairedRelativeMatrix
  rw [globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_plus,
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_relative]
  change
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
          (regularGeneralMetricC2VariationMatrix period hPeriod
            plusBase plusVariation))
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          (regularGeneralMetricC2VariationMatrix period hPeriod
            plusBase relativeTensor)
          (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
            (regularGeneralMetricC2VariationMatrix period hPeriod
              plusBase plusVariation))) = _
  rw [hInverse]
  unfold smoothMatrixFieldToC2
  change
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (smoothFiniteMatrixToC2 period hPeriod 4
          (smoothMatrixFieldCoefficients period hPeriod inverseField))
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          (smoothFiniteMatrixToC2 period hPeriod 4
            (fun row column =>
              smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod
                  plusBase) plusBase.metric relativeTensor row column))
          (smoothFiniteMatrixToC2 period hPeriod 4
            (smoothMatrixFieldCoefficients period hPeriod inverseField))) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (fun row column =>
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod
              (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
                plusBase plusVariation hPlus))
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              plusBase plusVariation hPlus).metric relativeTensor row column)
  rw [c2FiniteMatrixProduct_smooth, c2FiniteMatrixProduct_smooth]
  funext row column
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore
    period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change
    (regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod
        plusBase plusVariation point *
      (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix period hPeriod
            plusBase relativeTensor) point *
        regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod
          plusBase plusVariation point)) row column =
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            plusBase plusVariation hPlus))
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase plusVariation hPlus).metric relativeTensor row column point
  have hTransport :=
    regularGeneralMetricC2LorentzChartVariationMatrix_valueAt
      period hPeriod plusBase plusVariation relativeTensor hPlus point
  have hEntry := congrFun (congrFun hTransport row) column
  change
    smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            plusBase plusVariation hPlus))
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase plusVariation hPlus).metric relativeTensor row column point =
      (regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod
          plusBase plusVariation point *
        (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2VariationMatrix period hPeriod
              plusBase relativeTensor) point *
          regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod
            plusBase plusVariation point)) row column at hEntry
  exact hEntry.symm

/-- Under full paired admissibility, the equality is exactly the relative
input used by the existing paired Candidate-A geometry. -/
theorem regularGeneralMetricC2PairedRelativeMatrix_projected_admissible_exact
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation) :
    regularGeneralMetricC2PairedRelativeMatrix period hPeriod
        plusBase minusBase
        (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
          configuration plusBase minusBase direction) =
      regularGeneralMetricC2VariationMatrix period hPeriod
        (regularGeneralMetricC2PairedPlusMetric period hPeriod
          plusBase minusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          (direction.1.completeVariation.fullMetricPerturbation .minus)
          hAdmissible)
        (regularGeneralMetricC2PairedRelativeTensor period hPeriod
          plusBase minusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          (direction.1.completeVariation.fullMetricPerturbation .minus)) :=
  regularGeneralMetricC2PairedRelativeMatrix_projected_exact
    period hPeriod configuration plusBase minusBase direction
      hAdmissible.plus_mem

/-- Gate marker: Gate 371's pointwise identification now holds in the full
completed C² matrix algebra. -/
theorem regular_general_metric_c2_paired_relative_matrix_c2_exact_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    ∀ (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration)
      (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
        period hPeriod plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation),
      regularGeneralMetricC2PairedRelativeMatrix period hPeriod
          plusBase minusBase
          (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period
            hPeriod configuration plusBase minusBase direction) =
        regularGeneralMetricC2VariationMatrix period hPeriod
          (regularGeneralMetricC2PairedPlusMetric period hPeriod
            plusBase minusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus)
            (direction.1.completeVariation.fullMetricPerturbation .minus)
            hAdmissible)
          (regularGeneralMetricC2PairedRelativeTensor period hPeriod
            plusBase minusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus)
            (direction.1.completeVariation.fullMetricPerturbation .minus)) :=
  fun direction hAdmissible =>
    regularGeneralMetricC2PairedRelativeMatrix_projected_admissible_exact
      period hPeriod configuration plusBase minusBase direction hAdmissible

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixC2Exact4D
end JanusFormal
