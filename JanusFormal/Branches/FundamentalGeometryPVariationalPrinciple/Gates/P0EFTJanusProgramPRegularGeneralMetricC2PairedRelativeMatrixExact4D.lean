import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D

/-!
# Exact paired relative-matrix identification

The parametric C² sandwich is exactly the relative variation matrix in the
genuine transported plus metric, point by point.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixExact4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixEvaluation4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D

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

/-- Exact identification requiring only admissibility of the plus chart. -/
theorem regularGeneralMetricC2PairedRelativeMatrix_projected_exact_valueAt
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
      c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            plusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus)
            hPlus)
          (regularGeneralMetricC2PairedRelativeTensor period hPeriod
            plusBase minusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus)
            (direction.1.completeVariation.fullMetricPerturbation .minus)))
        point := by
  rw [regularGeneralMetricC2PairedRelativeMatrix_projected_valueAt
    period hPeriod configuration plusBase minusBase direction hPlus point]
  exact (regularGeneralMetricC2LorentzChartVariationMatrix_valueAt
    period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus)
      (regularGeneralMetricC2PairedRelativeTensor period hPeriod
        plusBase minusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus)
        (direction.1.completeVariation.fullMetricPerturbation .minus))
      hPlus point).symm

/-- Under full paired admissibility, the same matrix is exactly the relative
chart input used to construct the Candidate-A geometry. -/
theorem regularGeneralMetricC2PairedRelativeMatrix_projected_admissible_valueAt
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2PairedRelativeMatrix period hPeriod
          plusBase minusBase
          (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
            configuration plusBase minusBase direction)) point =
      c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod
          (regularGeneralMetricC2PairedPlusMetric period hPeriod
            plusBase minusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus)
            (direction.1.completeVariation.fullMetricPerturbation .minus)
            hAdmissible)
          (regularGeneralMetricC2PairedRelativeTensor period hPeriod
            plusBase minusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus)
            (direction.1.completeVariation.fullMetricPerturbation .minus)))
        point := by
  exact regularGeneralMetricC2PairedRelativeMatrix_projected_exact_valueAt
    period hPeriod configuration plusBase minusBase direction
      hAdmissible.plus_mem point

/-- Gate marker: the parametric relative core and the genuine nested Lorentz
chart use the same pointwise matrix. -/
theorem regular_general_metric_c2_paired_relative_matrix_exact_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    ∀ (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration)
      (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
        period hPeriod plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation)
      (point : EffectiveQuotient period hPeriod),
      c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeMatrix period hPeriod
            plusBase minusBase
            (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period
              hPeriod configuration plusBase minusBase direction)) point =
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix period hPeriod
            (regularGeneralMetricC2PairedPlusMetric period hPeriod
              plusBase minusBase
              (direction.1.completeVariation.fullMetricPerturbation .plus)
              (direction.1.completeVariation.fullMetricPerturbation .minus)
              hAdmissible)
            (regularGeneralMetricC2PairedRelativeTensor period hPeriod
              plusBase minusBase
              (direction.1.completeVariation.fullMetricPerturbation .plus)
              (direction.1.completeVariation.fullMetricPerturbation .minus)))
          point :=
  fun direction hAdmissible point =>
    regularGeneralMetricC2PairedRelativeMatrix_projected_admissible_valueAt
      period hPeriod configuration plusBase minusBase direction
        hAdmissible point

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixExact4D
end JanusFormal
