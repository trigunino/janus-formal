import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualInvariantOrthogonalNamedKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D

/-!
# H10--H14 from an invariant finite block and named zero modes

When the concrete reference modes span an invariant subspace, the Schur operator
is exactly the finite block `A`.  A named finite basis of its kernel reconstructs
all actual zero modes of the complete augmented Candidate-A Hessian.  A norm gap
on the invariant orthogonal complement supplies the reduced Green and Fredholm
package.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixInvariantOrthogonalNamedKernelFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 16600000
set_option synthInstance.maxHeartbeats 8300000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAActualInvariantOrthogonalNamedKernel4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Terminal invariant-subspace gate with named actual zero modes. -/
def global_candidateA_hessian_canonicalSix_invariantOrthogonalNamedKernel_frontier_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)))
    (Mode ZeroMode : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (named : GlobalCandidateAActualInvariantOrthogonalNamedKernelData4D period
      hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixSchurNamedPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            chartBound)
        Mode ZeroMode) :=
  let namedKernel := named.toNamedKernelData period hPeriod
  let terminal :=
    global_candidateA_hessian_canonicalSix_schurNamedZeroMode_frontier_gate
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound Mode ZeroMode namedKernel
  (terminal,
    named.invariant.invariantGap.gap,
    named.invariant.invariantGap.gap_pos,
    named.invariant.invariantGap.lowerBound,
    named.invariant.invariantGap.toInvariantData.blockB_eq_zero,
    named.invariant.invariantGap.toInvariantData.blockC_eq_zero,
    named.schur_eq_finiteBlock period hPeriod,
    (namedKernel.toNamedZeroModeData period hPeriod).namedFamily period hPeriod,
    (namedKernel.toNamedZeroModeData period hPeriod).kernel_finrank_eq_card
      period hPeriod)

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixInvariantOrthogonalNamedKernelFrontier4D
end JanusFormal
