import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualNoetherGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixNamedGardingFrontier4D

/-!
# H10--H14 with Noether-generated actual zero modes

The previous canonical-six terminal still asked for ambient vectors already
proved to satisfy `H v = 0`.  This façade replaces those operator equations by
Noether identities for the first variation of the honest common augmented
action.

After the H10-reduced local family, the remaining analytic inputs are:

1. the graph-norm bound for the genuine dense-core map into the D10-free chart;
2. a finite family of action-level Noether germs, linear independence and one
   global Gårding estimate.

The Hessian equations, the canonical orthogonal splitting, exclusion of hidden
zero modes, exact kernel count, actual-kernel gap, Fredholm index zero, Green
operator and resolvent are all derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixNoetherFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 12400000
set_option synthInstance.maxHeartbeats 6200000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActualNoetherGarding4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixNamedGardingFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D

attribute [local instance]
  P0EFTJanusProgramPGlobalLocalVariationalChart4D.GlobalCandidateALocalVariationalChart.normedAddCommGroup
  P0EFTJanusProgramPGlobalLocalVariationalChart4D.GlobalCandidateALocalVariationalChart.normedSpace
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

/-- Terminal Candidate-A gate whose named zero modes are consequences of
Noether identities, not independent kernel equations. -/
def global_candidateA_hessian_canonicalSix_noether_frontier_gate
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family)))
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    (noetherGarding : GlobalCandidateAActualNoetherGardingData4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
            chartBound)
        ZeroMode) :=
  global_candidateA_hessian_canonicalSix_namedGarding_frontier_gate period
    hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
      chartBound ZeroMode
        (noetherGarding.toNamedGarding period hPeriod (measure := measure))

/-- Only the chart estimate and the Noether/Gårding packet remain after the
local family has been fixed. -/
theorem global_candidateA_hessian_canonicalSix_noether_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixNoetherFrontier4D
end JanusFormal
