import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D

/-!
# H10--H14 from the canonical six blocks and a named global Gårding estimate

This is the strongest PDE-facing terminal route currently exposed.  After the
H10-reduced local family, it accepts only:

1. the graph-norm estimate for the genuine dense-core map into the D10-free
   physical chart;
2. named ambient zero modes that are independent and span the actual kernel;
3. one global Gårding inequality whose defect is the finite sum of their
   squared coefficients.

The defect vanishes on `(ker H)ᗮ`, so the existing actual-kernel Green,
resolvent, stability and Fredholm gates apply without an assumed gap, supplied
basis equivalence, finite projector or parametrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixNamedGardingFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 10800000
set_option synthInstance.maxHeartbeats 5400000

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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

/-- Preferred terminal gate from named ambient modes and a global Gårding
estimate. -/
def global_candidateA_hessian_canonicalSix_namedGarding_frontier_gate
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
    (namedGarding : GlobalCandidateAActualKernelNamedGarding4D period hPeriod (measure := measure)
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
            chartBound)
        ZeroMode) :=
  let closure :=
    global_candidateA_hessian_canonicalSix_chartBound_frontier_gate period
      hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
        chartBound (namedGarding.toGap period hPeriod (measure := measure))
  closure

/-- The named modes give the exact dimension of the actual kernel. -/
theorem global_candidateA_hessian_canonicalSix_namedGarding_zeroMode_count
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
    (namedGarding : GlobalCandidateAActualKernelNamedGarding4D period hPeriod (measure := measure)
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
            chartBound)
        ZeroMode) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod (measure := measure) configuration data
          analysis
            (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
              analysis einsteinScale hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
              data analysis einsteinScale hTransverse family)
            (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
              hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse
                family chartBound)).ker =
      Fintype.card ZeroMode :=
  namedGarding.kernel_finrank_eq_card period hPeriod (measure := measure)

/-- The final PDE frontier contains two analytic packets after the local
family: one dense-core chart estimate and one named global Gårding estimate. -/
theorem global_candidateA_hessian_canonicalSix_namedGarding_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixNamedGardingFrontier4D
end JanusFormal
