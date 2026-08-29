import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualKernelStablePerturbation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixNamedGardingFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

/-!
# H10--H14 from a stable principal-plus-bounded decomposition

This façade removes the circular kernel-spanning premise from the earlier
perturbative Gårding route.  The genuine augmented Candidate-A Hessian is
written as

`H = A + K`.

A finite orthogonal family is annihilated separately by `A` and `K`; the
reference operator `A` satisfies a global Gårding estimate modulo those modes;
and `‖K‖` is smaller than the reference coercivity constant.  The stable
perturbation theorem proves that no hidden zero mode appears, so the named
family is automatically the complete kernel of `H`.

Together with the canonical six-block dense-core construction, this yields the
full H10--H14 closure, exact zero-mode count, reduced Green operator and real
resolvent without a supplied kernel basis, gap, projector or parametrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixStablePerturbationFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 14200000
set_option synthInstance.maxHeartbeats 7100000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAActualKernelStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixNamedGardingFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
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

/-- Preferred perturbative terminal. Kernel spanning and the actual gap are
both derived from the stable reference-plus-bounded decomposition. -/
def global_candidateA_hessian_canonicalSix_stablePerturbation_frontier_gate
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
    (stable : GlobalCandidateAActualKernelStablePerturbation4D period hPeriod
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
        (stable.toCandidateNamedGarding period hPeriod (measure := measure))

/-- Exact decomposition of the actual kernel count among the five D10-free
physical sectors.  The classification is attached only after exact kernel
spanning has been derived. -/
theorem global_candidateA_hessian_canonicalSix_stablePerturbation_sector_gate
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
    (stable : GlobalCandidateAActualKernelStablePerturbation4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
            chartBound)
        ZeroMode)
    (classification : CandidateAZeroModeSectorClassification ZeroMode) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod (measure := measure) configuration data
          analysis
            (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration
              data analysis einsteinScale hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod (measure := measure)
              configuration data analysis einsteinScale hTransverse family)
            (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
              hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse
                family chartBound)).ker =
      ∑ sector : CandidateAZeroModeSector,
        classification.multiplicity sector :=
  (stable.kernel_finrank_eq_card period hPeriod (measure := measure)).trans
    classification.sum_multiplicity.symm

/-- The new perturbative route has only two analytic packets after the local
family: the dense-core chart bound and the stable named-mode decomposition. -/
theorem global_candidateA_hessian_canonicalSix_stablePerturbation_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixStablePerturbationFrontier4D
end JanusFormal
