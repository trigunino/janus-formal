import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

/-!
# Sector classification of Schur-derived Candidate-A zero modes

The finite Schur kernel is transported exactly to the kernel of the complete
augmented Candidate-A Hessian.  Once its basis vectors are physically named,
one may classify them among the five D10-free sectors without assuming that
the coupled Hessian is block diagonal.

This façade retains the full H10--H14 closure and adds the exact decomposition
of the actual kernel dimension into sector multiplicities.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixSchurSectorModesFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 14600000
set_option synthInstance.maxHeartbeats 7300000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedKernel4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurNamedZeroMode4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixSchurNamedZeroModeFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
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

/-- Schur-derived actual zero modes together with their physical sector map. -/
structure GlobalCandidateAOrthogonalSchurSectorModesData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (Mode : Type*) (ZeroMode : Type)
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode] where
  named : GlobalCandidateAActualOrthogonalSchurNamedKernelData4D period hPeriod
    configuration data analysis chart sameAction physical Mode ZeroMode
  classification : CandidateAZeroModeSectorClassification ZeroMode

/-- The actual augmented-kernel dimension is the sum of the five physical
sector multiplicities. -/
theorem GlobalCandidateAOrthogonalSchurSectorModesData4D.kernel_finrank_eq_sum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Mode : Type*} {ZeroMode : Type}
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (sectorData : GlobalCandidateAOrthogonalSchurSectorModesData4D period hPeriod
      (measure := measure) configuration data analysis chart sameAction physical
        Mode ZeroMode) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          (measure := measure) analysis chart sameAction physical).ker =
      ∑ sector : CandidateAZeroModeSector,
        sectorData.classification.multiplicity sector := by
  rw [(sectorData.named.toNamedZeroModeData period hPeriod
      (measure := measure)).kernel_finrank_eq_card period hPeriod
        (measure := measure)]
  exact sectorData.classification.sum_multiplicity.symm

/-- Terminal H10--H14 gate with Schur-derived named modes and their sector
multiplicities. -/
def global_candidateA_hessian_canonicalSix_schurSectorModes_frontier_gate
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
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure)
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure)
            configuration data analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)))
    (Mode : Type*) (ZeroMode : Type)
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (sectorData : GlobalCandidateAOrthogonalSchurSectorModesData4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixSchurNamedPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        Mode ZeroMode) :=
  let terminal :=
    global_candidateA_hessian_canonicalSix_schurNamedZeroMode_frontier_gate
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale hTransverse family chartBound Mode ZeroMode
          sectorData.named
  show _ ∧ Nonempty _ ∧ _ ∧ Nonempty _ from
  ⟨terminal,
    ⟨sectorData.classification⟩,
    sectorData.kernel_finrank_eq_sum period hPeriod (measure := measure),
    ⟨fun sector => sectorData.classification.multiplicity sector⟩⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixSchurSectorModesFrontier4D
end JanusFormal
