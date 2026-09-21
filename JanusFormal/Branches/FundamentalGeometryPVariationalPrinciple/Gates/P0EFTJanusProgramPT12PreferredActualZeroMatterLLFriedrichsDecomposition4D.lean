import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MinimalPhysicalMatterLLLocalFriedrichsPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D

/-!
# Preferred actual-zero matter--LL Friedrichs decomposition

The preferred family operator at zero, restricted to the minimal physical
matter--LL slice, is the natural Friedrichs pairing plus the explicit local
seven-block action residual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12PreferredActualZeroMatterLLFriedrichsDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 19000000
set_option synthInstance.maxHeartbeats 9500000
set_option maxRecDepth 100000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLLocalFriedrichsPairing4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmNormedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmModule
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmCompleteSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The completed four-block graph restricts to the natural matter--LL
Friedrichs pairing on the minimal physical slice. -/
theorem programPT12MinimalPhysicalMatterLLReducedSlice_graphHessian_eq_friedrichsPairing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration data
        analysis
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second) =
      inner Real
        (programPGlobalGaugeFixedLLFriedrichsHessianOperator period hPeriod
          covector couplings.matterMassSquared analysis
          (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
            covector couplings.matterMassSquared analysis
            (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
              (iota := iota) analysis first)))
        (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
          covector couplings.matterMassSquared analysis
          (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
            (iota := iota) analysis second) :
          ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod
            iota analysis) := by
  let firstCore := programPT12MinimalPhysicalMatterLLReducedSliceCore
    period hPeriod configuration analysis first
  let secondCore := programPT12MinimalPhysicalMatterLLReducedSliceCore
    period hPeriod configuration analysis second
  calc
    _ = diagonalExtendedBulkMatterLLHessianOnCore period hPeriod configuration
          data analysis firstCore secondCore := by
      simp [firstCore, secondCore, diagonalExtendedBulkGraphHessianOnCore,
        diagonalExtendedBulkMatterLLHessianOnCore,
        programPT12MinimalPhysicalMatterLLReducedSliceCore,
        diagonalExtendedBulkHessian_apply]
    _ = _ := by
      unfold diagonalExtendedBulkMatterLLHessianOnCore
      change
        programPPrimitiveSpinCMatterGraphForm period hPeriod
              couplings.matterMassSquared
              (programPPrimitiveSpinCMatterGraphFinite period hPeriod
                couplings.matterMassSquared first.1)
              (programPPrimitiveSpinCMatterGraphFinite period hPeriod
                couplings.matterMassSquared second.1) +
            globalCandidateAFullLLGraphForm period hPeriod data analysis
              (globalCandidateAFullLLSmoothEmbedding period hPeriod data
                analysis ((0, first.2) : GlobalFullLLSmooth period hPeriod analysis))
              (globalCandidateAFullLLSmoothEmbedding period hPeriod data
                analysis ((0, second.2) : GlobalFullLLSmooth period hPeriod analysis)) = _
      rw [globalCandidateAFullLLGraphForm_zeroAuxMeasure_eq_fluxHessian]
      exact (programPGlobalGaugeFixedMatterLLSmoothSlice_pairing period hPeriod
        covector couplings.matterMassSquared analysis first second).symm

/-- At parameter zero, the preferred family pairing on the matter--LL slice
is the natural Friedrichs pairing plus the explicit seven-block local action
residual. -/
theorem globalHessianPreferredFiveSector_actualOperator_zero_matterLLSlice_pairing_decomposition
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
      (measure := measure) period hPeriod configuration data analysis
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
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}
    (baseFamily : GlobalHessianPreferredFiveSectorBismutFreedFamily4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    inner Real
        (baseFamily.actualOperator 0
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis
            (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
              configuration analysis first)))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second)) =
      inner Real
          (programPGlobalGaugeFixedLLFriedrichsHessianOperator period hPeriod
            covector couplings.matterMassSquared analysis
            (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
              covector couplings.matterMassSquared analysis
              (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
                (iota := iota) analysis first)))
          (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
            covector couplings.matterMassSquared analysis
            (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
              (iota := iota) analysis second) :
            ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod
              iota analysis) +
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
          hPeriod configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family).chartBridge
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second) := by
  let chart := globalCandidateAActualKernelChart period hPeriod configuration
    data analysis einsteinScale hTransverse family
  let sameAction := globalCandidateAActualKernelSameAction period hPeriod
    configuration data analysis einsteinScale hTransverse family
  let physical := globalCandidateACanonicalSixPhysicalExtension_of_chartBound
    period hPeriod configuration data analysis einsteinScale hTransverse family
      chartBound
  let firstCore := programPT12MinimalPhysicalMatterLLReducedSliceCore
    period hPeriod configuration analysis first
  let secondCore := programPT12MinimalPhysicalMatterLLReducedSliceCore
    period hPeriod configuration analysis second
  calc
    _ = diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
          hPeriod configuration data analysis chart sameAction.chartBridge
            firstCore secondCore := by
      rw [baseFamily.actual_zero]
      change inner Real
          (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
            configuration data analysis chart sameAction physical
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis firstCore))
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis secondCore) = _
      exact globalCandidateAFaithfulAugmentedRieszOperator_smooth_pairing
        period hPeriod configuration data analysis chart sameAction physical
          firstCore secondCore
    _ = diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
          data analysis firstCore secondCore +
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
          hPeriod configuration data analysis chart sameAction.chartBridge
            firstCore secondCore :=
      diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical period
        hPeriod configuration data analysis chart sameAction firstCore secondCore
    _ = _ := by
      rw [programPT12MinimalPhysicalMatterLLReducedSlice_graphHessian_eq_friedrichsPairing
        period hPeriod configuration data analysis covector first second]

end
end P0EFTJanusProgramPT12PreferredActualZeroMatterLLFriedrichsDecomposition4D
end JanusFormal
