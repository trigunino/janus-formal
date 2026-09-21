import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PreferredActualZeroMatterLLFriedrichsDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D

/-!
# Preferred actual-zero matter--LL seven-physical Riesz decomposition

The local physical residual is expanded into its seven retained blocks and,
for the canonical bounded extension, represented by its physical Riesz
operator on the matter--LL slice.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12PreferredActualZeroMatterLLSevenPhysicalRieszDecomposition4D

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
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
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
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12PreferredActualZeroMatterLLFriedrichsDecomposition4D

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

/-- On the matter--LL slice, the local physical residual is exactly the sum
of its seven retained action-block Hessians. -/
theorem programPT12MinimalPhysicalMatterLLReducedSlice_localPhysicalHessian_eq_seven
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
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge
        (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
          configuration analysis first)
        (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
          configuration analysis second) =
      ((((((diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
          configuration data analysis chart sameAction
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second) +
        diagonalExtendedBulkH11GHYHessianOnCore period hPeriod configuration
          data analysis chart sameAction
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second)) +
        diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
          configuration data analysis chart sameAction
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second)) +
        diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
          configuration data analysis chart sameAction
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second)) +
        diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
          configuration data analysis chart sameAction
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second)) +
        diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
          configuration data analysis chart sameAction
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second)) +
        diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
          configuration data analysis chart sameAction
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis first)
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis second)) := by
  exact diagonalExtendedBulkH11PhysicalHessian_eq_seven period hPeriod
    configuration data analysis chart sameAction
      (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
        configuration analysis first)
      (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
        configuration analysis second)

/-- The zero fibre of the common-domain D11 family gives exactly the natural
Friedrichs pairing on the matter--LL slice. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_zero_matterLLSlice_pairing
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    inner Real
        (programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
          couplings.matterMassSquared analysis 0
          (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
            covector couplings.matterMassSquared analysis
            (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
              (iota := iota) analysis first)))
        (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
          covector couplings.matterMassSquared analysis
          (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
            (iota := iota) analysis second) :
          ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod
            iota analysis) =
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
  let firstDomain :=
    programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod covector
      couplings.matterMassSquared analysis
      (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
        (iota := iota) analysis first)
  apply congrArg
    (fun value : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period
        hPeriod iota analysis =>
      inner Real value
        (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
          covector couplings.matterMassSquared analysis
          (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
            (iota := iota) analysis second)))
  have hApply :=
    (LinearPMap.ext_iff.mp
      (programPT12GaugeFixedLLFriedrichsD11Operator_zero period hPeriod
        covector couplings.matterMassSquared analysis)).2
      (x := (firstDomain :
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod
          iota analysis))
      (hf := firstDomain.property) (hg := firstDomain.property)
  convert hApply using 1
  all_goals congr 1

/-- With the canonical bounded seven-block extension, the preferred operator
at zero is the Friedrichs matter--LL pairing plus the exact physical Riesz
pairing on the same slice. -/
theorem globalHessianPreferredFiveSector_actualOperator_zero_matterLLSlice_pairing_friedrichs_add_physicalRiesz
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
        inner Real
          (globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
            configuration data analysis
            (globalCandidateAActualKernelChart period hPeriod configuration data
              analysis einsteinScale hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod configuration
              data analysis einsteinScale hTransverse family)
            (globalCandidateACanonicalSixPhysicalExtension_of_chartBound
              period hPeriod configuration data analysis einsteinScale
                hTransverse family chartBound)
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis
              (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
                configuration analysis first)))
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis
            (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
              configuration analysis second)) := by
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
  let firstEmbedding := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis firstCore
  let secondEmbedding := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis secondCore
  calc
    _ = inner Real
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
          hPeriod configuration data analysis chart sameAction.chartBridge
            firstCore secondCore := by
      exact
        globalHessianPreferredFiveSector_actualOperator_zero_matterLLSlice_pairing_decomposition
          period hPeriod configuration data analysis einsteinScale hTransverse
            family chartBound baseFamily covector first second
    _ = _ := by
      congr 1
      calc
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
            hPeriod configuration data analysis chart sameAction.chartBridge
              firstCore secondCore =
            physical.form firstEmbedding secondEmbedding :=
          (physical.smooth_agreement firstCore secondCore).symm
        _ = inner Real
              (globalCandidateACanonicalStablePhysicalPerturbation period
                hPeriod configuration data analysis chart sameAction physical
                  firstEmbedding)
              secondEmbedding := by
          exact
            (globalCandidateASevenPhysicalCommonRieszOperator_pairing period
              hPeriod configuration data analysis chart sameAction physical
                firstEmbedding secondEmbedding).symm

/-- On the matter--LL slice, agreement of the preferred zero fibre with the
zero D11 Friedrichs fibre is equivalent to vanishing of the retained physical
Riesz pairing. -/
theorem globalHessianPreferredFiveSector_actualOperator_zero_matterLLSlice_eq_d11_iff_physicalRiesz_pairing_eq_zero
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
    let firstEmbedding := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis firstCore
    let secondEmbedding := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis secondCore
    let firstFriedrichs :=
      programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod covector
        couplings.matterMassSquared analysis
        (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
          (iota := iota) analysis first)
    let secondFriedrichs :=
      programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod covector
        couplings.matterMassSquared analysis
        (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
          (iota := iota) analysis second)
    (inner Real (baseFamily.actualOperator 0 firstEmbedding) secondEmbedding =
        inner Real
          (programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
            couplings.matterMassSquared analysis 0 firstFriedrichs)
          secondFriedrichs) ↔
      inner Real
        (globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
          configuration data analysis chart sameAction physical firstEmbedding)
        secondEmbedding = 0 := by
  simp only
    [programPT12GaugeFixedLLFriedrichsD11Operator_zero_matterLLSlice_pairing]
  rw [globalHessianPreferredFiveSector_actualOperator_zero_matterLLSlice_pairing_friedrichs_add_physicalRiesz
    period hPeriod configuration data analysis einsteinScale hTransverse family
      chartBound baseFamily covector first second]
  constructor
  · intro hEqual
    linarith
  · intro hZero
    rw [hZero, add_zero]

end
end P0EFTJanusProgramPT12PreferredActualZeroMatterLLSevenPhysicalRieszDecomposition4D
end JanusFormal
