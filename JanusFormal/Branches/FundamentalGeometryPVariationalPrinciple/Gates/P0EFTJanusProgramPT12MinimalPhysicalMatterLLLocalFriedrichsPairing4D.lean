import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D

/-!
# Local matter--LL Hessian and the Friedrichs product pairing

On the injective minimal physical matter--LL slice, the actual local
Candidate-A matter--LL Hessian is the pairing of the global matter--LL
Friedrichs product operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MinimalPhysicalMatterLLLocalFriedrichsPairing4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusFullLLSameActionFredholmRestriction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalLLAuxMeasureSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

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

/-- The full LL graph form restricted to zero auxiliary/measure directions is
the reduced smooth LL Hessian. -/
theorem globalCandidateAFullLLGraphForm_zeroAuxMeasure_eq_fluxHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second :
      LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    globalCandidateAFullLLGraphForm period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          ((0, first) : GlobalFullLLSmooth period hPeriod analysis))
        (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          ((0, second) : GlobalFullLLSmooth period hPeriod analysis)) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (analysis.llH1Data period hPeriod).frame
        (analysis.llH1Data period hPeriod).fields
        first.toTest second.toTest
        (analysis.llH1Data period hPeriod).mu := by
  letI : IsFiniteMeasure (analysis.llH1Data period hPeriod).mu :=
    (analysis.llH1Data period hPeriod).finiteMeasure
  rw [globalCandidateAFullLLGraphForm_apply]
  rw [globalCandidateAFullLLContinuousHessian_smooth]
  unfold globalCandidateAFullLLSameActionHessian
  simpa [globalCandidateAFullLLDirection, globalCandidateALLAuxMeasureDirection,
    fullLLFredholmDirection, addDirection, fullRobinLLDirection,
    commonRobinLLDirection, fullLLHessian, GlobalAnalysisData.llH1Data,
    GlobalBoundaryVariationData.llFields] using
    fullLLHessian_zeroAuxMeasure_eq_fluxHessian period hPeriod
      (analysis.llH1Data period hPeriod).frame
      (analysis.llH1Data period hPeriod).fields
      (0 : SmoothThroatField period hPeriod Real) 0
      first.toTest second.toTest
      (analysis.llH1Data period hPeriod).mu

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

/-- On the faithful minimal physical matter--LL slice, the local action
Hessian is exactly the global matter--LL Friedrichs operator pairing. -/
theorem programPT12MinimalPhysicalMatterLLReducedSlice_localHessian_eq_friedrichsPairing
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    globalCandidateALocalMatterLLHessian period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
        (programPT12MinimalPhysicalMatterLLReducedSliceToChart period hPeriod
          configuration data analysis chartData first)
        (programPT12MinimalPhysicalMatterLLReducedSliceToChart period hPeriod
          configuration data analysis chartData second) =
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
  let chart := globalCandidateAMinimalPhysicalLocalVariationalChart period
    hPeriod configuration data analysis chartData
  let sameAction := globalCandidateAMinimalPhysicalMatterLLSameActionBridge
    period hPeriod configuration data analysis chartData
  let firstCore := programPT12MinimalPhysicalMatterLLReducedSliceCore
    period hPeriod configuration analysis first
  let secondCore := programPT12MinimalPhysicalMatterLLReducedSliceCore
    period hPeriod configuration analysis second
  rw [programPT12MinimalPhysicalMatterLLReducedSliceToChart_mk,
    programPT12MinimalPhysicalMatterLLReducedSliceToChart_mk,
    globalCandidateAMinimalPhysicalReducedCoreToChart_mk,
    globalCandidateAMinimalPhysicalReducedCoreToChart_mk]
  simp only [globalCandidateACanonicalSixCoreToChart, LinearMap.comp_apply]
  change
    diagonalExtendedBulkMinimalPhysicalLocalMatterLLHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge firstCore
          secondCore = _
  rw [diagonalExtendedBulkH13LocalMatterLLHessian_eq_graph period hPeriod
    configuration data analysis chart sameAction firstCore secondCore]
  unfold diagonalExtendedBulkMatterLLHessianOnCore
  change
    programPPrimitiveSpinCMatterGraphForm period hPeriod
          couplings.matterMassSquared
          (programPPrimitiveSpinCMatterGraphFinite period hPeriod
            couplings.matterMassSquared first.1)
          (programPPrimitiveSpinCMatterGraphFinite period hPeriod
            couplings.matterMassSquared second.1) +
        globalCandidateAFullLLGraphForm period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            ((0, first.2) : GlobalFullLLSmooth period hPeriod analysis))
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            ((0, second.2) : GlobalFullLLSmooth period hPeriod analysis)) = _
  rw [globalCandidateAFullLLGraphForm_zeroAuxMeasure_eq_fluxHessian]
  exact (programPGlobalGaugeFixedMatterLLSmoothSlice_pairing period hPeriod
    covector couplings.matterMassSquared analysis first second).symm

end
end
end P0EFTJanusProgramPT12MinimalPhysicalMatterLLLocalFriedrichsPairing4D
end JanusFormal
