import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsMatterLLMatchFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction4D

/-!
# Reduced-coordinate criterion for the T12 matter--LL form match

The canonical seven-block form factors through the minimal physical Hilbert
reduction.  Hence equality of the transported and actual reduced coordinates
is exactly the missing sufficient input for the physical-form comparison.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsMatterLLReducedFormMatch4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 10000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfReducedHilbertChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSmoothSliceReadout4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period
  hPeriod (measure := measure) configuration data analysis)
variable (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D
  period hPeriod configuration data analysis chartData)

private abbrev CanonicalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev CanonicalSameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

private abbrev CanonicalExtensions :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_reducedHilbertChart
    period hPeriod configuration data analysis chartData reducedChart

private abbrev CanonicalBlocks :=
  globalCandidateASevenPhysicalBlockExtensions_of_canonical period hPeriod
    configuration data analysis
      (CanonicalChart period hPeriod configuration data analysis chartData)
      (CanonicalSameAction period hPeriod configuration data analysis chartData)
      (CanonicalExtensions period hPeriod configuration data analysis chartData
        reducedChart)

private abbrev CanonicalPhysical :=
  globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
    configuration data analysis chartData reducedChart

private theorem canonicalPhysical_form_reduction_left
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    (CanonicalPhysical period hPeriod configuration data analysis chartData
        reducedChart).form
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      (CanonicalPhysical period hPeriod configuration data analysis chartData
        reducedChart).form state := by
  change
    (globalCandidateASevenPhysicalCommonDomainExtension_of_blocks period hPeriod
      configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis chartData)
        (CanonicalBlocks period hPeriod configuration data analysis chartData
          reducedChart)).form
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) = _
  exact
    globalCandidateASevenPhysicalCommonDomainExtension_of_blocks_form_reduction_left
      period hPeriod configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis chartData)
        (CanonicalBlocks period hPeriod configuration data analysis chartData
          reducedChart) state

private theorem canonicalPhysical_form_reduction_right
    (state test : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    (CanonicalPhysical period hPeriod configuration data analysis chartData
        reducedChart).form test
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      (CanonicalPhysical period hPeriod configuration data analysis chartData
        reducedChart).form test state := by
  change
    (globalCandidateASevenPhysicalCommonDomainExtension_of_blocks period hPeriod
      configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis chartData)
        (CanonicalBlocks period hPeriod configuration data analysis chartData
          reducedChart)).form test
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) = _
  exact
    globalCandidateASevenPhysicalCommonDomainExtension_of_blocks_form_reduction_right
      period hPeriod configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis chartData)
        (CanonicalBlocks period hPeriod configuration data analysis chartData
          reducedChart) state test

/-- Equality of transported and actual minimal reductions on the two tested
directions suffices for the canonical physical-form match. -/
theorem programPT12GaugeFixedLLFriedrichsMatterLL_physicalForm_eq_actual_of_reductions_eq
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis)
    (hFirst :
      globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (programPT12GaugeFixedLLFriedrichsToActualTransport
            (configuration := configuration) (data := data)
              (analysis := analysis) (iota := iota) period hPeriod
              (programPT12FriedrichsMatterLLSmoothSliceEmbedding
                (couplings := couplings) period hPeriod configuration analysis
                  covector first)) =
        globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis first))
    (hSecond :
      globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (programPT12GaugeFixedLLFriedrichsToActualTransport
            (configuration := configuration) (data := data)
              (analysis := analysis) (iota := iota) period hPeriod
              (programPT12FriedrichsMatterLLSmoothSliceEmbedding
                (couplings := couplings) period hPeriod configuration analysis
                  covector second)) =
        globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis second)) :
    (CanonicalPhysical period hPeriod configuration data analysis chartData
      reducedChart).form
        (programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) (iota := iota) period hPeriod
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector first))
        (programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) (iota := iota) period hPeriod
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector second)) =
      (CanonicalPhysical period hPeriod configuration data analysis chartData
        reducedChart).form
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis first)
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis second) := by
  let transportedFirst :=
    programPT12GaugeFixedLLFriedrichsToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis)
        (iota := iota) period hPeriod
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector first)
  let transportedSecond :=
    programPT12GaugeFixedLLFriedrichsToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis)
        (iota := iota) period hPeriod
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector second)
  let actualFirst := programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
    configuration data analysis first
  let actualSecond := programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
    configuration data analysis second
  let reduction := globalCandidateAMinimalPhysicalHilbertReduction period
    hPeriod configuration data analysis
  let physical := CanonicalPhysical period hPeriod configuration data analysis
    chartData reducedChart
  have hFactor : ∀ state test,
      physical.form state test =
        physical.form (reduction state) (reduction test) := by
    intro state test
    calc
      physical.form state test = physical.form (reduction state) test := by
        exact congrArg (fun functional => functional test)
          (canonicalPhysical_form_reduction_left period hPeriod configuration
            data analysis chartData reducedChart state).symm
      _ = physical.form (reduction state) (reduction test) := by
        exact (canonicalPhysical_form_reduction_right period hPeriod
          configuration data analysis chartData reducedChart test
            (reduction state)).symm
  have hFirst' : reduction transportedFirst = reduction actualFirst := by
    simpa [reduction, transportedFirst, actualFirst] using hFirst
  have hSecond' : reduction transportedSecond = reduction actualSecond := by
    simpa [reduction, transportedSecond, actualSecond] using hSecond
  change physical.form transportedFirst transportedSecond =
    physical.form actualFirst actualSecond
  calc
    physical.form transportedFirst transportedSecond =
        physical.form (reduction transportedFirst)
          (reduction transportedSecond) := hFactor _ _
    _ = physical.form (reduction actualFirst) (reduction actualSecond) := by
      rw [hFirst', hSecond']
    _ = physical.form actualFirst actualSecond := (hFactor _ _).symm

end
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsMatterLLReducedFormMatch4D
end JanusFormal
