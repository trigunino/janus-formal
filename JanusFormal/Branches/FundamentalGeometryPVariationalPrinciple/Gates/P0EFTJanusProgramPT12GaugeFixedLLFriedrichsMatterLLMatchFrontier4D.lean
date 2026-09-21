import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalActualSmoothCoreIdentification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSmoothSliceReadout4D

/-!
# Canonical actual--Friedrichs matter--LL matching frontier

On the reduced smooth matter--LL slice, both zero-fibre pairings have the
same Friedrichs graph term.  Their exact difference is therefore the
difference between the transported and actual physical forms.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsMatterLLMatchFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 10000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12PreferredActualZeroMatterLLFriedrichsDecomposition4D
open P0EFTJanusProgramPT12PreferredActualZeroMatterLLSevenPhysicalRieszDecomposition4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSmoothSliceReadout4D
open P0EFTJanusProgramPT12CanonicalActualSmoothCoreIdentification4D

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

private abbrev CanonicalPhysical :=
  globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
    configuration data analysis chartData reducedChart

private theorem friedrichs_zero_matterLLSlice_pairing_decomposition
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    inner Real
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data)
            (analysis := analysis)
            (chart := CanonicalChart period hPeriod configuration data analysis
              chartData)
            (sameAction := CanonicalSameAction period hPeriod configuration
              data analysis chartData)
            (physical := CanonicalPhysical period hPeriod configuration data
              analysis chartData reducedChart)
            period hPeriod covector 0
            (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
              covector couplings.matterMassSquared analysis
              (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
                (iota := iota) analysis first)))
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector second) =
      inner Real
          (programPGlobalGaugeFixedLLFriedrichsHessianOperator period hPeriod
            covector couplings.matterMassSquared analysis
            (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
              covector couplings.matterMassSquared analysis
              (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
                (iota := iota) analysis first)))
          (programPT12FriedrichsMatterLLSmoothSliceEmbedding
            (couplings := couplings) period hPeriod configuration analysis
              covector second) +
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
                  covector second)) := by
  rw [programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_pairing]
  have hD11 :=
    programPT12GaugeFixedLLFriedrichsD11Operator_zero_matterLLSlice_pairing
      (configuration := configuration) (couplings := couplings)
        period hPeriod analysis covector first second
  rw [show
    inner Real
        (programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
          couplings.matterMassSquared analysis 0
          (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
            covector couplings.matterMassSquared analysis
            (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
              (iota := iota) analysis first)))
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector second) =
      inner Real
        (programPGlobalGaugeFixedLLFriedrichsHessianOperator period hPeriod
          covector couplings.matterMassSquared analysis
          (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
            covector couplings.matterMassSquared analysis
            (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
              (iota := iota) analysis first)))
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector second) by
      simpa [programPT12FriedrichsMatterLLSmoothSliceEmbedding] using hD11]
  rfl

private theorem actual_matterLLSlice_pairing_decomposition
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    inner Real
        (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
          configuration data analysis chartData reducedChart
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis first))
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis second) =
      inner Real
          (programPGlobalGaugeFixedLLFriedrichsHessianOperator period hPeriod
            covector couplings.matterMassSquared analysis
            (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
              covector couplings.matterMassSquared analysis
              (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
                (iota := iota) analysis first)))
          (programPT12FriedrichsMatterLLSmoothSliceEmbedding
            (couplings := couplings) period hPeriod configuration analysis
              covector second) +
        (CanonicalPhysical period hPeriod configuration data analysis chartData
          reducedChart).form
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis first)
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis second) := by
  let firstCore := programPT12MinimalPhysicalMatterLLReducedSliceCore period
    hPeriod configuration analysis first
  let secondCore := programPT12MinimalPhysicalMatterLLReducedSliceCore period
    hPeriod configuration analysis second
  calc
    _ = diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
          hPeriod configuration data analysis
          (CanonicalChart period hPeriod configuration data analysis chartData)
          (CanonicalSameAction period hPeriod configuration data analysis
            chartData).chartBridge firstCore secondCore := by
      convert
        (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator_smooth_pairing
          period hPeriod configuration data analysis chartData reducedChart
            firstCore secondCore) using 1; rfl
    _ = diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
          data analysis firstCore secondCore +
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
          hPeriod configuration data analysis
          (CanonicalChart period hPeriod configuration data analysis chartData)
          (CanonicalSameAction period hPeriod configuration data analysis
            chartData).chartBridge firstCore secondCore :=
      diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical period
        hPeriod configuration data analysis
          (CanonicalChart period hPeriod configuration data analysis chartData)
          (CanonicalSameAction period hPeriod configuration data analysis
            chartData) firstCore secondCore
    _ = _ := by
      rw [programPT12MinimalPhysicalMatterLLReducedSlice_graphHessian_eq_friedrichsPairing
        period hPeriod configuration data analysis covector first second]
      congr 1
      convert
        ((CanonicalPhysical period hPeriod configuration data analysis
          chartData reducedChart).smooth_agreement firstCore secondCore).symm
          using 1; rfl

/-- Exact common-core comparison: the graph contribution cancels, leaving
only the discrepancy between the transported and actual physical forms. -/
theorem programPT12GaugeFixedLLFriedrichsMatterLL_pairing_sub_actual
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    inner Real
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data)
            (analysis := analysis)
            (chart := CanonicalChart period hPeriod configuration data analysis
              chartData)
            (sameAction := CanonicalSameAction period hPeriod configuration
              data analysis chartData)
            (physical := CanonicalPhysical period hPeriod configuration data
              analysis chartData reducedChart)
            period hPeriod covector 0
            (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
              covector couplings.matterMassSquared analysis
              (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
                (iota := iota) analysis first)))
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector second) -
      inner Real
        (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
          configuration data analysis chartData reducedChart
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis first))
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis second) =
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
                  covector second)) -
        (CanonicalPhysical period hPeriod configuration data analysis chartData
          reducedChart).form
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis first)
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis second) := by
  rw [friedrichs_zero_matterLLSlice_pairing_decomposition period hPeriod
    configuration data analysis chartData reducedChart covector first second]
  rw [actual_matterLLSlice_pairing_decomposition period hPeriod configuration
    data analysis chartData reducedChart covector first second]
  ring

/-- Equality of the two zero-fibre pairings is exactly equality of their
physical forms on the reduced smooth matter--LL slice. -/
theorem programPT12GaugeFixedLLFriedrichsMatterLL_pairing_eq_actual_iff
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    inner Real
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data)
            (analysis := analysis)
            (chart := CanonicalChart period hPeriod configuration data analysis
              chartData)
            (sameAction := CanonicalSameAction period hPeriod configuration
              data analysis chartData)
            (physical := CanonicalPhysical period hPeriod configuration data
              analysis chartData reducedChart)
            period hPeriod covector 0
            (programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
              covector couplings.matterMassSquared analysis
              (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
                (iota := iota) analysis first)))
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector second) =
      inner Real
        (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
          configuration data analysis chartData reducedChart
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis first))
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis second) ↔
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
  have hDifference :=
    programPT12GaugeFixedLLFriedrichsMatterLL_pairing_sub_actual period hPeriod
      configuration data analysis chartData reducedChart covector first second
  constructor <;> intro h <;> linarith

end
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsMatterLLMatchFrontier4D
end JanusFormal
