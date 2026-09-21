import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalActualSmoothCoreIdentification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D

/-!
Conditional smooth-core graph intertwiner between the canonical actual
augmented operator and the physical Friedrichs zero fibre.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12CanonicalActualSmoothCoreIdentification4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
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

private abbrev SmoothCore :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev ActualHilbert :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

private abbrev FriedrichsHilbert (iota : Type*) :=
  ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
    analysis

private def smoothEmbedding :
    SmoothCore period hPeriod configuration analysis →ₗ[Real]
      ActualHilbert period hPeriod configuration data analysis :=
  diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

private abbrev PhysicalZeroOperator
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    FriedrichsHilbert period hPeriod configuration analysis iota →ₗ.[Real]
      FriedrichsHilbert period hPeriod configuration analysis iota :=
  programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
    (configuration := configuration) (data := data) (analysis := analysis)
      (chart := CanonicalChart period hPeriod configuration data analysis
        chartData)
      (sameAction := CanonicalSameAction period hPeriod configuration data
        analysis chartData)
      (physical := CanonicalPhysical period hPeriod configuration data analysis
        chartData reducedChart)
      period hPeriod covector 0

/-- Exact missing input: an isometric ambient realization that carries the
complete actual smooth core into the zero-fibre domain and intertwines the
two operators there. -/
structure ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) where
  ambient :
    ActualHilbert period hPeriod configuration data analysis →ₗᵢ[Real]
      FriedrichsHilbert period hPeriod configuration analysis iota
  smooth_mem_domain :
    ∀ core : SmoothCore period hPeriod configuration analysis,
      ambient
          (smoothEmbedding period hPeriod configuration data analysis core) ∈
        (PhysicalZeroOperator period hPeriod configuration data analysis
          chartData reducedChart covector).domain
  intertwines :
    ∀ core : SmoothCore period hPeriod configuration analysis,
      PhysicalZeroOperator period hPeriod configuration data analysis chartData
          reducedChart covector
          ⟨ambient
              (smoothEmbedding period hPeriod configuration data analysis core),
            smooth_mem_domain core⟩ =
        ambient
          (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
            configuration data analysis chartData reducedChart
            (smoothEmbedding period hPeriod configuration data analysis core))

namespace ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D

variable {iota : Type*} [DecidableEq iota]
variable (covector : iota → TangentVector3)

/-- Canonical lift of the complete actual smooth core to the physical
Friedrichs zero-fibre domain. -/
def smoothDomain
    (bridge : ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
      period hPeriod configuration data analysis chartData reducedChart
        covector)
    (core : SmoothCore period hPeriod configuration analysis) :
    (PhysicalZeroOperator period hPeriod configuration data analysis chartData
      reducedChart covector).domain :=
  ⟨bridge.ambient
      (smoothEmbedding period hPeriod configuration data analysis core),
    bridge.smooth_mem_domain core⟩

@[simp]
theorem smoothDomain_value
    (bridge : ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
      period hPeriod configuration data analysis chartData reducedChart
        covector)
    (core : SmoothCore period hPeriod configuration analysis) :
    ((bridge.smoothDomain period hPeriod configuration data analysis chartData
        reducedChart covector core :
      (PhysicalZeroOperator period hPeriod configuration data analysis
        chartData reducedChart covector).domain) :
      FriedrichsHilbert period hPeriod configuration analysis iota) =
        bridge.ambient
          (smoothEmbedding period hPeriod configuration data analysis core) :=
  rfl

/-- The conditional graph intertwiner identifies the physical Friedrichs
zero-fibre pairing with the genuine second derivative of the canonical action
on the complete actual smooth core. -/
theorem zero_fibre_action_second_fderiv_pairing
    (bridge : ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
      period hPeriod configuration data analysis chartData reducedChart
        covector)
    (base : ActualHilbert period hPeriod configuration data analysis)
    (first second : SmoothCore period hPeriod configuration analysis) :
    inner Real
        (PhysicalZeroOperator period hPeriod configuration data analysis
          chartData reducedChart covector
          (bridge.smoothDomain period hPeriod configuration data analysis
            chartData reducedChart covector first))
        (bridge.ambient
          (smoothEmbedding period hPeriod configuration data analysis second)) =
      (fderiv Real
          (fun state => fderiv Real
            (globalCandidateAGaugeFixedAugmentedBRSTAction period hPeriod
              configuration data analysis chartData reducedChart) state)
          base)
          (smoothEmbedding period hPeriod configuration data analysis first)
          (smoothEmbedding period hPeriod configuration data analysis second) := by
  calc
    _ = inner Real
          (bridge.ambient
            (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
              configuration data analysis chartData reducedChart
              (smoothEmbedding period hPeriod configuration data analysis
                first)))
          (bridge.ambient
            (smoothEmbedding period hPeriod configuration data analysis
              second)) := by
        apply congrArg (fun state => inner Real state
          (bridge.ambient
            (smoothEmbedding period hPeriod configuration data analysis
              second)))
        simpa [smoothDomain] using bridge.intertwines first
    _ = inner Real
          (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
            configuration data analysis chartData reducedChart
            (smoothEmbedding period hPeriod configuration data analysis first))
          (smoothEmbedding period hPeriod configuration data analysis second) :=
      bridge.ambient.inner_map_map _ _
    _ = diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
          hPeriod configuration data analysis
          (CanonicalChart period hPeriod configuration data analysis chartData)
          (CanonicalSameAction period hPeriod configuration data analysis
            chartData).chartBridge first second :=
      globalCandidateAGaugeFixedAugmentedBRSTRieszOperator_smooth_pairing period
        hPeriod configuration data analysis chartData reducedChart first second
    _ = _ :=
      (globalCandidateAGaugeFixedAugmentedBRSTAction_second_fderiv_smooth period
        hPeriod configuration data analysis chartData reducedChart base first
          second).symm

end ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
end
end
end P0EFTJanusProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D
end JanusFormal
