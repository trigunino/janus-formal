import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D

/-!
# Canonical available reduced quadratic Euler operator

The canonical seven physical continuous extensions are converted, without an
additional analytic hypothesis, into the blockwise packet used by the reduced
quadratic construction.  This exposes the strongest presently available
reduced action and Euler operator with the canonical extension packet as its
only H11 input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGaugeAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticEuler4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section Adapter

variable
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
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
      period hPeriod configuration data analysis chart sameAction)

/-- Canonical continuous extensions, repackaged as the seven independently
named H11 block extensions. -/
def globalCandidateASevenPhysicalBlockExtensions_of_canonical :
    GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod configuration
      data analysis chart sameAction where
  interaction :=
    { form := extensions.extension .candidateA
      symmetric := extensions.symmetric .candidateA
      smooth_agreement := by
        intro first second
        change
          extensions.extension .candidateA
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first)
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second) =
            globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
              configuration data analysis chart sameAction .candidateA first
                second
        exact extensions.extension_agrees .candidateA first second }
  ghy :=
    { form := extensions.extension .robin
      symmetric := extensions.symmetric .robin
      smooth_agreement := by
        intro first second
        change
          extensions.extension .robin
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first)
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second) =
            globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
              configuration data analysis chart sameAction .robin first second
        exact extensions.extension_agrees .robin first second }
  einsteinHilbertPlus :=
    { form := extensions.extension .einsteinHilbertPlus
      symmetric := extensions.symmetric .einsteinHilbertPlus
      smooth_agreement := by
        intro first second
        change
          extensions.extension .einsteinHilbertPlus
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first)
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second) =
            globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
              configuration data analysis chart sameAction
                .einsteinHilbertPlus first second
        exact extensions.extension_agrees .einsteinHilbertPlus first second }
  einsteinHilbertMinus :=
    { form := extensions.extension .einsteinHilbertMinus
      symmetric := extensions.symmetric .einsteinHilbertMinus
      smooth_agreement := by
        intro first second
        change
          extensions.extension .einsteinHilbertMinus
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first)
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second) =
            globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
              configuration data analysis chart sameAction
                .einsteinHilbertMinus first second
        exact extensions.extension_agrees .einsteinHilbertMinus first second }
  maxwellPlus :=
    { form := extensions.extension .maxwellPlus
      symmetric := extensions.symmetric .maxwellPlus
      smooth_agreement := by
        intro first second
        change
          extensions.extension .maxwellPlus
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first)
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second) =
            globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
              configuration data analysis chart sameAction .maxwellPlus first
                second
        exact extensions.extension_agrees .maxwellPlus first second }
  maxwellMinus :=
    { form := extensions.extension .maxwellMinus
      symmetric := extensions.symmetric .maxwellMinus
      smooth_agreement := by
        intro first second
        change
          extensions.extension .maxwellMinus
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first)
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second) =
            globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
              configuration data analysis chart sameAction .maxwellMinus first
                second
        exact extensions.extension_agrees .maxwellMinus first second }
  finiteBV :=
    { form := extensions.extension .finiteBV
      symmetric := extensions.symmetric .finiteBV
      smooth_agreement := by
        intro first second
        change
          extensions.extension .finiteBV
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first)
              (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second) =
            globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
              configuration data analysis chart sameAction .finiteBV first
                second
        exact extensions.extension_agrees .finiteBV first second }

end Adapter

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

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev SameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

variable
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData)
      einsteinScale)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
      period hPeriod configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData))

private abbrev Core :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

/-- The canonical H11 packet in the blockwise format consumed by Gate 193. -/
def globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks :
    GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod configuration
      data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData) :=
  globalCandidateASevenPhysicalBlockExtensions_of_canonical period hPeriod
    configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData)
      extensions

/-- The genuine Robin domain remains the domain of the canonical wrapper. -/
def globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain :
    Set (Reduced period hPeriod configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain period
    hPeriod configuration data analysis chartData einsteinScale projection

theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain_isOpen :
    IsOpen
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) :=
  globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain_isOpen
    period hPeriod configuration data analysis chartData einsteinScale projection

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain_zero_mem :
    (0 : Reduced period hPeriod configuration data analysis) ∈
      globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection :=
  globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain_zero_mem
    period hPeriod configuration data analysis chartData einsteinScale
      hTransverse projection

/-- Strongest available reduced action, specialized to the canonical seven
physical extension packet. -/
def globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction :
    Reduced period hPeriod configuration data analysis → Real :=
  globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction period
    hPeriod configuration data analysis chartData einsteinScale projection
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
        hPeriod configuration data analysis chartData extensions)

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_contDiffOn_two :
    ContDiffOn Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection extensions)
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_contDiffOn_two
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
          hPeriod configuration data analysis chartData extensions)

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_contDiffAt_zero :
    ContDiffAt Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection extensions) 0 := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_contDiffAt_zero
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
          hPeriod configuration data analysis chartData extensions)

/-- Frechet Euler covector of the canonically instantiated available action. -/
noncomputable def globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis →L[Real] Real :=
  globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticEulerCovector
    period hPeriod configuration data analysis chartData einsteinScale projection
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
        hPeriod configuration data analysis chartData extensions) state

/-- Strong Riesz residual of the canonical available action. -/
noncomputable def globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticRieszResidual
    period hPeriod configuration data analysis chartData einsteinScale projection
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
        hPeriod configuration data analysis chartData extensions) state

theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_pairing
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual
          period hPeriod configuration data analysis chartData einsteinScale
            projection extensions state) test =
      globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector
        period hPeriod configuration data analysis chartData einsteinScale
          projection extensions state test := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticRieszResidual_pairing
      period hPeriod configuration data analysis chartData einsteinScale
        projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
          hPeriod configuration data analysis chartData extensions) state test

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_fderiv_add
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction
          period hPeriod configuration data analysis chartData einsteinScale
            projection extensions) state =
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
            period hPeriod configuration data analysis chartData einsteinScale
              projection
              (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks
                period hPeriod configuration data analysis chartData
                  extensions).maxwellPlus
              (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks
                period hPeriod configuration data analysis chartData
                  extensions).maxwellMinus) state +
        globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
          period hPeriod configuration data analysis chartData
            (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks
              period hPeriod configuration data analysis chartData extensions)
              state := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_fderiv_add
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
          hPeriod configuration data analysis chartData extensions) state hState

/-- Criticality for the canonically instantiated available action. -/
def GlobalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical
    (state : Reduced period hPeriod configuration data analysis) : Prop :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual
    period hPeriod configuration data analysis chartData einsteinScale projection
      extensions state = 0

theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical_iff_fderiv_eq_zero
    (state : Reduced period hPeriod configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical
        period hPeriod configuration data analysis chartData einsteinScale
          projection extensions state ↔
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction
            period hPeriod configuration data analysis chartData einsteinScale
              projection extensions) state = 0 := by
  change
    GlobalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticIsCritical
        period hPeriod configuration data analysis chartData einsteinScale
          projection
          (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
            hPeriod configuration data analysis chartData extensions) state ↔ _
  exact
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticIsCritical_iff_fderiv_eq_zero
      period hPeriod configuration data analysis chartData einsteinScale
        projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
          hPeriod configuration data analysis chartData extensions) state

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_core
    (core : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection extensions
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (globalCandidateAMinimalPhysicalReducedCompletedGraphAction period hPeriod
          configuration data analysis
          (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis
            (Submodule.Quotient.mk core)) +
        (globalCandidateACanonicalSixLocalBlocks period hPeriod
          (MinimalChart period hPeriod configuration data analysis chartData)).robin
          (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
            configuration data analysis chartData
            (Submodule.Quotient.mk core)) +
        ((1 / 2 : Real) *
            diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core +
          (1 / 2 : Real) *
            diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core)) +
        (1 / 2 : Real) *
          (((diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core +
            diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) +
            diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) +
            diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_core
      period hPeriod configuration data analysis chartData einsteinScale
        projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period
          hPeriod configuration data analysis chartData extensions) core

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D
end JanusFormal
