import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction4D

/-!
# Reduced graph + Robin + Maxwell-quadratic Euler operator

This gate assembles every currently completed compatible reduced action without
calling the result the full Candidate-A action: the five graph sectors, the
genuine Robin action on its natural open domain, and the conditional Maxwell
Hessian quadratic energy.  It constructs the resulting Frechet Euler
covector, its strong Riesz residual, and the exact derivative decomposition on
the Robin domain.  Nonlinear Einstein--Hilbert, curvature-Maxwell,
interaction, and finite-BV completions remain absent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEuler4D

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
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGaugeAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRobinAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMaxwellQuadraticAction4D

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
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)
      einsteinScale)
    (maxwellPlus :
      GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
        configuration data analysis
        (diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
          configuration data analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData)))
    (maxwellMinus :
      GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
        configuration data analysis
        (diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
          configuration data analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData)))

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

/-- Natural domain inherited from the genuine completed Robin summand. -/
def globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain :
    Set (Reduced period hPeriod configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedRobinDomain period hPeriod
    configuration data analysis chartData einsteinScale projection

theorem globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain_isOpen :
    IsOpen
      (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) := by
  exact globalCandidateAMinimalPhysicalReducedRobinDomain_isOpen period hPeriod
    configuration data analysis chartData einsteinScale projection

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain_zero_mem :
    (0 : Reduced period hPeriod configuration data analysis) ∈
      globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection := by
  exact globalCandidateAMinimalPhysicalReducedRobinDomain_zero_mem period hPeriod
    configuration data analysis chartData einsteinScale hTransverse projection

/-- Honest sum of the presently completed graph, Robin, and Maxwell-quadratic
reduced actions. -/
def globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction :
    Reduced period hPeriod configuration data analysis → Real :=
  fun state =>
    globalCandidateAMinimalPhysicalReducedCompletedGraphAction period hPeriod
        configuration data analysis state +
      globalCandidateAMinimalPhysicalReducedCompletedRobinAction period hPeriod
        configuration data analysis chartData einsteinScale projection state +
      globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction
        period hPeriod configuration data analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData)
          maxwellPlus maxwellMinus state

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction_contDiffOn_two :
    ContDiffOn Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection maxwellPlus maxwellMinus)
      (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) := by
  exact
    (((globalCandidateAMinimalPhysicalReducedCompletedGraphAction_contDiff_two
      period hPeriod configuration data analysis).contDiffOn.add
      (globalCandidateAMinimalPhysicalReducedCompletedRobinAction_contDiffOn_two
        period hPeriod configuration data analysis chartData einsteinScale
          hTransverse projection)).add
      (globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction_contDiff_two
        period hPeriod configuration data analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData)
          maxwellPlus maxwellMinus).contDiffOn)

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction_contDiffAt_zero :
    ContDiffAt Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection maxwellPlus maxwellMinus) 0 :=
  (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction_contDiffOn_two
    period hPeriod configuration data analysis chartData einsteinScale
      hTransverse projection maxwellPlus maxwellMinus).contDiffAt
    ((globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain_isOpen
      period hPeriod configuration data analysis chartData einsteinScale
        projection).mem_nhds
      (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain_zero_mem
        period hPeriod configuration data analysis chartData einsteinScale
          hTransverse projection))

/-- Frechet Euler covector of the available partial reduced action. -/
noncomputable def globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEulerCovector
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis →L[Real] Real :=
  fderiv Real
    (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
      period hPeriod configuration data analysis chartData einsteinScale
        projection maxwellPlus maxwellMinus) state

/-- Strong Riesz residual of the available partial reduced action. -/
noncomputable def globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticRieszResidual
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  (InnerProductSpace.toDual Real
    (Reduced period hPeriod configuration data analysis)).symm
      (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEulerCovector
        period hPeriod configuration data analysis chartData einsteinScale
          projection maxwellPlus maxwellMinus state)

theorem globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticRieszResidual_pairing
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticRieszResidual
          period hPeriod configuration data analysis chartData einsteinScale
            projection maxwellPlus maxwellMinus state)
        test =
      globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEulerCovector
        period hPeriod configuration data analysis chartData einsteinScale
          projection maxwellPlus maxwellMinus state test := by
  unfold globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticRieszResidual
  exact InnerProductSpace.toDual_symm_apply

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction_fderiv_add
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
          period hPeriod configuration data analysis chartData einsteinScale
            projection maxwellPlus maxwellMinus) state =
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedGraphAction period
            hPeriod configuration data analysis) state +
        fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedRobinAction period
            hPeriod configuration data analysis chartData einsteinScale
              projection) state +
        fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction
            period hPeriod configuration data analysis
              (globalCandidateAMinimalPhysicalLocalVariationalChart period
                hPeriod configuration data analysis chartData)
              (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
                hPeriod configuration data analysis chartData)
              maxwellPlus maxwellMinus) state := by
  have hGraph : DifferentiableAt Real
      (globalCandidateAMinimalPhysicalReducedCompletedGraphAction period hPeriod
        configuration data analysis) state :=
    ((globalCandidateAMinimalPhysicalReducedCompletedGraphAction_contDiff_two
      period hPeriod configuration data analysis).differentiable
        (by norm_num)).differentiableAt
  have hRobin : DifferentiableAt Real
      (globalCandidateAMinimalPhysicalReducedCompletedRobinAction period hPeriod
        configuration data analysis chartData einsteinScale projection) state :=
    ((globalCandidateAMinimalPhysicalReducedCompletedRobinAction_contDiffOn_two
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection).contDiffAt
      ((globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain_isOpen
        period hPeriod configuration data analysis chartData einsteinScale
          projection).mem_nhds hState)).differentiableAt (by norm_num)
  have hMaxwell : DifferentiableAt Real
      (globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction
        period hPeriod configuration data analysis
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData)
          maxwellPlus maxwellMinus) state :=
    ((globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction_contDiff_two
      period hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData)
        maxwellPlus maxwellMinus).differentiable
          (by norm_num)).differentiableAt
  unfold globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
  change fderiv Real
      ((globalCandidateAMinimalPhysicalReducedCompletedGraphAction period hPeriod
          configuration data analysis +
        globalCandidateAMinimalPhysicalReducedCompletedRobinAction period hPeriod
          configuration data analysis chartData einsteinScale projection) +
        globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction
          period hPeriod configuration data analysis
            (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
              configuration data analysis chartData)
            (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
              configuration data analysis chartData)
            maxwellPlus maxwellMinus) state = _
  rw [fderiv_add (hGraph.add hRobin) hMaxwell, fderiv_add hGraph hRobin]

def GlobalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticIsCritical
    (state : Reduced period hPeriod configuration data analysis) : Prop :=
  globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticRieszResidual
    period hPeriod configuration data analysis chartData einsteinScale projection
      maxwellPlus maxwellMinus state = 0

theorem globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticIsCritical_iff_fderiv_eq_zero
    (state : Reduced period hPeriod configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticIsCritical
        period hPeriod configuration data analysis chartData einsteinScale
          projection maxwellPlus maxwellMinus state ↔
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
            period hPeriod configuration data analysis chartData einsteinScale
              projection maxwellPlus maxwellMinus) state = 0 := by
  unfold GlobalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticIsCritical
    globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticRieszResidual
    globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEulerCovector
  exact (InnerProductSpace.toDual Real
    (Reduced period hPeriod configuration data analysis)).symm.map_eq_zero_iff

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection maxwellPlus maxwellMinus
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalCandidateAMinimalPhysicalReducedCompletedGraphAction period hPeriod
          configuration data analysis
          (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis
            (Submodule.Quotient.mk core)) +
        (globalCandidateACanonicalSixLocalBlocks period hPeriod
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)).robin
          (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
            configuration data analysis chartData
            (Submodule.Quotient.mk core)) +
        ((1 / 2 : Real) *
            diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
              configuration data analysis
              (globalCandidateAMinimalPhysicalLocalVariationalChart period
                hPeriod configuration data analysis chartData)
              (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
                hPeriod configuration data analysis chartData) core core +
          (1 / 2 : Real) *
            diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
              configuration data analysis
              (globalCandidateAMinimalPhysicalLocalVariationalChart period
                hPeriod configuration data analysis chartData)
              (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
                hPeriod configuration data analysis chartData) core core) := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction,
    globalCandidateAMinimalPhysicalReducedCompletedRobinAction_core,
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction_core]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEuler4D
end JanusFormal
