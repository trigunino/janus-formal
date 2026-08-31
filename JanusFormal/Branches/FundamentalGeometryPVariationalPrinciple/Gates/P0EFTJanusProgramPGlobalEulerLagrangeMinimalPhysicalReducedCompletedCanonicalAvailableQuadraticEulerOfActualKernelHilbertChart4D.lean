import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerOfHilbertChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D

/-!
# Canonical available Euler operator on the actual-kernel Hilbert chart

For the H10-reduced family, the common Hilbert chart supplies both the seven
canonical H11 extensions and the sole core-to-chart estimate needed to extend
the genuine local Robin projection.  Thus the strongest available quadratic
Euler operator no longer takes an independent Robin projection packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerOfActualKernelHilbertChart4D

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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfBounds4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10ContinuousClosure4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerOfHilbertChart4D

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

variable
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

include family in
/-- Admissibility of the H10 family at zero already forces the background
throat metric to have no tangential radical. -/
theorem globalCandidateAH10ReducedFamily_hasNoTangentialRadical :
    HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric := by
  letI := family.normedAddCommGroup
  letI := family.normedSpace
  have hZero :
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real) ∈
        candidateANormalBoundaryGHYDomain period hPeriod
          data.plusGravity.metric := by
    simpa using
      (family.boundaryProjection_mem
        (0 : ReducedFamilyModel period hPeriod configuration)
        family.zero_mem_domain)
  have hGraph :
      NormalGraphNonNullAt period hPeriod data.plusGravity.metric.metric
        (0 : SmoothNormalDisplacement period hPeriod) 0 := by
    refine normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod
      data.plusGravity.metric
      (0 : SmoothSymmetricCovariantTwoTensor period hPeriod)
      data.plusGravity.metric.metric ?_ 0 0 ?_
    · simp
    · change
        ((smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric)
          (0 : SmoothSymmetricCovariantTwoTensor period hPeriod ×
            SmoothNormalDisplacement period hPeriod), 0) ∈
          candidateANormalBoundaryGHYDomain period hPeriod
            data.plusGravity.metric
      rw [map_zero]
      exact hZero
  apply
    (throatTrace_nondegenerate_iff_no_tangential_radical period hPeriod
      data.plusGravity.metric.metric).1
  intro point
  change Function.Injective
    (generalLorentzMetricThroatTraceValue period hPeriod
      data.plusGravity.metric.metric point)
  simpa only [normalGraphInducedMetricValue_zero] using hGraph point

private abbrev ActualChart :=
  globalCandidateAActualKernelChart period hPeriod configuration data analysis
    einsteinScale hTransverse family

private abbrev ActualSameAction :=
  globalCandidateAActualKernelSameAction period hPeriod configuration data
    analysis einsteinScale hTransverse family

private abbrev ActualChartData :=
  diracGreenClosureChartData period hPeriod configuration data analysis
    (globalCandidateAH10ContinuousReducedFamily period hPeriod configuration
      data analysis einsteinScale hTransverse family)

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

variable
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis
      (ActualChart period hPeriod configuration data analysis einsteinScale
        hTransverse family)
      (ActualSameAction period hPeriod configuration data analysis einsteinScale
        hTransverse family))

/-- The common Hilbert chart supplies the chart estimate in the exact form
consumed by the H10 Robin extension constructor. -/
def globalCandidateAActualKernelCanonicalCoreToChartBound_of_hilbertChart :
    DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (ActualChart period hPeriod configuration data analysis einsteinScale
          hTransverse family)
        (ActualSameAction period hPeriod configuration data analysis
          einsteinScale hTransverse family)) :=
  globalCandidateASevenPhysicalCanonicalCoreToChartBound_of_hilbertChart
    period hPeriod configuration data analysis
      (ActualChart period hPeriod configuration data analysis einsteinScale
        hTransverse family)
      (ActualSameAction period hPeriod configuration data analysis einsteinScale
        hTransverse family)
      hilbertChart

/-- The genuine H10 Robin projection packet is derived from that same chart. -/
def globalCandidateAActualKernelH10ProjectionCoreData_of_hilbertChart :
    GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod configuration
      data analysis
      (ActualChart period hPeriod configuration data analysis einsteinScale
        hTransverse family)
      (ActualSameAction period hPeriod configuration data analysis einsteinScale
        hTransverse family)
      einsteinScale :=
  globalCandidateAH10ProjectionCoreData_of_chartBound period hPeriod
    configuration data analysis einsteinScale hTransverse family
      (globalCandidateAActualKernelCanonicalCoreToChartBound_of_hilbertChart
        period hPeriod configuration data analysis einsteinScale hTransverse
          family hilbertChart)

/-- Strongest available reduced quadratic action on the actual-kernel chart. -/
def globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_hilbertChart :
    Reduced period hPeriod configuration data analysis → Real :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart
    period hPeriod configuration data analysis
      (ActualChartData period hPeriod configuration data analysis einsteinScale
        hTransverse family)
      einsteinScale
      (globalCandidateAActualKernelH10ProjectionCoreData_of_hilbertChart period
        hPeriod configuration data analysis einsteinScale hTransverse family
          hilbertChart)
      hilbertChart

theorem globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_hilbertChart_contDiffOn_two :
    ContDiffOn Real 2
      (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_hilbertChart
        period hPeriod configuration data analysis einsteinScale hTransverse
          family hilbertChart)
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis
          (ActualChartData period hPeriod configuration data analysis
            einsteinScale hTransverse family)
          einsteinScale
          (globalCandidateAActualKernelH10ProjectionCoreData_of_hilbertChart
            period hPeriod configuration data analysis einsteinScale hTransverse
              family hilbertChart)) := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart_contDiffOn_two
      period hPeriod configuration data analysis
        (ActualChartData period hPeriod configuration data analysis einsteinScale
          hTransverse family)
        einsteinScale hTransverse
        (globalCandidateAActualKernelH10ProjectionCoreData_of_hilbertChart period
          hPeriod configuration data analysis einsteinScale hTransverse family
            hilbertChart)
        hilbertChart

/-- Frechet Euler covector with both H11 and Robin extensions derived. -/
noncomputable def globalCandidateAActualKernelCanonicalAvailableQuadraticEulerCovector_of_hilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis →L[Real] Real :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector_of_hilbertChart
    period hPeriod configuration data analysis
      (ActualChartData period hPeriod configuration data analysis einsteinScale
        hTransverse family)
      einsteinScale
      (globalCandidateAActualKernelH10ProjectionCoreData_of_hilbertChart period
        hPeriod configuration data analysis einsteinScale hTransverse family
          hilbertChart)
      hilbertChart state

/-- Strong Riesz residual with both H11 and Robin extensions derived. -/
noncomputable def globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_hilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_of_hilbertChart
    period hPeriod configuration data analysis
      (ActualChartData period hPeriod configuration data analysis einsteinScale
        hTransverse family)
      einsteinScale
      (globalCandidateAActualKernelH10ProjectionCoreData_of_hilbertChart period
        hPeriod configuration data analysis einsteinScale hTransverse family
          hilbertChart)
      hilbertChart state

/-- Gate 198: one actual-kernel Hilbert chart determines the separated H11
packet, the completed Robin projection, and the strong quadratic Euler pairing. -/
theorem candidate_a_actualKernel_canonical_available_quadratic_euler_of_hilbertChart_gate
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_hilbertChart
          period hPeriod configuration data analysis einsteinScale hTransverse
            family hilbertChart state) test =
      fderiv Real
        (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_hilbertChart
          period hPeriod configuration data analysis einsteinScale hTransverse
            family hilbertChart) state test := by
  exact
    candidate_a_canonical_available_quadratic_euler_of_hilbertChart_gate
      period hPeriod configuration data analysis
        (ActualChartData period hPeriod configuration data analysis einsteinScale
          hTransverse family)
        einsteinScale
        (globalCandidateAActualKernelH10ProjectionCoreData_of_hilbertChart period
          hPeriod configuration data analysis einsteinScale hTransverse family
            hilbertChart)
        hilbertChart state test

private abbrev FamilyTransverse :=
  globalCandidateAH10ReducedFamily_hasNoTangentialRadical period hPeriod
    configuration data analysis einsteinScale family

private abbrev FamilyActualChart :=
  ActualChart period hPeriod configuration data analysis einsteinScale
    (FamilyTransverse period hPeriod configuration data analysis einsteinScale
      family) family

private abbrev FamilyActualSameAction :=
  ActualSameAction period hPeriod configuration data analysis einsteinScale
    (FamilyTransverse period hPeriod configuration data analysis einsteinScale
      family) family

private abbrev FamilyActualChartData :=
  ActualChartData period hPeriod configuration data analysis einsteinScale
    (FamilyTransverse period hPeriod configuration data analysis einsteinScale
      family) family

variable
    (familyHilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D
      period hPeriod configuration data analysis
      (FamilyActualChart period hPeriod configuration data analysis
        einsteinScale family)
      (FamilyActualSameAction period hPeriod configuration data analysis
        einsteinScale family))

/-- Strongest Robin packet: the H10 family supplies transversality and the
Hilbert chart supplies its completed projection. -/
def globalCandidateAActualKernelH10ProjectionCoreData_of_familyHilbertChart :
    GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod configuration
      data analysis
      (FamilyActualChart period hPeriod configuration data analysis
        einsteinScale family)
      (FamilyActualSameAction period hPeriod configuration data analysis
        einsteinScale family)
      einsteinScale :=
  globalCandidateAActualKernelH10ProjectionCoreData_of_hilbertChart period
    hPeriod configuration data analysis einsteinScale
      (FamilyTransverse period hPeriod configuration data analysis einsteinScale
        family)
      family familyHilbertChart

/-- Available action from the H10 family and its actual-kernel Hilbert chart;
no independent transversality or Robin-projection input remains. -/
def globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_familyHilbertChart :
    Reduced period hPeriod configuration data analysis → Real :=
  globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_hilbertChart
    period hPeriod configuration data analysis einsteinScale
      (FamilyTransverse period hPeriod configuration data analysis einsteinScale
        family)
      family familyHilbertChart

theorem globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_familyHilbertChart_contDiffOn_two :
    ContDiffOn Real 2
      (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_familyHilbertChart
        period hPeriod configuration data analysis einsteinScale family
          familyHilbertChart)
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis
          (FamilyActualChartData period hPeriod configuration data analysis
            einsteinScale family)
          einsteinScale
          (globalCandidateAActualKernelH10ProjectionCoreData_of_familyHilbertChart
            period hPeriod configuration data analysis einsteinScale family
              familyHilbertChart)) := by
  exact
    globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_hilbertChart_contDiffOn_two
      period hPeriod configuration data analysis einsteinScale
        (FamilyTransverse period hPeriod configuration data analysis
          einsteinScale family)
        family familyHilbertChart

noncomputable def globalCandidateAActualKernelCanonicalAvailableQuadraticEulerCovector_of_familyHilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis →L[Real] Real :=
  globalCandidateAActualKernelCanonicalAvailableQuadraticEulerCovector_of_hilbertChart
    period hPeriod configuration data analysis einsteinScale
      (FamilyTransverse period hPeriod configuration data analysis einsteinScale
        family)
      family familyHilbertChart state

@[simp]
theorem globalCandidateAActualKernelCanonicalAvailableQuadraticEulerCovector_eq_fderiv_of_familyHilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    globalCandidateAActualKernelCanonicalAvailableQuadraticEulerCovector_of_familyHilbertChart
        period hPeriod configuration data analysis einsteinScale family
          familyHilbertChart state =
      fderiv Real
        (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_familyHilbertChart
          period hPeriod configuration data analysis einsteinScale family
            familyHilbertChart) state :=
  rfl

noncomputable def globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_familyHilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_hilbertChart
    period hPeriod configuration data analysis einsteinScale
      (FamilyTransverse period hPeriod configuration data analysis einsteinScale
        family)
      family familyHilbertChart state

/-- Strong criticality for the fully derived actual-kernel endpoint. -/
def GlobalCandidateAActualKernelCanonicalAvailableQuadraticIsCritical_of_familyHilbertChart
    (state : Reduced period hPeriod configuration data analysis) : Prop :=
  globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_familyHilbertChart
    period hPeriod configuration data analysis einsteinScale family
      familyHilbertChart state = 0

theorem globalCandidateAActualKernelCanonicalAvailableQuadraticIsCritical_iff_fderiv_eq_zero_of_familyHilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    GlobalCandidateAActualKernelCanonicalAvailableQuadraticIsCritical_of_familyHilbertChart
        period hPeriod configuration data analysis einsteinScale family
          familyHilbertChart state ↔
      fderiv Real
        (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_familyHilbertChart
          period hPeriod configuration data analysis einsteinScale family
            familyHilbertChart) state = 0 := by
  change
    GlobalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical_of_hilbertChart
        period hPeriod configuration data analysis
          (FamilyActualChartData period hPeriod configuration data analysis
            einsteinScale family)
          einsteinScale
          (globalCandidateAActualKernelH10ProjectionCoreData_of_familyHilbertChart
            period hPeriod configuration data analysis einsteinScale family
              familyHilbertChart)
          familyHilbertChart state ↔ _
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical_iff_fderiv_eq_zero_of_hilbertChart
      period hPeriod configuration data analysis
        (FamilyActualChartData period hPeriod configuration data analysis
          einsteinScale family)
        einsteinScale
        (globalCandidateAActualKernelH10ProjectionCoreData_of_familyHilbertChart
          period hPeriod configuration data analysis einsteinScale family
            familyHilbertChart)
        familyHilbertChart state

/-- Strongest Gate 198 form: the H10 family and one actual-kernel Hilbert chart
determine the available action and its exact strong Euler pairing. -/
theorem candidate_a_actualKernel_canonical_available_quadratic_euler_of_familyHilbertChart_gate
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_familyHilbertChart
          period hPeriod configuration data analysis einsteinScale family
            familyHilbertChart state) test =
      fderiv Real
        (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_familyHilbertChart
          period hPeriod configuration data analysis einsteinScale family
            familyHilbertChart) state test := by
  exact
    candidate_a_actualKernel_canonical_available_quadratic_euler_of_hilbertChart_gate
      period hPeriod configuration data analysis einsteinScale
        (FamilyTransverse period hPeriod configuration data analysis
          einsteinScale family)
        family familyHilbertChart state test

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerOfActualKernelHilbertChart4D
end JanusFormal
