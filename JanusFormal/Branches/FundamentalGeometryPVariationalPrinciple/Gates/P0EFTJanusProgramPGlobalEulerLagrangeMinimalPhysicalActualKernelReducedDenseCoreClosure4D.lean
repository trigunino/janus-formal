import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerOfActualKernelHilbertChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertOfDenseCoreClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfReducedHilbertChart4D

/-!
# Actual-kernel nonlinear and quadratic Euler routes from reduced closure

The H10 family supplies tangential transversality.  The honest quotient-core
closure supplies the reduced Hilbert chart, which in turn supplies the seven
canonical H11 extensions and the completed genuine Robin projection.  The
same data therefore determines both the exact nonlinear Euler equation and
the strongest available canonical quadratic model.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalActualKernelReducedDenseCoreClosure4D

set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option synthInstance.maxHeartbeats 2200000

noncomputable section

open Set MeasureTheory
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
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10ContinuousClosure4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerOfActualKernelHilbertChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertOfDenseCoreClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfReducedHilbertChart4D

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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)

private abbrev FamilyTransverse :=
  globalCandidateAH10ReducedFamily_hasNoTangentialRadical period hPeriod
    configuration data analysis einsteinScale family

private abbrev FamilyChartData :=
  diracGreenClosureChartData period hPeriod configuration data analysis
    (globalCandidateAH10ContinuousReducedFamily period hPeriod configuration
      data analysis einsteinScale
        (FamilyTransverse period hPeriod configuration data analysis
          einsteinScale family)
        family)

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

variable
    (closure : ProgramPGlobalMinimalPhysicalReducedDenseCoreHilbertClosureData4D
      period hPeriod configuration data analysis
        (FamilyChartData period hPeriod configuration data analysis
          einsteinScale family))

private abbrev FamilyReducedChart :=
  globalCandidateAMinimalPhysicalReducedHilbertChart_of_denseCoreClosure period
    hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      closure

/-- Honest core-to-chart bound from quotient-core closure. -/
def globalCandidateAActualKernelCanonicalCoreToChartBound_of_reducedDenseCoreClosure :=
  globalCandidateASevenPhysicalCanonicalCoreToChartBound_of_reducedHilbertChart
    period hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      (FamilyReducedChart period hPeriod configuration data analysis
        einsteinScale family closure)

/-- Seven canonical H11 extensions from the same reduced closure. -/
def globalCandidateAActualKernelCanonicalExtensions_of_reducedDenseCoreClosure :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_reducedHilbertChart
    period hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      (FamilyReducedChart period hPeriod configuration data analysis
        einsteinScale family closure)

/-- Genuine completed Robin projection from the H10 family and reduced
core-to-chart bound. -/
def globalCandidateAActualKernelH10ProjectionCoreData_of_reducedDenseCoreClosure :=
  globalCandidateAH10ProjectionCoreData_of_chartBound period hPeriod
    configuration data analysis einsteinScale
      (FamilyTransverse period hPeriod configuration data analysis einsteinScale
        family)
      family
      (globalCandidateAActualKernelCanonicalCoreToChartBound_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure)

/-- Strongest available canonical quadratic action on the actual-kernel
reduced closure. -/
def globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_reducedDenseCoreClosure :
    Reduced period hPeriod configuration data analysis → Real :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction
    period hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      einsteinScale
      (globalCandidateAActualKernelH10ProjectionCoreData_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure)
      (globalCandidateAActualKernelCanonicalExtensions_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure)

theorem globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_reducedDenseCoreClosure_contDiffOn_two :
    ContDiffOn Real 2
      (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure)
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis
          (FamilyChartData period hPeriod configuration data analysis
            einsteinScale family)
          einsteinScale
          (globalCandidateAActualKernelH10ProjectionCoreData_of_reducedDenseCoreClosure
            period hPeriod configuration data analysis einsteinScale family
              closure)) := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_contDiffOn_two
      period hPeriod configuration data analysis
        (FamilyChartData period hPeriod configuration data analysis einsteinScale
          family)
        einsteinScale
        (FamilyTransverse period hPeriod configuration data analysis
          einsteinScale family)
        (globalCandidateAActualKernelH10ProjectionCoreData_of_reducedDenseCoreClosure
          period hPeriod configuration data analysis einsteinScale family
            closure)
        (globalCandidateAActualKernelCanonicalExtensions_of_reducedDenseCoreClosure
          period hPeriod configuration data analysis einsteinScale family
            closure)

noncomputable def globalCandidateAActualKernelCanonicalAvailableQuadraticEulerCovector_of_reducedDenseCoreClosure
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis →L[Real] Real :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector
    period hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      einsteinScale
      (globalCandidateAActualKernelH10ProjectionCoreData_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure)
      (globalCandidateAActualKernelCanonicalExtensions_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure)
      state

@[simp]
theorem globalCandidateAActualKernelCanonicalAvailableQuadraticEulerCovector_eq_fderiv_of_reducedDenseCoreClosure
    (state : Reduced period hPeriod configuration data analysis) :
    globalCandidateAActualKernelCanonicalAvailableQuadraticEulerCovector_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure
          state =
      fderiv Real
        (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_reducedDenseCoreClosure
          period hPeriod configuration data analysis einsteinScale family
            closure)
        state :=
  rfl

noncomputable def globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_reducedDenseCoreClosure
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual
    period hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      einsteinScale
      (globalCandidateAActualKernelH10ProjectionCoreData_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure)
      (globalCandidateAActualKernelCanonicalExtensions_of_reducedDenseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure)
      state

/-- The exact nonlinear action on that same closure-derived reduced chart. -/
def globalCandidateAActualKernelReducedNonlinearAction_of_denseCoreClosure :
    Reduced period hPeriod configuration data analysis → Real :=
  globalCandidateAMinimalPhysicalReducedHilbertAction_of_denseCoreClosure period
    hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      closure

noncomputable def globalCandidateAActualKernelReducedNonlinearRieszResidual_of_denseCoreClosure
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_of_denseCoreClosure
    period hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      closure state

def globalCandidateAActualKernelReducedNonlinearAdmissibleDomain_of_denseCoreClosure :
    Set (Reduced period hPeriod configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedHilbertAdmissibleDomain_of_denseCoreClosure
    period hPeriod configuration data analysis
      (FamilyChartData period hPeriod configuration data analysis einsteinScale
        family)
      closure

/-- Gate 201: one H10 family and its honest reduced dense-core closure determine
both strong Euler pairings, quadratic and exact nonlinear. -/
theorem candidate_a_actualKernel_reduced_denseCoreClosure_euler_gate
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAActualKernelReducedNonlinearAdmissibleDomain_of_denseCoreClosure
        period hPeriod configuration data analysis einsteinScale family closure) :
    (∀ test : Reduced period hPeriod configuration data analysis,
      inner Real
          (globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_reducedDenseCoreClosure
            period hPeriod configuration data analysis einsteinScale family
              closure state)
          test =
        fderiv Real
          (globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_reducedDenseCoreClosure
            period hPeriod configuration data analysis einsteinScale family
              closure)
          state test) ∧
      (∀ test : Reduced period hPeriod configuration data analysis,
        inner Real
            (globalCandidateAActualKernelReducedNonlinearRieszResidual_of_denseCoreClosure
              period hPeriod configuration data analysis einsteinScale family
                closure state)
            test =
          fderiv Real
            (globalCandidateAActualKernelReducedNonlinearAction_of_denseCoreClosure
              period hPeriod configuration data analysis einsteinScale family
                closure)
            state test) := by
  constructor
  · intro test
    unfold
      globalCandidateAActualKernelCanonicalAvailableQuadraticRieszResidual_of_reducedDenseCoreClosure
      globalCandidateAActualKernelCanonicalAvailableQuadraticAction_of_reducedDenseCoreClosure
    rw [globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_pairing]
    rfl
  · intro test
    exact
      globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing_fderiv_of_denseCoreClosure
        period hPeriod configuration data analysis
          (FamilyChartData period hPeriod configuration data analysis
            einsteinScale family)
          closure state hState test

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalActualKernelReducedDenseCoreClosure4D
end JanusFormal
