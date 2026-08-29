import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianConstructiveAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveParametrix4D

/-!
# H14 closure from a coercive finite-defect shift

This is the terminal adapter in which H12 no longer accepts a generalized
inverse.  The only new H12 data are a finite defect projection, coercivity on
its complement, surjectivity of `H + P`, and the already selected LL
stationarity.  The bounded parametrix and both finite defects are constructed
canonically before invoking the existing H14 assembly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCoerciveAnalyticClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveParametrix4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPGlobalHessianConstructiveAnalyticClosure4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Preferred H14 gate with no supplied H12 inverse or defects. -/
def global_candidateA_hessian_coercive_analytic_closure_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family :
      ProgramPGlobalMinimalPhysicalLocalActionFamilyPhysicalC2Data4D
        period hPeriod (measure := measure) configuration data analysis
          (diracGreenClosureMatterRealization period hPeriod
            couplings.matterMassSquared))
    (bounds : GlobalCandidateASevenPhysicalBlockCoreBounds4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAHessianConstructiveChart period hPeriod
          (measure := measure) configuration data analysis family)
        (globalCandidateAHessianConstructiveSameAction period hPeriod
          (measure := measure) configuration data analysis family))
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAHessianConstructiveChart period hPeriod
          (measure := measure) configuration data analysis family)
        (globalCandidateAHessianConstructiveSameAction period hPeriod
          (measure := measure) configuration data analysis family)
        (globalCandidateAHessianConstructivePhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family bounds))
    (hShiftSurjective : Function.Surjective
      (@finiteDefectShiftedOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          (measure := measure) configuration data analysis
            (globalCandidateAHessianConstructiveChart period hPeriod
              (measure := measure) configuration data analysis family)
            (globalCandidateAHessianConstructiveSameAction period hPeriod
              (measure := measure) configuration data analysis family)
            (globalCandidateAHessianConstructivePhysicalExtension period hPeriod
              (measure := measure) configuration data analysis family bounds)) shift))
    (hLLStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :=
  global_candidateA_hessian_constructive_analytic_closure_gate period hPeriod
    (measure := measure) configuration data analysis einsteinScale
      hBoundaryTransverse family bounds
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_coerciveShift
        period hPeriod (measure := measure) configuration data analysis
          (globalCandidateAHessianConstructiveChart period hPeriod
            (measure := measure) configuration data analysis family)
          (globalCandidateAHessianConstructiveSameAction period hPeriod
            (measure := measure) configuration data analysis family)
          (globalCandidateAHessianConstructivePhysicalExtension period hPeriod
            (measure := measure) configuration data analysis family bounds)
          shift hShiftSurjective hLLStationary)

/-- Public marker for the reduced H12/H14 interface. -/
theorem global_candidateA_hessian_coercive_analytic_frontier_gate :
    Nonempty Unit := ⟨()⟩

end
end P0EFTJanusProgramPGlobalHessianCoerciveAnalyticClosure4D
end JanusFormal
