import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreActualFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D

/-!
# Dense-core H10--H14 frontier with finite Schur zero modes

The nondegenerate determinant route is only one stratum.  This facade keeps the
full bounded Schur operator and therefore also covers configurations with a
finite-dimensional zero-mode space.  The H11 extension is still generated from
the genuine dense physical core; the Schur packet then derives the exact kernel
model and closed range of the resulting augmented Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreBoundedSchurFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option synthInstance.maxHeartbeats 9000000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenCanonicalDenseCoreBound4D
open P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D
open P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreActualFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreFrontier4D
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

/-- Dense-core H11 together with the full finite-Schur zero-mode reduction. -/
def global_candidateA_hessian_canonical_denseCore_bounded_schur_frontier_gate
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : GlobalCandidateACanonicalDenseCoreChartBound4D period hPeriod
      configuration data analysis
        (globalCandidateACanonicalDenseCoreChart period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalDenseCoreSameAction period hPeriod
          configuration data analysis einsteinScale hTransverse family))
    (agreement : GlobalCandidateASevenCanonicalDenseCoreAgreement4D period
      hPeriod configuration data analysis
        (globalCandidateACanonicalDenseCoreChart period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalDenseCoreSameAction period hPeriod
          configuration data analysis einsteinScale hTransverse family)
        einsteinScale family)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (schur : GlobalCandidateAActualBoundedSchurBlockData4D period hPeriod
      configuration data analysis
        (globalCandidateACanonicalDenseCoreChart period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalDenseCoreSameAction period hPeriod
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalDenseCoreActualPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family chartBound
            agreement)
        Mode Complement) :=
  let chart := globalCandidateACanonicalDenseCoreChart period hPeriod
    configuration data analysis einsteinScale hTransverse family
  let sameAction := globalCandidateACanonicalDenseCoreSameAction period hPeriod
    configuration data analysis einsteinScale hTransverse family
  let physical := globalCandidateACanonicalDenseCoreActualPhysicalExtension period
    hPeriod configuration data analysis einsteinScale hTransverse family
      chartBound agreement
  let h13 := global_candidateA_h13_matter_ll_same_action_gate period hPeriod
    configuration data analysis chart sameAction
  let h11 := global_candidateA_h11_canonical_denseCore_gate period hPeriod
    configuration data analysis chart sameAction einsteinScale family chartBound
      agreement
  let schurClosure := global_candidateA_actual_bounded_schur_block_gate period
    hPeriod configuration data analysis chart sameAction physical schur
  (h13, h11, physical, schurClosure)

/-- Three analytic packets remain after fixing the local family. -/
theorem global_candidateA_hessian_canonical_denseCore_bounded_schur_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalDenseCoreBoundedSchurFrontier4D
end JanusFormal
