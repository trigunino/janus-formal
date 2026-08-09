import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAOrthogonalCoordinateFiniteMarginActualKernelGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASelfAdjointProjectionFiniteMarginH12Closure4D

/-!
# Candidate-A H12 closure from one orthogonal sector decomposition

The orthogonal coordinate equivalence generates the five natural projectors and
then reuses the established natural-projection Fredholm, Green, resolvent and
stability chain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAOrthogonalCoordinateFiniteMarginH12Closure4D

set_option autoImplicit false
set_option maxHeartbeats 8600000
set_option synthInstance.maxHeartbeats 4300000

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
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAOrthogonalCoordinateFiniteMarginActualKernelGap4D
open P0EFTJanusProgramPGlobalCandidateASelfAdjointProjectionFiniteMarginH12Closure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

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

/-- H12 and the complete reduced spectral package generated from one
orthogonal sector coordinate equivalence. -/
def global_candidateA_orthogonal_coordinate_h12_closure_gate
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (Component : CandidateAZeroModeSector → Type*)
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, NormedSpace Real (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (orthogonal :
      GlobalCandidateAOrthogonalCoordinateFiniteMarginActualKernelGap4D period
        hPeriod configuration data analysis chart sameAction physical Component) :=
  global_candidateA_selfAdjoint_projection_h12_closure_gate period hPeriod
    configuration data analysis chart sameAction physical
      (orthogonal.toSelfAdjointProjection period hPeriod)

/-- Quantitative stability from the same orthogonal coordinates. -/
def global_candidateA_orthogonal_coordinate_h12_stability_gate
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (Component : CandidateAZeroModeSector → Type*)
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, NormedSpace Real (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (orthogonal :
      GlobalCandidateAOrthogonalCoordinateFiniteMarginActualKernelGap4D period
        hPeriod configuration data analysis chart sameAction physical Component)
    (perturbation : GlobalCandidateAActualKernelPerturbation4D period hPeriod
      configuration data analysis chart sameAction physical
        (orthogonal.toActualKernelGap period hPeriod)) :=
  global_candidateA_actual_kernel_stability_gate period hPeriod configuration
    data analysis chart sameAction physical
      (orthogonal.toActualKernelGap period hPeriod) perturbation

end
end P0EFTJanusProgramPGlobalCandidateAOrthogonalCoordinateFiniteMarginH12Closure4D
end JanusFormal
