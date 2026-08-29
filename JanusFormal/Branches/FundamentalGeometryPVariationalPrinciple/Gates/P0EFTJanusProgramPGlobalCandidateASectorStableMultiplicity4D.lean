import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateASectorModeMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D

/-!
# Explicit five-term kernel count for stable Candidate-A sectors

The sector-stable Noether/Gårding packet already identifies the actual Hessian
kernel with the assembled mode family.  Combining it with the classification
fiber equivalence turns the abstract sector multiplicities into the five
concrete finite cardinalities supplied by the physical sectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASectorStableMultiplicity4D

set_option autoImplicit false
set_option maxHeartbeats 7800000
set_option synthInstance.maxHeartbeats 3900000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D
open P0EFTJanusProgramPCandidateASectorModeMultiplicity4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

noncomputable local instance candidateASectorGlobalModeDecidableEq
    (types : CandidateASectorModeTypes) : DecidableEq types.GlobalMode :=
  Classical.decEq _

local instance candidateASectorModeFintype
    (types : CandidateASectorModeTypes)
    (sector : CandidateAZeroModeSector) : Fintype (types.Mode sector) :=
  types.modeFintype sector

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

/-- Exact kernel count written directly as the sum of the five supplied mode
cardinalities. -/
theorem GlobalCandidateASectorActionTranslationStablePhysicalFormData4D.kernel_finrank_eq_explicit_sector_cards
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {types : CandidateASectorModeTypes}
    (input : GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis chart sameAction physical
        types) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).ker =
      ∑ sector : CandidateAZeroModeSector,
        Fintype.card (types.Mode sector) := by
  rw [input.kernel_finrank_eq_sector_sum period hPeriod]
  apply Finset.sum_congr rfl
  intro sector _
  exact candidateASectorMultiplicity_eq_card types sector

/-- Public concrete five-sector count checkpoint. -/
def global_candidateA_sector_stable_explicit_multiplicity_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {types : CandidateASectorModeTypes}
    (input : GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis chart sameAction physical
        types) :
    PSigma fun _ :
      GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
        chart sameAction physical =>
      Module.finrank Real
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical).ker =
        ∑ sector : CandidateAZeroModeSector,
          Fintype.card (types.Mode sector) :=
  ⟨(input.toStable period hPeriod).toNamedGarding.toGap period hPeriod,
    GlobalCandidateASectorActionTranslationStablePhysicalFormData4D.kernel_finrank_eq_explicit_sector_cards
      period hPeriod input⟩

end
end P0EFTJanusProgramPGlobalCandidateASectorStableMultiplicity4D
end JanusFormal
