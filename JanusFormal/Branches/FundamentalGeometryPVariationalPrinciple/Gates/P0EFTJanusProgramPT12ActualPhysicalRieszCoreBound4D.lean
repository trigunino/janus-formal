import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalFormStablePerturbation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalExtensionNorm4D

/-!
# Quantitative physical Riesz bound on the actual Candidate-A Hilbert space

The H11 dense-core constant bounds the seven-physical Riesz perturbation and
each of its Hilbert pairings. This estimate can be applied to sector-projected
vectors without specializing the projectors here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12ActualPhysicalRieszCoreBound4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalFormStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalExtensionNorm4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

private abbrev Hilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

/-- The H11 core constant bounds the seven-physical Riesz operator on the
actual Candidate-A L2 Hilbert space. -/
theorem physicalRiesz_opNorm_le_coreConstant
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction) :
    ‖globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
      configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
        configuration data analysis chart sameAction bound)‖ ≤
      bound.constant := by
  exact le_trans
    (globalCandidateACanonicalStablePhysicalPerturbation_opNorm_le_form period
      hPeriod configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
        configuration data analysis chart sameAction bound))
    (globalCandidateASevenPhysicalExtension_form_opNorm_le period hPeriod
      configuration data analysis chart sameAction bound)

/-- Every physical Riesz pairing inherits the explicit H11 core constant. -/
theorem physicalRiesz_pairing_bound
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction)
    (first second : Hilbert period hPeriod configuration data analysis) :
    ‖inner Real
      (globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
        configuration data analysis chart sameAction
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis chart sameAction bound) first)
      second‖ ≤
      bound.constant * ‖first‖ * ‖second‖ := by
  let physical := globalCandidateASevenPhysicalCommonDomainExtension_of_bound
    period hPeriod configuration data analysis chart sameAction bound
  let riesz := globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
    configuration data analysis chart sameAction physical
  change ‖inner Real (riesz first) second‖ ≤
    bound.constant * ‖first‖ * ‖second‖
  calc
    ‖inner Real (riesz first) second‖ ≤
        ‖riesz first‖ * ‖second‖ := norm_inner_le_norm _ _
    _ ≤ (‖riesz‖ * ‖first‖) * ‖second‖ :=
      mul_le_mul_of_nonneg_right (riesz.le_opNorm first) (norm_nonneg second)
    _ ≤ (bound.constant * ‖first‖) * ‖second‖ := by
      gcongr
      exact physicalRiesz_opNorm_le_coreConstant period hPeriod
        configuration data analysis chart sameAction bound
    _ = bound.constant * ‖first‖ * ‖second‖ := rfl

end
end P0EFTJanusProgramPT12ActualPhysicalRieszCoreBound4D
end JanusFormal
