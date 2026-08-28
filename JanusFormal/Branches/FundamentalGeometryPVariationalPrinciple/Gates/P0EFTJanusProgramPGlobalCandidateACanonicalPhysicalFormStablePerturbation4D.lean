import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRieszBilinearNorm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNamedModeKernelStablePerturbationBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D

/-!
# Candidate-A stable perturbation controlled by the H11 form norm

The canonical physical perturbation is the Riesz representative of the seven
physical H11 blocks.  Its operator norm is therefore bounded by the norm of the
underlying continuous bilinear form.  The perturbative hypothesis can be
stated directly as

`‖physical.form‖ < referenceConstant`,

which is the natural output of the H11 estimates.  No separate operator-norm
calculation for the Riesz representative remains.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalFormStablePerturbation4D

set_option autoImplicit false
set_option maxHeartbeats 11200000
set_option synthInstance.maxHeartbeats 5600000

noncomputable section

universe u

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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPNamedModeKernelStablePerturbationBound4D
open P0EFTJanusProgramPRieszBilinearNorm4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

private abbrev PhysicalFormHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) physicalFormNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (PhysicalFormHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalFormInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (PhysicalFormHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalFormNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (PhysicalFormHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalFormModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (PhysicalFormHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalFormCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (PhysicalFormHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The canonical physical Riesz representative is controlled by the H11 form
norm. -/
theorem globalCandidateACanonicalStablePhysicalPerturbation_opNorm_le_form
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
      hPeriod configuration data analysis chart sameAction) :
    ‖globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
        configuration data analysis chart sameAction physical‖ ≤
      ‖physical.form‖ := by
  unfold globalCandidateACanonicalStablePhysicalPerturbation
    globalCandidateASevenPhysicalCommonRieszOperator
  exact continuousLinearMapOfBilin_opNorm_le physical.form

/-- Stable named modes with smallness measured directly by the H11 bilinear
form. -/
structure GlobalCandidateACanonicalPhysicalFormStablePerturbation4D
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
    (ZeroMode : Type u) [Fintype ZeroMode] [DecidableEq ZeroMode] : Type u where
  vector : ZeroMode → PhysicalFormHilbert period hPeriod configuration data
    analysis
  reference_annihilated : ∀ mode,
    globalCandidateACanonicalStableReferenceOperator period hPeriod
      configuration data analysis (vector mode) = 0
  physical_annihilated : ∀ mode,
    globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
      configuration data analysis chart sameAction physical (vector mode) = 0
  nonzero : ∀ mode, vector mode ≠ 0
  orthogonal : Pairwise fun first second =>
    ⟪vector first, vector second⟫_Real = 0
  referenceConstant : Real
  physical_form_small : ‖physical.form‖ < referenceConstant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  reference_garding : ∀ current,
    referenceConstant * ‖current‖ ^ 2 ≤
      ⟪current,
        globalCandidateACanonicalStableReferenceOperator period hPeriod
          configuration data analysis current⟫_Real +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪current, vector mode⟫_Real ^ 2
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Build the canonical stable perturbation packet; Riesz norm control supplies
the only missing majorant proof. -/
def GlobalCandidateACanonicalPhysicalFormStablePerturbation4D.toCanonicalStable
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
    {ZeroMode : Type u} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (input : GlobalCandidateACanonicalPhysicalFormStablePerturbation4D period
      hPeriod configuration data analysis chart sameAction physical ZeroMode) :
    GlobalCandidateACanonicalStableNamedPerturbation4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode where
  stable :=
    (show FiniteKernelStableOrthogonalNamedModePerturbationBoundData
      (globalCandidateACanonicalStableReferenceOperator period hPeriod
        configuration data analysis)
      (globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
        configuration data analysis chart sameAction physical)
      ZeroMode from
      { vector := input.vector
        reference_annihilated := input.reference_annihilated
        perturbation_annihilated := input.physical_annihilated
        nonzero := input.nonzero
        orthogonal := input.orthogonal
        referenceConstant := input.referenceConstant
        perturbationBound := ‖physical.form‖
        perturbationBound_nonneg := norm_nonneg physical.form
        perturbation_norm_le :=
          globalCandidateACanonicalStablePhysicalPerturbation_opNorm_le_form
            period hPeriod configuration data analysis chart sameAction physical
        perturbationBound_lt_reference := input.physical_form_small
        defectConstant := input.defectConstant
        defectConstant_nonneg := input.defectConstant_nonneg
        reference_garding := input.reference_garding }).toStable
  ll_stationary := input.ll_stationary

/-- Public form-norm perturbation checkpoint. -/
def global_candidateA_canonical_physical_form_stable_perturbation_gate
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
    {ZeroMode : Type u} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (input : GlobalCandidateACanonicalPhysicalFormStablePerturbation4D period
      hPeriod configuration data analysis chart sameAction physical ZeroMode) :
    GlobalCandidateACanonicalStableNamedPerturbation4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode :=
  input.toCanonicalStable period hPeriod

end
end P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalFormStablePerturbation4D
end JanusFormal
