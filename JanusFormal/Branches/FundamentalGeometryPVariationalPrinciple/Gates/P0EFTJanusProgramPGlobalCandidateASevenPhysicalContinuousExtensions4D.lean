import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D

/-!
# H11 block bounds from continuous extensions

Sometimes the natural proof of an H11 estimate is not a direct inequality on
the smooth core: a physical block is first extended as a continuous bilinear
form on the common Hilbert completion.  In that situation the product bound is
a formal consequence of the two operator-norm inequalities.

This module converts seven continuous block extensions, together with exact
agreement on the dense core, into the blockwise bounds expected by the H11
assembler.  No arbitrary aggregate form is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtensions4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open Filter Set Topology MeasureTheory
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
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

private abbrev PhysicalCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev PhysicalHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

/-- Seven continuous bilinear extensions and their exact restrictions to the
smooth core. -/
structure GlobalCandidateASevenPhysicalContinuousBlockExtensions4D
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
      period hPeriod configuration data analysis chart) : Type where
  coreForm : GlobalCandidateAPhysicalBlock →
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalCore period hPeriod analysis →ₗ[Real] Real
  reconstruct : ∀ first second : PhysicalCore period hPeriod analysis,
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
        data analysis chart sameAction first second =
      ∑ block : GlobalCandidateAPhysicalBlock,
        coreForm block first second
  extension : GlobalCandidateAPhysicalBlock →
    PhysicalHilbert period hPeriod configuration data analysis →L[Real]
      PhysicalHilbert period hPeriod configuration data analysis →L[Real] Real
  extension_agrees : ∀ block first second,
    extension block
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
          configuration data analysis first)
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
          configuration data analysis second) =
      coreForm block first second

/-- The operator norm of a continuous bilinear extension controls its
restriction to the smooth core. -/
theorem continuousBilinearExtension_core_bound
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (form : PhysicalHilbert period hPeriod configuration data analysis →L[Real]
      PhysicalHilbert period hPeriod configuration data analysis →L[Real] Real)
    (first second : PhysicalCore period hPeriod analysis) :
    ‖form
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first)
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second)‖ ≤
      ‖form‖ *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first‖ *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second‖ := by
  let firstH := globalCandidateASevenPhysicalCoreEmbedding period hPeriod
    configuration data analysis first
  let secondH := globalCandidateASevenPhysicalCoreEmbedding period hPeriod
    configuration data analysis second
  calc
    ‖form firstH secondH‖ ≤ ‖form firstH‖ * ‖secondH‖ :=
      ContinuousLinearMap.le_opNorm (form firstH) secondH
    _ ≤ (‖form‖ * ‖firstH‖) * ‖secondH‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm form firstH) (norm_nonneg secondH)
    _ = ‖form‖ * ‖firstH‖ * ‖secondH‖ := rfl

/-- Convert continuous block extensions into the seven core estimates. -/
def globalCandidateASevenPhysicalBlockCoreBounds_of_continuousExtensions
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
    (extensions : GlobalCandidateASevenPhysicalContinuousBlockExtensions4D
      period hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalBlockCoreBounds4D period hPeriod configuration
      data analysis chart sameAction where
  form := extensions.coreForm
  reconstruct := extensions.reconstruct
  constant := fun block => ‖extensions.extension block‖
  constant_nonneg := by
    intro block
    positivity
  estimate := by
    intro block first second
    rw [← extensions.extension_agrees block first second]
    exact continuousBilinearExtension_core_bound period hPeriod configuration
      data analysis (extensions.extension block) first second

/-- H11 directly from seven continuous physical extensions. -/
def global_candidateA_h11_common_augmented_domain_gate_of_continuousExtensions
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
    (extensions : GlobalCandidateASevenPhysicalContinuousBlockExtensions4D
      period hPeriod configuration data analysis chart sameAction) :=
  global_candidateA_h11_common_augmented_domain_gate_of_blockBounds period
    hPeriod configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalBlockCoreBounds_of_continuousExtensions
        period hPeriod configuration data analysis chart sameAction extensions)

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtensions4D
end JanusFormal
