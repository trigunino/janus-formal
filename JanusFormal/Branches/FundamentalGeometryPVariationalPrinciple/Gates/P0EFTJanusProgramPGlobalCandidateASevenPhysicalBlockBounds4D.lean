import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCoreEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D

/-!
# The seven physical Hessian bounds, block by block

H11 needs one product estimate for the sum of the seven physical Hessian
blocks. Analytically, however, each block is controlled by its own standard
estimate. This file packages those seven estimates separately and proves the
single common bound by the triangle inequality and a finite sum.

The reconstruction equality ties the seven supplied forms to the actual
Candidate-A physical Hessian on the existing diagonal core. Hence this is not
an arbitrary bounded perturbation and no eighth block can enter unnoticed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D

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
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The seven retained physical summands, with no matter or LL duplicate. -/
inductive GlobalCandidateAPhysicalBlock
  | candidateA
  | robin
  | einsteinHilbertPlus
  | einsteinHilbertMinus
  | maxwellPlus
  | maxwellMinus
  | finiteBV
  deriving DecidableEq, Fintype

/-- Seven exact core forms, one estimate per physical action block, and an
identity reconstructing their sum as the true physical Hessian. -/
structure GlobalCandidateASevenPhysicalBlockCoreBounds4D
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
  form : GlobalCandidateAPhysicalBlock →
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalCore period hPeriod analysis →ₗ[Real] Real
  reconstruct : ∀ first second : PhysicalCore period hPeriod analysis,
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
        data analysis chart sameAction first second =
      ∑ block : GlobalCandidateAPhysicalBlock, form block first second
  constant : GlobalCandidateAPhysicalBlock → Real
  constant_nonneg : ∀ block, 0 ≤ constant block
  estimate : ∀ (block : GlobalCandidateAPhysicalBlock)
      (first second : PhysicalCore period hPeriod analysis),
    ‖form block first second‖ ≤
      constant block *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first‖ *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second‖

/-- Sum the seven blockwise estimates into the sole H11 product bound. -/
def globalCandidateASevenPhysicalCoreBound_of_blockBounds
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
    (bounds : GlobalCandidateASevenPhysicalBlockCoreBounds4D period hPeriod
      configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCoreBound4D period hPeriod configuration data
      analysis chart sameAction where
  constant := ∑ block : GlobalCandidateAPhysicalBlock, bounds.constant block
  constant_nonneg :=
    Finset.sum_nonneg fun block _ => bounds.constant_nonneg block
  estimate := by
    intro first second
    rw [bounds.reconstruct first second]
    change
      ‖∑ block : GlobalCandidateAPhysicalBlock,
          bounds.form block first second‖ ≤
        (∑ block : GlobalCandidateAPhysicalBlock, bounds.constant block) *
          ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis first‖ *
          ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis second‖
    calc
      ‖∑ block : GlobalCandidateAPhysicalBlock,
          bounds.form block first second‖
          ≤ ∑ block : GlobalCandidateAPhysicalBlock,
              ‖bounds.form block first second‖ :=
        norm_sum_le Finset.univ
          (fun block : GlobalCandidateAPhysicalBlock =>
            bounds.form block first second)
      _ ≤ ∑ block : GlobalCandidateAPhysicalBlock,
          bounds.constant block *
            ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
              configuration data analysis first‖ *
            ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
              configuration data analysis second‖ := by
        exact Finset.sum_le_sum fun block _ =>
          bounds.estimate block first second
      _ = (∑ block : GlobalCandidateAPhysicalBlock, bounds.constant block) *
          ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis first‖ *
          ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis second‖ := by
        simp only [Finset.sum_mul]

/-- H11 from seven named block estimates rather than one opaque aggregate
estimate. -/
theorem global_candidateA_h11_common_augmented_domain_gate_of_blockBounds
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
    (bounds : GlobalCandidateASevenPhysicalBlockCoreBounds4D period hPeriod
      configuration data analysis chart sameAction) :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis chart sameAction
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis chart sameAction
            (globalCandidateASevenPhysicalCoreBound_of_blockBounds period hPeriod
              configuration data analysis chart sameAction bounds)) :=
  global_candidateA_h11_common_augmented_domain_gate_of_bound period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCoreBound_of_blockBounds period hPeriod
        configuration data analysis chart sameAction bounds)

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
end JanusFormal
