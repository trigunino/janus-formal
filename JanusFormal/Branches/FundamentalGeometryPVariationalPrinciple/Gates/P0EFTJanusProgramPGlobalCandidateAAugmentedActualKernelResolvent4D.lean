import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementResolvent4D

/-!
# Candidate-A resolvent on the actual kernel complement

This file specializes the canonical real-gap resolvent to the faithful
augmented Candidate-A Hessian.  The reduced space is definitionally the
orthogonal complement of the genuine Hessian kernel; the resolvent therefore
requires no supplied zero-mode projector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option synthInstance.maxHeartbeats 2400000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementResolvent4D

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

private abbrev ResolventHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) resolventNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (ResolventHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) resolventInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (ResolventHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) resolventNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (ResolventHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) resolventModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (ResolventHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) resolventCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (ResolventHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)

/-- Open real interval certified by the actual-kernel gap. -/
def globalCandidateAActualKernelResolventInterval
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
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis chart sameAction physical) : Set Real :=
  Set.Ioo (-gap.gapData.gap) gap.gapData.gap

/-- Candidate-A reduced resolvent on `(ker H)ᗮ`. -/
noncomputable def globalCandidateAActualKernelResolvent
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
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis chart sameAction physical)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < gap.gapData.gap) :=
  selfAdjointKernelComplementResolvent
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    gap.gapData spectralParameter hSpectral

/-- Full real-gap resolvent certificate. -/
structure GlobalCandidateAActualKernelResolventCertificate4D
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
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis chart sameAction physical) : Prop where
  complement : GlobalCandidateAActualKernelComplementCertificate4D period
    hPeriod configuration data analysis chart sameAction physical gap
  interval_open : IsOpen
    (globalCandidateAActualKernelResolventInterval period hPeriod configuration
      data analysis chart sameAction physical gap)
  zero_mem_interval : 0 ∈
    globalCandidateAActualKernelResolventInterval period hPeriod configuration
      data analysis chart sameAction physical gap
  resolvent : ∀ spectralParameter,
    |spectralParameter| < gap.gapData.gap →
      Function.LeftInverse
        (globalCandidateAActualKernelResolvent period hPeriod configuration data
          analysis chart sameAction physical gap spectralParameter ‹_›)
        (selfAdjointKernelComplementShiftedOperator
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical)
          (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
            configuration data analysis chart sameAction physical)
          spectralParameter) ∧
      Function.RightInverse
        (globalCandidateAActualKernelResolvent period hPeriod configuration data
          analysis chart sameAction physical gap spectralParameter ‹_›)
        (selfAdjointKernelComplementShiftedOperator
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical)
          (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
            configuration data analysis chart sameAction physical)
          spectralParameter) ∧
      ‖globalCandidateAActualKernelResolvent period hPeriod configuration data
          analysis chart sameAction physical gap spectralParameter ‹_›‖ ≤
        (gap.gapData.gap - |spectralParameter|)⁻¹

/-- Construction of the Candidate-A actual-kernel resolvent certificate. -/
def globalCandidateAActualKernelResolventCertificate
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
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis chart sameAction physical) :
    GlobalCandidateAActualKernelResolventCertificate4D period hPeriod
      configuration data analysis chart sameAction physical gap where
  complement := globalCandidateAActualKernelComplementCertificate period hPeriod
    configuration data analysis chart sameAction physical gap
  interval_open := isOpen_Ioo
  zero_mem_interval := by
    constructor <;> linarith [gap.gapData.gap_pos]
  resolvent := by
    intro spectralParameter hSpectral
    exact self_adjoint_actual_kernel_resolvent_gate
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical)
      (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
        configuration data analysis chart sameAction physical)
      gap.gapData spectralParameter hSpectral

/-- Public Candidate-A actual-kernel resolvent gate. -/
theorem global_candidateA_actual_kernel_resolvent_gate
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
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis chart sameAction physical) :
    GlobalCandidateAActualKernelResolventCertificate4D period hPeriod
      configuration data analysis chart sameAction physical gap :=
  globalCandidateAActualKernelResolventCertificate period hPeriod
    configuration data analysis chart sameAction physical gap

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
end JanusFormal
