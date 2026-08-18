import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D

/-!
# Candidate-A Hessian on the complement of its actual zero modes

The augmented Candidate-A Riesz representative is already bounded and
self-adjoint.  Consequently its canonical reduced space is the orthogonal
complement of its genuine kernel.  This file specializes the generic
kernel-complement reduction and removes the finite projection from the H12
interface.

The sole operator estimate is a positive gap on `(ker H)ᗮ`; the finite space is
the actual kernel itself.  From this data we derive closed range, Fredholmness,
index zero, exact range splitting and the reduced Green operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

def ActualKernelHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) : Type :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) actualKernelNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (ActualKernelHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) actualKernelInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (ActualKernelHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) actualKernelNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (ActualKernelHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) actualKernelModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (ActualKernelHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) actualKernelCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (ActualKernelHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- Public abbreviation for the genuine augmented Candidate-A operator. -/
def globalCandidateAActualKernelOperator
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
    ActualKernelHilbert period hPeriod configuration data analysis →L[Real]
      ActualKernelHilbert period hPeriod configuration data analysis :=
  globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
    data analysis chart sameAction physical

/-- The actual self-adjointness theorem attached to the preceding spelling. -/
def globalCandidateAActualKernelOperator_isSelfAdjoint
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
    IsSelfAdjoint
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical) :=
  globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
    configuration data analysis chart sameAction physical

/-- Narrowest operator-specific H12 input: finite actual kernel and a positive
gap on its orthogonal complement. -/
structure GlobalCandidateAActualKernelGap4D
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
      hPeriod configuration data analysis chart sameAction) where
  gapData : SelfAdjointKernelComplementGapData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- The canonical reduced Candidate-A Hessian on the exact zero-mode
complement. -/
def globalCandidateAActualKernelComplementOperator
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
      hPeriod configuration data analysis chart sameAction) :=
  selfAdjointKernelComplementOperator
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)

/-- Canonical reduced Green operator with no chosen defect projection. -/
noncomputable def globalCandidateAActualKernelGreen
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
      analysis chart sameAction physical) :=
  selfAdjointKernelComplementGreen
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    gap.gapData

/-- Closed range and finite kernel are derived directly from the actual-kernel
gap. -/
def globalCandidateAActualKernelFredholmEstimates
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
    GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period hPeriod
      configuration data analysis chart sameAction physical where
  ll_stationary := gap.ll_stationary
  range_closed := selfAdjoint_operator_range_closed
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    gap.gapData
  kernel_finite := gap.gapData.kernel_finite

/-- H12 closes without introducing a finite projection. -/
theorem global_candidateA_h12_fredholm_gate_of_actualKernelGap
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
    GlobalCandidateAFaithfulAugmentedFredholmCertificate4D period hPeriod
      configuration data analysis chart sameAction physical
        (globalCandidateAActualKernelFredholmEstimates period hPeriod
          configuration data analysis chart sameAction physical gap) :=
  global_candidateA_h12_faithful_augmented_fredholm_gate period hPeriod
    configuration data analysis chart sameAction physical
      (globalCandidateAActualKernelFredholmEstimates period hPeriod
        configuration data analysis chart sameAction physical gap)

/-- Exact operator-level output of the actual-kernel route. -/
structure GlobalCandidateAActualKernelComplementCertificate4D
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
  range_eq_kernelComplement :
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical).range =
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical).kerᗮ
  fredholm :
    IsClosed
        ((globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).range :
          Set (ActualKernelHilbert period hPeriod configuration data analysis)) ∧
      FiniteDimensional Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).ker ∧
      FiniteDimensional Real
        (ActualKernelHilbert period hPeriod configuration data analysis ⧸
          (globalCandidateAActualKernelOperator period hPeriod configuration
            data analysis chart sameAction physical).range)
  index_zero :
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical).toLinearMap.index = 0
  green_leftInverse : Function.LeftInverse
    (globalCandidateAActualKernelGreen period hPeriod configuration data analysis
      chart sameAction physical gap)
    (globalCandidateAActualKernelComplementOperator period hPeriod configuration
      data analysis chart sameAction physical)
  green_rightInverse : Function.RightInverse
    (globalCandidateAActualKernelGreen period hPeriod configuration data analysis
      chart sameAction physical gap)
    (globalCandidateAActualKernelComplementOperator period hPeriod configuration
      data analysis chart sameAction physical)
  green_opNorm_le :
    ‖globalCandidateAActualKernelGreen period hPeriod configuration data analysis
      chart sameAction physical gap‖ ≤ gap.gapData.gap⁻¹

/-- Construction of the exact Candidate-A zero-mode complement certificate. -/
def globalCandidateAActualKernelComplementCertificate
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
    GlobalCandidateAActualKernelComplementCertificate4D period hPeriod
      configuration data analysis chart sameAction physical gap := by
  let operator := globalCandidateAActualKernelOperator period hPeriod
    configuration data analysis chart sameAction physical
  let hSelfAdjoint := globalCandidateAActualKernelOperator_isSelfAdjoint period
    hPeriod configuration data analysis chart sameAction physical
  let generic := selfAdjointKernelComplementCertificate operator hSelfAdjoint
    gap.gapData
  exact
    { range_eq_kernelComplement := generic.range_eq_kernelComplement
      fredholm := generic.fredholm
      index_zero := generic.index_zero
      green_leftInverse := generic.green_leftInverse
      green_rightInverse := generic.green_rightInverse
      green_opNorm_le := generic.green_opNorm_le }

/-- Public actual-zero-mode checkpoint. -/
theorem global_candidateA_actual_kernel_complement_gate
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
    GlobalCandidateAActualKernelComplementCertificate4D period hPeriod
      configuration data analysis chart sameAction physical gap :=
  globalCandidateAActualKernelComplementCertificate period hPeriod
    configuration data analysis chart sameAction physical gap

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
end JanusFormal
