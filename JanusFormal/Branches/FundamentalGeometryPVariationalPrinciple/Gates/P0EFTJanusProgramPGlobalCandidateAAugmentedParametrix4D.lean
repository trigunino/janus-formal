import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D

/-!
# Finite-defect parametrix for the augmented H12 operator

H12 currently exposes the two correct analytic estimates for the faithful
augmented Candidate-A operator: closed range and finite-dimensional kernel.
This file gives a standard constructive route to both.  A bounded parametrix
with a finite-dimensional left defect and a right defect annihilating the
operator range identifies the range with the kernel of a bounded map and
embeds the operator kernel in the finite defect range.

Thus the terminal Fredholm estimates can be produced from explicit Green or
pseudodifferential parametrices without being stored independently.  No new
field, action, completion, Fredholm hypothesis, or physical assumption is
introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev AugmentedParametrixHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) augmentedParametrixNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (AugmentedParametrixHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedParametrixInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (AugmentedParametrixHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedParametrixNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (AugmentedParametrixHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedParametrixModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (AugmentedParametrixHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedParametrixCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (AugmentedParametrixHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- A bounded two-sided parametrix modulo finite left defect.  The right defect
annihilates the operator range, which identifies that range with its kernel.
The optional finite right defect records the usual Fredholm parametrix shape
and can be used later for determinant constructions. -/
structure GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
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
      hPeriod configuration data analysis chart sameAction) : Type where
  parametrix :
    AugmentedParametrixHilbert period hPeriod configuration data analysis
      →L[Real]
    AugmentedParametrixHilbert period hPeriod configuration data analysis
  kernelDefect :
    AugmentedParametrixHilbert period hPeriod configuration data analysis
      →L[Real]
    AugmentedParametrixHilbert period hPeriod configuration data analysis
  cokernelDefect :
    AugmentedParametrixHilbert period hPeriod configuration data analysis
      →L[Real]
    AugmentedParametrixHilbert period hPeriod configuration data analysis
  left_identity : ∀ vector,
    parametrix
        ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) vector) =
      vector - kernelDefect vector
  right_identity : ∀ vector,
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical)
        (parametrix vector) =
      vector - cokernelDefect vector
  cokernel_annihilates_range :
    cokernelDefect.comp
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) = 0
  kernelDefect_range_finite : FiniteDimensional Real kernelDefect.range
  cokernelDefect_range_finite : FiniteDimensional Real cokernelDefect.range
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- The augmented operator range is exactly the kernel of the right defect. -/
theorem augmentedParametrix_range_eq_cokernelDefect_ker
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
    (parametrix : GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
      period hPeriod configuration data analysis chart sameAction physical) :
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
        data analysis chart sameAction physical).range =
      parametrix.cokernelDefect.ker := by
  let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
    configuration data analysis chart sameAction physical
  apply le_antisymm
  · intro vector hVector
    rcases hVector with ⟨source, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hZero := congrArg
      (fun map :
        AugmentedParametrixHilbert period hPeriod configuration data analysis
          →L[Real]
        AugmentedParametrixHilbert period hPeriod configuration data analysis =>
        map source) parametrix.cokernel_annihilates_range
    simpa [ContinuousLinearMap.comp_apply] using hZero
  · intro vector hVector
    have hKernel : parametrix.cokernelDefect vector = 0 :=
      LinearMap.mem_ker.mp hVector
    refine ⟨parametrix.parametrix vector, ?_⟩
    have hRight := parametrix.right_identity vector
    change operator (parametrix.parametrix vector) =
      vector - parametrix.cokernelDefect vector at hRight
    rw [hKernel, sub_zero] at hRight
    exact hRight

/-- The right-defect kernel description makes the augmented range closed. -/
theorem augmentedParametrix_range_closed
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
    (parametrix : GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
      period hPeriod configuration data analysis chart sameAction physical) :
    IsClosed
      ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical).range :
        Set
          (AugmentedParametrixHilbert period hPeriod configuration data
            analysis)) := by
  rw [augmentedParametrix_range_eq_cokernelDefect_ker period hPeriod
    configuration data analysis chart sameAction physical parametrix]
  letI := augmentedParametrixNormedAddCommGroup period hPeriod configuration data
    analysis
  letI : T0Space
      (AugmentedParametrixHilbert period hPeriod configuration data analysis) :=
    MetricSpace.instT0Space
  letI : T1Space
      (AugmentedParametrixHilbert period hPeriod configuration data analysis) :=
    inferInstance
  exact parametrix.cokernelDefect.isClosed_ker

/-- A kernel vector is fixed by the finite-dimensional left defect. -/
theorem augmentedParametrix_kernel_eq_kernelDefect
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
    (parametrix : GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
      period hPeriod configuration data analysis chart sameAction physical)
    (vector :
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker) :
    parametrix.kernelDefect vector.1 = vector.1 := by
  let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
    configuration data analysis chart sameAction physical
  have hOperator : operator vector.1 = 0 := LinearMap.mem_ker.mp vector.2
  have hLeft := parametrix.left_identity vector.1
  change parametrix.parametrix (operator vector.1) =
    vector.1 - parametrix.kernelDefect vector.1 at hLeft
  rw [hOperator, map_zero] at hLeft
  exact (sub_eq_zero.mp hLeft.symm).symm

private def augmentedParametrix_kernelToDefectRange
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
    (parametrix : GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
      period hPeriod configuration data analysis chart sameAction physical) :
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
        data analysis chart sameAction physical).ker →ₗ[Real]
      parametrix.kernelDefect.range where
  toFun vector :=
    ⟨vector.1, ⟨vector.1,
      (augmentedParametrix_kernel_eq_kernelDefect period hPeriod configuration
        data analysis chart sameAction physical parametrix vector)⟩⟩
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar vector := by
    apply Subtype.ext
    rfl

private theorem augmentedParametrix_kernelToDefectRange_injective
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
    (parametrix : GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
      period hPeriod configuration data analysis chart sameAction physical) :
    Function.Injective
      (augmentedParametrix_kernelToDefectRange period hPeriod configuration data
        analysis chart sameAction physical parametrix) := by
  intro first second hEqual
  apply Subtype.ext
  exact congrArg (fun vector : parametrix.kernelDefect.range => vector.1) hEqual

/-- The augmented operator kernel embeds in the finite left-defect range. -/
theorem augmentedParametrix_kernel_finite
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
    (parametrix : GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
      period hPeriod configuration data analysis chart sameAction physical) :
    FiniteDimensional Real
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker := by
  letI : FiniteDimensional Real parametrix.kernelDefect.range :=
    parametrix.kernelDefect_range_finite
  exact FiniteDimensional.of_injective
    (augmentedParametrix_kernelToDefectRange period hPeriod configuration data
      analysis chart sameAction physical parametrix)
    (augmentedParametrix_kernelToDefectRange_injective period hPeriod
      configuration data analysis chart sameAction physical parametrix)

/-- The finite-defect parametrix constructs exactly the H12 estimate package. -/
def globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix
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
    (parametrix : GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
      period hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period hPeriod
      configuration data analysis chart sameAction physical where
  ll_stationary := parametrix.ll_stationary
  range_closed := augmentedParametrix_range_closed period hPeriod configuration
    data analysis chart sameAction physical parametrix
  kernel_finite := augmentedParametrix_kernel_finite period hPeriod
    configuration data analysis chart sameAction physical parametrix

/-- H12 Fredholm and index-zero certificate obtained from the explicit
finite-defect parametrix. -/
theorem global_candidateA_h12_faithful_augmented_fredholm_gate_of_parametrix
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
    (parametrix : GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D
      period hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAFaithfulAugmentedFredholmCertificate4D period hPeriod
      configuration data analysis chart sameAction physical
        (globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix period
          hPeriod configuration data analysis chart sameAction physical
            parametrix) :=
  global_candidateA_h12_faithful_augmented_fredholm_gate period hPeriod
    configuration data analysis chart sameAction physical
      (globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix period
        hPeriod configuration data analysis chart sameAction physical
          parametrix)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
end JanusFormal
