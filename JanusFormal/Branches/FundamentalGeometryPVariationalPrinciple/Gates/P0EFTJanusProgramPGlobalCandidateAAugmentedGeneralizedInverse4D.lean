import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

/-!
# Finite-defect parametrix from one generalized inverse

The H12 packet previously asked independently for a parametrix, two defect
operators, both defect identities and the annihilation of the operator range.
For a standard generalized inverse these objects are canonical:

`K = I - QH`, `C = I - HQ`.

The single relation `HQH = H` then proves `CH = 0`, while the left and right
parametrix identities are algebraic. Thus the remaining analytic input is one
bounded generalized inverse together with finite-dimensionality of the two
canonical defect ranges and LL stationarity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
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

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmNormedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmModule
  P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmCompleteSpace

private abbrev AugmentedEndomorphism
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data analysis
    →L[Real]
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data analysis

private def adaptedAugmentedRieszOperator
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
    AugmentedEndomorphism period hPeriod configuration data analysis where
  toFun := fun vector =>
    globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical vector
  map_add' first second := by
    exact map_add
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) first second
  map_smul' scalar vector := by
    let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical
    change operator (scalar • vector) = scalar • operator vector
    exact map_smul operator scalar vector
  cont :=
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical).cont

@[simp] private theorem adaptedAugmentedRieszOperator_apply
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
    (vector : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    adaptedAugmentedRieszOperator period hPeriod configuration data analysis
        chart sameAction physical vector =
      globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical vector := rfl

private def augmentedEndomorphismSub
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : AugmentedEndomorphism period hPeriod configuration data
      analysis) :
    AugmentedEndomorphism period hPeriod configuration data analysis := by
  letI hAdd := augmentedFredholmNormedAddCommGroup period hPeriod configuration data analysis
  let hModule := augmentedFredholmModule period hPeriod configuration data analysis
  let hSeminormed := @NormedAddCommGroup.toSeminormedAddCommGroup
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis) hAdd
  let hTopology := hSeminormed.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let hGroup := hSeminormed.toAddCommGroup
  let hTopologicalAdd := @SeminormedAddCommGroup.toIsTopologicalAddGroup
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis) hSeminormed
  letI : TopologicalSpace
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) := hTopology
  letI : AddCommGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) := hGroup
  letI : Module Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) := hModule
  exact @Sub.sub (AugmentedEndomorphism period hPeriod configuration data analysis)
    (@ContinuousLinearMap.sub Real inferInstance Real inferInstance
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) hTopology hGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) hTopology hGroup hModule hModule
      (RingHom.id Real) hTopologicalAdd) first second

@[simp] private theorem augmentedEndomorphismSub_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : AugmentedEndomorphism period hPeriod configuration data
      analysis)
    (vector : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    augmentedEndomorphismSub period hPeriod configuration data analysis first
        second vector =
      first vector - second vector := rfl

/-- Canonical left defect `I - QH`. -/
def globalCandidateAAugmentedKernelDefect
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
    (parametrix : AugmentedEndomorphism period hPeriod configuration data
      analysis) :
    AugmentedEndomorphism period hPeriod configuration data analysis := by
  exact augmentedEndomorphismSub period hPeriod configuration data analysis
    (ContinuousLinearMap.id Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
        analysis))
    (parametrix.comp
    (adaptedAugmentedRieszOperator period hPeriod configuration data analysis
        chart sameAction physical))

@[simp]
theorem globalCandidateAAugmentedKernelDefect_apply
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
    (parametrix : AugmentedEndomorphism period hPeriod configuration data
      analysis)
    (vector : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    globalCandidateAAugmentedKernelDefect period hPeriod configuration data
        analysis chart sameAction physical parametrix vector =
      vector - parametrix
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical vector) :=
  rfl

/-- Canonical right defect `I - HQ`. -/
def globalCandidateAAugmentedCokernelDefect
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
    (parametrix : AugmentedEndomorphism period hPeriod configuration data
      analysis) :
    AugmentedEndomorphism period hPeriod configuration data analysis := by
  exact augmentedEndomorphismSub period hPeriod configuration data analysis
    (ContinuousLinearMap.id Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
        analysis))
    ((adaptedAugmentedRieszOperator period hPeriod configuration data analysis
      chart sameAction physical).comp parametrix)

@[simp]
theorem globalCandidateAAugmentedCokernelDefect_apply
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
    (parametrix : AugmentedEndomorphism period hPeriod configuration data
      analysis)
    (vector : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    globalCandidateAAugmentedCokernelDefect period hPeriod configuration data
        analysis chart sameAction physical parametrix vector =
      vector -
        globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical
            (parametrix vector) :=
  rfl

/-- A bounded generalized inverse with finite canonical left and right defects.
The relation `HQH = H` is precisely what is needed to make the right defect
annihilate the operator range. -/
structure GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D
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
  parametrix : AugmentedEndomorphism period hPeriod configuration data analysis
  generalized_inverse :
    ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).comp
      parametrix).comp
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) =
      globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical
  kernelDefect_range_finite : FiniteDimensional Real
    (globalCandidateAAugmentedKernelDefect period hPeriod configuration data
      analysis chart sameAction physical parametrix).range
  cokernelDefect_range_finite : FiniteDimensional Real
    (globalCandidateAAugmentedCokernelDefect period hPeriod configuration data
      analysis chart sameAction physical parametrix).range
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Build the finite-defect H12 parametrix. The two defect identities are now
algebraic and range annihilation follows from `HQH = H`. -/
def globalCandidateAFaithfulAugmentedFiniteDefectParametrix_of_generalizedInverse
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
    (inverse : GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis chart sameAction physical where
  parametrix := inverse.parametrix
  kernelDefect := globalCandidateAAugmentedKernelDefect period hPeriod
    configuration data analysis chart sameAction physical inverse.parametrix
  cokernelDefect := globalCandidateAAugmentedCokernelDefect period hPeriod
    configuration data analysis chart sameAction physical inverse.parametrix
  left_identity := by
    intro vector
    simp [globalCandidateAAugmentedKernelDefect,
      ContinuousLinearMap.comp_apply]
  right_identity := by
    intro vector
    simp [globalCandidateAAugmentedCokernelDefect,
      ContinuousLinearMap.comp_apply]
  cokernel_annihilates_range := by
    let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical
    ext vector
    have hGeneralized := congrArg
      (fun map : AugmentedEndomorphism period hPeriod configuration data
        analysis => map vector) inverse.generalized_inverse
    change operator (inverse.parametrix (operator vector)) =
      operator vector at hGeneralized
    change
      (globalCandidateAAugmentedCokernelDefect period hPeriod configuration data
        analysis chart sameAction physical inverse.parametrix)
        (operator vector) = 0
    simp only [globalCandidateAAugmentedCokernelDefect,
      augmentedEndomorphismSub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, adaptedAugmentedRieszOperator_apply]
    exact sub_eq_zero.mpr hGeneralized.symm
  kernelDefect_range_finite := inverse.kernelDefect_range_finite
  cokernelDefect_range_finite := inverse.cokernelDefect_range_finite
  ll_stationary := inverse.ll_stationary

/-- H12 from the standard generalized-inverse packet. -/
def global_candidateA_h12_faithful_augmented_fredholm_gate_of_generalizedInverse
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
    (inverse : GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :=
  global_candidateA_h12_faithful_augmented_fredholm_gate_of_parametrix period
    hPeriod configuration data analysis chart sameAction physical
      (globalCandidateAFaithfulAugmentedFiniteDefectParametrix_of_generalizedInverse
        period hPeriod configuration data analysis chart sameAction physical
          inverse)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
end JanusFormal
