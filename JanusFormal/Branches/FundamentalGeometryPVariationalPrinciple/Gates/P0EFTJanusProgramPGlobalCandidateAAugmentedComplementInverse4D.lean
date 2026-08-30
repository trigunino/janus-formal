import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D

/-!
# H12 generalized inverse from finite kernel/cokernel complements

The standard PDE construction of a generalized inverse chooses finite-rank
projections onto the kernel and cokernel and inverts the operator on their
complements.  In this presentation

`QH = I - Pker`, `HQ = I - Pcoker`,

and `Pcoker H = 0`.  Consequently `HQH = H`, while the canonical H12 defects
are exactly `Pker` and `Pcoker`.

This module turns that complement-level data into the generalized-inverse
packet already consumed by the terminal Fredholm gate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedComplementInverse4D

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 6000000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
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

private abbrev ComplementHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) complementNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup (ComplementHilbert period hPeriod configuration data
      analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) complementInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real (ComplementHilbert period hPeriod configuration data
      analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) complementNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real (ComplementHilbert period hPeriod configuration data
      analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) complementModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real (ComplementHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) complementCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace (ComplementHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

private abbrev ComplementEndomorphism
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  ComplementHilbert period hPeriod configuration data analysis →L[Real]
    ComplementHilbert period hPeriod configuration data analysis

/-- Complement-level inverse data for the augmented operator. -/
structure GlobalCandidateAFaithfulAugmentedComplementInverse4D
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
  inverseOnComplement :
    ComplementEndomorphism period hPeriod configuration data analysis
  kernelProjection :
    ComplementEndomorphism period hPeriod configuration data analysis
  cokernelProjection :
    ComplementEndomorphism period hPeriod configuration data analysis
  inverse_comp_operator : ∀ vector,
    inverseOnComplement
        ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) vector) =
      vector - kernelProjection vector
  operator_comp_inverse : ∀ vector,
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical)
        (inverseOnComplement vector) =
      vector - cokernelProjection vector
  cokernelProjection_annihilates_operator : ∀ vector,
    cokernelProjection
        ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) vector) = 0
  kernelProjection_range_finite :
    FiniteDimensional Real kernelProjection.range
  cokernelProjection_range_finite :
    FiniteDimensional Real cokernelProjection.range
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- The complement identities imply the generalized-inverse identity `HQH=H`. -/
theorem GlobalCandidateAFaithfulAugmentedComplementInverse4D.generalized_inverse
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
    (inverse : GlobalCandidateAFaithfulAugmentedComplementInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :
    ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).comp
      inverse.inverseOnComplement).comp
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) =
      globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical := by
  let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
    configuration data analysis chart sameAction physical
  ext vector
  have hRight := inverse.operator_comp_inverse (operator vector)
  have hZero := inverse.cokernelProjection_annihilates_operator vector
  change operator (inverse.inverseOnComplement (operator vector)) =
    operator vector
  rw [hZero, sub_zero] at hRight
  exact hRight

/-- The canonical generalized-inverse packet generated by complement data. -/
def globalCandidateAFaithfulAugmentedGeneralizedInverse_of_complement
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
    (inverse : GlobalCandidateAFaithfulAugmentedComplementInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period hPeriod
      configuration data analysis chart sameAction physical where
  parametrix := inverse.inverseOnComplement
  generalized_inverse := inverse.generalized_inverse
  kernelDefect_range_finite := by
    have hDefect :
        globalCandidateAAugmentedKernelDefect period hPeriod configuration data
            analysis chart sameAction physical inverse.inverseOnComplement =
          inverse.kernelProjection := by
      apply ContinuousLinearMap.ext
      intro vector
      rw [globalCandidateAAugmentedKernelDefect_apply]
      rw [inverse.inverse_comp_operator vector]
      abel
    rw [hDefect]
    exact inverse.kernelProjection_range_finite
  cokernelDefect_range_finite := by
    have hDefect :
        globalCandidateAAugmentedCokernelDefect period hPeriod configuration data
            analysis chart sameAction physical inverse.inverseOnComplement =
          inverse.cokernelProjection := by
      apply ContinuousLinearMap.ext
      intro vector
      rw [globalCandidateAAugmentedCokernelDefect_apply]
      rw [inverse.operator_comp_inverse vector]
      abel
    rw [hDefect]
    exact inverse.cokernelProjection_range_finite
  ll_stationary := inverse.ll_stationary

/-- H12 directly from finite kernel/cokernel complements. -/
def global_candidateA_h12_faithful_augmented_fredholm_gate_of_complement
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
    (inverse : GlobalCandidateAFaithfulAugmentedComplementInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :=
  global_candidateA_h12_faithful_augmented_fredholm_gate_of_generalizedInverse
    period hPeriod configuration data analysis chart sameAction physical
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_complement period
        hPeriod configuration data analysis chart sameAction physical inverse)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedComplementInverse4D
end JanusFormal
