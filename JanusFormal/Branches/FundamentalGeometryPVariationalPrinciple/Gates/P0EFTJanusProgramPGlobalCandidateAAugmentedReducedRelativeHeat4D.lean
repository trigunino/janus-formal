import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponentialCompactNoGo4D

/-!
# Relative heat frontier for the reduced Candidate-A Hessian

The actual bounded Candidate-A reduced exponential is invertible and is not an
absolute nuclear heat kernel in infinite dimension.  The determinant-level
bounded input is instead a self-adjoint coercive reference operator on the same
zero-mode complement together with a norm-summable compact expansion of the
actual-minus-reference exponential at every positive time.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedReducedRelativeHeat4D

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option synthInstance.maxHeartbeats 3500000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusCircleDiracHeatTraceCancellation
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
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponential4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponentialCompactNoGo4D
open P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D

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

/-- Candidate-A spelling of the valid relative heat input. -/
abbrev GlobalCandidateAAugmentedReducedRelativeHeatData4D
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical) :=
  FiniteDefectReducedRelativeHeatData
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift.coerciveShift

/-- The Candidate-A actual-minus-reference heat difference. -/
def globalCandidateAAugmentedReducedRelativeHeatDifference
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (relative : GlobalCandidateAAugmentedReducedRelativeHeatData4D period hPeriod
      configuration data analysis chart sameAction physical shift)
    (time : HeatTime) :=
  finiteDefectReducedRelativeHeatDifference
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift.coerciveShift relative.referenceOperator time

/-- The supplied relative expansion makes the Candidate-A heat difference
compact. -/
theorem globalCandidateAAugmentedReducedRelativeHeatDifference_compact
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (relative : GlobalCandidateAAugmentedReducedRelativeHeatData4D period hPeriod
      configuration data analysis chart sameAction physical shift)
    (time : HeatTime) :
    IsCompactOperator
      (globalCandidateAAugmentedReducedRelativeHeatDifference period hPeriod
        configuration data analysis chart sameAction physical shift relative
          time) :=
  relative.relativeHeat_compact
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift.coerciveShift time

/-- The absolute compactness obstruction remains visible in the Candidate-A
frontier. -/
theorem globalCandidateAAugmentedAbsoluteReducedHeat_compact_implies_finiteDimensional
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (time : HeatTime)
    (hCompact : IsCompactOperator
      (globalCandidateAAugmentedReducedExponential period hPeriod configuration
        data analysis chart sameAction physical shift time.1)) :
    FiniteDimensional Real shift.coerciveShift.projection.ker :=
  globalCandidateAAugmentedReducedExponential_compact_implies_finiteDimensional
    period hPeriod configuration data analysis chart sameAction physical shift
      time.1 hCompact

/-- Public Candidate-A relative-heat checkpoint. -/
theorem global_candidateA_augmented_reduced_relative_heat_gate
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (relative : GlobalCandidateAAugmentedReducedRelativeHeatData4D period hPeriod
      configuration data analysis chart sameAction physical shift) :
    ∀ time : HeatTime,
      IsCompactOperator
        (globalCandidateAAugmentedReducedRelativeHeatDifference period hPeriod
          configuration data analysis chart sameAction physical shift relative
            time) :=
  globalCandidateAAugmentedReducedRelativeHeatDifference_compact period hPeriod
    configuration data analysis chart sameAction physical shift relative

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedReducedRelativeHeat4D
end JanusFormal
