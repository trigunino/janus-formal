import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedExponentialCompactNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponential4D

/-!
# Candidate-A no-go for compactness of the bounded reduced exponential

The exact bounded exponential of the Candidate-A reduced Riesz operator is an
invertible one-parameter group.  Compactness at even one time therefore forces
the exact zero-mode complement to be finite-dimensional.

This rules out identifying that bounded exponential with an infinite-
dimensional nuclear elliptic heat kernel.  The determinant layer must instead
use an unbounded compact-resolvent realization or a relative determinant
construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponentialCompactNoGo4D

set_option autoImplicit false
set_option maxHeartbeats 6800000
set_option synthInstance.maxHeartbeats 3400000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponential4D
open P0EFTJanusProgramPFiniteDefectReducedExponentialCompactNoGo4D

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

/-- Compactness of one Candidate-A bounded reduced exponential forces finite
dimension of the reduced physical space. -/
theorem globalCandidateAAugmentedReducedExponential_compact_implies_finiteDimensional
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
    (time : Real)
    (hCompact : IsCompactOperator
      (globalCandidateAAugmentedReducedExponential period hPeriod configuration
        data analysis chart sameAction physical shift time)) :
    FiniteDimensional Real shift.coerciveShift.projection.ker :=
  finiteDimensional_of_compact_finiteDefectReducedExponential
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift.coerciveShift time hCompact

/-- Public Candidate-A no-go checkpoint. -/
theorem global_candidateA_bounded_reduced_heat_no_go_gate
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
    (time : Real)
    (hCompact : IsCompactOperator
      (globalCandidateAAugmentedReducedExponential period hPeriod configuration
        data analysis chart sameAction physical shift time)) :
    FiniteDimensional Real shift.coerciveShift.projection.ker :=
  globalCandidateAAugmentedReducedExponential_compact_implies_finiteDimensional
    period hPeriod configuration data analysis chart sameAction physical shift
      time hCompact

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponentialCompactNoGo4D
end JanusFormal
