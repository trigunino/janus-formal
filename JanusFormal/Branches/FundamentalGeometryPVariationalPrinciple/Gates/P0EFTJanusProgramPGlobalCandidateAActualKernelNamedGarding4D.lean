import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

/-!
# Candidate-A actual zero modes from a global named-mode Gårding estimate

This specialization attaches the generic named-mode Gårding reduction to the
true augmented Candidate-A Hessian.  The analytic input is now expressed in
ambient physical terms:

* named vectors are killed by the displayed Hessian;
* they are independent and span its full kernel;
* one global Gårding inequality has a defect supported only on their scalar
  coefficients.

The existing actual-kernel gap, Fredholm, Green and resolvent packets are then
reconstructed automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 3600000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
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

/-- Named-mode Gårding packet for the genuine augmented Candidate-A Hessian. -/
structure GlobalCandidateAActualKernelNamedGarding4D
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
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  garding : FiniteKernelNamedModeGardingData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical) ZeroMode
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- The named global Gårding estimate supplies the exact gap packet already
consumed by H12. -/
def GlobalCandidateAActualKernelNamedGarding4D.toGap
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
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (input : GlobalCandidateAActualKernelNamedGarding4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
      chart sameAction physical where
  gapData := input.garding.toGapData
    (hSelfAdjoint :=
      globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
        configuration data analysis chart sameAction physical)
  ll_stationary := input.ll_stationary

/-- Exact number of actual Candidate-A zero modes. -/
theorem GlobalCandidateAActualKernelNamedGarding4D.kernel_finrank_eq_card
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
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (input : GlobalCandidateAActualKernelNamedGarding4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).ker =
      Fintype.card ZeroMode :=
  input.garding.spanning.kernel_finrank_eq_card

/-- Public Candidate-A checkpoint. -/
theorem global_candidateA_actual_kernel_named_garding_gate
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
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (input : GlobalCandidateAActualKernelNamedGarding4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    Nonempty (GlobalCandidateAActualKernelGap4D period hPeriod configuration data
        analysis chart sameAction physical) ∧
      Module.finrank Real
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical).ker =
        Fintype.card ZeroMode :=
  ⟨⟨input.toGap period hPeriod⟩,
    input.kernel_finrank_eq_card period hPeriod⟩

end
end P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D
end JanusFormal
