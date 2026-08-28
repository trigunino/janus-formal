import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualContinuousSchurBlock4D

/-!
# Candidate-A bounded four-block Schur packet

This is the irreducible Schur input for the actual augmented Candidate-A
Hessian.  All four blocks, the decomposition and the inverse complementary
block are continuous.  The reduced coordinate map and closed range are
therefore constructed rather than supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000

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
open P0EFTJanusProgramPGlobalCandidateAActualContinuousSchurBlock4D
open P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D
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

/-- Fully bounded four-block presentation of the actual Candidate-A Hessian. -/
structure GlobalCandidateAActualBoundedSchurBlockData4D
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
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement] where
  blocks : FiniteModeContinuousSchurBlockData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    Mode Complement
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Construct the previous continuous-coordinate packet automatically. -/
def GlobalCandidateAActualBoundedSchurBlockData4D.toContinuousSchurBlockData
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
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (blockData : GlobalCandidateAActualBoundedSchurBlockData4D period hPeriod
      configuration data analysis chart sameAction physical Mode Complement) :
    GlobalCandidateAActualContinuousSchurBlockData4D period hPeriod
      configuration data analysis chart sameAction physical Mode Complement where
  blocks := blockData.blocks.toLinearBlockData
  rangeCoordinates := finiteModeContinuousSchurRangeCoordinates blockData.blocks
  rangeCoordinates_eq :=
    finiteModeContinuousSchurRangeCoordinates_eq blockData.blocks
  ll_stationary := blockData.ll_stationary

/-- Public Candidate-A checkpoint from bounded blocks only. -/
def global_candidateA_actual_bounded_schur_block_gate
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
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (blockData : GlobalCandidateAActualBoundedSchurBlockData4D period hPeriod
      configuration data analysis chart sameAction physical Mode Complement) :=
  global_candidateA_actual_continuous_schur_block_gate period hPeriod
    configuration data analysis chart sameAction physical Mode Complement
      (blockData.toContinuousSchurBlockData period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D
end JanusFormal
