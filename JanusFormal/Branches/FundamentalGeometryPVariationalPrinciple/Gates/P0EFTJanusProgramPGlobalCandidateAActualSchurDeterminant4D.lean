import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualSchurNondegenerate4D

/-!
# Candidate-A nondegeneracy from the finite Schur determinant

The finite Schur complement of the bounded Candidate-A block decomposition has
a standard-basis matrix.  A nonzero determinant constructs its inverse and
therefore the full Candidate-A Green operator on the zero-mode-free stratum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualSchurDeterminant4D

set_option autoImplicit false
set_option maxHeartbeats 7800000
set_option synthInstance.maxHeartbeats 3900000

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
open P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurNondegenerate4D
open P0EFTJanusProgramPFiniteModeSchurDeterminant4D

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

/-- Bounded Candidate-A Schur data with an explicit nonzero finite determinant. -/
structure GlobalCandidateAActualSchurDeterminantData4D
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
    [NormedAddCommGroup Complement] [NormedSpace Real Complement] : Type _ where
  blockData : GlobalCandidateAActualBoundedSchurBlockData4D period hPeriod
    configuration data analysis chart sameAction physical Mode Complement
  determinant_ne_zero :
    (finiteModeSchurMatrix blockData.blocks.toLinearBlockData).det ≠ 0

/-- Convert the determinant certificate to Candidate-A Schur nondegeneracy. -/
def GlobalCandidateAActualSchurDeterminantData4D.toNondegenerateData
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
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        Complement) :
    GlobalCandidateAActualBoundedSchurNondegenerateData4D period hPeriod
      configuration data analysis chart sameAction physical Mode Complement where
  blockData := determinantData.blockData
  schur_bijective :=
    finiteModeSchurBlockOperator_bijective_of_det_ne_zero
      { blockData := determinantData.blockData.blocks.toLinearBlockData
        determinant_ne_zero := determinantData.determinant_ne_zero }

/-- Public determinant-level Candidate-A nondegeneracy checkpoint. -/
def global_candidateA_actual_schur_determinant_gate
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
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        Complement) :=
  global_candidateA_actual_schur_nondegenerate_gate period hPeriod configuration
    data analysis chart sameAction physical Mode Complement
      (determinantData.toNondegenerateData period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateAActualSchurDeterminant4D
end JanusFormal
