import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoercivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

/-!
# Candidate-A named actual kernel from complementary coercivity

Concrete reference vectors and coercivity on their canonical orthogonal
complement construct the complete Schur reduction, including the inverse of the
infinite block `D`.  A finite named basis of the resulting `ker S` then
reconstructs the genuine ambient zero modes of the full Candidate-A Hessian.

This package combines both computations without accepting a supplied
complement inverse or a basis of the infinite-dimensional kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoerciveNamedKernel4D

set_option autoImplicit false
set_option maxHeartbeats 10800000
set_option synthInstance.maxHeartbeats 5400000

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
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoercivity4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedKernel4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurNamedZeroMode4D
open P0EFTJanusProgramPFiniteModeSchurNamedKernelModes4D

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

private abbrev CoerciveNamedHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  ActualKernelHilbert period hPeriod configuration data analysis

/-- Named reference modes with complementary coercivity, together with a named
basis of the finite Schur kernel they generate. -/
structure GlobalCandidateAActualOrthogonalSchurCoerciveNamedKernelData4D
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
    (Mode : Type*) (ZeroMode : Type)
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode] where
  coercive : GlobalCandidateAActualOrthogonalSchurNamedCoercivityData4D period
    hPeriod configuration data analysis chart sameAction physical Mode
  zeroModeBasis : FiniteModeSchurNamedKernelBasisData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    Mode
      (coercive.toNamedVectorsData period hPeriod).orthogonalData.modeSubspaceᗮ
    ZeroMode
      (coercive.toNamedVectorsData period hPeriod).schurZeroModeData.schur

/-- Convert to the previous named-kernel packet. -/
def GlobalCandidateAActualOrthogonalSchurCoerciveNamedKernelData4D.toNamedKernelData
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
    {Mode : Type*} {ZeroMode : Type}
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (named : GlobalCandidateAActualOrthogonalSchurCoerciveNamedKernelData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        ZeroMode) :
    GlobalCandidateAActualOrthogonalSchurNamedKernelData4D period hPeriod
      configuration data analysis chart sameAction physical Mode ZeroMode where
  reference := named.coercive.toNamedVectorsData period hPeriod
  zeroModeBasis := named.zeroModeBasis

/-- Public checkpoint: complementary coercivity plus a finite basis of `ker S`
produces the named actual-kernel gap. -/
def global_candidateA_actual_orthogonal_schur_coercive_named_kernel_gate
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
    (Mode : Type*) (ZeroMode : Type)
    [Fintype Mode] [DecidableEq Mode]
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    (named : GlobalCandidateAActualOrthogonalSchurCoerciveNamedKernelData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        ZeroMode) :=
  And.intro
    (global_candidateA_actual_orthogonal_schur_named_coercivity_gate period
      hPeriod configuration data analysis chart sameAction physical Mode
      named.coercive)
    (global_candidateA_actual_orthogonal_schur_named_kernel_gate period hPeriod
      configuration data analysis chart sameAction physical Mode ZeroMode
      (named.toNamedKernelData period hPeriod))

end
end P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoerciveNamedKernel4D
end JanusFormal
