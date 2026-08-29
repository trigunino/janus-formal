import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurAmbientCoercivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoerciveNamedKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

/-!
# Actual Candidate-A zero modes from ambient coercivity and `ker S`

The estimate supplied here is the physical one for the complete augmented
Hessian on the orthogonal complement of finitely many reference vectors.  It
constructs the inverse complementary block, after which a finite named basis
of `ker S` reconstructs all ambient zero modes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernel4D

set_option autoImplicit false
set_option maxHeartbeats 11600000
set_option synthInstance.maxHeartbeats 5800000

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
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurAmbientCoercivity4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoerciveNamedKernel4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedKernel4D
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

private abbrev AmbientNamedHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  ActualKernelHilbert period hPeriod configuration data analysis

/-- Ambient Hessian coercivity plus a finite named basis of the Schur kernel. -/
structure GlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernelData4D
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
  ambient : GlobalCandidateAActualOrthogonalSchurNamedAmbientCoercivityData4D
    period hPeriod configuration data analysis chart sameAction physical Mode
  zeroModeBasis : FiniteModeSchurNamedKernelBasisData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    Mode
      ((ambient.toComplementCoercivityData period hPeriod).toNamedVectorsData
        period hPeriod).orthogonalData.modeSubspaceᗮ
    ZeroMode
      ((ambient.toComplementCoercivityData period hPeriod).toNamedVectorsData
        period hPeriod).schurZeroModeData.schur

/-- Convert to the preceding complementary-block coercive named-kernel packet. -/
def GlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernelData4D.toCoerciveNamedKernelData
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
    (named : GlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernelData4D
      period hPeriod configuration data analysis chart sameAction physical Mode
        ZeroMode) :
    GlobalCandidateAActualOrthogonalSchurCoerciveNamedKernelData4D period hPeriod
      configuration data analysis chart sameAction physical Mode ZeroMode where
  coercive := named.ambient.toComplementCoercivityData period hPeriod
  zeroModeBasis := named.zeroModeBasis

/-- Public ambient-coercivity named-kernel checkpoint. -/
def global_candidateA_actual_orthogonal_schur_ambient_coercive_named_kernel_gate
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
    (named : GlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernelData4D
      period hPeriod configuration data analysis chart sameAction physical Mode
        ZeroMode) :=
  And.intro
    (global_candidateA_actual_orthogonal_schur_named_ambient_coercivity_gate
      period hPeriod configuration data analysis chart sameAction physical Mode
      named.ambient)
    (global_candidateA_actual_orthogonal_schur_coercive_named_kernel_gate period
      hPeriod configuration data analysis chart sameAction physical Mode ZeroMode
      (named.toCoerciveNamedKernelData period hPeriod))

end
end P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurAmbientCoerciveNamedKernel4D
end JanusFormal
