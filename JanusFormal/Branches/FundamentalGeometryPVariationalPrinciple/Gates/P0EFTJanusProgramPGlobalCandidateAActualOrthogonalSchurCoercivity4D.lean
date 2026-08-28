import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeOrthogonalSchurCoercivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedVectors4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

/-!
# Candidate-A orthogonal Schur data from complementary coercivity

Concrete reference-mode vectors determine the finite subspace of the actual
augmented Candidate-A Hilbert space.  The full Hessian is already self-adjoint,
so coercivity of its canonical compression to the orthogonal complement
constructs the inverse complementary block automatically.

This replaces the supplied `D⁻¹` in the Candidate-A Schur packet by the PDE
estimate naturally produced by elliptic analysis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoercivity4D

set_option autoImplicit false
set_option maxHeartbeats 9800000
set_option synthInstance.maxHeartbeats 4900000

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
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurBlock4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurNamedVectors4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurCoercivity4D
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

private abbrev CoerciveSchurHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  ActualKernelHilbert period hPeriod configuration data analysis

/-- Candidate-A reference vectors, coercivity on their canonical orthogonal
complement, and LL stationarity. -/
structure GlobalCandidateAActualOrthogonalSchurNamedCoercivityData4D
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
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode] where
  namedCoercivity : FiniteModeOrthogonalSchurNamedCoercivityData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    (Mode := Mode)
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Recover the earlier named-vector Schur packet, with the inverse of `D`
constructed from coercivity. -/
def GlobalCandidateAActualOrthogonalSchurNamedCoercivityData4D.toNamedVectorsData
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
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (coercive : GlobalCandidateAActualOrthogonalSchurNamedCoercivityData4D period
      hPeriod configuration data analysis chart sameAction physical Mode) :
    GlobalCandidateAActualOrthogonalSchurNamedVectorsData4D period hPeriod
      configuration data analysis chart sameAction physical Mode where
  namedData :=
    { vector := coercive.namedCoercivity.vector
      linearIndependent := coercive.namedCoercivity.linearIndependent
      complementEquiv := coercive.namedCoercivity.toCoercivityData.complementEquiv
      complementEquiv_eq :=
        (coercive.namedCoercivity.toCoercivityData.toOrthogonalSchurData).complementEquiv_eq }
  ll_stationary := coercive.ll_stationary

/-- Recover the direct orthogonal Schur packet. -/
def GlobalCandidateAActualOrthogonalSchurNamedCoercivityData4D.toOrthogonalData
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
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (coercive : GlobalCandidateAActualOrthogonalSchurNamedCoercivityData4D period
      hPeriod configuration data analysis chart sameAction physical Mode) :
    GlobalCandidateAActualOrthogonalSchurData4D period hPeriod configuration
      data analysis chart sameAction physical Mode :=
  (coercive.toNamedVectorsData period hPeriod).toBasisData period hPeriod
    |>.toOrthogonalData period hPeriod

/-- Public Candidate-A checkpoint: the inverse complementary block and all
Schur conclusions are generated from one orthogonal coercivity estimate. -/
def global_candidateA_actual_orthogonal_schur_named_coercivity_gate
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
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (coercive : GlobalCandidateAActualOrthogonalSchurNamedCoercivityData4D period
      hPeriod configuration data analysis chart sameAction physical Mode) :=
  And.intro
    (FiniteModeOrthogonalSchurNamedCoercivityData.finite_mode_orthogonal_schur_named_coercivity_gate
      coercive.namedCoercivity)
    (global_candidateA_actual_orthogonal_schur_named_vectors_gate period hPeriod
      configuration data analysis chart sameAction physical Mode
      (coercive.toNamedVectorsData period hPeriod))

end
end P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurCoercivity4D
end JanusFormal
