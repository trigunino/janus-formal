import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D

/-!
# Candidate-A Schur reduction from a physical finite mode subspace

For the actual augmented Candidate-A Hessian the finite/complement splitting is
now the orthogonal decomposition associated with one finite physical mode
subspace.  The four bounded Schur blocks and the continuous reduced coordinate
map are extracted automatically.

The packet retains only:

* a finite subspace with physical coordinates `Mode → ℝ`;
* invertibility of the canonical complementary block on its orthogonal
  complement;
* the already required LL stationarity.

No arbitrary global decomposition and no separately supplied blocks `A,B,C,D`
remain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurBlock4D

set_option autoImplicit false
set_option maxHeartbeats 8200000
set_option synthInstance.maxHeartbeats 4100000

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
open P0EFTJanusProgramPGlobalCandidateAActualContinuousSchurBlock4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurClosedRange4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurZeroMode4D
open P0EFTJanusProgramPGlobalCandidateAActualZeroModeModel4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D
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

private abbrev OrthogonalSchurHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) orthogonalSchurNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (OrthogonalSchurHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) orthogonalSchurInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (OrthogonalSchurHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) orthogonalSchurNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (OrthogonalSchurHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) orthogonalSchurModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (OrthogonalSchurHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) orthogonalSchurCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (OrthogonalSchurHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)

/-- Orthogonal finite-mode input for the displayed augmented Candidate-A
operator. -/
structure GlobalCandidateAActualOrthogonalSchurData4D
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
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode] : Prop where
  modeSubspace : Submodule Real
    (OrthogonalSchurHilbert period hPeriod configuration data analysis)
  modeEquiv : (Mode → Real) ≃L[Real] modeSubspace
  complementEquiv : modeSubspaceᗮ ≃L[Real] modeSubspaceᗮ
  complementEquiv_eq :
    complementEquiv.toContinuousLinearMap =
      finiteModeCanonicalBlockD
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical)
        (finiteModeOrthogonalDecomposition modeSubspace modeEquiv)
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Generic orthogonal Schur packet associated with the actual Candidate-A
operator. -/
def GlobalCandidateAActualOrthogonalSchurData4D.toOrthogonalSchurData
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
    (schur : GlobalCandidateAActualOrthogonalSchurData4D period hPeriod
      configuration data analysis chart sameAction physical Mode) :
    FiniteModeOrthogonalSchurDecompositionData
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical) where
  modeSubspace := schur.modeSubspace
  modeEquiv := schur.modeEquiv
  complementEquiv := schur.complementEquiv
  complementEquiv_eq := schur.complementEquiv_eq

/-- Fully bounded Candidate-A four-block packet, with the orthogonal complement
used as the infinite block. -/
def GlobalCandidateAActualOrthogonalSchurData4D.toBoundedSchurBlockData
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
    (schur : GlobalCandidateAActualOrthogonalSchurData4D period hPeriod
      configuration data analysis chart sameAction physical Mode) :
    GlobalCandidateAActualBoundedSchurBlockData4D period hPeriod configuration
      data analysis chart sameAction physical Mode schur.modeSubspaceᗮ where
  blocks := schur.toOrthogonalSchurData.toContinuousSchurBlockData
  ll_stationary := schur.ll_stationary

/-- Closed-range Schur packet generated from the orthogonal data. -/
def GlobalCandidateAActualOrthogonalSchurData4D.toSchurZeroModeData
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
    (schur : GlobalCandidateAActualOrthogonalSchurData4D period hPeriod
      configuration data analysis chart sameAction physical Mode) :=
  ((schur.toBoundedSchurBlockData period hPeriod).toContinuousSchurBlockData
      period hPeriod).toClosedRangeData period hPeriod |>.toSchurZeroModeData
        period hPeriod

/-- Actual-kernel gap derived from the finite orthogonal Schur complement. -/
noncomputable def GlobalCandidateAActualOrthogonalSchurData4D.toActualKernelGap
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
    (schur : GlobalCandidateAActualOrthogonalSchurData4D period hPeriod
      configuration data analysis chart sameAction physical Mode) :=
  (schur.toSchurZeroModeData period hPeriod).toActualZeroModeGap period hPeriod
    |>.toActualKernelGap period hPeriod

/-- Public Candidate-A checkpoint from a finite physical subspace and
invertibility of the canonical orthogonal-complement block. -/
theorem global_candidateA_actual_orthogonal_schur_block_gate
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
    (schur : GlobalCandidateAActualOrthogonalSchurData4D period hPeriod
      configuration data analysis chart sameAction physical Mode) :=
  global_candidateA_actual_bounded_schur_block_gate period hPeriod configuration
    data analysis chart sameAction physical Mode schur.modeSubspaceᗮ
      (schur.toBoundedSchurBlockData period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurBlock4D
end JanusFormal
