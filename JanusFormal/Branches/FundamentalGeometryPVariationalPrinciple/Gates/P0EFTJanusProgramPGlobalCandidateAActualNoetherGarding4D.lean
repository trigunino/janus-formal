import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualNoetherModes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D

/-!
# Candidate-A Gårding closure with Noether-generated modes

The preceding Noether layer derives `H v = 0` from a germ-level identity for
the first variation of the honest augmented action.  The finite named-mode
Gårding route can therefore be narrowed: annihilation by the Hessian is no
longer analytic input.

A finite Noether family, linear independence of its kernel vectors and one
global Gårding inequality are sufficient.  The finite span has its canonical
orthogonal projection, Gårding excludes hidden zero modes, and the existing
actual-kernel machinery constructs the gap, Fredholm index, Green operator and
resolvent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualNoetherGarding4D

set_option autoImplicit false
set_option maxHeartbeats 8200000
set_option synthInstance.maxHeartbeats 4100000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActualNoetherModes4D
open P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D
open P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D
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

private abbrev NoetherGardingHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) noetherGardingNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (NoetherGardingHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) noetherGardingInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (NoetherGardingHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) noetherGardingNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (NoetherGardingHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) noetherGardingModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (NoetherGardingHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) noetherGardingCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (NoetherGardingHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- Irreducible Candidate-A zero-mode packet after Noether has supplied the
operator equations and finite-dimensionality supplies the orthogonal split. -/
structure GlobalCandidateAActualNoetherGardingData4D
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
    (ZeroMode : Type*) [Fintype ZeroMode] where
  modes : GlobalCandidateAActualNoetherModeFamily4D period hPeriod configuration
    data analysis chart sameAction physical ZeroMode
  linearIndependent : LinearIndependent Real
    (finiteKernelNamedVector
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical)
      modes.vector (modes.vector_mem_kernel period hPeriod))
  constant : Real
  constant_pos : 0 < constant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  garding : ∀ current :
      NoetherGardingHilbert period hPeriod configuration data analysis,
    constant * ‖current‖ ^ 2 ≤
      ⟪current,
        globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical current⟫_Real +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪current, modes.vector mode⟫_Real ^ 2
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Insert the Noether-derived annihilation proof into the generic automatic
split/Gårding packet. -/
def GlobalCandidateAActualNoetherGardingData4D.toAutomaticSplit
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
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (input : GlobalCandidateAActualNoetherGardingData4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    FiniteKernelNamedModeAutomaticSplitData
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical) ZeroMode where
  vector := input.modes.vector
  annihilated := input.modes.vector_mem_kernel period hPeriod
  linearIndependent := input.linearIndependent
  constant := input.constant
  constant_pos := input.constant_pos
  defectConstant := input.defectConstant
  defectConstant_nonneg := input.defectConstant_nonneg
  garding := input.garding

/-- Convert the Noether/Gårding data to the existing Candidate-A named Gårding
interface. Hidden modes and the exact finite kernel basis are derived. -/
def GlobalCandidateAActualNoetherGardingData4D.toNamedGarding
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
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (input : GlobalCandidateAActualNoetherGardingData4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    GlobalCandidateAActualKernelNamedGarding4D period hPeriod configuration data
      analysis chart sameAction physical ZeroMode where
  garding := input.toAutomaticSplit.toNoHidden.toNamedGarding
  ll_stationary := input.ll_stationary

/-- Public Noether/Gårding zero-mode checkpoint. -/
def global_candidateA_actual_noether_garding_gate
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
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (input : GlobalCandidateAActualNoetherGardingData4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    PSigma fun _ : GlobalCandidateAActualKernelGap4D period hPeriod configuration
        data analysis chart sameAction physical =>
      Module.finrank Real
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical).ker =
        Fintype.card ZeroMode := by
  let named := input.toNamedGarding period hPeriod
  exact ⟨named.toGap period hPeriod,
    named.kernel_finrank_eq_card period hPeriod⟩

end
end P0EFTJanusProgramPGlobalCandidateAActualNoetherGarding4D
end JanusFormal
