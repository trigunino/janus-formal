import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousSum4D

/-!
# Canonical core forms for the seven physical Candidate-A blocks

The smooth-core form of each physical block is not arbitrary: it is the second
Fréchet derivative of the corresponding action in the actual local chart,
pulled back along the typed diagonal-core tangent map.  This module fixes those
seven forms canonically.  An H11 input now supplies only their continuous
extensions and exact restriction identities.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 1300000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousSum4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

private abbrev PhysicalCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev PhysicalHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The actual local action blocks attached to the chart base point. -/
def globalCandidateASevenPhysicalLocalBlocks
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) : FullCoupledActionBlocks chart.Model :=
  globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure

/-- Select one of the seven retained physical action functions. -/
def globalCandidateAPhysicalBlockAction
    {Model : Type*}
    (blocks : FullCoupledActionBlocks Model) :
    GlobalCandidateAPhysicalBlock → Model → Real
  | .candidateA => blocks.candidateA
  | .robin => blocks.robin
  | .einsteinHilbertPlus => blocks.einsteinHilbertPlus
  | .einsteinHilbertMinus => blocks.einsteinHilbertMinus
  | .maxwellPlus => blocks.maxwellPlus
  | .maxwellMinus => blocks.maxwellMinus
  | .finiteBV => blocks.finiteBV

/-- Genuine local second Fréchet derivative of one selected physical block. -/
def globalCandidateAPhysicalBlockLocalHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameActionBase : chart.Model)
    (block : GlobalCandidateAPhysicalBlock) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  fderiv Real
    (fun state => fderiv Real
      (globalCandidateAPhysicalBlockAction
        (globalCandidateASevenPhysicalLocalBlocks period hPeriod chart) block)
      state)
    sameActionBase

/-- Canonical restriction of one physical block Hessian to the typed diagonal
smooth core. -/
def globalCandidateAPhysicalBlockCanonicalCoreForm
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
    (block : GlobalCandidateAPhysicalBlock) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalCore period hPeriod analysis →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun first second =>
      globalCandidateAPhysicalBlockLocalHessian period hPeriod chart
        sameAction.chartBridge.basePoint block
        (sameAction.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis first))
        (sameAction.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis second)))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)

/-- Canonical extension packet: only the completed forms and their exact core
restrictions are supplied. -/
structure GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
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
      period hPeriod configuration data analysis chart) : Type where
  extension : GlobalCandidateAPhysicalBlock →
    PhysicalHilbert period hPeriod configuration data analysis →L[Real]
      PhysicalHilbert period hPeriod configuration data analysis →L[Real] Real
  extension_agrees : ∀ block first second,
    extension block
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first)
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second) =
      globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
        configuration data analysis chart sameAction block first second
  symmetric : ∀ block first second,
    extension block first second = extension block second first
  reconstruct : ∀ first second : PhysicalCore period hPeriod analysis,
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
        data analysis chart sameAction first second =
      ∑ block : GlobalCandidateAPhysicalBlock,
        globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
          configuration data analysis chart sameAction block first second

/-- Forget the canonical construction into the previous continuous-extension
packet. -/
def GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D.toContinuous
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
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
      period hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalContinuousBlockExtensions4D period hPeriod
      configuration data analysis chart sameAction where
  coreForm := globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
    configuration data analysis chart sameAction
  reconstruct := extensions.reconstruct
  extension := extensions.extension
  extension_agrees := extensions.extension_agrees

/-- Forget into the symmetric continuous-extension packet. -/
def GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D.toSymmetric
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
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
      period hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalSymmetricContinuousExtensions4D period hPeriod
      configuration data analysis chart sameAction where
  extensions := extensions.toContinuous period hPeriod
  symmetric := extensions.symmetric

/-- Public canonical H11 extension gate. -/
def candidate_a_seven_physical_canonical_extensions_gate
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
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
      period hPeriod configuration data analysis chart sameAction) :=
  candidate_a_seven_physical_continuous_sum_gate period hPeriod configuration
    data analysis chart sameAction (extensions.toSymmetric period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
end JanusFormal
