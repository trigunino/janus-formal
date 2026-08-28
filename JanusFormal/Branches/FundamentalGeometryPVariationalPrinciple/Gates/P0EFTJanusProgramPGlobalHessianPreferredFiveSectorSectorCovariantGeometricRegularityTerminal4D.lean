import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreed4D

/-!
# Sector-covariant terminal frontier for Candidate-A

This terminal strengthens the sector-preserving D11 frontier by requiring the
represented geometric pullbacks themselves to preserve all five physical
sectors.  Forgetting this covariance witness recovers the previous terminal, so
all Fredholm, determinant, zeta and Bismut--Freed constructions remain the same
objects.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminal4D

set_option autoImplicit false
set_option maxHeartbeats 46000000
set_option synthInstance.maxHeartbeats 23000000
noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminal4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreed4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

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

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    [LinearOrder ZeroMode]
    {fold : Fold} {Index Base Tangent : Type*}

/-- Preferred terminal input with sector-covariant D11 geometry. -/
structure GlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminalData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (Base Tangent : Type*) where
  regularity :
    GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
      period hPeriod input
  geometry :
    GlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreedData4D
      period hPeriod input Base Tangent

namespace GlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminalData4D

/-- Forget only pullback covariance and recover the sector-reduced terminal. -/
def toSectorReducedTerminalData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (closure : GlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminalData4D
      period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminalData4D
      period hPeriod input Base Tangent where
  regularity := closure.regularity
  geometry := closure.geometry.toSectorReducedGeometricData period hPeriod input

/-- Public preferred sector-covariant terminal checkpoint. -/
theorem sector_covariant_geometric_regularity_terminal_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (closure : GlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminalData4D
      period hPeriod input Base Tangent) :
    Nonempty
      (GlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminalData4D
        period hPeriod input Base Tangent) ∧
    (∀ {first second : Real}
      (morphism : P0EFTJanusSpinCImmersionCategory.AdmissibleMorphism
        closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          immersionCategory
        (closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          representation.objectAt first)
        (closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          representation.objectAt second))
      (sector : FivePhysicalSector)
      (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
        configuration data analysis),
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
          sectorProjector sector
          (closure.geometry.naturalCovariance.sectorRepresentation.bridge.
            representation.representedSourcePullback morphism state) =
        closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          representation.representedSourcePullback morphism
          ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
            sectorProjector sector state)) ∧
    (∀ {first second : Real}
      (morphism : P0EFTJanusSpinCImmersionCategory.AdmissibleMorphism
        closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          immersionCategory
        (closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          representation.objectAt first)
        (closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          representation.objectAt second))
      (sector : FivePhysicalSector)
      (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
        configuration data analysis),
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
          sectorProjector sector
          (closure.geometry.naturalCovariance.sectorRepresentation.bridge.
            representation.representedTargetPullback morphism state) =
        closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          representation.representedTargetPullback morphism
          ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
            sectorProjector sector state)) ∧
    (∀ parameter,
      closure.geometry.naturalCovariance.sectorRepresentation.bridge.
          representation.representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) :=
  ⟨⟨closure.toSectorReducedTerminalData period hPeriod input⟩,
    closure.geometry.naturalCovariance.pullback.source_commutes,
    closure.geometry.naturalCovariance.pullback.target_commutes,
    closure.geometry.naturalCovariance.sectorRepresentation.
      representedNaturalOperator_eq_actual period hPeriod input⟩

end GlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminalData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminal4D
end JanusFormal
