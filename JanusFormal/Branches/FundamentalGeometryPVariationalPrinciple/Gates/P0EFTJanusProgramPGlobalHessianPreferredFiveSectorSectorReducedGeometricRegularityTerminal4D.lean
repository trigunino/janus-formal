import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricRegularityTerminal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreed4D

/-!
# Sector-preserving terminal geometric frontier for Candidate-A

This is the preferred refinement of the stable reduced terminal.  It keeps the
same C1 Fredholm-splitting and Bismut--Freed/families-index obligations, but the
D11 representation is additionally required to factor through the literal
five-sector Hilbert decomposition already used by H12/H14.

Forgetting that factorization witness recovers the previous stable terminal,
so no determinant, trace, connection or operator is rebuilt.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminal4D

set_option autoImplicit false
set_option maxHeartbeats 44000000
set_option synthInstance.maxHeartbeats 22000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricRegularityTerminal4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreed4D
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

/-- Preferred terminal input: C1 Fredholm splitting plus sector-preserving D11
geometric comparison. -/
structure GlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminalData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (Base Tangent : Type*) where
  regularity :
    GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
      period hPeriod input
  geometry :
    GlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreedData4D
      period hPeriod input Base Tangent

namespace GlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminalData4D

/-- Forget only sector-factorization and recover the already established stable
terminal input. -/
def toReducedTerminalData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (closure : GlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminalData4D
      period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorReducedGeometricRegularityTerminalData4D
      period hPeriod input Base Tangent where
  regularity := closure.regularity
  geometry := closure.geometry.toReducedGeometricData period hPeriod input

/-- All earlier terminal consequences remain available, while source/target D11
coordinates are now certified to use the physical Candidate-A sectors. -/
theorem sector_reduced_geometric_regularity_terminal_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (closure : GlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminalData4D
      period hPeriod input Base Tangent) :
    Nonempty
      (GlobalHessianPreferredFiveSectorReducedGeometricRegularityTerminalData4D
        period hPeriod input Base Tangent) ∧
    (∀ parameter,
      closure.geometry.sectorRepresentation.bridge.representation.sourceEquiv
          parameter =
        (closure.geometry.sectorRepresentation.sectorRefinement.sourceProductEquiv
          parameter).trans
          ((closure.geometry.sectorRepresentation.sectorRefinement.
            sourceSectorCoordinates parameter).ambientEquiv
              (preferredCandidateAFiveSectorHilbertCoordinates
                period hPeriod input))) ∧
    (∀ parameter,
      closure.geometry.sectorRepresentation.bridge.representation.targetEquiv
          parameter =
        (closure.geometry.sectorRepresentation.sectorRefinement.targetProductEquiv
          parameter).trans
          ((closure.geometry.sectorRepresentation.sectorRefinement.
            targetSectorCoordinates parameter).ambientEquiv
              (preferredCandidateAFiveSectorHilbertCoordinates
                period hPeriod input))) ∧
    (∀ parameter,
      closure.geometry.sectorRepresentation.bridge.representation.
          representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) :=
  ⟨⟨closure.toReducedTerminalData period hPeriod input⟩,
    closure.geometry.sectorRepresentation.sectorRefinement.sourceEquiv_agreement,
    closure.geometry.sectorRepresentation.sectorRefinement.targetEquiv_agreement,
    closure.geometry.sectorRepresentation.representedNaturalOperator_eq_actual
      period hPeriod input⟩

end GlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminalData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricRegularityTerminal4D
end JanusFormal
