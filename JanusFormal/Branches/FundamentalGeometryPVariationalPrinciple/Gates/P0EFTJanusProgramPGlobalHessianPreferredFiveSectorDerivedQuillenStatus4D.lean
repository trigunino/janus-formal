import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorTopologicalDeterminantBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaParallel4D

/-!
# Quillen/Bismut--Freed status derived from the preferred Candidate-A family

The D10/D11 `QuillenBismutFreedStatus` is a logical interface.  For the
preferred Candidate-A family most of that interface is no longer external:
the actual full Fredholm--zeta complex vector bundle, zeta/finite-part metric,
intrinsic trace connection, operator-generated spectral-cut descent and circle
holonomy are already constructed in Program P.

Only the genuinely higher-dimensional geometric curvature theorem remains an
independent geometric input here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDerivedQuillenStatus4D

set_option autoImplicit false
set_option maxHeartbeats 34000000
set_option synthInstance.maxHeartbeats 17000000

noncomputable section

open Set Topology MeasureTheory Bundle
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusCircleQuillenMetricFlatConnection
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorTopologicalDeterminantBundle4D
open P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D
open P0EFTJanusProgramPFullTensorZetaConnection4D
open P0EFTJanusProgramPFullTensorZetaParallel4D
open P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTopologicalBundle4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D
open P0EFTJanusQuillenFamilyCanonicity
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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

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

/-- The D10/D11 Quillen status instantiated by the actual Candidate-A
constructions.  In particular, `determinantLineConstructed` now means that the
dependent full determinant fibres carry an actual Mathlib complex vector-bundle
structure, not merely that one pointwise frame is nonzero. -/
def candidateAOperatorGeneratedQuillenBismutFreedStatus
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (curvature : GeometricFamiliesIndexCurvatureData Base Tangent) :
    QuillenBismutFreedStatus where
  determinantLineConstructed :=
    let fredholm :=
      globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input
    Nonempty (VectorBundle Complex Complex fredholm.FullDeterminantFiber)
  quillenMetricConstructed := ∀ parameter,
    ‖relativeHeatMellinZetaFamilyDeterminant
        input.familyIndex.baseFamily.familyIndex.zetaFamily parameter‖ =
      P0EFTJanusProgramPRelativeHeatFinitePartFamily4D.
        relativeHeatFinitePartDeterminantFamily
          input.familyIndex.baseFamily.familyIndex.zetaFamily.finitePartFamily
          parameter
  bismutFreedConnectionConstructed := ∀ parameter,
    fullTensorZetaConnectionAt
        (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input)
        input.familyIndex.baseFamily.familyIndex.zetaFamily parameter
        (relativeHeatMellinZetaFamilyDeterminant
          input.familyIndex.baseFamily.familyIndex.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          input.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily
            parameter) = 0
  localFamiliesIndexCurvatureProved := ∀ base first second,
    curvature.bismutFreedCurvature base first second =
      curvature.localFamiliesIndexCurvature base first second
  holonomyFormulaProved :=
    circleQuillenClosedHolonomy fold =
      relativeZetaFinitePartPhase
          input.familyIndex.baseFamily.familyIndex.zetaFamily.toFinitePartComparison 0 /
        relativeZetaFinitePartPhase
          input.familyIndex.baseFamily.familyIndex.zetaFamily.toFinitePartComparison 1
  gaugeEquivariantDescentProved :=
    RelativeZetaDeterminantLineAtlasCertificate
      input.familyIndex.referenceAtlas.zetaAtlas

/-- Every non-curvature field of the D10/D11 status is already a theorem of the
preferred Program-P family; the curvature field is exactly the supplied
families-index comparison. -/
theorem candidateAOperatorGeneratedQuillenBismutFreedStatus_closed
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (curvature : GeometricFamiliesIndexCurvatureData Base Tangent) :
    quillenBismutFreedClosed
      (candidateAOperatorGeneratedQuillenBismutFreedStatus
        period hPeriod input curvature) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (global_hessian_preferred_five_sector_topological_determinant_bundle_gate
        period hPeriod input).1
  · exact norm_relativeHeatMellinZetaFamilyDeterminant
      input.familyIndex.baseFamily.familyIndex.zetaFamily
  · exact fullTensorZetaSection_parallel
      (globalHessianPreferredFiveSectorFredholmDeterminantFamily
        period hPeriod input)
      input.familyIndex.baseFamily.familyIndex.zetaFamily
  · exact curvature.curvature_agreement
  · exact input.familyIndex.baseFamily.toCircleTraceBridge.closedHolonomy_eq_phase_ratio
  · exact input.familyIndex.referenceAtlas.determinantLineAtlasCertificate

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDerivedQuillenStatus4D
end JanusFormal
