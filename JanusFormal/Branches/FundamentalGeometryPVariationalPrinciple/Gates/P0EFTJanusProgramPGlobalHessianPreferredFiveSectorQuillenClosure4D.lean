import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenMetricAnchor4D

/-!
# Preferred five-sector H14--Quillen closure

The preferred Quillen atlas already contains the H14, reduced Green, resolvent,
stability, relative trace, scalar Mellin determinant, differentiable zeta
family, circle connection and multi-chart cocycle.  This final façade adds the
actual periodic determinant-line element and exports the geometric consequences
of the explicit circle connection:

* the anchor is nonzero and has the correct finite-part Quillen norm;
* the selected atlas base coordinate is the anchor coordinate;
* the circle connection is flat;
* its parallel transport is metric preserving;
* its closed holonomy is unitary and is computed by transport followed by the
  exact large-gauge clutching.

No new analytic input is introduced at this layer.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenClosure4D

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 8000000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusCircleDeterminantLineFamily
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenAtlas4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenMetricAnchor4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
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

/-- Terminal preferred H14--Quillen certificate. -/
structure GlobalHessianPreferredFiveSectorQuillenClosureCertificate4D
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
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorQuillenAtlas4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) : Prop where
  quillenAtlas : GlobalHessianPreferredFiveSectorQuillenAtlasOutput4D input
  anchorCoordinate :
    circleDeterminantCoordinate fold periodicTwist
        (globalHessianPreferredFiveSectorQuillenMetricAnchor fold
          input.spectralFamily.basepoint) =
      input.spectralFamily.basepoint.determinant
  anchorAtlasAgreement :
    circleDeterminantCoordinate fold periodicTwist
        (globalHessianPreferredFiveSectorQuillenMetricAnchor fold
          input.spectralFamily.basepoint) =
      relativeZetaLocalDeterminant input.atlas input.baseIndex 0
  anchorNormSq :
    circleQuillenNormSq fold periodicTwist
        (globalHessianPreferredFiveSectorQuillenMetricAnchor fold
          input.spectralFamily.basepoint) =
      (relativeHeatFinitePartDeterminant
        input.spectralFamily.basepoint.finitePart) ^ 2
  anchorNonzero :
    globalHessianPreferredFiveSectorQuillenMetricAnchor fold
      input.spectralFamily.basepoint ≠ 0
  connectionFlat :
    circleQuillenConnectionCurvature fold = fun _ _ => 0
  transportIsometry : ∀ first second value,
    circleQuillenCoordinateNormSq fold second
        (circleQuillenParallelTransport fold first second value) =
      circleQuillenCoordinateNormSq fold first value
  closedHolonomyUnitary : ‖circleQuillenClosedHolonomy fold‖ = 1
  transportThenClutching : ∀ value,
    circleLargeGaugeFrameCoordinateTransition fold
        (circleQuillenParallelTransport fold 0 1 value) =
      circleQuillenClosedHolonomy fold * value

/-- Construct the terminal certificate without additional hypotheses. -/
def globalHessianPreferredFiveSectorQuillenClosureCertificate
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
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorQuillenAtlas4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    GlobalHessianPreferredFiveSectorQuillenClosureCertificate4D input where
  quillenAtlas := input.close
  anchorCoordinate :=
    globalHessianPreferredFiveSectorQuillenMetricAnchor_coordinate fold
      input.spectralFamily.basepoint
  anchorAtlasAgreement := by
    rw [globalHessianPreferredFiveSectorQuillenMetricAnchor_coordinate]
    exact (input.toGeneric.atlas_basepoint_eq_scalar).symm
  anchorNormSq :=
    globalHessianPreferredFiveSectorQuillenMetricAnchor_normSq fold
      input.spectralFamily.basepoint
  anchorNonzero :=
    globalHessianPreferredFiveSectorQuillenMetricAnchor_ne_zero fold
      input.spectralFamily.basepoint
  connectionFlat := circleQuillenConnection_is_flat fold
  transportIsometry := circleQuillenParallelTransport_isometry fold
  closedHolonomyUnitary := circleQuillenClosedHolonomy_norm_one fold
  transportThenClutching := circleQuillen_transport_then_clutching fold

/-- Public terminal preferred H14--Quillen checkpoint. -/
theorem global_hessian_preferred_five_sector_quillen_closure_gate
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
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorQuillenAtlas4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    GlobalHessianPreferredFiveSectorQuillenClosureCertificate4D input :=
  globalHessianPreferredFiveSectorQuillenClosureCertificate input

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenClosure4D
end JanusFormal
