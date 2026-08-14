import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreed4D

/-!
# Terminal geometric Bismut--Freed comparison interface for Candidate-A

This gate joins the exact Candidate-A full Fredholm--zeta determinant line to
the D11 natural-family Quillen geometry.  It deliberately makes the two genuine
geometric theorems visible: equality of the pulled connection one-form with the
intrinsic logarithmic trace, and equality of the Bismut--Freed curvature with
the local families-index curvature.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreedClosure4D

set_option autoImplicit false
set_option maxHeartbeats 34000000
set_option synthInstance.maxHeartbeats 17000000

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreed4D
open P0EFTJanusProgramPGeometricBismutFreedPathComparison4D
open P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D
open P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D
open P0EFTJanusNaturalFamilyQuillenBridge
open P0EFTJanusQuillenFamilyCanonicity
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

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

/-- Public Candidate-A geometric Bismut--Freed/families-index checkpoint. -/
theorem global_hessian_preferred_five_sector_geometric_bismut_freed_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (geometric : GlobalHessianPreferredFiveSectorGeometricBismutFreedComparison4D
      period hPeriod input Base Tangent) :
    ellipticFamilyInputClosed
        (toEllipticFamilyInputStatus geometric.analyticFamily) ∧
    quillenBismutFreedClosed geometric.quillen ∧
    (∀ parameter value derivative,
      geometricFullTensorConnectionAt
          (globalHessianPreferredFiveSectorFredholmDeterminantFamily
            period hPeriod input)
          (geometric.toPathComparison period hPeriod input)
          parameter value derivative =
        P0EFTJanusProgramPFullTensorZetaConnection4D.fullTensorZetaConnectionAt
          (globalHessianPreferredFiveSectorFredholmDeterminantFamily
            period hPeriod input)
          input.familyIndex.baseFamily.familyIndex.zetaFamily
          parameter value derivative) ∧
    (∀ parameter,
      geometricFullTensorConnectionAt
          (globalHessianPreferredFiveSectorFredholmDeterminantFamily
            period hPeriod input)
          (geometric.toPathComparison period hPeriod input)
          parameter
          (relativeHeatMellinZetaFamilyDeterminant
            input.familyIndex.baseFamily.familyIndex.zetaFamily parameter)
          (relativeZetaDeterminantCoordinateDerivative
            input.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily
              parameter) = 0) ∧
    (∀ base first second,
      geometric.curvature.bismutFreedCurvature base first second =
        geometric.curvature.localFamiliesIndexCurvature base first second) := by
  let pathComparison := geometric.toPathComparison period hPeriod input
  have hPath :=
    geometric_operator_bismut_freed_path_comparison_gate pathComparison
  have hTensor :=
    geometric_bismut_freed_full_tensor_comparison_gate
      (globalHessianPreferredFiveSectorFredholmDeterminantFamily
        period hPeriod input)
      pathComparison
  have hCurvature :=
    geometric_bismut_freed_families_index_comparison_gate
      (geometric.toFamiliesIndexComparison period hPeriod input)
  exact ⟨hPath.1, hPath.2.1, hTensor.1, hTensor.2, hCurvature.2.1⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreedClosure4D
end JanusFormal
