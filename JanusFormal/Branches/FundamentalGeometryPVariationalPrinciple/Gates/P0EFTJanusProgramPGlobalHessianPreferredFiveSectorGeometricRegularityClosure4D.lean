import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreedClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D

/-!
# Geometric-regularity closure of the preferred Candidate-A determinant family

This façade joins the two genuine family-level inputs left after the full
Fredholm--zeta tensor line has been constructed:

* C1 regularity of the actual kernel/complement Fredholm splitting;
* geometric identification of the operator-trace connection and curvature with
  the D11 Quillen/Bismut--Freed families-index package.

No scalar circle surrogate is used in place of the higher-dimensional
families-index curvature.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricRegularityClosure4D

set_option autoImplicit false
set_option maxHeartbeats 36000000
set_option synthInstance.maxHeartbeats 18000000

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreed4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreedClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
open P0EFTJanusNaturalFamilyQuillenBridge
open P0EFTJanusQuillenFamilyCanonicity
open P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D
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

/-- The two remaining genuine family-level inputs packaged together. -/
structure GlobalHessianPreferredFiveSectorGeometricRegularityData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) where
  regularity :
    GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
      period hPeriod input
  geometry :
    GlobalHessianPreferredFiveSectorGeometricBismutFreedComparison4D
      period hPeriod input Base Tangent

/-- Public joint geometric/regularity checkpoint for the preferred Candidate-A
full determinant family. -/
theorem global_hessian_preferred_five_sector_geometric_regularity_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorGeometricRegularityData4D
      period hPeriod input Base Tangent) :
    (∀ mode,
      Differentiable Real
        (fun parameter : Real => input.kernels.vector parameter mode)) ∧
    ellipticFamilyInputClosed
      (toEllipticFamilyInputStatus closure.geometry.analyticFamily) ∧
    quillenBismutFreedClosed closure.geometry.quillen ∧
    (∀ parameter,
      geometricFullTensorConnectionAt
          (P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D.
            globalHessianPreferredFiveSectorFredholmDeterminantFamily
              period hPeriod input)
          (closure.geometry.toPathComparison period hPeriod input)
          parameter
          (relativeHeatMellinZetaFamilyDeterminant
            input.familyIndex.baseFamily.familyIndex.zetaFamily parameter)
          (relativeZetaDeterminantCoordinateDerivative
            input.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily
              parameter) = 0) ∧
    (∀ base first second,
      closure.geometry.curvature.bismutFreedCurvature base first second =
        closure.geometry.curvature.localFamiliesIndexCurvature
          base first second) := by
  have hRegularity :=
    global_hessian_preferred_five_sector_differentiable_fredholm_splitting_gate
      period hPeriod input closure.regularity
  have hGeometry :=
    global_hessian_preferred_five_sector_geometric_bismut_freed_gate
      period hPeriod input closure.geometry
  exact ⟨hRegularity.1,
    hGeometry.1,
    hGeometry.2.1,
    hGeometry.2.2.2.1,
    hGeometry.2.2.2.2⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricRegularityClosure4D
end JanusFormal
