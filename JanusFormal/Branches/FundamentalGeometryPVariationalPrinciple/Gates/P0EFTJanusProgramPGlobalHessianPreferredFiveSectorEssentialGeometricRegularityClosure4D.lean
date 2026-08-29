import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricRegularityClosure4D

/-!
# Essential terminal geometric-regularity frontier for Candidate-A

After the determinant tensor line and the operator-generated Quillen package are
constructed, the preferred terminal family interface has only two kinds of
input left:

* C1 regularity of the genuine Fredholm splitting;
* the D11 natural-family geometry, with connection and curvature comparison.

The Quillen status itself is generated from Program P and is not supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricRegularityClosure4D

set_option autoImplicit false
set_option maxHeartbeats 38000000
set_option synthInstance.maxHeartbeats 19000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricRegularityClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreed4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D
open P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D
open P0EFTJanusNaturalFamilyQuillenBridge
open P0EFTJanusQuillenFamilyCanonicity
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance effectiveQuotientChartedSpace : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveQuotientMeasurableSpace : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance effectiveQuotientBorelSpace : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D period hPeriod configuration data analysis
      (diracGreenClosureMatterRealization period hPeriod couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]
    {fold : Fold} {Index Base Tangent : Type*}

/-- Preferred final family input after eliminating the redundant Quillen-status
hypothesis. -/
structure GlobalHessianPreferredFiveSectorEssentialGeometricRegularityData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) : Prop where
  regularity : GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D period hPeriod input
  geometry : GlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedData4D period hPeriod input Base Tangent

/-- Forget to the older joint interface only after deriving its Quillen status
from Program P. -/
def toGeometricRegularityData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorEssentialGeometricRegularityData4D period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorGeometricRegularityData4D period hPeriod input Base Tangent where
  regularity := closure.regularity
  geometry := essentialToGeometricComparison period hPeriod input closure.geometry

/-- Public essential terminal gate. -/
theorem global_hessian_preferred_five_sector_essential_geometric_regularity_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorEssentialGeometricRegularityData4D period hPeriod input Base Tangent) :
    (∀ mode, Differentiable Real (fun parameter : Real => input.kernels.vector parameter mode)) ∧
    ellipticFamilyInputClosed (toEllipticFamilyInputStatus closure.geometry.analyticFamily) ∧
    quillenBismutFreedClosed
      (candidateAOperatorGeneratedQuillenBismutFreedStatus period hPeriod input closure.geometry.curvature) ∧
    (∀ parameter,
      geometricFullTensorConnectionAt
        (P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D.
          globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input)
        ((essentialToGeometricComparison period hPeriod input closure.geometry).toPathComparison period hPeriod input)
        parameter
        (relativeHeatMellinZetaFamilyDeterminant input.familyIndex.baseFamily.familyIndex.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative input.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily parameter) = 0) ∧
    (∀ base first second,
      closure.geometry.curvature.bismutFreedCurvature base first second =
      closure.geometry.curvature.localFamiliesIndexCurvature base first second) := by
  have h := global_hessian_preferred_five_sector_geometric_regularity_gate
    period hPeriod input (toGeometricRegularityData period hPeriod input closure)
  exact ⟨h.1, h.2.1,
    candidateAOperatorGeneratedQuillenBismutFreedStatus_closed period hPeriod input closure.geometry.curvature,
    h.2.2.2.1, h.2.2.2.2⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricRegularityClosure4D
end JanusFormal
