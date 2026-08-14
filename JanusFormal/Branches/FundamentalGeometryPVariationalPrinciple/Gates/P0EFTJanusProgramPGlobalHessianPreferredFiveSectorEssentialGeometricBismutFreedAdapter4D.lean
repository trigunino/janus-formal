import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreed4D

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreed4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDerivedQuillenStatus4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreed4D
open P0EFTJanusQuillenFamilyCanonicity
open P0EFTJanusNaturalFamilyQuillenBridge
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

/-- Recover the older full comparison packet, deriving its Quillen status from
Program P rather than accepting it as an independent input. -/
def essentialToGeometricComparison
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (essential : GlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedData4D period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorGeometricBismutFreedComparison4D period hPeriod input Base Tangent where
  analyticFamily := essential.analyticFamily
  analyticFamilyClosed := essential.analyticFamilyClosed
  quillen := candidateAOperatorGeneratedQuillenBismutFreedStatus period hPeriod input essential.curvature
  quillenClosed := candidateAOperatorGeneratedQuillenBismutFreedStatus_closed period hPeriod input essential.curvature
  geometry := essential.geometry
  path := essential.path
  coefficient_agreement := essential.coefficient_agreement
  curvature := essential.curvature

/-- The reduced interface contains exactly the inputs which remain genuinely
external after the Program-P Quillen construction. -/
theorem essential_geometric_bismut_freed_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (essential : GlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedData4D period hPeriod input Base Tangent) :
    ellipticFamilyInputClosed (toEllipticFamilyInputStatus essential.analyticFamily) ∧
    quillenBismutFreedClosed
      (candidateAOperatorGeneratedQuillenBismutFreedStatus period hPeriod input essential.curvature) ∧
    (∀ parameter,
      P0EFTJanusProgramPGeometricBismutFreedPathComparison4D.pulledGeometricCoefficient
        essential.geometry essential.path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      essential.curvature.bismutFreedCurvature base first second =
      essential.curvature.localFamiliesIndexCurvature base first second) :=
  ⟨essential.analyticFamilyClosed,
    candidateAOperatorGeneratedQuillenBismutFreedStatus_closed period hPeriod input essential.curvature,
    essential.coefficient_agreement,
    essential.curvature.curvature_agreement⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D
end JanusFormal
