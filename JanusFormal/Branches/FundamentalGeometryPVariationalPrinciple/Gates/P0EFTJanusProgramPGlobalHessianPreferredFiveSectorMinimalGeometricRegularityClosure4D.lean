import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMinimalGeometricBismutFreed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricRegularityClosure4D

/-!
# Minimal terminal geometric-regularity frontier for Candidate-A

This is the preferred family-level interface after eliminating both the free
Quillen status and the free D11 analytic-family status.

The only inputs retained are:

* C1 regularity of the actual kernel/complement Fredholm splitting;
* an exact D11 natural elliptic representation of the same Candidate-A Hessian;
* the remaining natural metric/connection geometry;
* the geometric/operator Bismut--Freed one-form identity;
* the multidimensional local families-index curvature identity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMinimalGeometricRegularityClosure4D

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 20000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMinimalGeometricBismutFreed4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricRegularityClosure4D
open P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusNaturalFamilyQuillenBridge
open P0EFTJanusQuillenFamilyCanonicity
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

/-- Final reduced family-level inputs. -/
structure GlobalHessianPreferredFiveSectorMinimalGeometricRegularityData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) where
  regularity : GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D period hPeriod input
  geometry : GlobalHessianPreferredFiveSectorMinimalGeometricBismutFreedData4D period hPeriod input Base Tangent

/-- Convert the minimal packet to the previous essential terminal packet. -/
def toEssentialGeometricRegularityData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorMinimalGeometricRegularityData4D period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorEssentialGeometricRegularityData4D period hPeriod input Base Tangent where
  regularity := closure.regularity
  geometry := closure.geometry.toEssentialGeometricData period hPeriod input

/-- Public minimal terminal gate. -/
theorem global_hessian_preferred_five_sector_minimal_geometric_regularity_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorMinimalGeometricRegularityData4D period hPeriod input Base Tangent) :
    (∀ mode, Differentiable Real (fun parameter : Real => input.kernels.vector parameter mode)) ∧
    (∀ parameter,
      closure.geometry.naturalRepresentation.representation.representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    ellipticFamilyInputClosed
      (toEllipticFamilyInputStatus
        (candidateANaturalAnalyticPathUpgrade period hPeriod input
          closure.geometry.naturalRepresentation closure.geometry.naturalPathGeometry)) ∧
    quillenBismutFreedClosed
      (P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDerivedQuillenStatus4D.
        candidateAOperatorGeneratedQuillenBismutFreedStatus
          period hPeriod input closure.geometry.curvature) ∧
    (∀ parameter,
      pulledGeometricCoefficient closure.geometry.geometry closure.geometry.path parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      closure.geometry.curvature.bismutFreedCurvature base first second =
        closure.geometry.curvature.localFamiliesIndexCurvature base first second) := by
  have hRegularity :=
    global_hessian_preferred_five_sector_differentiable_fredholm_splitting_gate
      period hPeriod input closure.regularity
  have hMinimal := closure.geometry.minimal_geometric_bismut_freed_gate period hPeriod input
  have hEssential :=
    global_hessian_preferred_five_sector_essential_geometric_regularity_gate
      period hPeriod input (toEssentialGeometricRegularityData period hPeriod input closure)
  exact ⟨hRegularity.1,
    hMinimal.1,
    hMinimal.2.1,
    hEssential.2.2.1,
    hMinimal.2.2.1,
    hMinimal.2.2.2⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMinimalGeometricRegularityClosure4D
end JanusFormal
