import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricBismutFreed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorTopologicalDeterminantBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaC1CoordinateSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D

/-!
# Reduced terminal geometric-regularity closure for the preferred Candidate-A family

This façade is the preferred family-level endpoint after eliminating all
redundant status packets.  It combines:

* C1 regularity of the actual kernel/complement Fredholm splitting;
* an exact D11 natural elliptic representation of the same Candidate-A Hessian;
* concrete Candidate-A metrics and connection-descent data generated from that
  representation and the existing action geometry;
* the actual Mathlib complex determinant `VectorBundle` and its C1 zeta
  coordinate section;
* the only remaining external geometric comparisons: Bismut--Freed one-form
  versus intrinsic operator trace, and Bismut--Freed curvature versus the local
  families-index curvature.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricRegularityClosure4D

set_option autoImplicit false
set_option maxHeartbeats 42000000
set_option synthInstance.maxHeartbeats 21000000
noncomputable section

open Set Topology MeasureTheory Bundle
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricBismutFreed4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorTopologicalDeterminantBundle4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDerivedQuillenStatus4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaC1CoordinateSection4D
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

/-- Final reduced family-level input. -/
structure GlobalHessianPreferredFiveSectorReducedGeometricRegularityData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) where
  regularity :
    GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D period hPeriod input
  geometry :
    GlobalHessianPreferredFiveSectorReducedGeometricBismutFreedData4D period hPeriod input Base Tangent

/-- Public preferred reduced terminal gate. -/
theorem global_hessian_preferred_five_sector_reduced_geometric_regularity_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorReducedGeometricRegularityData4D period hPeriod input Base Tangent) :
    let fredholm := globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input
    (∀ mode,
      Differentiable Real (fun parameter : Real => input.kernels.vector parameter mode)) ∧
    (∀ parameter,
      closure.geometry.naturalRepresentation.representation.representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    ellipticFamilyInputClosed
      (toEllipticFamilyInputStatus
        (P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalAnalyticUpgrade4D.
          candidateAConcreteNaturalAnalyticUpgrade period hPeriod input
            closure.geometry.naturalRepresentation)) ∧
    Nonempty (VectorBundle Complex Complex fredholm.FullDeterminantFiber) ∧
    Continuous
      (P0EFTJanusProgramPSelfAdjointFredholmZetaTopologicalSection4D.
        fullDeterminantZetaTotalSection fredholm
          input.familyIndex.baseFamily.familyIndex.zetaFamily) ∧
    Differentiable Real
      (fullDeterminantZetaCoordinate fredholm
        input.familyIndex.baseFamily.familyIndex.zetaFamily) ∧
    quillenBismutFreedClosed
      (candidateAOperatorGeneratedQuillenBismutFreedStatus
        period hPeriod input closure.geometry.curvature) ∧
    (∀ parameter,
      pulledGeometricCoefficient closure.geometry.geometry closure.geometry.path parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ parameter,
      geometricFullTensorConnectionAt fredholm
        ((closure.geometry.toEssentialGeometricData period hPeriod input)
          |> essentialToGeometricComparison period hPeriod input
          |> fun comparison => comparison.toPathComparison period hPeriod input)
        parameter
        (relativeHeatMellinZetaFamilyDeterminant
          input.familyIndex.baseFamily.familyIndex.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          input.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily parameter) = 0) ∧
    (∀ base first second,
      closure.geometry.curvature.bismutFreedCurvature base first second =
        closure.geometry.curvature.localFamiliesIndexCurvature base first second) := by
  dsimp
  let fredholm := globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input
  have hRegularity :=
    global_hessian_preferred_five_sector_differentiable_fredholm_splitting_gate
      period hPeriod input closure.regularity
  have hGeometry := closure.geometry.reduced_geometric_bismut_freed_gate period hPeriod input
  have hBundle := global_hessian_preferred_five_sector_topological_determinant_bundle_gate
    period hPeriod input
  have hC1 := self_adjoint_fredholm_zeta_c1_coordinate_section_gate fredholm
    input.familyIndex.baseFamily.familyIndex.zetaFamily
  let essential := closure.geometry.toEssentialGeometricData period hPeriod input
  let comparison := essentialToGeometricComparison period hPeriod input essential
  have hTensor := geometric_bismut_freed_full_tensor_comparison_gate
    fredholm (comparison.toPathComparison period hPeriod input)
  exact ⟨hRegularity.1,
    hGeometry.1,
    hGeometry.2.1,
    hBundle.1,
    hBundle.2.1,
    hC1.1,
    candidateAOperatorGeneratedQuillenBismutFreedStatus_closed
      period hPeriod input closure.geometry.curvature,
    hGeometry.2.2.1,
    hTensor.2,
    hGeometry.2.2.2⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricRegularityClosure4D
end JanusFormal
