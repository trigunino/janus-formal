import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaTopologicalSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTransportHomeomorph4D

/-!
# Topological full determinant bundle of the preferred Candidate-A family

The actual Candidate-A Fredholm family now inherits the generic full
Fredholm--zeta complex vector bundle.  Its zeta determinant is a continuous
dependent section and the canonical family transports are fibre
homeomorphisms.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorTopologicalDeterminantBundle4D

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 16000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTopologicalBundle4D
open P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTransportHomeomorph4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaTopologicalSection4D
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
    {fold : Fold} {Index : Type*}

/-- Public topological full determinant-bundle checkpoint for Candidate-A. -/
theorem global_hessian_preferred_five_sector_topological_determinant_bundle_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    let fredholm := globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input
    Nonempty (VectorBundle Complex Complex fredholm.FullDeterminantFiber) ∧
    Continuous
      (fullDeterminantZetaTotalSection fredholm
        input.familyIndex.baseFamily.familyIndex.zetaFamily) ∧
    (∀ parameter,
      fredholm.fullTensorDeterminantCoordinateEquiv parameter
          (fullDeterminantZetaSection fredholm
            input.familyIndex.baseFamily.familyIndex.zetaFamily parameter) =
        P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
          relativeHeatMellinZetaFamilyDeterminant
            input.familyIndex.baseFamily.familyIndex.zetaFamily parameter) := by
  dsimp
  let fredholm := globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input
  have hBundle := fredholm.self_adjoint_fredholm_full_determinant_topological_bundle_gate
  have hSection := self_adjoint_fredholm_zeta_topological_section_gate fredholm
    input.familyIndex.baseFamily.familyIndex.zetaFamily
  exact ⟨hBundle.1, hSection.1, hSection.2⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorTopologicalDeterminantBundle4D
end JanusFormal
