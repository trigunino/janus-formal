import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D

/-!
# Full split Fredholm-determinant closure for the preferred Candidate-A family

This terminal façade combines, without identifying unlike objects:

* the actual one-dimensional real Fredholm line
  `Hom(det coker H_a, det ker H_a)`;
* its named nonzero source and target volumes;
* the complex reduced Mellin/zeta determinant of the invertible complement;
* the intrinsic Bismut--Freed parallelism and reference-generated atlas;
* the exact action-generator basis at the physical basepoint.

The result is a complete split Fredholm determinant package.  The remaining
geometric comparison is the complexification/tensor-product theorem that turns
this split packet into one complex determinant-line bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFullFredholmDeterminantClosure4D

set_option autoImplicit false
set_option maxHeartbeats 28000000
set_option synthInstance.maxHeartbeats 14000000

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
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
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

/-- Terminal split Fredholm determinant certificate. -/
structure GlobalHessianPreferredFiveSectorFullFredholmDeterminantCertificate4D
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
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) : Prop where
  determinantFamily :
    GlobalHessianPreferredFiveSectorFredholmDeterminantFamilyOutput4D period
      hPeriod input
  namedSourceVolume : ∀ parameter,
    cokernelNamedVolume
        (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod
          input) parameter ≠ 0
  frameNormalization : ∀ parameter,
    (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod
        input).determinantFrame parameter
        (cokernelNamedVolume
          (globalHessianPreferredFiveSectorFredholmDeterminantFamily period
            hPeriod input) parameter) =
      P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D.
        finiteKernelNamedVolume input.kernels parameter
  basepointActionBasis : ∀ mode,
    input.kernels.vector 0 mode =
      input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.
        closure.frontier.generators.translations.vector mode
  reducedDeterminant_nonzero : ∀ parameter,
    relativeHeatMellinZetaFamilyDeterminant
      input.familyIndex.baseFamily.familyIndex.zetaFamily parameter ≠ 0
  reducedDeterminant_parallel : ∀ parameter,
    input.familyIndex.baseFamily.familyIndex.toBismutFreed.connectionAt parameter
        (relativeHeatMellinZetaFamilyDeterminant
          input.familyIndex.baseFamily.familyIndex.zetaFamily parameter)
        (P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaDeterminantCoordinateDerivative
            input.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily
              parameter) = 0
  finitePart_logDerivative : ∀ parameter,
    input.familyIndex.baseFamily.familyIndex.zetaFamily.finitePartFamily.
        logDerivative parameter =
      input.familyIndex.baseFamily.familyIndex.relativeTrace.trace parameter

/-- Assemble the full split Fredholm determinant certificate. -/
def globalHessianPreferredFiveSectorFullFredholmDeterminantCertificate
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
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :
    GlobalHessianPreferredFiveSectorFullFredholmDeterminantCertificate4D period
      hPeriod input where
  determinantFamily :=
    globalHessianPreferredFiveSectorFredholmDeterminantFamilyOutput period
      hPeriod input
  namedSourceVolume :=
    (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod
      input).cokernelNamedVolume_ne_zero
  frameNormalization :=
    (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod
      input).determinantFrame_cokernelNamedVolume
  basepointActionBasis := input.vector_zero_eq_actionGenerator period hPeriod
  reducedDeterminant_nonzero := by
    intro parameter
    exact P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
      relativeZetaDeterminantCoordinate_ne_zero
        input.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily
          parameter
  reducedDeterminant_parallel :=
    input.familyIndex.baseFamily.familyIndex.determinant_parallel
  finitePart_logDerivative :=
    input.familyIndex.baseFamily.familyIndex.
      finitePart_logDerivative_eq_relativeTrace

/-- Public terminal split Fredholm determinant checkpoint. -/
theorem global_hessian_preferred_five_sector_full_fredholm_determinant_gate
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
    {fold : Fold} {Index : Type*}
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :
    GlobalHessianPreferredFiveSectorFullFredholmDeterminantCertificate4D period
      hPeriod input :=
  globalHessianPreferredFiveSectorFullFredholmDeterminantCertificate period
    hPeriod input

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFullFredholmDeterminantClosure4D
end JanusFormal
