import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaDeterminantSection4D

/-!
# Candidate-A complex Fredholm section

This façade specializes the generic zeta-weighted complex Fredholm section to
the preferred Candidate-A family.  The intrinsic reduced determinant now acts
on the actual complexified kernel/cokernel Fredholm frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAComplexFredholmSection4D

set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option synthInstance.maxHeartbeats 15000000

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
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexCoordinateFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaDeterminantSection4D
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
    {fold : Fold} {Index : Type*}

variable (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
  period hPeriod configuration data analysis einsteinScale hTransverse family
    chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)

/-- Candidate-A intrinsic zeta coordinates on the actual complexified Fredholm line. -/
def complexFredholmCoordinateFamily :=
  selfAdjointFredholmZetaCoordinateFamily
    (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input)
    input.familyIndex.baseFamily.familyIndex.zetaFamily

/-- Candidate-A determinant section in the actual complexified Fredholm fibre. -/
def complexFredholmDeterminantSection (parameter : Real) :=
  selfAdjointFredholmZetaDeterminantSection
    (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input)
    input.familyIndex.baseFamily.familyIndex.zetaFamily parameter

/-- Exact tensor-line formula for the preferred Candidate-A determinant. -/
theorem complexFredholmDeterminantSection_eq_zeta_smul_frame
    (parameter : Real) :
    complexFredholmDeterminantSection period hPeriod input parameter =
      relativeHeatMellinZetaFamilyDeterminant
          input.familyIndex.baseFamily.familyIndex.zetaFamily parameter •
        (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input).
          complexifiedDeterminantFrame parameter :=
  selfAdjointFredholmZetaDeterminantSection_eq
    (globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input)
    input.familyIndex.baseFamily.familyIndex.zetaFamily parameter

/-- The complex coordinate multiplying the actual Fredholm frame never vanishes. -/
theorem complexFredholmCoordinate_ne_zero (parameter : Real) :
    (complexFredholmCoordinateFamily period hPeriod input).coordinate parameter ≠ 0 :=
  (complexFredholmCoordinateFamily period hPeriod input).coordinate_ne_zero parameter

end
end P0EFTJanusProgramPCandidateAComplexFredholmSection4D
end JanusFormal
