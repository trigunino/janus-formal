import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenHolonomy4D

/-!
# Intrinsic preferred five-sector H14--Quillen closure

This is the terminal façade of the preferred route.  It keeps the
presentation-independent relative trace as part of the certificate while
reusing, through a definitionally faithful adapter, all already constructed
H14 and Quillen consequences:

* complete named actual kernel and sector multiplicities;
* reduced Green operator, resolvent and perturbative stability;
* exact reduced exponential and intrinsic relative heat trace;
* finite-part and Mellin/zeta determinant;
* compatible Quillen metric and connection;
* determinant-line atlas and circle clutching;
* unitary phase monodromy equal to the closed Quillen holonomy.

No finite-defect projection, second completion, second trace or second
determinant is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenClosure4D

set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option synthInstance.maxHeartbeats 8500000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenAtlas4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenHolonomy4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D
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

/-- Terminal intrinsic H14--Quillen certificate. -/
structure GlobalHessianPreferredFiveSectorIntrinsicQuillenClosureCertificate4D
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
    (input : GlobalHessianPreferredFiveSectorIntrinsicQuillenAtlas4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) : Prop where
  intrinsicAtlas :
    GlobalHessianPreferredFiveSectorIntrinsicQuillenAtlasOutput4D input
  intrinsicTrace :
    GlobalHessianPreferredFiveSectorIntrinsicTraceFrontierOutput4D
      input.intrinsicFamily.basepoint.intrinsic
  quillenClosure :
    GlobalHessianPreferredFiveSectorQuillenClosureCertificate4D
      input.toPresentationAtlas
  quillenHolonomy :
    GlobalHessianPreferredFiveSectorQuillenHolonomyCertificate4D
      input.toPresentationAtlas
  basepointDeterminant :
    relativeZetaLocalDeterminant input.atlas input.baseIndex 0 =
      input.intrinsicFamily.basepoint.determinant
  phaseHolonomy :
    circleQuillenClosedHolonomy fold =
      relativeZetaFinitePartPhase
          input.intrinsicFamily.mellinFamily.toFinitePartComparison 0 /
        relativeZetaFinitePartPhase
          input.intrinsicFamily.mellinFamily.toFinitePartComparison 1

/-- Construct the terminal intrinsic certificate. -/
def globalHessianPreferredFiveSectorIntrinsicQuillenClosureCertificate
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
    (input : GlobalHessianPreferredFiveSectorIntrinsicQuillenAtlas4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :
    GlobalHessianPreferredFiveSectorIntrinsicQuillenClosureCertificate4D input where
  intrinsicAtlas := input.close
  intrinsicTrace := input.intrinsicFamily.basepoint.intrinsic.close
  quillenClosure :=
    globalHessianPreferredFiveSectorQuillenClosureCertificate
      input.toPresentationAtlas
  quillenHolonomy :=
    globalHessianPreferredFiveSectorQuillenHolonomyCertificate
      input.toPresentationAtlas
  basepointDeterminant := by
    rw [input.toGeneric.atlas_basepoint_eq_scalar]
    rfl
  phaseHolonomy :=
    circleQuillenClosedHolonomy_eq_zetaPhase_ratio fold
      input.intrinsicFamily.mellinFamily input.circleBridge

/-- Public terminal intrinsic H14--Quillen checkpoint. -/
theorem global_hessian_preferred_five_sector_intrinsic_quillen_closure_gate
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
    (input : GlobalHessianPreferredFiveSectorIntrinsicQuillenAtlas4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :
    GlobalHessianPreferredFiveSectorIntrinsicQuillenClosureCertificate4D input :=
  globalHessianPreferredFiveSectorIntrinsicQuillenClosureCertificate input

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenClosure4D
end JanusFormal
