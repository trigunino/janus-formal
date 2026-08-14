import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAComplexFredholmSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D

/-!
# Geometric Bismut--Freed comparison for the preferred Candidate-A family

This façade attaches the D11 natural-family/Quillen geometry to the exact
Candidate-A operator family already used by the H14/Fredholm/zeta construction.
No second Hessian, reduced family, reference family or determinant coordinate is
introduced.

The remaining geometric content is explicit:

* the D11 natural-family analytic input is closed;
* the Quillen/Bismut--Freed geometric package is closed;
* the pulled geometric connection one-form agrees with the intrinsic
  Candidate-A logarithmic-trace coefficient;
* the geometric curvature agrees with the local families-index curvature.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreed4D

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 16000000

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
open P0EFTJanusProgramPGeometricBismutFreedPathComparison4D
open P0EFTJanusProgramPGeometricBismutFreedFullTensorComparison4D
open P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D
open P0EFTJanusNaturalFamilyQuillenBridge
open P0EFTJanusQuillenFamilyCanonicity
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

/-- Preferred Candidate-A family plus the genuine geometric data needed to
identify its operator trace connection with the D11 geometric
Bismut--Freed/families-index package. -/
structure GlobalHessianPreferredFiveSectorGeometricBismutFreedComparison4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) where
  analyticFamily : NaturalFamilyAnalyticUpgrade
  analyticFamilyClosed :
    ellipticFamilyInputClosed (toEllipticFamilyInputStatus analyticFamily)
  quillen : QuillenBismutFreedStatus
  quillenClosed : quillenBismutFreedClosed quillen
  geometry : GeometricBismutFreedOneFormData Base Tangent
  path : GeometricFamilyPathData Base Tangent
  coefficient_agreement : ∀ parameter,
    pulledGeometricCoefficient geometry path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
        bismutFreedCoefficient parameter
  curvature : GeometricFamiliesIndexCurvatureData Base Tangent

namespace GlobalHessianPreferredFiveSectorGeometricBismutFreedComparison4D

/-- Forget the Candidate-A specialization to the generic geometric/operator
path comparison, using exactly the existing reduced actual/reference family. -/
def toPathComparison
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (geometric : GlobalHessianPreferredFiveSectorGeometricBismutFreedComparison4D
      period hPeriod input Base Tangent) :
    GeometricOperatorBismutFreedPathComparisonData
      input.familyIndex.baseFamily.familyIndex.actualGap.fixedOperator
      input.familyIndex.baseFamily.referenceOperator Base Tangent where
  analyticFamily := geometric.analyticFamily
  analyticFamilyClosed := geometric.analyticFamilyClosed
  quillen := geometric.quillen
  quillenClosed := geometric.quillenClosed
  geometry := geometric.geometry
  path := geometric.path
  operatorFamily := input.familyIndex.baseFamily.familyIndex.toBismutFreed
  coefficient_agreement := geometric.coefficient_agreement

/-- Candidate-A specialization of the multidimensional families-index
comparison packet. -/
def toFamiliesIndexComparison
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (geometric : GlobalHessianPreferredFiveSectorGeometricBismutFreedComparison4D
      period hPeriod input Base Tangent) :
    GeometricBismutFreedFamiliesIndexComparisonData
      input.familyIndex.baseFamily.familyIndex.actualGap.fixedOperator
      input.familyIndex.baseFamily.referenceOperator Base Tangent where
  pathComparison := geometric.toPathComparison period hPeriod input
  curvature := geometric.curvature

end GlobalHessianPreferredFiveSectorGeometricBismutFreedComparison4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorGeometricBismutFreed4D
end JanusFormal
