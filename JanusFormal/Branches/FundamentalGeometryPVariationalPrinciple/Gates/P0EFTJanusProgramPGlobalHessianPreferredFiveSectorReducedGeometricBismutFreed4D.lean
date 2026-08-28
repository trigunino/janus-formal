import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalAnalyticUpgrade4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D

/-!
# Reduced geometric Bismut--Freed inputs for Candidate-A

The ordinary D11 analytic/Quillen input is now generated from the exact D11
representation of the actual Candidate-A Hessian.  Hence no analytic-family,
metric, connection or Quillen-status packet is accepted here as external data.

The remaining genuinely geometric inputs are only:

* the exact D11 natural elliptic representation itself;
* a geometric Bismut--Freed one-form and the Candidate-A path through its base;
* equality of its pullback coefficient with the intrinsic operator trace;
* equality of geometric Bismut--Freed curvature with the local families-index
  curvature.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricBismutFreed4D

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalAnalyticUpgrade4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreed4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D
open P0EFTJanusProgramPGeometricBismutFreedPathComparison4D
open P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D
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

/-- Minimal geometric input after the ordinary D11 analytic family is generated
from Candidate-A. -/
structure GlobalHessianPreferredFiveSectorReducedGeometricBismutFreedData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) where
  naturalRepresentation :
    GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input
  geometry : GeometricBismutFreedOneFormData Base Tangent
  path : GeometricFamilyPathData Base Tangent
  coefficient_agreement : ∀ parameter,
    pulledGeometricCoefficient geometry path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
        bismutFreedCoefficient parameter
  curvature : GeometricFamiliesIndexCurvatureData Base Tangent

namespace GlobalHessianPreferredFiveSectorReducedGeometricBismutFreedData4D

/-- Recover the previous essential packet with the analytic family generated
from concrete Candidate-A data. -/
def toEssentialGeometricData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (reduced : GlobalHessianPreferredFiveSectorReducedGeometricBismutFreedData4D period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedData4D period hPeriod input Base Tangent where
  analyticFamily := candidateAConcreteNaturalAnalyticUpgrade
    period hPeriod input reduced.naturalRepresentation
  analyticFamilyClosed := candidateAConcreteNaturalAnalyticUpgrade_closed
    period hPeriod input reduced.naturalRepresentation
  geometry := reduced.geometry
  path := reduced.path
  coefficient_agreement := reduced.coefficient_agreement
  curvature := reduced.curvature

/-- Public reduced geometric checkpoint. -/
theorem reduced_geometric_bismut_freed_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (reduced : GlobalHessianPreferredFiveSectorReducedGeometricBismutFreedData4D period hPeriod input Base Tangent) :
    (∀ parameter,
      reduced.naturalRepresentation.representation.representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    P0EFTJanusQuillenFamilyCanonicity.ellipticFamilyInputClosed
      (toEllipticFamilyInputStatus
        (candidateAConcreteNaturalAnalyticUpgrade period hPeriod input
          reduced.naturalRepresentation)) ∧
    (∀ parameter,
      pulledGeometricCoefficient reduced.geometry reduced.path parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      reduced.curvature.bismutFreedCurvature base first second =
        reduced.curvature.localFamiliesIndexCurvature base first second) :=
  ⟨reduced.naturalRepresentation.representedNaturalOperator_eq_actual
      period hPeriod input,
    candidateAConcreteNaturalAnalyticUpgrade_closed
      period hPeriod input reduced.naturalRepresentation,
    reduced.coefficient_agreement,
    reduced.curvature.curvature_agreement⟩

end GlobalHessianPreferredFiveSectorReducedGeometricBismutFreedData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricBismutFreed4D
end JanusFormal
