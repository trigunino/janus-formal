import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalAnalyticPathUpgrade4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedAdapter4D

/-!
# Minimal geometric Bismut--Freed inputs after the exact D11 Candidate-A bridge

The earlier essential interface still accepted a closed
`NaturalFamilyAnalyticUpgrade`.  This file removes that remaining freedom.
The analytic upgrade is now generated from:

* the exact D11 natural elliptic representation of the Candidate-A Hessian;
* the remaining natural metric/connection geometry;
* existing Candidate-A self-adjoint and differentiable reduced-family data.

Thus the external geometric Bismut--Freed input contains no freely supplied
operator-family status.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMinimalGeometricBismutFreed4D

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalAnalyticPathUpgrade4D
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

/-- Minimal genuine geometric input after the D11 operator representation and
Program-P analytic family have been fixed. -/
structure GlobalHessianPreferredFiveSectorMinimalGeometricBismutFreedData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) where
  naturalRepresentation :
    GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input
  naturalPathGeometry :
    GlobalHessianPreferredFiveSectorNaturalPathGeometryData4D period hPeriod input naturalRepresentation
  geometry : GeometricBismutFreedOneFormData Base Tangent
  path : GeometricFamilyPathData Base Tangent
  coefficient_agreement : ∀ parameter,
    pulledGeometricCoefficient geometry path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
        bismutFreedCoefficient parameter
  curvature : GeometricFamiliesIndexCurvatureData Base Tangent

namespace GlobalHessianPreferredFiveSectorMinimalGeometricBismutFreedData4D

/-- Recover the previous essential geometric packet, with its analytic family
now generated rather than supplied. -/
def toEssentialGeometricData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (minimal : GlobalHessianPreferredFiveSectorMinimalGeometricBismutFreedData4D period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorEssentialGeometricBismutFreedData4D period hPeriod input Base Tangent where
  analyticFamily := candidateANaturalAnalyticPathUpgrade
    period hPeriod input minimal.naturalRepresentation minimal.naturalPathGeometry
  analyticFamilyClosed := candidateANaturalAnalyticPathUpgrade_closes_quillen_input
    period hPeriod input minimal.naturalRepresentation minimal.naturalPathGeometry
  geometry := minimal.geometry
  path := minimal.path
  coefficient_agreement := minimal.coefficient_agreement
  curvature := minimal.curvature

/-- The minimal packet already forces the exact D11 representation and closes
the ordinary analytic Quillen input. -/
theorem minimal_geometric_bismut_freed_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (minimal : GlobalHessianPreferredFiveSectorMinimalGeometricBismutFreedData4D period hPeriod input Base Tangent) :
    (∀ parameter,
      minimal.naturalRepresentation.representation.representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    ellipticFamilyInputClosed
      (toEllipticFamilyInputStatus
        (candidateANaturalAnalyticPathUpgrade period hPeriod input
          minimal.naturalRepresentation minimal.naturalPathGeometry)) ∧
    (∀ parameter,
      pulledGeometricCoefficient minimal.geometry minimal.path parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      minimal.curvature.bismutFreedCurvature base first second =
        minimal.curvature.localFamiliesIndexCurvature base first second) :=
  ⟨minimal.naturalRepresentation.representedNaturalOperator_eq_actual
      period hPeriod input,
    candidateANaturalAnalyticPathUpgrade_closes_quillen_input
      period hPeriod input minimal.naturalRepresentation minimal.naturalPathGeometry,
    minimal.coefficient_agreement,
    minimal.curvature.curvature_agreement⟩

end GlobalHessianPreferredFiveSectorMinimalGeometricBismutFreedData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMinimalGeometricBismutFreed4D
end JanusFormal
