import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricBismutFreed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D

/-!
# Sector-preserving reduced geometric Bismut--Freed input

The reduced geometric frontier previously accepted any exact D11
representation of the Candidate-A Hessian.  This refinement accepts only a
representation whose source and target coordinate equivalences factor through
the literal five-sector completion isometry already used by H12/H14.

Thus the geometric family cannot identify the correct total Hessian while
silently mixing its physical sectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreed4D

set_option autoImplicit false
set_option maxHeartbeats 42000000
set_option synthInstance.maxHeartbeats 21000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorReducedGeometricBismutFreed4D
open P0EFTJanusProgramPGeometricBismutFreedPathComparison4D
open P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D
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

/-- Reduced geometric input whose D11 representation is constrained by the
same physical five-sector decomposition used by the Candidate-A Hessian. -/
structure GlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreedData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (Base Tangent : Type*) : Prop where
  sectorRepresentation :
    GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
      period hPeriod input
  geometry : GeometricBismutFreedOneFormData Base Tangent
  path : GeometricFamilyPathData Base Tangent
  coefficient_agreement : ∀ parameter,
    pulledGeometricCoefficient geometry path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
        bismutFreedCoefficient parameter
  curvature : GeometricFamiliesIndexCurvatureData Base Tangent

namespace GlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreedData4D

/-- Forget only the sector-factorization witness and recover the previous
reduced geometric packet. -/
def toReducedGeometricData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (data : GlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreedData4D
      period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorReducedGeometricBismutFreedData4D
      period hPeriod input Base Tangent where
  naturalRepresentation := data.sectorRepresentation.bridge
  geometry := data.geometry
  path := data.path
  coefficient_agreement := data.coefficient_agreement
  curvature := data.curvature

/-- Public sector-preserving reduced geometric checkpoint. -/
theorem sector_reduced_geometric_bismut_freed_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (data : GlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreedData4D
      period hPeriod input Base Tangent) :
    (∀ parameter,
      data.sectorRepresentation.bridge.representation.representedNaturalOperator
          parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    (∀ parameter,
      data.sectorRepresentation.bridge.representation.sourceEquiv parameter =
        (data.sectorRepresentation.sectorRefinement.sourceProductEquiv parameter).trans
          ((data.sectorRepresentation.sectorRefinement.sourceSectorCoordinates
            parameter).ambientEquiv
              (preferredCandidateAFiveSectorHilbertCoordinates
                period hPeriod input))) ∧
    (∀ parameter,
      data.sectorRepresentation.bridge.representation.targetEquiv parameter =
        (data.sectorRepresentation.sectorRefinement.targetProductEquiv parameter).trans
          ((data.sectorRepresentation.sectorRefinement.targetSectorCoordinates
            parameter).ambientEquiv
              (preferredCandidateAFiveSectorHilbertCoordinates
                period hPeriod input))) ∧
    (∀ parameter,
      pulledGeometricCoefficient data.geometry data.path parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      data.curvature.bismutFreedCurvature base first second =
        data.curvature.localFamiliesIndexCurvature base first second) :=
  ⟨data.sectorRepresentation.representedNaturalOperator_eq_actual
      period hPeriod input,
    data.sectorRepresentation.sectorRefinement.sourceEquiv_agreement,
    data.sectorRepresentation.sectorRefinement.targetEquiv_agreement,
    data.coefficient_agreement,
    data.curvature.curvature_agreement⟩

end GlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreedData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreed4D
end JanusFormal
