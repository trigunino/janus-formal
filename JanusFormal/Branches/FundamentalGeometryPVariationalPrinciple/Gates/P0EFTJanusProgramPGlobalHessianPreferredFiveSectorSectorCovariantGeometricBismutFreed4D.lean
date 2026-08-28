import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D

/-!
# Bismut--Freed data bound to a sector-covariant D11 family

The geometric comparison is attached here to a D11 representation whose
pointwise coordinates and geometric pullbacks both preserve the unique five
physical sectors of the preferred Candidate-A Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreed4D

set_option autoImplicit false
set_option maxHeartbeats 44000000
set_option synthInstance.maxHeartbeats 22000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreed4D
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

/-- Geometric BF/families-index input attached to a sector-covariant D11
representation of the exact Candidate-A Hessian. -/
structure GlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreedData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (Base Tangent : Type*) where
  naturalCovariance :
    GlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
      period hPeriod input
  geometry : GeometricBismutFreedOneFormData Base Tangent
  path : GeometricFamilyPathData Base Tangent
  coefficient_agreement : ∀ parameter,
    pulledGeometricCoefficient geometry path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
        bismutFreedCoefficient parameter
  curvature : GeometricFamiliesIndexCurvatureData Base Tangent

namespace GlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreedData4D

/-- Forget pullback covariance and recover the previous sector-reduced geometric
packet. -/
def toSectorReducedGeometricData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (data : GlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreedData4D
      period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorSectorReducedGeometricBismutFreedData4D
      period hPeriod input Base Tangent where
  sectorRepresentation := data.naturalCovariance.sectorRepresentation
  geometry := data.geometry
  path := data.path
  coefficient_agreement := data.coefficient_agreement
  curvature := data.curvature

/-- Public sector-covariant geometric checkpoint. -/
theorem sector_covariant_geometric_bismut_freed_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (data : GlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreedData4D
      period hPeriod input Base Tangent) :
    (∀ parameter,
      data.naturalCovariance.sectorRepresentation.bridge.representation.
          representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    (∀ {first second : Real}
      (morphism : P0EFTJanusSpinCImmersionCategory.AdmissibleMorphism
        data.naturalCovariance.sectorRepresentation.bridge.immersionCategory
        (data.naturalCovariance.sectorRepresentation.bridge.representation.objectAt
          first)
        (data.naturalCovariance.sectorRepresentation.bridge.representation.objectAt
          second))
      (sector : P0EFTJanusProgramPFiveSectorHilbertCoordinates4D.FivePhysicalSector)
      (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
        configuration data analysis),
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
          sectorProjector sector
          (data.naturalCovariance.sectorRepresentation.bridge.representation.
            representedSourcePullback morphism state) =
        data.naturalCovariance.sectorRepresentation.bridge.representation.
          representedSourcePullback morphism
          ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
            sectorProjector sector state)) ∧
    (∀ parameter,
      pulledGeometricCoefficient data.geometry data.path parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      data.curvature.bismutFreedCurvature base first second =
        data.curvature.localFamiliesIndexCurvature base first second) :=
  ⟨data.naturalCovariance.sectorRepresentation.representedNaturalOperator_eq_actual
      period hPeriod input,
    data.naturalCovariance.pullback.source_commutes,
    data.coefficient_agreement,
    data.curvature.curvature_agreement⟩

end GlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreedData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreed4D
end JanusFormal
