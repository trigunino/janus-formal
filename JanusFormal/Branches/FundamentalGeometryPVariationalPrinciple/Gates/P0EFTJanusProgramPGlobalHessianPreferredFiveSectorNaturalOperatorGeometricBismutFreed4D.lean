import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D

/-!
# Bismut--Freed geometry bound to the componentwise D11 Candidate-A family

The preceding geometric frontier only required sector-preserving coordinates and
pullbacks.  Here the same geometric one-form and families-index curvature are
bound to the stronger D11 realization whose natural operator itself is exactly
factorized into the five physical sector operators.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreed4D

set_option autoImplicit false
set_option maxHeartbeats 46000000
set_option synthInstance.maxHeartbeats 23000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreed4D
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

/-- Geometric BF/families-index input attached to the actual componentwise D11
operator family. -/
structure GlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreedData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) where
  natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
    period hPeriod input
  geometry : GeometricBismutFreedOneFormData Base Tangent
  path : GeometricFamilyPathData Base Tangent
  coefficient_agreement : ∀ parameter,
    pulledGeometricCoefficient geometry path parameter =
      input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
        bismutFreedCoefficient parameter
  curvature : GeometricFamiliesIndexCurvatureData Base Tangent

namespace GlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreedData4D

/-- Forget only the componentwise operator-factorization witness. -/
def toSectorCovariantGeometricData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (data : GlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreedData4D
      period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorSectorCovariantGeometricBismutFreedData4D
      period hPeriod input Base Tangent where
  naturalCovariance := data.natural.covariance
  geometry := data.geometry
  path := data.path
  coefficient_agreement := data.coefficient_agreement
  curvature := data.curvature

/-- Public componentwise-natural geometric BF checkpoint. -/
theorem natural_operator_geometric_bismut_freed_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (data : GlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreedData4D
      period hPeriod input Base Tangent) :
    (∀ parameter state,
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
        decomposition (input.familyIndex.baseFamily.actualOperator parameter state) =
        fiveSectorMetricAxis
          (data.natural.operatorFactorization.representedMetricBlock
            data.natural.covariance.sectorRepresentation.bridge.representation
            (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
            data.natural.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorMetricCoordinate
              ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
                decomposition state))) +
        fiveSectorAbelianAxis
          (data.natural.operatorFactorization.representedAbelianBlock
            data.natural.covariance.sectorRepresentation.bridge.representation
            (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
            data.natural.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorAbelianCoordinate
              ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
                decomposition state))) +
        fiveSectorMatterAxis
          (data.natural.operatorFactorization.representedMatterBlock
            data.natural.covariance.sectorRepresentation.bridge.representation
            (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
            data.natural.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorMatterCoordinate
              ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
                decomposition state))) +
        fiveSectorLongitudinalAxis
          (data.natural.operatorFactorization.representedLongitudinalBlock
            data.natural.covariance.sectorRepresentation.bridge.representation
            (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
            data.natural.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorLongitudinalCoordinate
              ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
                decomposition state))) +
        fiveSectorBoundaryAxis
          (data.natural.operatorFactorization.representedBoundaryBlock
            data.natural.covariance.sectorRepresentation.bridge.representation
            (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
            data.natural.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorBoundaryCoordinate
              ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
                decomposition state)))) ∧
    (∀ parameter,
      pulledGeometricCoefficient data.geometry data.path parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      data.curvature.bismutFreedCurvature base first second =
        data.curvature.localFamiliesIndexCurvature base first second) :=
  ⟨data.natural.actualOperator_blockFormula period hPeriod input,
    data.coefficient_agreement,
    data.curvature.curvature_agreement⟩

end GlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreedData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreed4D
end JanusFormal
