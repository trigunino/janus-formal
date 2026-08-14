import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBasepointBlockDiagonalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D

/-!
# Agreement of the D11 and H12 five-sector blocks at the basepoint

The D11 sector operators and the H12 blocks are not independent constructions.
At parameter zero both five-sector sums are equal to the same conjugated actual
Hessian `C H_0 C⁻¹`.  Applying the five coordinate projections therefore
identifies every represented D11 block with the corresponding continuous-linear
H12 block.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalBasepointBlockAgreement4D

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBasepointBlockDiagonalization4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorOperatorBlockDiagonalization4D
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
    {fold : Fold} {Index : Type*}

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

private def naturalMetricBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) : Metric → Metric :=
  natural.operatorFactorization.representedMetricBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement 0

private def naturalAbelianBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) : Abelian → Abelian :=
  natural.operatorFactorization.representedAbelianBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement 0

private def naturalMatterBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) : Matter → Matter :=
  natural.operatorFactorization.representedMatterBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement 0

private def naturalLongitudinalBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) : Longitudinal → Longitudinal :=
  natural.operatorFactorization.representedLongitudinalBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement 0

private def naturalBoundaryBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) : Boundary → Boundary :=
  natural.operatorFactorization.representedBoundaryBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement 0

/-- Equality of the two complete five-sector sums at the basepoint. -/
theorem basepoint_product_sums_agree
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (x : FiveSectorProduct Metric Abelian Matter Longitudinal Boundary) :
    fiveSectorMetricAxis (naturalMetricBlock period hPeriod input natural
        (fiveSectorMetricCoordinate x)) +
      fiveSectorAbelianAxis (naturalAbelianBlock period hPeriod input natural
        (fiveSectorAbelianCoordinate x)) +
      fiveSectorMatterAxis (naturalMatterBlock period hPeriod input natural
        (fiveSectorMatterCoordinate x)) +
      fiveSectorLongitudinalAxis
        (naturalLongitudinalBlock period hPeriod input natural
          (fiveSectorLongitudinalCoordinate x)) +
      fiveSectorBoundaryAxis (naturalBoundaryBlock period hPeriod input natural
        (fiveSectorBoundaryCoordinate x)) =
    fiveSectorMetricAxis
        (preferredCandidateABasepointMetricBlock period hPeriod input
          (fiveSectorMetricCoordinate x)) +
      fiveSectorAbelianAxis
        (preferredCandidateABasepointAbelianBlock period hPeriod input
          (fiveSectorAbelianCoordinate x)) +
      fiveSectorMatterAxis
        (preferredCandidateABasepointMatterBlock period hPeriod input
          (fiveSectorMatterCoordinate x)) +
      fiveSectorLongitudinalAxis
        (preferredCandidateABasepointLongitudinalBlock period hPeriod input
          (fiveSectorLongitudinalCoordinate x)) +
      fiveSectorBoundaryAxis
        (preferredCandidateABasepointBoundaryBlock period hPeriod input
          (fiveSectorBoundaryCoordinate x)) := by
  let base := preferredCandidateABasepointCommutingOperator period hPeriod input
  let state := base.fromProduct x
  have hNatural := natural.actualOperator_blockFormula period hPeriod input 0 state
  have hNatural' :
      base.conjugatedOperator x =
        fiveSectorMetricAxis (naturalMetricBlock period hPeriod input natural
            (fiveSectorMetricCoordinate x)) +
          fiveSectorAbelianAxis (naturalAbelianBlock period hPeriod input natural
            (fiveSectorAbelianCoordinate x)) +
          fiveSectorMatterAxis (naturalMatterBlock period hPeriod input natural
            (fiveSectorMatterCoordinate x)) +
          fiveSectorLongitudinalAxis
            (naturalLongitudinalBlock period hPeriod input natural
              (fiveSectorLongitudinalCoordinate x)) +
          fiveSectorBoundaryAxis (naturalBoundaryBlock period hPeriod input natural
            (fiveSectorBoundaryCoordinate x)) := by
    simpa [base, state, naturalMetricBlock, naturalAbelianBlock,
      naturalMatterBlock, naturalLongitudinalBlock, naturalBoundaryBlock,
      FiveSectorCommutingOperatorData.conjugatedOperator,
      FiveSectorCommutingOperatorData.toProduct,
      FiveSectorCommutingOperatorData.fromProduct] using hNatural
  exact hNatural'.symm.trans
    (preferredCandidateABasepoint_blockDiagonal period hPeriod input x)

/-- D11 metric block equals the H12 metric block. -/
theorem naturalMetricBlock_eq_H12
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (value : Metric) :
    naturalMetricBlock period hPeriod input natural value =
      preferredCandidateABasepointMetricBlock period hPeriod input value := by
  have h := congrArg fiveSectorMetricCoordinate
    (basepoint_product_sums_agree period hPeriod input natural
      (fiveSectorMetricAxis value))
  simpa using h

/-- D11 Abelian block equals the H12 Abelian block. -/
theorem naturalAbelianBlock_eq_H12
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (value : Abelian) :
    naturalAbelianBlock period hPeriod input natural value =
      preferredCandidateABasepointAbelianBlock period hPeriod input value := by
  have h := congrArg fiveSectorAbelianCoordinate
    (basepoint_product_sums_agree period hPeriod input natural
      (fiveSectorAbelianAxis value))
  simpa using h

/-- D11 primitive SpinC block equals the H12 matter block. -/
theorem naturalMatterBlock_eq_H12
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (value : Matter) :
    naturalMatterBlock period hPeriod input natural value =
      preferredCandidateABasepointMatterBlock period hPeriod input value := by
  have h := congrArg fiveSectorMatterCoordinate
    (basepoint_product_sums_agree period hPeriod input natural
      (fiveSectorMatterAxis value))
  simpa using h

/-- D11 longitudinal/LL block equals the H12 longitudinal block. -/
theorem naturalLongitudinalBlock_eq_H12
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (value : Longitudinal) :
    naturalLongitudinalBlock period hPeriod input natural value =
      preferredCandidateABasepointLongitudinalBlock period hPeriod input value := by
  have h := congrArg fiveSectorLongitudinalCoordinate
    (basepoint_product_sums_agree period hPeriod input natural
      (fiveSectorLongitudinalAxis value))
  simpa using h

/-- D11 boundary/finite-BV block equals the H12 boundary block. -/
theorem naturalBoundaryBlock_eq_H12
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (value : Boundary) :
    naturalBoundaryBlock period hPeriod input natural value =
      preferredCandidateABasepointBoundaryBlock period hPeriod input value := by
  have h := congrArg fiveSectorBoundaryCoordinate
    (basepoint_product_sums_agree period hPeriod input natural
      (fiveSectorBoundaryAxis value))
  simpa using h

/-- Public five-block basepoint agreement checkpoint. -/
theorem natural_basepoint_blocks_agree_H12_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    (∀ value, naturalMetricBlock period hPeriod input natural value =
      preferredCandidateABasepointMetricBlock period hPeriod input value) ∧
    (∀ value, naturalAbelianBlock period hPeriod input natural value =
      preferredCandidateABasepointAbelianBlock period hPeriod input value) ∧
    (∀ value, naturalMatterBlock period hPeriod input natural value =
      preferredCandidateABasepointMatterBlock period hPeriod input value) ∧
    (∀ value, naturalLongitudinalBlock period hPeriod input natural value =
      preferredCandidateABasepointLongitudinalBlock period hPeriod input value) ∧
    (∀ value, naturalBoundaryBlock period hPeriod input natural value =
      preferredCandidateABasepointBoundaryBlock period hPeriod input value) :=
  ⟨naturalMetricBlock_eq_H12 period hPeriod input natural,
    naturalAbelianBlock_eq_H12 period hPeriod input natural,
    naturalMatterBlock_eq_H12 period hPeriod input natural,
    naturalLongitudinalBlock_eq_H12 period hPeriod input natural,
    naturalBoundaryBlock_eq_H12 period hPeriod input natural⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalBasepointBlockAgreement4D
end JanusFormal
