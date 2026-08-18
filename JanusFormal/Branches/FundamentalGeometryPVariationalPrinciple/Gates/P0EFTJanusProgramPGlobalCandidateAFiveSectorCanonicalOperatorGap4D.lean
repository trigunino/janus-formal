import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorCanonicalGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAReducedPrincipalOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteProjectionOperatorOffDiagonalGarding4D

/-!
# Canonical Candidate-A H12 frontier in projected-operator form

The preceding canonical gap packet still states its two principal estimates as
bilinear-form inequalities.  This file lowers them to the concrete operator
level on the actual kernel complement.

Let `A_red` be the Riesz representative of the genuine reduced principal form
and let `P_s` be the projectors inherited from the one full-space commuting
five-sector decomposition.  The remaining principal input is exactly

* five inequalities for `⟪A_red P_s x, P_s x⟫`;
* one estimate for
  `‖A_red - Σ_s P_s A_red P_s‖`.

The represented-form norm is no larger than the operator-remainder norm, so the
same strict margin also dominates the canonical H11 constant computed on the
dense core.  These operator facts therefore imply the previous canonical gap
packet and its Fredholm/Green certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorCanonicalOperatorGap4D

set_option autoImplicit false
set_option maxHeartbeats 9800000
set_option synthInstance.maxHeartbeats 4900000
set_option maxRecDepth 4000

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
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D
open P0EFTJanusProgramPGlobalCandidateACanonicalReducedPhysicalBound4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorActualHessianCommutation4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCanonicalGap4D
open P0EFTJanusProgramPGlobalCandidateAReducedCanonicalEnergies4D
open P0EFTJanusProgramPGlobalCandidateAReducedPrincipalOperator4D
open P0EFTJanusProgramPFiniteProjectionOperatorOffDiagonalGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorProductOperatorOffDiagonalGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

variable {measure : Measure (EffectiveQuotient period hPeriod)}

private abbrev CanonicalPrincipalOperator
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :=
  globalCandidateAReducedPrincipalOperator period hPeriod configuration data
    analysis
    (CanonicalChart period hPeriod einsteinScale hTransverse family)
    (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
    (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)

/-- Preferred H12 inputs stated entirely through the projected reduced principal
operator. -/
structure GlobalCandidateAFiveSectorCanonicalOperatorGapData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family)))
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary] where
  geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
    hPeriod configuration data analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)
      Metric Abelian Matter Longitudinal Boundary
  kernel_finite : FiniteDimensional Real
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family
        chartBound)).ker
  diagonalConstants : CandidateAFiveSectorDiagonalConstants
  diagonal_lower : ∀ sector vector,
    diagonalConstants.sectorConstant sector *
        ‖geometry.reducedResolution.projection sector vector‖ ^ 2 ≤
      inner Real
        (CanonicalPrincipalOperator period hPeriod einsteinScale hTransverse
          family chartBound
          (geometry.reducedResolution.projection sector vector))
        (geometry.reducedResolution.projection sector vector)
  offDiagonalOperator_small :
    ‖CanonicalPrincipalOperator period hPeriod einsteinScale hTransverse family
        chartBound -
      ∑ sector : CandidateAZeroModeSector,
        (geometry.reducedResolution.projection sector).comp
          ((CanonicalPrincipalOperator period hPeriod einsteinScale hTransverse
            family chartBound).comp
            (geometry.reducedResolution.projection sector))‖ <
      diagonalConstants.sectorFloor
  canonicalPhysical_small :
    globalCandidateACanonicalSevenPhysicalConstant period hPeriod configuration
        data analysis einsteinScale hTransverse family chartBound <
      diagonalConstants.sectorFloor -
        ‖CanonicalPrincipalOperator period hPeriod einsteinScale hTransverse
            family chartBound -
          ∑ sector : CandidateAZeroModeSector,
            (geometry.reducedResolution.projection sector).comp
              ((CanonicalPrincipalOperator period hPeriod einsteinScale
                hTransverse family chartBound).comp
                (geometry.reducedResolution.projection sector))‖
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

namespace GlobalCandidateAFiveSectorCanonicalOperatorGapData4D

/-- Generic inherited-resolution operator Gårding packet. -/
def principalOperatorGarding
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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (input : GlobalCandidateAFiveSectorCanonicalOperatorGapData4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary) :
    FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := CandidateAZeroModeSector)
      (CanonicalPrincipalOperator period hPeriod einsteinScale hTransverse family
        chartBound) where
  operator_selfAdjoint :=
    globalCandidateAReducedPrincipalOperator_isSelfAdjoint period hPeriod
      configuration data analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)
  resolution := input.geometry.reducedResolution
  sectorConstant := input.diagonalConstants.sectorConstant
  sectorConstant_pos := input.diagonalConstants.sectorConstant_pos
  sectorFloor := input.diagonalConstants.sectorFloor
  sectorFloor_pos := input.diagonalConstants.sectorFloor_pos
  sectorFloor_le := input.diagonalConstants.sectorFloor_le
  diagonal_lower := input.diagonal_lower
  offDiagonalOperator_small := input.offDiagonalOperator_small

/-- The operator-represented form is exactly the canonical reduced principal
form. -/
theorem principalOperator_form_eq
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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (input : GlobalCandidateAFiveSectorCanonicalOperatorGapData4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary) :
    operatorBilinearForm
        (CanonicalPrincipalOperator period hPeriod einsteinScale hTransverse
          family chartBound) =
      CanonicalPrincipalForm period hPeriod einsteinScale hTransverse family
        chartBound := by
  ext first second
  exact globalCandidateAReducedPrincipalOperator_pairing period hPeriod
    configuration data analysis
    (CanonicalChart period hPeriod einsteinScale hTransverse family)
    (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
    (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)
    first second

/-- Convert the operator-level frontier to the canonical form-level gap packet. -/
def toCanonicalGap
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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (input : GlobalCandidateAFiveSectorCanonicalOperatorGapData4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary) :
    GlobalCandidateAFiveSectorCanonicalGapData4D period hPeriod configuration
      data analysis einsteinScale hTransverse family chartBound Metric Abelian
        Matter Longitudinal Boundary where
  geometry := input.geometry
  kernel_finite := input.kernel_finite
  diagonalConstants := input.diagonalConstants
  diagonal_lower := by
    intro sector vector
    rw [← globalCandidateAReducedPrincipalOperator_pairing period hPeriod
      configuration data analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)]
    exact input.diagonal_lower sector vector
  offDiagonalConstant := ‖input.principalOperatorGarding.offDiagonalOperator‖
  offDiagonalConstant_nonneg := norm_nonneg _
  offDiagonal_bound := by
    intro vector
    rw [← input.principalOperator_form_eq period hPeriod]
    have hResolution :
        input.principalOperatorGarding.resolution =
          CanonicalReducedResolution period hPeriod einsteinScale hTransverse
            family chartBound input.geometry := rfl
    rw [← hResolution]
    change |((operatorBilinearForm
        (CanonicalPrincipalOperator period hPeriod einsteinScale hTransverse
          family chartBound) -
      ∑ sector : CandidateAZeroModeSector,
        (operatorBilinearForm
          (CanonicalPrincipalOperator period hPeriod einsteinScale hTransverse
            family chartBound)).bilinearComp
              (input.principalOperatorGarding.resolution.projection sector)
              (input.principalOperatorGarding.resolution.projection sector))
        vector) vector| ≤ _
    rw [input.principalOperatorGarding.offDiagonalOperator_form]
    exact input.principalOperatorGarding.toFiniteSectorGarding.coupling_bound vector
  offDiagonal_small := input.offDiagonalOperator_small
  canonicalPhysical_small := input.canonicalPhysical_small
  ll_stationary := input.ll_stationary

/-- Actual-kernel gap from the projected reduced principal operator estimates. -/
def toActualKernelGap
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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (input : GlobalCandidateAFiveSectorCanonicalOperatorGapData4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary) :=
  input.toCanonicalGap.toActualKernelGap

/-- Public operator-level preferred H12 checkpoint. -/
theorem global_candidateA_five_sector_canonical_operator_gap_gate
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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (input : GlobalCandidateAFiveSectorCanonicalOperatorGapData4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary) :
    GlobalCandidateAActualKernelComplementCertificate4D period hPeriod
      configuration data analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family
        chartBound)
      input.toActualKernelGap :=
  input.toCanonicalGap.certificate

end GlobalCandidateAFiveSectorCanonicalOperatorGapData4D

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorCanonicalOperatorGap4D
end JanusFormal
