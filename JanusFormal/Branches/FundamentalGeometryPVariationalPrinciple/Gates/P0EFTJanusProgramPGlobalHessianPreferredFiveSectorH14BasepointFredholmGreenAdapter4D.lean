import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelComplementBasepointDataTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14Certificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D

/-!
# Concrete H14 basepoint adapter for the D11 unitary Fredholm--Green closure

The unitary family continuation was intentionally formulated using generic
basepoint gap and Green packets.  The preferred Candidate-A route already owns
those objects at H14:

* `closure.frontier.analytic.toActualKernelGap.gapData` is the genuine gap on
  the orthogonal complement of the actual kernel;
* `globalCandidateAActualKernelGreen` is the genuine two-sided reduced Green;
* the H12/H14 complement certificate proves its operator-norm bound by the
  inverse gap.

The only apparent mismatch is notation.  The family package calls its
basepoint `baseFamily.actualOperator 0`, while H14 spells the same operator as
the canonical Candidate-A actual-kernel operator.  The field `actual_zero`
identifies them exactly.  This file transports the H14 data through that
identity and constructs the terminal D11 unitary Fredholm--Green closure with no
new analytic hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14BasepointFredholmGreenAdapter4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
set_option maxRecDepth 10000
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14Certificate4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
open P0EFTJanusProgramPFiniteKernelComplementBasepointDataTransport4D
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

attribute [local instance 40000]
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

attribute [local instance 20000]
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelModule
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelCompleteSpace

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

variable {measure : Measure (EffectiveQuotient period hPeriod)}

private abbrev CandidateAHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  ActualKernelHilbert period hPeriod configuration data analysis

private abbrev CanonicalChart
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
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelChart period hPeriod configuration data analysis
    einsteinScale hTransverse family

private abbrev CanonicalSameAction
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
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelSameAction period hPeriod configuration data
    analysis einsteinScale hTransverse family

private abbrev CanonicalPhysical
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
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :=
  globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound

private abbrev CanonicalOperator
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
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :
    CandidateAHilbert period hPeriod configuration data analysis →L[Real]
      CandidateAHilbert period hPeriod configuration data analysis :=
  globalCandidateAActualKernelOperator period hPeriod configuration data analysis
    (CanonicalChart period hPeriod einsteinScale hTransverse family)
    (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
    (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)

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
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

private abbrev BasepointClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure

private abbrev BasepointActualGap
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  (BasepointClosure period hPeriod input).frontier.analytic.toActualKernelGap

private def CanonicalOperatorFamily
  (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Real → CandidateAHilbert period hPeriod configuration data analysis →L[Real]
      CandidateAHilbert period hPeriod configuration data analysis :=
  fun _ => input.familyIndex.baseFamily.actualOperator 0

/-- The exact H14 norm gap, using the canonical basepoint spelling. -/
private def canonicalH14BasepointGap
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    FiniteKernelComplementBasepointNormGapData
      (CanonicalOperatorFamily period hPeriod input) where
  gap := input.familyIndex.baseFamily.familyIndex.actualGap.gap
  gap_pos := input.familyIndex.baseFamily.familyIndex.actualGap.gap_pos
  lower_bound := by
    intro vector hVector
    let bf := input.familyIndex.baseFamily.familyIndex
    have hLower := bf.actualGap.toUniformGapFamily.lowerBound 0
      ⟨vector, hVector⟩
    rw [bf.fixedOperator_zero] at hLower
    exact hLower

/-- The exact H14 two-sided reduced Green, using the canonical basepoint
spelling. -/
private def canonicalH14BasepointGreen
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    FiniteKernelComplementBasepointGreenData
      (CanonicalOperatorFamily period hPeriod input) := by
  let operator := input.familyIndex.baseFamily.actualOperator 0
  let bf := input.familyIndex.baseFamily.familyIndex
  let hSelfAdjoint := bf.actual_selfAdjoint 0
  let uniform := bf.actualGap.toUniformGapFamily
  refine
    { operator_mem_complement := by
        intro vector
        exact selfAdjoint_operator_mem_kernelComplement operator hSelfAdjoint
          vector
      green := uniform.green 0
      operator_green := by
        intro vector
        have hInverse := uniform.operator_green 0 vector
        rw [bf.fixedOperator_zero] at hInverse
        exact congrArg Subtype.val hInverse
      green_operator := by
        intro vector
        have hInverse := uniform.green_operator 0 vector
        rw [bf.fixedOperator_zero] at hInverse
        exact hInverse }

private theorem canonicalH14BasepointGreen_norm_le_gap_inv
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    ‖(canonicalH14BasepointGreen period hPeriod input).green‖ ≤
      (canonicalH14BasepointGap period hPeriod input).gap⁻¹ := by
  exact input.familyIndex.baseFamily.familyIndex.actualGap.toUniformGapFamily.green_opNorm_le 0

/-- H14 gap transported to the literal zero fibre of the selected family. -/
def h14BasepointGap
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    FiniteKernelComplementBasepointNormGapData
      input.familyIndex.baseFamily.actualOperator :=
  P0EFTJanusProgramPFiniteKernelComplementBasepointDataTransport4D.FiniteKernelComplementBasepointNormGapData.transportZero
    (canonicalH14BasepointGap period hPeriod input)
      rfl

/-- H14 Green transported to the literal zero fibre of the selected family. -/
def h14BasepointGreen
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    FiniteKernelComplementBasepointGreenData
      input.familyIndex.baseFamily.actualOperator :=
  P0EFTJanusProgramPFiniteKernelComplementBasepointDataTransport4D.FiniteKernelComplementBasepointGreenData.transportZero
    (canonicalH14BasepointGreen period hPeriod input)
      rfl

/-- The H14 inverse-gap Green bound survives the exact zero-fibre transport. -/
theorem h14BasepointGreen_norm_le_gap_inv
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    ‖(h14BasepointGreen period hPeriod input).green‖ ≤
      (h14BasepointGap period hPeriod input).gap⁻¹ :=
  transportZero_green_norm_le_gap_inv
    (canonicalH14BasepointGap period hPeriod input)
    (canonicalH14BasepointGreen period hPeriod input)
    rfl
    (canonicalH14BasepointGreen_norm_le_gap_inv period hPeriod input)

/-- Construct the complete D11 unitary Fredholm--Green closure directly from
its concrete H14 basepoint. -/
def toD11UnitaryFredholmGreenClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural where
  d11Unitary := d11Unitary
  basepointGreen := h14BasepointGreen period hPeriod input
  basepointGap := h14BasepointGap period hPeriod input
  green_norm_le_gap_inv := h14BasepointGreen_norm_le_gap_inv period hPeriod input

/-- Public concrete-H14-to-unitary-family checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_basepoint_fredholm_green_adapter_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    let closure := toD11UnitaryFredholmGreenClosure period hPeriod input natural
      d11Unitary
    closure.basepointGap.gap =
        input.familyIndex.baseFamily.familyIndex.actualGap.gap ∧
      ‖closure.basepointGreen.green‖ ≤ closure.basepointGap.gap⁻¹ ∧
      closure.d11Unitary = d11Unitary := by
  dsimp only
  exact
    ⟨rfl,
      h14BasepointGreen_norm_le_gap_inv period hPeriod input,
      rfl⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14BasepointFredholmGreenAdapter4D
end JanusFormal
