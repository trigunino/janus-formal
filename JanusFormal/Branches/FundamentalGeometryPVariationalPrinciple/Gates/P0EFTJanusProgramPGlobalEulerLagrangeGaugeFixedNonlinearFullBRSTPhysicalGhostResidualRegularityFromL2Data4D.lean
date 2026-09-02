import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingEightRegularity4D

/-!
# Physical-ghost residual regularity from fixed-carrier data

The explicit graph formula turns the smooth fixed-carrier Euler datum into
global `C∞` regularity of the authentic fixed-ambient physical-ghost residual.
Existence of that datum is not asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostResidualRegularityFromL2Data4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszFormula4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GhostMeasure :=
  intrinsicCanonicalThroatVolumeMeasure period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure (GhostMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

section ResidualRegularity

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    (measure := measure) configuration data analysis chartData

private abbrev PhysicalGhostCarrier :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D
    period hPeriod

private abbrev PhysicalGhostClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
    period hPeriod

private abbrev PhysicalGhostHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Hilbert4D
    period hPeriod

private abbrev PhysicalGhostEulerBase :=
  WithLp 2 (PhysicalGhostCarrier period hPeriod × Real)

private abbrev PhysicalGhostResidual :=
  WithLp 2 (PhysicalGhostEulerBase period hPeriod × Real)

private abbrev RegularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData

private abbrev RegularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedSpace period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedSpace period hPeriod configuration data analysis
    chartData

local instance physicalGhostHilbertCompleteSpace :
    CompleteSpace (PhysicalGhostHilbert period hPeriod) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2CompleteSpace4D
    period hPeriod

/-- Fixed smooth map that converts a carrier Riesz representative into the
ambient residual formula. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostFixedCarrierRieszFormula
    (representative : PhysicalGhostHilbert period hPeriod) :
    PhysicalGhostResidual period hPeriod :=
  let scale := (1 + ‖representative‖ ^ 2)⁻¹
  WithLp.toLp 2
    (WithLp.toLp 2
      ((((scale • representative : PhysicalGhostHilbert period hPeriod) :
          PhysicalGhostCarrier period hPeriod),
        scale * ‖representative‖ ^ 2)),
      (0 : Real))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostFixedCarrierRieszFormula_contDiff :
    ContDiff Real ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostFixedCarrierRieszFormula
        period hPeriod) := by
  let normSq := fun representative : PhysicalGhostHilbert period hPeriod =>
    ‖representative‖ ^ 2
  let denominator := fun representative : PhysicalGhostHilbert period hPeriod =>
    1 + normSq representative
  let scale := fun representative : PhysicalGhostHilbert period hPeriod =>
    (denominator representative)⁻¹
  have hNormSq : ContDiff Real ∞ normSq := (contDiff_id.norm_sq Real)
  have hDenominator : ContDiff Real ∞ denominator := contDiff_const.add hNormSq
  have hScale : ContDiff Real ∞ scale := hDenominator.inv (fun representative => by
    dsimp only [denominator, normSq]
    positivity)
  have hScaled : ContDiff Real ∞ (fun representative =>
      scale representative • representative) := hScale.smul contDiff_id
  have hCarrier : ContDiff Real ∞ (fun representative =>
      ((scale representative • representative :
          PhysicalGhostHilbert period hPeriod) :
        PhysicalGhostCarrier period hPeriod)) :=
    (PhysicalGhostClosure period hPeriod).subtypeL.contDiff.comp hScaled
  have hScalar : ContDiff Real ∞ (fun representative =>
      scale representative * normSq representative) := hScale.mul hNormSq
  have hPair : ContDiff Real ∞ (fun representative =>
      (((scale representative • representative :
          PhysicalGhostHilbert period hPeriod) :
        PhysicalGhostCarrier period hPeriod),
        scale representative * normSq representative)) :=
    hCarrier.prodMk hScalar
  have hInner : ContDiff Real ∞ (fun representative => WithLp.toLp 2
      (((scale representative • representative :
          PhysicalGhostHilbert period hPeriod) :
        PhysicalGhostCarrier period hPeriod),
        scale representative * normSq representative)) :=
    (WithLp.prodContinuousLinearEquiv 2 Real
      (PhysicalGhostCarrier period hPeriod) Real).symm.toContinuousLinearMap.contDiff.comp
        hPair
  have hOuterPair : ContDiff Real ∞ (fun representative =>
      (WithLp.toLp 2
          (((scale representative • representative :
            PhysicalGhostHilbert period hPeriod) :
            PhysicalGhostCarrier period hPeriod),
            scale representative * normSq representative),
        (0 : Real))) :=
    hInner.prodMk contDiff_const
  have hFormula : ContDiff Real ∞ (fun representative => WithLp.toLp 2
      (WithLp.toLp 2
          (((scale representative • representative :
            PhysicalGhostHilbert period hPeriod) :
            PhysicalGhostCarrier period hPeriod),
            scale representative * normSq representative),
        (0 : Real))) :=
    (WithLp.prodContinuousLinearEquiv 2 Real
      (PhysicalGhostEulerBase period hPeriod) Real).symm.toContinuousLinearMap.contDiff.comp
        hOuterPair
  change ContDiff Real ∞ (fun representative : PhysicalGhostHilbert period hPeriod =>
    WithLp.toLp 2
      (WithLp.toLp 2
          ((1 + ‖(representative : PhysicalGhostCarrier period hPeriod)‖ ^ 2)⁻¹ •
              (representative : PhysicalGhostCarrier period hPeriod),
            (1 + ‖(representative : PhysicalGhostCarrier period hPeriod)‖ ^ 2)⁻¹ *
              ‖(representative : PhysicalGhostCarrier period hPeriod)‖ ^ 2),
        (0 : Real)))
  simpa [normSq, denominator, scale] using hFormula

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszAmbientFormula_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (PhysicalGhostResidual period hPeriod) inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity) := by
  let representative :
      FullChart period hPeriod configuration data analysis chartData →
        PhysicalGhostHilbert period hPeriod :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
      period hPeriod configuration data analysis chartData regularity
  have hRepresentative :
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (PhysicalGhostHilbert period hPeriod) inferInstance inferInstance ∞
        representative :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData regularity
  have hComposition := @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (PhysicalGhostHilbert period hPeriod)
    (PhysicalGhostResidual period hPeriod)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostFixedCarrierRieszFormula
      period hPeriod)
    representative
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostFixedCarrierRieszFormula_contDiff
      period hPeriod)
    hRepresentative
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (PhysicalGhostResidual period hPeriod) inferInstance inferInstance ∞
    (fun state =>
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostFixedCarrierRieszFormula
        period hPeriod (representative state))
  exact hComposition

theorem fixedNormedResidualPhysicalGhost_contDiff_of_l2EulerRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    CoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualPhysicalGhost period hPeriod configuration data analysis
        chartData) := by
  have hPointwise :
      fixedNormedResidualPhysicalGhost period hPeriod configuration data analysis
          chartData =
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity := by
    funext state
    change
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 = _
    exact
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual_val_eq_regularFormula
        period hPeriod configuration data analysis chartData regularity state
  rw [hPointwise]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostRegularGraphRieszAmbientFormula_contDiff
      period hPeriod configuration data analysis chartData regularity

/-- Gate 285: fixed-carrier Euler regularity implies global `C∞` regularity of
the authentic physical-ghost residual coordinate. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physicalGhost_residual_regularity_from_l2_data_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    CoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualPhysicalGhost period hPeriod configuration data analysis
        chartData) :=
  fixedNormedResidualPhysicalGhost_contDiff_of_l2EulerRegularityData
    period hPeriod configuration data analysis chartData regularity

end ResidualRegularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostResidualRegularityFromL2Data4D
end JanusFormal
