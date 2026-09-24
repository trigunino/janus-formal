import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMetricLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeLorenzRaisedCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LorenzRaisedCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LorenzLocalDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D

/-! Global Stokes for the actual Abelian Lorenz and Faddeev-Popov operators. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FrameFreeLorenzGlobalStokes4D

set_option autoImplicit false



noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

open P0EFTJanusProgramPT12CanonicalCurrentPullback4D
open P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D

open P0EFTJanusProgramPT12CanonicalCurrentLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D

open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D
open P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

open MeasureTheory
open P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D
open P0EFTJanusProgramPT12LorenzRaisedCurrent4D
open P0EFTJanusProgramPT12LorenzLocalDensity4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D

open P0EFTJanusProgramPT12FrameFreeCurrentPullback4D
open P0EFTJanusProgramPT12FrameFreeMetricDivergenceStokes4D
open P0EFTJanusProgramPT12FrameFreeMetricLocalDivergence4D
open P0EFTJanusProgramPT12FrameFreeLorenzRaisedCurrent4D
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

theorem frameFreeGlobalLorenz_eq_metricCurrentDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential point component =
      frameFreeMetricVolumeDivergence period hPeriod metric
        (frameFreeLorenzRaisedCurrent period hPeriod metric potential component) point := by
  let witness := canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq, globalGeneralMetricAbelianLorenzCodifferential_apply,
    globalGeneralMetricAbelianLorenzValue_eq_local, localLorenz_eq_densityDivergence,
    frameFreeMetricCurrentDivergence_eq_local]
  have hField : frameFreeCurrentPullback period hPeriod witness.patch
      (frameFreeLorenzRaisedCurrent period hPeriod metric potential component) =
      localRaisedAbelianGaugePotential period hPeriod metric potential component witness.patch := by
    funext coordinate
    exact frameFreeLorenzRaisedCurrent_pullback period hPeriod metric potential component witness.patch coordinate
  rw [hField]

/-- Genuine global integration by parts for the supplied smooth metric. -/
theorem frameFreeGlobalLorenz_weak_stokes
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (test : SmoothScalarField period hPeriod) :
    (∫ point, test point * globalGeneralMetricAbelianLorenzCodifferential
      period hPeriod metric potential point component
      ∂generalLorentzVolumeMeasure period hPeriod metric) =
    -∫ point, scalarDifferential period hPeriod test point
      (inverseMetricSharp period hPeriod metric point (potential.toFun component point))
      ∂generalLorentzVolumeMeasure period hPeriod metric := by
  simp_rw [frameFreeGlobalLorenz_eq_metricCurrentDivergence]
  rw [frameFreeMetricVolumeDivergence_weak_stokes]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with point
  rw [frameFreeLorenzRaisedCurrent_apply]
  rfl

/-- The FP component is paired by the true inverse-metric gradient contraction. -/
theorem frameFreeGlobalFP_component_green
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2)
    (test : SmoothScalarField period hPeriod) :
    (∫ point, test point * globalGeneralMetricAbelianFaddeevPopov
      period hPeriod metric ghost point component
      ∂generalLorentzVolumeMeasure period hPeriod metric) =
    -∫ point, inverseMetricContraction period hPeriod metric point
      (scalarDifferential period hPeriod test point)
      (scalarDifferential period hPeriod (ghostComponent period hPeriod ghost component) point)
      ∂generalLorentzVolumeMeasure period hPeriod metric :=
  frameFreeGlobalLorenz_weak_stokes period hPeriod metric (exactGaugePotential period hPeriod ghost) component test

/-- Symmetry is proved for the actual FP operator in its metric volume. -/
theorem frameFreeGlobalFP_component_metric_symmetry
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    (∫ point, first point component * globalGeneralMetricAbelianFaddeevPopov
      period hPeriod metric second point component
      ∂generalLorentzVolumeMeasure period hPeriod metric) =
    ∫ point, second point component * globalGeneralMetricAbelianFaddeevPopov
      period hPeriod metric first point component
      ∂generalLorentzVolumeMeasure period hPeriod metric := by
  have hFirst := frameFreeGlobalFP_component_green period hPeriod metric second component
    (ghostComponent period hPeriod first component)
  have hSecond := frameFreeGlobalFP_component_green period hPeriod metric first component
    (ghostComponent period hPeriod second component)
  exact hFirst.trans ((congrArg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall
    (fun point => inverseMetricContraction_comm period hPeriod metric point _ _)))).trans hSecond.symm)

end
end P0EFTJanusProgramPT12FrameFreeLorenzGlobalStokes4D
end JanusFormal
