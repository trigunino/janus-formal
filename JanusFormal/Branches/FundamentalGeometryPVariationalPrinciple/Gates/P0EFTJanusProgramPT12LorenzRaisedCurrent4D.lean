import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameLorenzCovariantTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LorenzLocalDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D

/-! Concrete smooth raised potential and its exact holonomic pullback. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LorenzRaisedCurrent4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

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

def lorenzRaisedCurrent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2) :
    SmoothTangentField period hPeriod where
  toFun := fun point => ∑ index : Fin 4,
    finiteFramePotentialCoefficient period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) potential component index point •
      effectiveD8SmoothInverseMusical ⟨period, hPeriod⟩ metric.metric
        (finiteFrameDualCovector period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric index) point
  contMDiff_toFun := by
    apply ContMDiff.sum_section
    intro index _
    exact (finiteFramePotentialCoefficient period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) potential component index).contMDiff_toFun.smul_section
      (effectiveD8SmoothInverseMusical ⟨period, hPeriod⟩ metric.metric
        (finiteFrameDualCovector period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric index)).contMDiff

theorem lorenzRaisedCurrent_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    lorenzRaisedCurrent period hPeriod metric potential component point =
      inverseMetricSharp period hPeriod metric.metric point (potential.toFun component point) := by
  simp only [lorenzRaisedCurrent, finiteFramePotentialCoefficient_apply, effectiveD8SmoothInverseMusical_apply,
    finiteFrameDualCovector_apply]
  have h := congrArg (inverseMetricSharp period hPeriod metric.metric point)
    (finiteFrameCovector_reconstructs period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric point
      (potential.toFun component point))
  simp only [map_sum, map_smul] at h
  exact h.symm

theorem lorenzRaisedCurrent_pullback
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    pulledRegularFrameExpansion period hPeriod metric patch
        (lorenzRaisedCurrent period hPeriod metric potential component) coordinate =
      localRaisedAbelianGaugePotential period hPeriod metric.metric potential component patch coordinate := by
  let equiv := (Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4))
  apply equiv.injective
  have hFirst := coordinateMap_mfderiv_pulledRegularFrameExpansion period hPeriod metric patch
    (lorenzRaisedCurrent period hPeriod metric potential component) coordinate
  have hSecond := coordinateMap_mfderiv_localRaisedAbelianGaugePotential period hPeriod
    metric.metric potential component patch coordinate
  rw [lorenzRaisedCurrent_apply] at hFirst
  have hFirst' := hFirst.trans hSecond.symm
  simpa only [coordinateMap_mfderiv_eq_frameEquiv, pulledRegularFrameExpansionTangent,
    pulledRegularFrameExpansion, equiv] using hFirst'

end
end P0EFTJanusProgramPT12LorenzRaisedCurrent4D
end JanusFormal
