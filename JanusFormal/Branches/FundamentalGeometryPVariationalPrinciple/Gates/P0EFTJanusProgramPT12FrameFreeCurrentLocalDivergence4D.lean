import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalCurrentPullback4D

/-! Canonical weak divergence equals intrinsic weighted coordinate divergence without a volume gauge. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FrameFreeCurrentLocalDivergence4D

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

open P0EFTJanusProgramPT12FrameFreeDirectionalH1L24D
open P0EFTJanusProgramPT12FrameFreeCurrentPullback4D
open P0EFTJanusProgramPT12FrameFreeGeneratorsDivergenceZero4D
open P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D

/-- The inverse coordinate derivative preserves the redundant generator expansion. -/
theorem frameFreeCurrentPullback_eq_tenFlowExpansion
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod) (coordinate : Vector4) :
    frameFreeCurrentPullback period hPeriod patch vector coordinate =
      ∑ index : Fin 10,
        frameFreeTenFlowDualCoefficient period hPeriod metric vector index
            (patch.coordinateMap coordinate) •
          frameFreeCurrentPullback period hPeriod patch
            (canonicalTenFlowVectorField period hPeriod index) coordinate := by
  rw [frameFreeCurrentPullback_apply,
    frameFreeTenFlowDual_reconstructs period hPeriod metric vector]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro index _
  rw [frameFreeCurrentPullback_apply]
  rfl
/-- The constructed weak divergence has the actual intrinsic-density local
formula for every smooth current, with no volume-gauge hypothesis. -/
theorem frameFreeCurrentDivergence_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod) (coordinate : Vector4) :
    frameFreeTenFlowDivergence period hPeriod metric vector (patch.coordinateMap coordinate) =
      holonomicLocalDensityDivergence
        (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
        (frameFreeCurrentPullback period hPeriod patch vector) coordinate := by
  let density := localMetricVolumeFactor period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
  let coefficient (index : Fin 10) :=
    (frameFreeTenFlowDualCoefficient period hPeriod metric vector index).toFun ∘ patch.coordinateMap
  let generator (index : Fin 10) := frameFreeCurrentPullback period hPeriod patch
    (canonicalTenFlowVectorField period hPeriod index)
  let term (index : Fin 10) := fun current => coefficient index current • generator index current
  have hDensity : ContDiff Real ∞ density :=
    localMetricVolumeFactor_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
  have hCoefficient (index : Fin 10) : ContDiff Real ∞ (coefficient index) :=
    ((frameFreeTenFlowDualCoefficient period hPeriod metric vector index).contMDiff_toFun.comp
      patch.coordinateMap_contMDiff).contDiff
  have hGenerator (index : Fin 10) : ContDiff Real ∞ (generator index) :=
    frameFreeCurrentPullback_contDiff period hPeriod patch
      (canonicalTenFlowVectorField period hPeriod index)
  have hExpansion : frameFreeCurrentPullback period hPeriod patch vector =
      fun current => ∑ index : Fin 10, term index current := by
    funext current
    exact frameFreeCurrentPullback_eq_tenFlowExpansion period hPeriod metric patch vector current
  have hTerm (index : Fin 10) :
      holonomicLocalDensityDivergence density (term index) coordinate =
        frameDerivative period hPeriod Real
          (P0EFTJanusMappingTorusCanonicalTenFlowFrame4D.canonicalTenFlowFrame period hPeriod)
          (frameFreeTenFlowDualCoefficient period hPeriod metric vector index)
          (patch.coordinateMap coordinate) index := by
    rw [holonomicLocalDensityDivergence_smul density (coefficient index) (generator index)
      coordinate (hDensity.differentiable (by simp) coordinate)
      (localMetricVolumeFactor_ne_zero period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
      ((hCoefficient index).differentiable (by simp) coordinate)
      ((hGenerator index).differentiable (by simp) coordinate)]
    have hZero : holonomicLocalDensityDivergence density (generator index) coordinate = 0 :=
      frameFreeCanonicalTenFlow_holonomic_density_divergence_eq_zero period hPeriod index patch coordinate
    rw [hZero, mul_zero, zero_add]
    exact frameFreeCurrentPullback_scalarDifferential period hPeriod patch
      (canonicalTenFlowVectorField period hPeriod index)
      (frameFreeTenFlowDualCoefficient period hPeriod metric vector index) coordinate
  change _ = holonomicLocalDensityDivergence density
    (frameFreeCurrentPullback period hPeriod patch vector) coordinate
  rw [hExpansion]
  have hSum := holonomicLocalDensityDivergence_finset_sum Finset.univ density term coordinate
    (hDensity.differentiable (by simp) coordinate)
    (fun index _ => ((hCoefficient index).smul (hGenerator index)).differentiable (by simp) coordinate)
  change _ = holonomicLocalDensityDivergence density
    (fun current => ∑ index ∈ Finset.univ, term index current) coordinate
  rw [hSum]
  simp_rw [hTerm]
  rfl

end
end P0EFTJanusProgramPT12FrameFreeCurrentLocalDivergence4D
end JanusFormal
