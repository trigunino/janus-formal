import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

/-! # Exact diffeomorphism BRST defect under a change of metric

The perturbation and full nonminimal state are fixed. The volume ratio,
de Donder operator, metric lowering of B, and FP operator all vary.
This compares the existing smooth real-linearized BRST actions; it does
not assert a completed variable-metric operator extension.
-/

namespace JanusFormal
namespace P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- The actual density `(D_g H)(B) - g(B,B)/2 - (FP_g c)(cbar)`. -/
def globalDiffeomorphismBRSTMetricDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    globalCovectorVectorPairingField period hPeriod
        (globalGeneralMetricDeDonderLinearMap period hPeriod metric state.metricPerturbation)
        state.nonminimal.nakanishiLautrup.field point -
      (1 / 2 : Real) * globalCovectorVectorPairingField period hPeriod
        (globalSmoothMetricFlat period hPeriod metric state.nonminimal.nakanishiLautrup.field)
        state.nonminimal.nakanishiLautrup.field point -
      globalCovectorVectorPairingField period hPeriod
        (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
          period hPeriod metric state.nonminimal.ghost)
        state.nonminimal.antighost.field point
  contMDiff_toFun :=
    (((globalCovectorVectorPairingField period hPeriod _ _).contMDiff_toFun).sub
      (contMDiff_const.mul
        (globalCovectorVectorPairingField period hPeriod _ _).contMDiff_toFun)).sub
      (globalCovectorVectorPairingField period hPeriod _ _).contMDiff_toFun

/-- The moving volume is represented by its genuine ratio to canonical volume. -/
def globalDiffeomorphismBRSTCanonicalDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point => globalMetricVolumeRatio period hPeriod metric point *
    globalDiffeomorphismBRSTMetricDensity period hPeriod metric state point
  contMDiff_toFun :=
    (globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun.mul
      (globalDiffeomorphismBRSTMetricDensity period hPeriod metric state).contMDiff_toFun

private theorem volumeWeightedSmooth_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Integrable (fun point => globalMetricVolumeRatio period hPeriod metric point * field point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  ((globalMetricVolumeRatio_continuous period hPeriod metric).mul
    field.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem globalDiffeomorphismBRSTCanonicalDensity_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    Integrable (globalDiffeomorphismBRSTCanonicalDensity period hPeriod metric state)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (globalDiffeomorphismBRSTCanonicalDensity period hPeriod metric state
    ).contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Exact conversion of all three terms from the mobile volume to canonical volume. -/
theorem globalDiffeomorphismGaugeFermionBRSTVariation_eq_canonicalIntegral
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state =
      ∫ point, globalDiffeomorphismBRSTCanonicalDensity period hPeriod metric state point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let deDonder := globalCovectorVectorPairingField period hPeriod
    (globalGeneralMetricDeDonderLinearMap period hPeriod metric state.metricPerturbation)
    state.nonminimal.nakanishiLautrup.field
  let metricFlat := globalCovectorVectorPairingField period hPeriod
    (globalSmoothMetricFlat period hPeriod metric state.nonminimal.nakanishiLautrup.field)
    state.nonminimal.nakanishiLautrup.field
  let fp := globalCovectorVectorPairingField period hPeriod
    (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
      period hPeriod metric state.nonminimal.ghost) state.nonminimal.antighost.field
  have hD := volumeWeightedSmooth_integrable period hPeriod metric deDonder
  have hB := volumeWeightedSmooth_integrable period hPeriod metric metricFlat
  have hFP := volumeWeightedSmooth_integrable period hPeriod metric fp
  rw [globalDiffeomorphismGaugeFermionBRSTVariation_formula]
  unfold globalDiffeomorphismGaugeFermionBRSTMixedAction globalIntegratedCovectorVectorPairing
  simp_rw [integral_generalLorentzVolumeMeasure_eq_reference]
  calc
    _ = ∫ point,
        ((globalMetricVolumeRatio period hPeriod metric point * deDonder point -
          (1 / 2 : Real) * (globalMetricVolumeRatio period hPeriod metric point *
            metricFlat point)) - globalMetricVolumeRatio period hPeriod metric point * fp point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      have hIntegral := integral_sub (hD.sub (hB.const_mul (1 / 2 : Real))) hFP
      simp only [Pi.sub_apply] at hIntegral
      rw [integral_sub hD (hB.const_mul (1 / 2 : Real)), integral_const_mul] at hIntegral
      exact hIntegral.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point => by
        change _ = globalMetricVolumeRatio period hPeriod metric point *
          (deDonder point - (1 / 2 : Real) * metricFlat point - fp point)
        ring

/-- Volume change plus the full change of the operator and metric-flat density. -/
def globalDiffeomorphismBRSTMetricChangeDensity
    (metric reference : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    (globalMetricVolumeRatio period hPeriod metric point -
      globalMetricVolumeRatio period hPeriod reference point) *
      globalDiffeomorphismBRSTMetricDensity period hPeriod reference state point +
    globalMetricVolumeRatio period hPeriod metric point *
      (globalDiffeomorphismBRSTMetricDensity period hPeriod metric state point -
        globalDiffeomorphismBRSTMetricDensity period hPeriod reference state point)
  contMDiff_toFun :=
    (((globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun.sub
      (globalSmoothMetricVolumeRatio period hPeriod reference).contMDiff_toFun).mul
        (globalDiffeomorphismBRSTMetricDensity period hPeriod reference state).contMDiff_toFun).add
      ((globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun.mul
        ((globalDiffeomorphismBRSTMetricDensity period hPeriod metric state).contMDiff_toFun.sub
          (globalDiffeomorphismBRSTMetricDensity period hPeriod reference state).contMDiff_toFun))

theorem globalDiffeomorphismBRSTMetricChangeDensity_eq_sub
    (metric reference : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalDiffeomorphismBRSTMetricChangeDensity period hPeriod metric reference state point =
      globalDiffeomorphismBRSTCanonicalDensity period hPeriod metric state point -
        globalDiffeomorphismBRSTCanonicalDensity period hPeriod reference state point := by
  change (_ - _) * _ + _ * (_ - _) = _ * _ - _ * _
  ring

theorem globalDiffeomorphismBRSTMetricChangeDensity_integrable
    (metric reference : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    Integrable (globalDiffeomorphismBRSTMetricChangeDensity period hPeriod metric reference state)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (globalDiffeomorphismBRSTMetricChangeDensity period hPeriod metric reference state
    ).contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

def globalDiffeomorphismBRSTMetricChangeAction
    (metric reference : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) : Real :=
  ∫ point, globalDiffeomorphismBRSTMetricChangeDensity period hPeriod metric reference state point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

/-- No metric-flat or volume term is dropped from the action difference. -/
theorem globalDiffeomorphismGaugeFermionBRSTVariation_sub_eq_metricChange
    (metric reference : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state -
      globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod reference state =
      globalDiffeomorphismBRSTMetricChangeAction period hPeriod metric reference state := by
  rw [globalDiffeomorphismGaugeFermionBRSTVariation_eq_canonicalIntegral,
    globalDiffeomorphismGaugeFermionBRSTVariation_eq_canonicalIntegral,
    ← integral_sub
      (globalDiffeomorphismBRSTCanonicalDensity_integrable period hPeriod metric state)
      (globalDiffeomorphismBRSTCanonicalDensity_integrable period hPeriod reference state)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    (globalDiffeomorphismBRSTMetricChangeDensity_eq_sub
      period hPeriod metric reference state point).symm

/-- Both sectors use the same nonminimal triple and their actual Einstein weights. -/
def globalCandidateADiagonalDiffeomorphismBRSTMetricChangeAction
    (couplings : GlobalCandidateAActionCouplings)
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) : Real :=
  candidateAPlusEinsteinKineticWeight couplings *
    globalDiffeomorphismBRSTMetricChangeAction period hPeriod (metric .plus) (reference .plus)
      (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .plus state) +
  candidateAMinusEinsteinKineticWeight couplings *
    globalDiffeomorphismBRSTMetricChangeAction period hPeriod (metric .minus) (reference .minus)
      (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .minus state)

theorem globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation_sub_eq_metricChange
    (couplings : GlobalCandidateAActionCouplings)
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod couplings metric state -
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod couplings reference state =
      globalCandidateADiagonalDiffeomorphismBRSTMetricChangeAction
        period hPeriod couplings metric reference state := by
  unfold globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
    globalCandidateADiagonalDiffeomorphismBRSTMetricChangeAction
  rw [← globalDiffeomorphismGaugeFermionBRSTVariation_sub_eq_metricChange,
    ← globalDiffeomorphismGaugeFermionBRSTVariation_sub_eq_metricChange]
  ring

end
end P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D
end JanusFormal
