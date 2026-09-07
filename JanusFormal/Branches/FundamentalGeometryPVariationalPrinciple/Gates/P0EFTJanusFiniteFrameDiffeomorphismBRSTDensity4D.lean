import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameBRSTPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D

/-! # The actual diffeomorphism BRST density in a finite generating family

The finite sums use the true smooth De Donder and FP operators, the actual
metric pairing, and its mobile volume ratio. Their density and action are
independent of the finite family and coefficient reference. The final C⁰
polynomial concerns independent features; it asserts no joint completed
metric-to-De-Donder or metric-to-FP regularity.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusFiniteFrameBRSTPairing4D
open P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Actual operator evaluations and redundant dual coefficients, with the moving volume. -/
def finiteFrameDiffeomorphismBRSTDensity
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) : EffectiveQuotient period hPeriod → Real :=
  fun point => globalMetricVolumeRatio period hPeriod metric point *
    ((∑ index : Fin frame.count,
      globalGeneralMetricDeDonderLinearMap period hPeriod metric state.metricPerturbation point
          (frame.vectorAt point index) *
        generalMetricFiniteFrameCoefficient period hPeriod frame reference
          state.nonminimal.nakanishiLautrup.field index point) -
      (1 / 2 : Real) * (∑ first : Fin frame.count, ∑ second : Fin frame.count,
        metric.tensor.tensor point (frame.vectorAt point first) (frame.vectorAt point second) *
          generalMetricFiniteFrameCoefficient period hPeriod frame reference
            state.nonminimal.nakanishiLautrup.field first point *
          generalMetricFiniteFrameCoefficient period hPeriod frame reference
            state.nonminimal.nakanishiLautrup.field second point) -
      (∑ index : Fin frame.count,
        globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric
            state.nonminimal.ghost point (frame.vectorAt point index) *
          generalMetricFiniteFrameCoefficient period hPeriod frame reference
            state.nonminimal.antighost.field index point))

/-- SAME-DENSITY follows from the actual finite-frame reconstruction in each pairing. -/
theorem finiteFrameDiffeomorphismBRSTDensity_eq_canonicalDensity
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameDiffeomorphismBRSTDensity period hPeriod frame reference metric state =
      globalDiffeomorphismBRSTCanonicalDensity period hPeriod metric state := by
  funext point
  have hDeDonder := finiteFrameSmoothCovector_pairing period hPeriod frame reference
    state.nonminimal.nakanishiLautrup.field point
    (globalGeneralMetricDeDonderLinearMap period hPeriod metric state.metricPerturbation point)
  have hAuxiliary := finiteFrameSmoothMetric_self_pairing period hPeriod frame reference metric
    state.nonminimal.nakanishiLautrup.field point
  have hFP := finiteFrameSmoothCovector_pairing period hPeriod frame reference
    state.nonminimal.antighost.field point
    (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric
      state.nonminimal.ghost point)
  change globalMetricVolumeRatio period hPeriod metric point *
      ((∑ index : Fin frame.count,
        globalGeneralMetricDeDonderLinearMap period hPeriod metric state.metricPerturbation point
            (frame.vectorAt point index) *
          generalMetricFiniteFrameCoefficient period hPeriod frame reference
            state.nonminimal.nakanishiLautrup.field index point) -
        (1 / 2 : Real) * (∑ first : Fin frame.count, ∑ second : Fin frame.count,
          metric.tensor.tensor point (frame.vectorAt point first) (frame.vectorAt point second) *
            generalMetricFiniteFrameCoefficient period hPeriod frame reference
              state.nonminimal.nakanishiLautrup.field first point *
            generalMetricFiniteFrameCoefficient period hPeriod frame reference
              state.nonminimal.nakanishiLautrup.field second point) -
        (∑ index : Fin frame.count,
          globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric
              state.nonminimal.ghost point (frame.vectorAt point index) *
            generalMetricFiniteFrameCoefficient period hPeriod frame reference
              state.nonminimal.antighost.field index point)) =
    globalMetricVolumeRatio period hPeriod metric point *
      (globalGeneralMetricDeDonderLinearMap period hPeriod metric state.metricPerturbation point
          (state.nonminimal.nakanishiLautrup.field point) -
        (1 / 2 : Real) * metric.tensor.tensor point (state.nonminimal.nakanishiLautrup.field point)
          (state.nonminimal.nakanishiLautrup.field point) -
        globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric
          state.nonminimal.ghost point (state.nonminimal.antighost.field point))
  rw [← hDeDonder, ← hAuxiliary, ← hFP]

theorem finiteFrameDiffeomorphismBRSTDensity_contMDiff
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (finiteFrameDiffeomorphismBRSTDensity period hPeriod frame reference metric state) := by
  rw [finiteFrameDiffeomorphismBRSTDensity_eq_canonicalDensity]
  exact (globalDiffeomorphismBRSTCanonicalDensity period hPeriod metric state).contMDiff_toFun

theorem finiteFrameDiffeomorphismBRSTDensity_integrable
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    Integrable (finiteFrameDiffeomorphismBRSTDensity period hPeriod frame reference metric state)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [finiteFrameDiffeomorphismBRSTDensity_eq_canonicalDensity]
  exact globalDiffeomorphismBRSTCanonicalDensity_integrable period hPeriod metric state

def finiteFrameDiffeomorphismBRSTAction
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) : Real :=
  ∫ point, finiteFrameDiffeomorphismBRSTDensity period hPeriod frame reference metric state point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

theorem finiteFrameDiffeomorphismBRSTAction_eq_BRST
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameDiffeomorphismBRSTAction period hPeriod frame reference metric state =
      globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state := by
  unfold finiteFrameDiffeomorphismBRSTAction
  rw [finiteFrameDiffeomorphismBRSTDensity_eq_canonicalDensity]
  exact (globalDiffeomorphismGaugeFermionBRSTVariation_eq_canonicalIntegral
    period hPeriod metric state).symm

theorem finiteFrameDiffeomorphismBRSTDensity_independent
    (firstFrame secondFrame : SmoothD8Frame period hPeriod)
    (firstReference secondReference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameDiffeomorphismBRSTDensity period hPeriod firstFrame firstReference metric state =
      finiteFrameDiffeomorphismBRSTDensity period hPeriod secondFrame secondReference metric state :=
  (finiteFrameDiffeomorphismBRSTDensity_eq_canonicalDensity period hPeriod firstFrame
    firstReference metric state).trans
      (finiteFrameDiffeomorphismBRSTDensity_eq_canonicalDensity period hPeriod secondFrame
        secondReference metric state).symm

theorem finiteFrameDiffeomorphismBRSTAction_independent
    (firstFrame secondFrame : SmoothD8Frame period hPeriod)
    (firstReference secondReference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameDiffeomorphismBRSTAction period hPeriod firstFrame firstReference metric state =
      finiteFrameDiffeomorphismBRSTAction period hPeriod secondFrame secondReference metric state :=
  (finiteFrameDiffeomorphismBRSTAction_eq_BRST period hPeriod firstFrame firstReference metric state).trans
    (finiteFrameDiffeomorphismBRSTAction_eq_BRST period hPeriod secondFrame secondReference metric state).symm

/-- The constructed global finite family realizes the same action without a global tangent basis. -/
theorem canonicalFiniteFrameDiffeomorphismBRSTAction_eq_BRST
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameDiffeomorphismBRSTAction period hPeriod (finiteSmoothTangentFrame period hPeriod)
        reference metric state =
      globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state :=
  finiteFrameDiffeomorphismBRSTAction_eq_BRST period hPeriod
    (finiteSmoothTangentFrame period hPeriod) reference metric state

private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

/-- Independent C⁰ features: volume, De Donder, metric entries, B, FP, and antighost. -/
abbrev FiniteFrameDiffeomorphismBRSTC0Features (frame : SmoothD8Frame period hPeriod) :=
  C0Scalar period hPeriod × ((Fin frame.count → C0Scalar period hPeriod) ×
    ((Fin frame.count → Fin frame.count → C0Scalar period hPeriod) ×
      ((Fin frame.count → C0Scalar period hPeriod) ×
        ((Fin frame.count → C0Scalar period hPeriod) × (Fin frame.count → C0Scalar period hPeriod)))))

def finiteFrameDiffeomorphismBRSTC0Polynomial
    (frame : SmoothD8Frame period hPeriod)
    (input : FiniteFrameDiffeomorphismBRSTC0Features period hPeriod frame) : C0Scalar period hPeriod :=
  input.1 * ((∑ i : Fin frame.count, input.2.1 i * input.2.2.2.1 i) -
    (1 / 2 : Real) • (∑ i : Fin frame.count, ∑ j : Fin frame.count,
      input.2.2.1 i j * input.2.2.2.1 i * input.2.2.2.1 j) -
    (∑ i : Fin frame.count, input.2.2.2.2.1 i * input.2.2.2.2.2 i))

/-- Polynomial regularity in independent features, without a completed operator realization claim. -/
theorem finiteFrameDiffeomorphismBRSTC0Polynomial_contDiff
    (frame : SmoothD8Frame period hPeriod) :
    ContDiff Real ∞ (finiteFrameDiffeomorphismBRSTC0Polynomial period hPeriod frame) := by
  have hDD (i : Fin frame.count) : ContDiff Real ∞
      (fun input : FiniteFrameDiffeomorphismBRSTC0Features period hPeriod frame => input.2.1 i) :=
    (contDiff_apply Real (C0Scalar period hPeriod) i).comp contDiff_snd.fst
  have hMetric (i j : Fin frame.count) : ContDiff Real ∞
      (fun input : FiniteFrameDiffeomorphismBRSTC0Features period hPeriod frame => input.2.2.1 i j) :=
    (contDiff_apply Real (C0Scalar period hPeriod) j).comp
      ((contDiff_apply Real (Fin frame.count → C0Scalar period hPeriod) i).comp contDiff_snd.snd.fst)
  have hB (i : Fin frame.count) : ContDiff Real ∞
      (fun input : FiniteFrameDiffeomorphismBRSTC0Features period hPeriod frame => input.2.2.2.1 i) :=
    (contDiff_apply Real (C0Scalar period hPeriod) i).comp contDiff_snd.snd.snd.fst
  have hFP (i : Fin frame.count) : ContDiff Real ∞
      (fun input : FiniteFrameDiffeomorphismBRSTC0Features period hPeriod frame => input.2.2.2.2.1 i) :=
    (contDiff_apply Real (C0Scalar period hPeriod) i).comp contDiff_snd.snd.snd.snd.fst
  have hAntighost (i : Fin frame.count) : ContDiff Real ∞
      (fun input : FiniteFrameDiffeomorphismBRSTC0Features period hPeriod frame => input.2.2.2.2.2 i) :=
    (contDiff_apply Real (C0Scalar period hPeriod) i).comp contDiff_snd.snd.snd.snd.snd
  unfold finiteFrameDiffeomorphismBRSTC0Polynomial
  exact contDiff_fst.mul
    (((ContDiff.sum (fun i _ => (hDD i).mul (hB i))).sub
      ((ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
        ((hMetric i j).mul (hB i)).mul (hB j)))).const_smul (1 / 2 : Real))).sub
      (ContDiff.sum (fun i _ => (hFP i).mul (hAntighost i))))

end
end P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D
end JanusFormal
