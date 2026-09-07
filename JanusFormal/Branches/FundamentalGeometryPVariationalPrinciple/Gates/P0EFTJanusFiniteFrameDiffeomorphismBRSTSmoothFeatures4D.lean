import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismC2Core4D

/-! # Realization of finite-frame BRST features

The volume, De Donder, metric, and FP entries below are obtained from the actual
smooth operators. A bounded assembly map reads B and antighost from the completed
nonminimal packet. On smooth packets, the FP feature uses that same ghost.
No completed metric-to-operator or ghost-to-FP extension is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

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
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

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
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Operator features in the order volume, De Donder, metric entries, FP. -/
abbrev FiniteFrameDiffeomorphismBRSTOperatorC0Features (frame : SmoothD8Frame period hPeriod) :=
  C0Scalar period hPeriod × ((Fin frame.count → C0Scalar period hPeriod) ×
    ((Fin frame.count → Fin frame.count → C0Scalar period hPeriod) ×
      (Fin frame.count → C0Scalar period hPeriod)))

def finiteFrameDiffeomorphismBRSTSmoothOperatorFeatures
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    FiniteFrameDiffeomorphismBRSTOperatorC0Features period hPeriod frame :=
  (smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (globalSmoothMetricVolumeRatio period hPeriod metric),
    ((fun index => smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (globalCovectorVectorPairingField period hPeriod
        (globalGeneralMetricDeDonderLinearMap period hPeriod metric state.metricPerturbation)
        (smoothFrameVectorSection period hPeriod frame index))),
      ((fun first second => smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalCovectorVectorPairingField period hPeriod
          (globalSmoothMetricFlat period hPeriod metric (smoothFrameVectorSection period hPeriod frame first))
          (smoothFrameVectorSection period hPeriod frame second))),
        (fun index => smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (globalCovectorVectorPairingField period hPeriod
            (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric state.nonminimal.ghost)
            (smoothFrameVectorSection period hPeriod frame index))))))

def finiteFrameDiffeomorphismBRSTSmoothFeatures
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    FiniteFrameDiffeomorphismBRSTC0Features period hPeriod frame :=
  let operators := finiteFrameDiffeomorphismBRSTSmoothOperatorFeatures period hPeriod frame metric state
  (operators.1, (operators.2.1, (operators.2.2.1,
    (finiteFrameSmoothDiffeomorphismC0Coefficients period hPeriod frame reference state.nonminimal.nakanishiLautrup.field,
      (operators.2.2.2,
        finiteFrameSmoothDiffeomorphismC0Coefficients period hPeriod frame reference state.nonminimal.antighost.field)))))

/-- Evaluating the polynomial on realized smooth features is the actual finite density. -/
theorem finiteFrameDiffeomorphismBRSTC0Polynomial_smooth_apply
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) (point : EffectiveQuotient period hPeriod) :
    finiteFrameDiffeomorphismBRSTC0Polynomial period hPeriod frame
        (finiteFrameDiffeomorphismBRSTSmoothFeatures period hPeriod frame reference metric state) point =
      finiteFrameDiffeomorphismBRSTDensity period hPeriod frame reference metric state point := by
  simp only [finiteFrameDiffeomorphismBRSTC0Polynomial, finiteFrameDiffeomorphismBRSTSmoothFeatures,
    finiteFrameDiffeomorphismBRSTSmoothOperatorFeatures, finiteFrameSmoothDiffeomorphismC0Coefficients,
    ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  rfl

theorem finiteFrameDiffeomorphismBRSTC0Polynomial_smooth
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameDiffeomorphismBRSTC0Polynomial period hPeriod frame
        (finiteFrameDiffeomorphismBRSTSmoothFeatures period hPeriod frame reference metric state) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalDiffeomorphismBRSTCanonicalDensity period hPeriod metric state) := by
  apply ContinuousMap.ext
  intro point
  rw [finiteFrameDiffeomorphismBRSTC0Polynomial_smooth_apply,
    finiteFrameDiffeomorphismBRSTDensity_eq_canonicalDensity]
  all_goals rfl

/-- Canonical integration is a bounded linear map on the realized C⁰ density. -/
def finiteFrameBRSTCanonicalIntegralCLM : C0Scalar period hPeriod →L[Real] Real :=
  (L1.integralCLM (α := EffectiveQuotient period hPeriod) (E := Real)
    (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).comp
      (ContinuousMap.toLp (1 : ENNReal) (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) Real)

theorem finiteFrameBRSTCanonicalIntegralCLM_apply (field : C0Scalar period hPeriod) :
    finiteFrameBRSTCanonicalIntegralCLM period hPeriod field =
      ∫ point, field point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold finiteFrameBRSTCanonicalIntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (𝕜 := Real)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field)

theorem finiteFrameDiffeomorphismBRSTSmoothFeatures_integral_eq_BRST
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameBRSTCanonicalIntegralCLM period hPeriod
        (finiteFrameDiffeomorphismBRSTC0Polynomial period hPeriod frame
          (finiteFrameDiffeomorphismBRSTSmoothFeatures period hPeriod frame reference metric state)) =
      globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state := by
  rw [finiteFrameDiffeomorphismBRSTC0Polynomial_smooth, finiteFrameBRSTCanonicalIntegralCLM_apply]
  exact (globalDiffeomorphismGaugeFermionBRSTVariation_eq_canonicalIntegral period hPeriod metric state).symm

/-- Bounded attachment of completed B and antighost to independently supplied operator features.
The ghost remains in the source packet for the operator realization stage. -/
def finiteFrameDiffeomorphismBRSTAttachNonminimalC2 (frame : SmoothD8Frame period hPeriod) :
    (FiniteFrameDiffeomorphismBRSTOperatorC0Features period hPeriod frame ×
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) →L[Real]
        FiniteFrameDiffeomorphismBRSTC0Features period hPeriod frame := by
  let operators :
      (FiniteFrameDiffeomorphismBRSTOperatorC0Features period hPeriod frame ×
        FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) →L[Real]
          FiniteFrameDiffeomorphismBRSTOperatorC0Features period hPeriod frame :=
    ContinuousLinearMap.fst Real _ _
  let fields :
      (FiniteFrameDiffeomorphismBRSTOperatorC0Features period hPeriod frame ×
        FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) →L[Real]
          FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame :=
    ContinuousLinearMap.snd Real _ _
  let rho := (ContinuousLinearMap.fst Real _ _).comp operators
  let dd := (ContinuousLinearMap.fst Real _ _).comp ((ContinuousLinearMap.snd Real _ _).comp operators)
  let metric := (ContinuousLinearMap.fst Real _ _).comp
    ((ContinuousLinearMap.snd Real _ _).comp ((ContinuousLinearMap.snd Real _ _).comp operators))
  let fp := (ContinuousLinearMap.snd Real _ _).comp
    ((ContinuousLinearMap.snd Real _ _).comp ((ContinuousLinearMap.snd Real _ _).comp operators))
  let B := (finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).comp
    ((ContinuousLinearMap.fst Real _ _).comp fields)
  let antighost := (finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).comp
    ((ContinuousLinearMap.fst Real _ _).comp ((ContinuousLinearMap.snd Real _ _).comp fields))
  exact rho.prod (dd.prod (metric.prod (B.prod (fp.prod antighost))))

@[simp] theorem finiteFrameDiffeomorphismBRSTAttachNonminimalC2_apply
    (frame : SmoothD8Frame period hPeriod)
    (operators : FiniteFrameDiffeomorphismBRSTOperatorC0Features period hPeriod frame)
    (fields : FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :
    finiteFrameDiffeomorphismBRSTAttachNonminimalC2 period hPeriod frame (operators, fields) =
      (operators.1, (operators.2.1, (operators.2.2.1,
        (finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame fields.1,
          (operators.2.2.2, finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame fields.2.1))))) := rfl

theorem finiteFrameDiffeomorphismBRSTAttachNonminimalC2_smooth
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameDiffeomorphismBRSTAttachNonminimalC2 period hPeriod frame
        (finiteFrameDiffeomorphismBRSTSmoothOperatorFeatures period hPeriod frame metric state,
          finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame reference state.nonminimal) =
      finiteFrameDiffeomorphismBRSTSmoothFeatures period hPeriod frame reference metric state := by
  simp only [finiteFrameDiffeomorphismBRSTAttachNonminimalC2_apply,
    finiteFrameSmoothDiffeomorphismNonminimalC2Core, finiteFrameDiffeomorphismC2ToContinuous_smooth,
    finiteFrameDiffeomorphismBRSTSmoothFeatures]

/-- A C∞ polynomial on independent operator features and the full completed nonminimal source. -/
theorem finiteFrameDiffeomorphismBRSTAttachedPolynomial_contDiff
    (frame : SmoothD8Frame period hPeriod) :
    ContDiff Real ∞ (fun input => finiteFrameDiffeomorphismBRSTC0Polynomial period hPeriod frame
      (finiteFrameDiffeomorphismBRSTAttachNonminimalC2 period hPeriod frame input)) := by
  have h := (finiteFrameDiffeomorphismBRSTC0Polynomial_contDiff period hPeriod frame).comp
    (finiteFrameDiffeomorphismBRSTAttachNonminimalC2 period hPeriod frame).contDiff
  simp only [Function.comp_def] at h
  exact h

/-- SAME-ACTION with B/cbar read through the actual completed coefficient maps and the same smooth ghost in FP. -/
theorem finiteFrameDiffeomorphismBRSTAttachedPolynomial_smooth_eq_BRST
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameBRSTCanonicalIntegralCLM period hPeriod
        (finiteFrameDiffeomorphismBRSTC0Polynomial period hPeriod frame
          (finiteFrameDiffeomorphismBRSTAttachNonminimalC2 period hPeriod frame
            (finiteFrameDiffeomorphismBRSTSmoothOperatorFeatures period hPeriod frame metric state,
              finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame reference state.nonminimal))) =
      globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state := by
  rw [finiteFrameDiffeomorphismBRSTAttachNonminimalC2_smooth]
  exact finiteFrameDiffeomorphismBRSTSmoothFeatures_integral_eq_BRST period hPeriod frame
    reference metric state

end
end P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
end JanusFormal
