import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DiffeomorphismFP4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2CanonicalVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

/-! # Genuine mobile finite-frame C² diffeomorphism BRST action

Metric, tensor, and the total B/antighost/ghost fields are independent inputs.
The volume, De Donder, metric pairing and FP are all computed from these
inputs; canonical integration gives the same action as the smooth BRST variation.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2DiffeomorphismFP4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
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

/-- Slots are metric variation, tensor perturbation, and total `(B, cbar, c)`. -/
abbrev FiniteFrameC2DiffeomorphismBRSTCore
    (frame : SmoothD8Frame period hPeriod) (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :=
  GeneralMetricRelativeC2Core period hPeriod frame baseMetric ×
    (GeneralMetricRelativeC2Core period hPeriod frame baseMetric ×
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame)

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Input" => FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame baseMetric

/-- The volume domain already includes the inverse-metric domain. -/
def finiteFrameC2DiffeomorphismBRSTDomain : Set Input :=
  generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric ×ˢ Set.univ

theorem finiteFrameC2DiffeomorphismBRSTDomain_isOpen :
    IsOpen (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric) :=
  (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame baseMetric).prod isOpen_univ

/-- Every operator slot is computed from the same metric and source fields. -/
def finiteFrameC2DiffeomorphismBRSTOperatorFeatures (input : Input) :
    FiniteFrameDiffeomorphismBRSTOperatorC0Features period hPeriod frame :=
  (finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric input.1,
    ((fun index => finiteFrameC2DeDonderCoefficient period hPeriod frame baseMetric index
      (input.1, input.2.1)),
      ((fun first second => finiteFrameMetricC0Coefficient period hPeriod frame baseMetric first second input.1),
        finiteFrameC2DiffeomorphismFP period hPeriod frame baseMetric (input.1, input.2.2.2.2))))

theorem finiteFrameC2DiffeomorphismBRSTOperatorFeatures_contDiffOn_two :
    ContDiffOn Real 2 (finiteFrameC2DiffeomorphismBRSTOperatorFeatures period hPeriod frame baseMetric)
      (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric) := by
  have hVolume := (finiteFrameCanonicalVolumeC0_contDiffOn_two period hPeriod frame baseMetric).comp
    (contDiff_fst.contDiffOn : ContDiffOn Real 2 (fun input : Input => input.1)
      (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric)) (fun _ h => h.1)
  have hTensorProjection : ContDiffOn Real ∞ (fun input : Input => (input.1, input.2.1))
      (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric) :=
    (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
  have hDD (index : Fin frame.count) : ContDiffOn Real 2
      (fun input : Input => finiteFrameC2DeDonderCoefficient period hPeriod frame baseMetric index
        (input.1, input.2.1)) (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric) := by
    have h := (finiteFrameC2DeDonderCoefficient_contDiffOn period hPeriod frame baseMetric index).comp
      hTensorProjection (fun _ h => ⟨h.1.1, Set.mem_univ _⟩)
    simp only [Function.comp_def] at h
    exact h.of_le (WithTop.coe_le_coe.mpr le_top)
  have hMetric (first second : Fin frame.count) : ContDiff Real ∞
      (fun input : Input => finiteFrameMetricC0Coefficient period hPeriod frame baseMetric first second input.1) :=
    (finiteFrameMetricC0Coefficient_contDiff period hPeriod frame baseMetric first second).comp contDiff_fst
  have hGhostProjection : ContDiffOn Real ∞ (fun input : Input => (input.1, input.2.2.2.2))
      (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric) :=
    (contDiff_fst.prodMk contDiff_snd.snd.snd.snd).contDiffOn
  have hFP := (finiteFrameC2DiffeomorphismFP_contDiffOn period hPeriod frame baseMetric).comp
    hGhostProjection (fun _ h => ⟨h.1.1, Set.mem_univ _⟩)
  simp only [Function.comp_def] at hVolume hFP
  have h := hVolume.prodMk ((contDiffOn_pi.mpr hDD).prodMk
    ((contDiffOn_pi.mpr fun first => contDiffOn_pi.mpr fun second =>
      (hMetric first second).contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)).prodMk (hFP.of_le (WithTop.coe_le_coe.mpr le_top))))
  exact h

def finiteFrameC2DiffeomorphismBRSTDensity (input : Input) : C(EffectiveQuotient period hPeriod, Real) :=
  finiteFrameDiffeomorphismBRSTC0Polynomial period hPeriod frame
    (finiteFrameDiffeomorphismBRSTAttachNonminimalC2 period hPeriod frame
      (finiteFrameC2DiffeomorphismBRSTOperatorFeatures period hPeriod frame baseMetric input, input.2.2))

theorem finiteFrameC2DiffeomorphismBRSTDensity_contDiffOn_two :
    ContDiffOn Real 2 (finiteFrameC2DiffeomorphismBRSTDensity period hPeriod frame baseMetric)
      (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric) := by
  have hInput := (finiteFrameC2DiffeomorphismBRSTOperatorFeatures_contDiffOn_two
    period hPeriod frame baseMetric).prodMk
      (contDiff_snd.snd.contDiffOn : ContDiffOn Real 2 (fun input : Input => input.2.2)
        (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric))
  have hPolynomial : ContDiff Real 2 (fun input => finiteFrameDiffeomorphismBRSTC0Polynomial period hPeriod frame
      (finiteFrameDiffeomorphismBRSTAttachNonminimalC2 period hPeriod frame input)) :=
    (finiteFrameDiffeomorphismBRSTAttachedPolynomial_contDiff period hPeriod frame).of_le (WithTop.coe_le_coe.mpr le_top)
  have h := hPolynomial.comp_contDiffOn hInput
  simp only [Function.comp_def] at h
  exact h

def finiteFrameC2DiffeomorphismBRSTAction (input : Input) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameC2DiffeomorphismBRSTDensity period hPeriod frame baseMetric input)

theorem finiteFrameC2DiffeomorphismBRSTAction_eq_integral (input : Input) :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric input =
      ∫ point, finiteFrameC2DiffeomorphismBRSTDensity period hPeriod frame baseMetric input point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod :=
  finiteFrameBRSTCanonicalIntegralCLM_apply period hPeriod _

theorem finiteFrameC2DiffeomorphismBRSTAction_contDiffOn_two :
    ContDiffOn Real 2 (finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric)
      (finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric) := by
  have h := (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).contDiff.comp_contDiffOn
    (finiteFrameC2DiffeomorphismBRSTDensity_contDiffOn_two period hPeriod frame baseMetric)
  simp only [Function.comp_def] at h
  exact h

/-- The actual Fréchet derivative of this concrete integrated action. -/
def finiteFrameC2DiffeomorphismBRSTEuler (input : Input) : Input →L[Real] Real :=
  fderiv Real (finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric) input

theorem finiteFrameC2DiffeomorphismBRSTAction_hasFDerivAt (input : Input)
    (hInput : input ∈ finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric) :
    HasFDerivAt (finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric)
      (finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric input) input :=
  ((finiteFrameC2DiffeomorphismBRSTAction_contDiffOn_two period hPeriod frame baseMetric input hInput).contDiffAt
    ((finiteFrameC2DiffeomorphismBRSTDomain_isOpen period hPeriod frame baseMetric).mem_nhds hInput)).differentiableAt
      (by simp) |>.hasFDerivAt

/-- The lift retains the tensor and all three given nonminimal fields. -/
def finiteFrameSmoothDiffeomorphismBRSTCore
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) : Input :=
  (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric state.metricPerturbation,
      finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame baseMetric state.nonminimal))

theorem finiteFrameSmoothDiffeomorphismBRSTCore_mem
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod)
    (hVolume : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric) :
    finiteFrameSmoothDiffeomorphismBRSTCore period hPeriod frame baseMetric variation state ∈
      finiteFrameC2DiffeomorphismBRSTDomain period hPeriod frame baseMetric :=
  ⟨hVolume, Set.mem_univ _⟩

/-- Exact operator realization, including FP applied to the same source ghost. -/
theorem finiteFrameC2DiffeomorphismBRSTOperatorFeatures_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVolume : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameC2DiffeomorphismBRSTOperatorFeatures period hPeriod frame baseMetric
      (finiteFrameSmoothDiffeomorphismBRSTCore period hPeriod frame baseMetric variation state) =
    finiteFrameDiffeomorphismBRSTSmoothOperatorFeatures period hPeriod frame metric state := by
  apply Prod.ext
  · exact finiteFrameCanonicalVolumeC0_smooth period hPeriod frame baseMetric variation metric hMetric hVolume
  · apply Prod.ext
    · funext index
      apply ContinuousMap.ext
      intro point
      exact finiteFrameC2DeDonderCoefficient_smooth period hPeriod frame baseMetric variation
        state.metricPerturbation metric hMetric hVolume.1 point index
    · apply Prod.ext
      · funext first second
        apply ContinuousMap.ext
        intro point
        have h := congrArg (fun field : C(EffectiveQuotient period hPeriod, Real) => field point)
          (finiteFrameMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric first second)
        exact h
      · funext index
        apply ContinuousMap.ext
        intro point
        exact finiteFrameC2DiffeomorphismFPCoefficient_smooth period hPeriod frame baseMetric variation
          metric hMetric hVolume.1 state.nonminimal.ghost point index

theorem finiteFrameC2DiffeomorphismBRSTAction_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVolume : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
      (finiteFrameSmoothDiffeomorphismBRSTCore period hPeriod frame baseMetric variation state) =
    globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state := by
  unfold finiteFrameC2DiffeomorphismBRSTAction finiteFrameC2DiffeomorphismBRSTDensity
  rw [finiteFrameC2DiffeomorphismBRSTOperatorFeatures_smooth period hPeriod frame baseMetric
    variation metric hMetric hVolume state]
  exact finiteFrameDiffeomorphismBRSTAttachedPolynomial_smooth_eq_BRST period hPeriod frame baseMetric metric state

end
end P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
end JanusFormal
