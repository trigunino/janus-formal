import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2CartanFirstJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D

/-! # Genuine finite-frame C² diffeomorphism Faddeev–Popov operator

De Donder acts on the first jet of the actual Cartan tensor. Both factors
use the same metric variation and only second spatial jets of metric and ghost.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2DiffeomorphismFP4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2CartanFirstJet4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "MetricCore" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "GhostCore" => FiniteFrameDiffeomorphismC2Core period hPeriod frame
local notation "Input" => MetricCore × GhostCore

def finiteFrameC2DiffeomorphismFPDomain : Set Input :=
  generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric ×ˢ Set.univ

theorem finiteFrameC2DiffeomorphismFPDomain_isOpen :
    IsOpen (finiteFrameC2DiffeomorphismFPDomain period hPeriod frame baseMetric) :=
  (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).prod isOpen_univ

/-- The actual completed composition `B_g(L_c g)`. -/
def finiteFrameC2DiffeomorphismFPCoefficient (last : Fin frame.count) (input : Input) :
    C(EffectiveQuotient period hPeriod, Real) :=
  finiteFrameC2DeDonderFirstJetCoefficient period hPeriod frame baseMetric last
    (input.1, finiteFrameC2CartanFirstJet period hPeriod frame baseMetric input.1 input.2)

theorem finiteFrameC2DiffeomorphismFPCoefficient_contDiffOn (last : Fin frame.count) :
    ContDiffOn Real ∞ (finiteFrameC2DiffeomorphismFPCoefficient period hPeriod frame baseMetric last)
      (finiteFrameC2DiffeomorphismFPDomain period hPeriod frame baseMetric) := by
  have hJet := contDiff_fst.prodMk (finiteFrameC2CartanFirstJet_contDiff period hPeriod frame baseMetric)
  have hProjection : ContDiffOn Real ∞
      (fun input : Input =>
        (input.1, finiteFrameC2CartanFirstJet period hPeriod frame baseMetric input.1 input.2))
      (finiteFrameC2DiffeomorphismFPDomain period hPeriod frame baseMetric) := hJet.contDiffOn
  have h := (finiteFrameC2DeDonderFirstJetCoefficient_contDiffOn period hPeriod frame baseMetric last).comp
    hProjection (fun _ h => ⟨h.1, Set.mem_univ _⟩)
  simp only [Function.comp_def] at h
  exact h

def finiteFrameC2DiffeomorphismFP (input : Input) :
    Fin frame.count → C(EffectiveQuotient period hPeriod, Real) :=
  fun last => finiteFrameC2DiffeomorphismFPCoefficient period hPeriod frame baseMetric last input

theorem finiteFrameC2DiffeomorphismFP_contDiffOn :
    ContDiffOn Real ∞ (finiteFrameC2DiffeomorphismFP period hPeriod frame baseMetric)
      (finiteFrameC2DiffeomorphismFPDomain period hPeriod frame baseMetric) :=
  contDiffOn_pi.mpr (finiteFrameC2DiffeomorphismFPCoefficient_contDiffOn period hPeriod frame baseMetric)

/-- Canonical ghost coefficients reproduce the existing intrinsic global FP operator. -/
theorem finiteFrameC2DiffeomorphismFPCoefficient_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod)
    (point : EffectiveQuotient period hPeriod) (last : Fin frame.count) :
    finiteFrameC2DiffeomorphismFPCoefficient period hPeriod frame baseMetric last
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
        finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame baseMetric ghost.field) point =
    globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric ghost point
      (frame.vectorAt point last) := by
  unfold finiteFrameC2DiffeomorphismFPCoefficient
  rw [finiteFrameC2CartanFirstJet_smooth_canonical period hPeriod frame baseMetric
    variation metric hMetric ghost.field]
  change finiteFrameC2DeDonderFirstJetCoefficient period hPeriod frame baseMetric last
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
      smoothFiniteFrameTensorC0FirstJet period hPeriod frame
        (smoothMetricCartanAction period hPeriod ghost.field metric.tensor)) point =
    globalGeneralMetricDeDonderLinearMap period hPeriod metric
      (smoothMetricCartanAction period hPeriod ghost.field metric.tensor) point (frame.vectorAt point last)
  exact finiteFrameC2DeDonderFirstJetCoefficient_smooth period hPeriod frame baseMetric variation
    (smoothMetricCartanAction period hPeriod ghost.field metric.tensor) metric hMetric hVariation point last

end
end P0EFTJanusFiniteFrameC2DiffeomorphismFP4D
end JanusFormal
