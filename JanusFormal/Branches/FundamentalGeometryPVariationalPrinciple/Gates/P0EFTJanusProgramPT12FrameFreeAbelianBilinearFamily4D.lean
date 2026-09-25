import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeAbelianOperatorFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

/-! The native Abelian BRST action is the diagonal of a smooth family of real
bilinear forms. Its actual second derivative at zero freezes only the metric coefficient. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators

section Bilinear
variable {E F G H X : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G] [NormedAddCommGroup H] [NormedSpace Real H]
  [NormedAddCommGroup X] [NormedSpace Real X]
local instance : NormedAddCommGroup (E →L[Real] G) := inferInstance
local instance : NormedSpace Real (E →L[Real] G) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] H) := inferInstance
local instance : NormedSpace Real (E →L[Real] H) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] E →L[Real] H) := inferInstance
local instance : NormedSpace Real (E →L[Real] E →L[Real] H) := inferInstance

private theorem bilinearComp_right_contDiffOn
    (B : F →L[Real] G →L[Real] H) (u : E →L[Real] F)
    {v : X → E →L[Real] G} {s : Set X} (hv : ContDiffOn Real ∞ v s) :
    ContDiffOn Real ∞ (fun x => B.bilinearComp u (v x)) s := by
  let productMap : (E →L[Real] G) →L[Real] E →L[Real] E →L[Real] H :=
    (ContinuousLinearMap.precompR E (B.comp u)).flip
  have hEq : (fun x => B.bilinearComp u (v x)) =
      (fun x => productMap (v x)) := by
    funext x
    ext first second
    rfl
  rw [hEq]
  exact productMap.contDiff.comp_contDiffOn hv
end Bilinear

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusProgramPT12FrameFreeAbelianOperatorFamily4D
open P0EFTJanusProgramPT12BilinearSecondJetFreeze4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance

abbrev FrameFreeAbelianBRSTFields (frame : SmoothD8Frame period hPeriod) :=
  FiniteFrameAbelianGaugeC2Core period hPeriod frame × FiniteFrameAbelianNonminimalC2Core period hPeriod

variable (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Fields" => FrameFreeAbelianBRSTFields period hPeriod frame
local notation "C0" => C(Q period hPeriod, Real)
local notation "Metric" => GeneralMetricRelativeC2Core period hPeriod frame metric
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := inferInstance
local instance : NormedAddCommGroup Metric := inferInstance
local instance : NormedSpace Real Metric := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] C0) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Fields →L[Real] C0) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Fields →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup ((Fields →L[Real] C0) →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real ((Fields →L[Real] C0) →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (FiniteFrameC2AbelianBRSTCore period hPeriod frame metric) := inferInstance
local instance : NormedSpace Real (FiniteFrameC2AbelianBRSTCore period hPeriod frame metric) := inferInstance
local instance : NormedAddCommGroup (FiniteFrameC2AbelianBRSTCore period hPeriod frame metric →L[Real] Real) :=
  inferInstance
local instance : NormedSpace Real (FiniteFrameC2AbelianBRSTCore period hPeriod frame metric →L[Real] Real) :=
  inferInstance

private def potentialProjection : Fields →L[Real] FiniteFrameAbelianGaugeC2Core period hPeriod frame :=
  ContinuousLinearMap.fst Real _ _
private def bProjection : Fields →L[Real] FiniteFrameAbelianGhostC2Core period hPeriod :=
  (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _)
private def antighostProjection : Fields →L[Real] FiniteFrameAbelianGhostC2Core period hPeriod :=
  (ContinuousLinearMap.fst Real _ _).comp
    ((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _))
private def ghostProjection : Fields →L[Real] FiniteFrameAbelianGhostC2Core period hPeriod :=
  (ContinuousLinearMap.snd Real _ _).comp
    ((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _))
private def bReadout (component : Fin 2) : Fields →L[Real] C0 :=
  (finiteFrameAbelianScalarC2Readout period hPeriod component).comp (bProjection period hPeriod frame)
private def antighostReadout (component : Fin 2) : Fields →L[Real] C0 :=
  (finiteFrameAbelianScalarC2Readout period hPeriod component).comp (antighostProjection period hPeriod frame)

def frameFreeAbelianBRSTBilinearDensity
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric) : Fields →L[Real] Fields →L[Real] C0 :=
  ∑ component : Fin 2,
    ((ContinuousLinearMap.mul Real C0).bilinearComp (bReadout period hPeriod frame component)
        ((frameFreeAbelianLorenzOperatorFamily period hPeriod frame metric component variation).comp
          (potentialProjection period hPeriod frame)) -
      (1 / 2 : Real) • (ContinuousLinearMap.mul Real C0).bilinearComp
        (bReadout period hPeriod frame component) (bReadout period hPeriod frame component) +
      (ContinuousLinearMap.mul Real C0).bilinearComp (antighostReadout period hPeriod frame component)
        ((frameFreeAbelianFPOperatorFamily period hPeriod frame metric component variation).comp
          (ghostProjection period hPeriod frame)))

def frameFreeAbelianBRSTBilinearCoefficient
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric) : Fields →L[Real] Fields →L[Real] Real :=
  (ContinuousLinearMap.compL Real Fields C0 Real (finiteFrameBRSTCanonicalIntegralCLM period hPeriod)).comp
    (frameFreeAbelianBRSTBilinearDensity period hPeriod frame metric variation)

theorem frameFreeAbelianBRSTBilinearDensity_contDiffOn :
    ContDiffOn Real ∞ (frameFreeAbelianBRSTBilinearDensity period hPeriod frame metric)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) := by
  unfold frameFreeAbelianBRSTBilinearDensity
  apply ContDiffOn.sum
  intro component _
  have hLorenz := (frameFreeAbelianLorenzOperatorFamily_contDiffOn period hPeriod frame metric component).clm_comp
    (show ContDiffOn Real ∞ (fun _ : Metric => potentialProjection period hPeriod frame)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) from contDiffOn_const)
  have hFP := (frameFreeAbelianFPOperatorFamily_contDiffOn period hPeriod frame metric component).clm_comp
    (show ContDiffOn Real ∞ (fun _ : Metric => ghostProjection period hPeriod frame)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) from contDiffOn_const)
  have hBB : ContDiffOn Real ∞ (fun _ : Metric =>
      (ContinuousLinearMap.mul Real C0).bilinearComp (bReadout period hPeriod frame component)
        (bReadout period hPeriod frame component))
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) := contDiffOn_const
  exact ((bilinearComp_right_contDiffOn (ContinuousLinearMap.mul Real C0)
    (bReadout period hPeriod frame component) hLorenz).sub (hBB.const_smul (1 / 2 : Real))).add
    (bilinearComp_right_contDiffOn (ContinuousLinearMap.mul Real C0)
      (antighostReadout period hPeriod frame component) hFP)

theorem frameFreeAbelianBRSTBilinearCoefficient_contDiffOn :
    ContDiffOn Real ∞ (frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) := by
  exact (show ContDiffOn Real ∞ (fun _ : Metric =>
      ContinuousLinearMap.compL Real Fields C0 Real (finiteFrameBRSTCanonicalIntegralCLM period hPeriod))
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) from contDiffOn_const).clm_comp
    (frameFreeAbelianBRSTBilinearDensity_contDiffOn period hPeriod frame metric)

theorem frameFreeAbelianBRSTBilinearCoefficient_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) :=
  (frameFreeAbelianBRSTBilinearCoefficient_contDiffOn period hPeriod frame metric).of_le
    (WithTop.coe_le_coe.mpr le_top)

theorem frameFreeAbelianBRSTAction_eq_bilinear
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (fields : FrameFreeAbelianBRSTFields period hPeriod frame) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame metric (variation, fields) =
      frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric variation fields fields := by
  change finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (finiteFrameC2AbelianBRSTDensity period hPeriod frame metric (variation, fields)) =
    finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (frameFreeAbelianBRSTBilinearDensity period hPeriod frame metric variation fields fields)
  congr 1
  simp only [finiteFrameC2AbelianBRSTDensity, frameFreeAbelianBRSTBilinearDensity,
    bReadout, antighostReadout, bProjection, antighostProjection, potentialProjection, ghostProjection,
    sum_apply, _root_.add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    frameFreeAbelianLorenzOperatorFamily_apply, frameFreeAbelianFPOperatorFamily_apply]

theorem frameFreeAbelianBRSTAction_second_fderiv_zero
    (first second : FiniteFrameC2AbelianBRSTCore period hPeriod frame metric) :
    fderiv Real (fderiv Real (finiteFrameC2AbelianBRSTAction period hPeriod frame metric)) 0 first second =
      frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric 0 first.2 second.2 +
        frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric 0 second.2 first.2 := by
  have hZero := zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric
  have hK : ContDiffAt Real 2 (frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric) 0 :=
    ((frameFreeAbelianBRSTBilinearCoefficient_contDiffOn_two period hPeriod frame metric) 0 hZero).contDiffAt
      ((generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame metric).mem_nhds hZero)
  have hAction : finiteFrameC2AbelianBRSTAction period hPeriod frame metric =
      (fun input => frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric input.1 input.2 input.2) :=
    funext fun input => frameFreeAbelianBRSTAction_eq_bilinear period hPeriod frame metric input.1 input.2
  have hCoreK := hK.comp 0
    (show ContDiffAt Real 2
      (Prod.fst : FiniteFrameC2AbelianBRSTCore period hPeriod frame metric → Metric) 0 from
      contDiff_fst.contDiffAt)
  rw [hAction]
  exact bilinearCoefficient_second_fderiv_zero
    (fun input : FiniteFrameC2AbelianBRSTCore period hPeriod frame metric =>
      frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric input.1)
    (ContinuousLinearMap.snd Real _ _) (ContinuousLinearMap.snd Real _ _)
    hCoreK first second

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D
