import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPOperatorFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

/-! The native diffeomorphism BRST action is a metric-dependent bilinear form
on (H,B,cbar,c), including its actual volume density and fixed canonical integral. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators

section Bilinear
variable {E F G H X : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G] [NormedAddCommGroup H] [NormedSpace Real H]
  [NormedAddCommGroup X] [NormedSpace Real X]
local instance : NormedAddCommGroup (E →L[Real] F) := inferInstance
local instance : NormedSpace Real (E →L[Real] F) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] H) := inferInstance
local instance : NormedSpace Real (E →L[Real] H) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] E →L[Real] H) := inferInstance
local instance : NormedSpace Real (F →L[Real] E →L[Real] H) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] E →L[Real] H) := inferInstance
local instance : NormedSpace Real (E →L[Real] E →L[Real] H) := inferInstance

private theorem bilinearComp_left_contDiffOn
    (B : F →L[Real] G →L[Real] H) (v : E →L[Real] G)
    {u : X → E →L[Real] F} {s : Set X} (hu : ContDiffOn Real ∞ u s) :
    ContDiffOn Real ∞ (fun x => B.bilinearComp (u x) v) s := by
  let operator : F →L[Real] E →L[Real] H := (ContinuousLinearMap.precompR E B).flip v
  have hEq : (fun x => B.bilinearComp (u x) v) = (fun x => operator.comp (u x)) := by
    funext x
    ext first second
    rfl
  rw [hEq]
  exact (show ContDiffOn Real ∞ (fun _ : X => operator) s from contDiffOn_const).clm_comp hu
end Bilinear

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D P0EFTJanusFiniteFrameC2DiffeomorphismFP4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismDeDonderOperatorFamily4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPOperatorFamily4D
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

abbrev FrameFreeDiffeomorphismBRSTFields (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  GeneralMetricRelativeC2Core period hPeriod frame metric ×
    FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame

variable (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Index" => Fin frame.count
local notation "Metric" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "Fields" => FrameFreeDiffeomorphismBRSTFields period hPeriod frame metric
local notation "Ghost" => FiniteFrameDiffeomorphismC2Core period hPeriod frame
local notation "C0" => C(Q period hPeriod, Real)
local notation "Domain" => generalMetricRelativeC2OpenDomain period hPeriod frame metric
local notation "VolumeDomain" => generalMetricRelativeC2VolumeDomain period hPeriod frame metric
local instance : NormedAddCommGroup Metric := inferInstance
local instance : NormedSpace Real Metric := inferInstance
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := inferInstance
local instance : NormedAddCommGroup (C0 →L[Real] C0) := inferInstance
local instance : NormedSpace Real (C0 →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (C0 →L[Real] Real) := inferInstance
local instance : NormedSpace Real (C0 →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] C0) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Fields →L[Real] C0) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Fields →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup ((Fields →L[Real] C0) →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real ((Fields →L[Real] C0) →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric) := inferInstance
local instance : NormedSpace Real (FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric) := inferInstance
local instance : NormedAddCommGroup (FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric →L[Real] Real) := inferInstance
local instance : NormedSpace Real (FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup
    (FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric →L[Real]
      FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric →L[Real] Real) := inferInstance
local instance : NormedSpace Real
    (FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric →L[Real]
      FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric →L[Real] Real) := inferInstance

private def tensorProjection : Fields →L[Real] Metric := ContinuousLinearMap.fst Real _ _
private def bProjection : Fields →L[Real] Ghost :=
  (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _)
private def antighostProjection : Fields →L[Real] Ghost :=
  (ContinuousLinearMap.fst Real _ _).comp
    ((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _))
private def ghostProjection : Fields →L[Real] Ghost :=
  (ContinuousLinearMap.snd Real _ _).comp
    ((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _))
private def bReadout (index : Index) : Fields →L[Real] C0 :=
  (ContinuousLinearMap.proj index).comp
    ((finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).comp (bProjection period hPeriod frame metric))
private def antighostReadout (index : Index) : Fields →L[Real] C0 :=
  (ContinuousLinearMap.proj index).comp
    ((finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).comp (antighostProjection period hPeriod frame metric))
private def deDonderReadout (index : Index) (variation : Metric) : Fields →L[Real] C0 :=
  (ContinuousLinearMap.proj index).comp
    ((frameFreeDiffeomorphismDeDonderOperatorFamily period hPeriod frame metric variation).comp
      ((finiteFrameTensorC0FirstJetCLM period hPeriod frame metric).comp (tensorProjection period hPeriod frame metric)))
private def fpReadout (index : Index) (variation : Metric) : Fields →L[Real] C0 :=
  (ContinuousLinearMap.proj index).comp
    ((frameFreeDiffeomorphismFPOperatorFamily period hPeriod frame metric variation).comp
      (ghostProjection period hPeriod frame metric))

/-- The polynomial before multiplication by the actual varying volume density. -/
def frameFreeDiffeomorphismBRSTBilinearPolynomial (variation : Metric) : Fields →L[Real] Fields →L[Real] C0 :=
  (∑ index : Index, (ContinuousLinearMap.mul Real C0).bilinearComp
      (deDonderReadout period hPeriod frame metric index variation) (bReadout period hPeriod frame metric index)) -
    (1 / 2 : Real) • (∑ row : Index, ∑ column : Index,
      (ContinuousLinearMap.mul Real C0).bilinearComp
        ((ContinuousLinearMap.mul Real C0
          (finiteFrameMetricC0Coefficient period hPeriod frame metric row column variation)).comp
          (bReadout period hPeriod frame metric row)) (bReadout period hPeriod frame metric column)) -
    (∑ index : Index, (ContinuousLinearMap.mul Real C0).bilinearComp
      (fpReadout period hPeriod frame metric index variation) (antighostReadout period hPeriod frame metric index))

private theorem deDonderReadout_contDiffOn (index : Index) :
    ContDiffOn Real ∞ (deDonderReadout period hPeriod frame metric index) Domain := by
  have hTensor : ContDiffOn Real ∞ (fun _ : Metric =>
      (finiteFrameTensorC0FirstJetCLM period hPeriod frame metric).comp
        (tensorProjection period hPeriod frame metric)) Domain := contDiffOn_const
  exact (show ContDiffOn Real ∞ (fun _ : Metric =>
    (ContinuousLinearMap.proj index : (Index → C0) →L[Real] C0)) Domain
      from contDiffOn_const).clm_comp
    ((frameFreeDiffeomorphismDeDonderOperatorFamily_contDiffOn period hPeriod frame metric).clm_comp hTensor)

private theorem fpReadout_contDiffOn (index : Index) :
    ContDiffOn Real ∞ (fpReadout period hPeriod frame metric index) Domain := by
  have hGhost : ContDiffOn Real ∞ (fun _ : Metric =>
      ghostProjection period hPeriod frame metric) Domain := contDiffOn_const
  exact (show ContDiffOn Real ∞ (fun _ : Metric =>
    (ContinuousLinearMap.proj index : (Index → C0) →L[Real] C0)) Domain
      from contDiffOn_const).clm_comp
    ((frameFreeDiffeomorphismFPOperatorFamily_contDiffOn period hPeriod frame metric).clm_comp hGhost)

private theorem metricBReadout_contDiffOn (row column : Index) :
    ContDiffOn Real ∞ (fun variation : Metric =>
      (ContinuousLinearMap.mul Real C0 (finiteFrameMetricC0Coefficient period hPeriod frame metric row column variation)).comp
        (bReadout period hPeriod frame metric row)) Domain := by
  have hB : ContDiffOn Real ∞ (fun _ : Metric =>
      bReadout period hPeriod frame metric row) Domain := contDiffOn_const
  exact ((ContinuousLinearMap.mul Real C0).contDiff.comp_contDiffOn
    (finiteFrameMetricC0Coefficient_contDiff period hPeriod frame metric row column).contDiffOn).clm_comp hB

theorem frameFreeDiffeomorphismBRSTBilinearPolynomial_contDiffOn :
    ContDiffOn Real ∞ (frameFreeDiffeomorphismBRSTBilinearPolynomial period hPeriod frame metric) Domain := by
  unfold frameFreeDiffeomorphismBRSTBilinearPolynomial
  exact ((ContDiffOn.sum fun index _ => bilinearComp_left_contDiffOn (ContinuousLinearMap.mul Real C0)
    (bReadout period hPeriod frame metric index) (deDonderReadout_contDiffOn period hPeriod frame metric index)).sub
      ((ContDiffOn.sum fun row _ => ContDiffOn.sum fun column _ =>
        bilinearComp_left_contDiffOn (ContinuousLinearMap.mul Real C0)
          (bReadout period hPeriod frame metric column)
          (metricBReadout_contDiffOn period hPeriod frame metric row column)).const_smul (1 / 2 : Real))).sub
    (ContDiffOn.sum fun index _ => bilinearComp_left_contDiffOn (ContinuousLinearMap.mul Real C0)
      (antighostReadout period hPeriod frame metric index) (fpReadout_contDiffOn period hPeriod frame metric index))

def frameFreeDiffeomorphismBRSTBilinearCoefficient (variation : Metric) : Fields →L[Real] Fields →L[Real] Real :=
  (ContinuousLinearMap.compL Real Fields C0 Real
    ((finiteFrameBRSTCanonicalIntegralCLM period hPeriod).comp
      (ContinuousLinearMap.mul Real C0 (finiteFrameCanonicalVolumeC0 period hPeriod frame metric variation)))).comp
    (frameFreeDiffeomorphismBRSTBilinearPolynomial period hPeriod frame metric variation)

theorem frameFreeDiffeomorphismBRSTBilinearCoefficient_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric) VolumeDomain := by
  have hWeightedIntegral : ContDiffOn Real 2 (fun variation : Metric =>
      (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).comp
        (ContinuousLinearMap.mul Real C0 (finiteFrameCanonicalVolumeC0 period hPeriod frame metric variation))) VolumeDomain :=
    (show ContDiffOn Real 2 (fun _ : Metric => finiteFrameBRSTCanonicalIntegralCLM period hPeriod) VolumeDomain
      from contDiffOn_const).clm_comp
      ((ContinuousLinearMap.mul Real C0).contDiff.comp_contDiffOn
        (finiteFrameCanonicalVolumeC0_contDiffOn_two period hPeriod frame metric))
  exact ((ContinuousLinearMap.compL Real Fields C0 Real).contDiff.comp_contDiffOn hWeightedIntegral).clm_comp
    (((frameFreeDiffeomorphismBRSTBilinearPolynomial_contDiffOn period hPeriod frame metric).of_le
      (WithTop.coe_le_coe.mpr le_top)).mono Set.inter_subset_left)

theorem frameFreeDiffeomorphismBRSTAction_eq_bilinear (variation : Metric) (fields : Fields) :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame metric (variation, fields) =
      frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric variation fields fields := by
  change finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (finiteFrameC2DiffeomorphismBRSTDensity period hPeriod frame metric (variation, fields)) =
    finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (finiteFrameCanonicalVolumeC0 period hPeriod frame metric variation *
        frameFreeDiffeomorphismBRSTBilinearPolynomial period hPeriod frame metric variation fields fields)
  congr 1
  simp only [finiteFrameC2DiffeomorphismBRSTDensity, finiteFrameC2DiffeomorphismBRSTOperatorFeatures,
    finiteFrameDiffeomorphismBRSTAttachNonminimalC2_apply, finiteFrameDiffeomorphismBRSTC0Polynomial,
    frameFreeDiffeomorphismBRSTBilinearPolynomial, deDonderReadout, fpReadout,
    tensorProjection, bReadout, antighostReadout, bProjection, antighostProjection, ghostProjection,
    sum_apply, sub_apply, smul_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    frameFreeDiffeomorphismDeDonderOperatorFamily_tensor_apply,
    frameFreeDiffeomorphismFPOperatorFamily_apply, finiteFrameC2DiffeomorphismFP]

private theorem bilinearCoefficient_contDiffAt_zero :
    ContDiffAt Real 2 (frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric) 0 := by
  have hZero := zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame metric
  exact ((frameFreeDiffeomorphismBRSTBilinearCoefficient_contDiffOn_two period hPeriod frame metric) 0 hZero).contDiffAt
    ((generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame metric).mem_nhds hZero)

private theorem coreBilinearCoefficient_contDiffAt_zero :
    ContDiffAt Real 2 (fun input : FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric =>
      frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric input.1) 0 := by
  have h := (bilinearCoefficient_contDiffAt_zero period hPeriod frame metric).comp 0
    (show ContDiffAt Real 2
      (Prod.fst : FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric → Metric) 0 from
       contDiff_fst.contDiffAt)
  exact h

private theorem action_eq_bilinear_function :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame metric =
      (fun input => frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric input.1 input.2 input.2) :=
  funext fun input => frameFreeDiffeomorphismBRSTAction_eq_bilinear period hPeriod frame metric input.1 input.2

theorem frameFreeDiffeomorphismBRSTAction_second_fderiv_zero
    (first second : FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric) :
    fderiv Real (fderiv Real (finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame metric)) 0 first second =
      frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric 0 first.2 second.2 +
        frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric 0 second.2 first.2 := by
  have hFreeze := bilinearCoefficient_second_fderiv_zero
    (fun input : FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric =>
      frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric input.1)
    (ContinuousLinearMap.snd Real _ _) (ContinuousLinearMap.snd Real _ _)
    (coreBilinearCoefficient_contDiffAt_zero period hPeriod frame metric) first second
  exact (congrArg
    (fun f : FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame metric → Real =>
      fderiv Real (fderiv Real f) 0 first second)
    (action_eq_bilinear_function period hPeriod frame metric)).trans hFreeze

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D
