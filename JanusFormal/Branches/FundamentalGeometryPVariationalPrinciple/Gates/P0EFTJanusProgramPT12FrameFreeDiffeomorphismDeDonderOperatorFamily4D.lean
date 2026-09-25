import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DeDonderFirstJet4D

/-! The native de Donder contraction as a smooth operator family on actual
tensor first jets, with an arbitrary redundant smooth generating frame. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismDeDonderOperatorFamily4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2DeDonder4D P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
variable (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Index" => Fin frame.count
local notation "C0" => C(Q period hPeriod, Real)
local notation "Jet" => FiniteFrameTensorC0FirstJet period hPeriod frame
local notation "Metric" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "Domain" => generalMetricRelativeC2OpenDomain period hPeriod frame metric
local instance : NormedAddCommGroup Jet := inferInstance
local instance : NormedSpace Real Jet := inferInstance
local instance : NormedAddCommGroup Metric := inferInstance
local instance : NormedSpace Real Metric := inferInstance
local instance : NormedAddCommGroup (C0 →L[Real] C0) := inferInstance
local instance : NormedSpace Real (C0 →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (Jet →L[Real] C0) := inferInstance
local instance : NormedSpace Real (Jet →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (Jet →L[Real] Index → C0) := inferInstance
local instance : NormedSpace Real (Jet →L[Real] Index → C0) := inferInstance
local instance : NormedAddCommGroup (Index → Jet →L[Real] C0) := inferInstance
local instance : NormedSpace Real (Index → Jet →L[Real] C0) := inferInstance

private def jetValue (row column : Index) : Jet →L[Real] C0 :=
  (ContinuousLinearMap.proj column).comp ((ContinuousLinearMap.proj row).comp
    (ContinuousLinearMap.fst Real (Index → Index → C0) (Index → Index → Index → C0)))

private def jetFirst (derivative row column : Index) : Jet →L[Real] C0 :=
  (ContinuousLinearMap.proj column).comp ((ContinuousLinearMap.proj row).comp
    ((ContinuousLinearMap.proj derivative).comp
      (ContinuousLinearMap.snd Real (Index → Index → C0) (Index → Index → Index → C0))))

private def deDonderCoefficient (last : Index) (variation : Metric) : Jet →L[Real] C0 :=
  (∑ derivative : Index, ∑ first : Index,
    (ContinuousLinearMap.mul Real C0
      (finiteFrameInverseMetricC0Coefficient period hPeriod frame metric derivative first variation)).comp
      (jetFirst period hPeriod frame derivative first last -
        (∑ index : Index,
          (ContinuousLinearMap.mul Real C0
            (finiteFrameChristoffelC0Coefficient period hPeriod frame metric index derivative first variation)).comp
            (jetValue period hPeriod frame index last)) -
        (∑ index : Index,
          (ContinuousLinearMap.mul Real C0
            (finiteFrameChristoffelC0Coefficient period hPeriod frame metric index derivative last variation)).comp
            (jetValue period hPeriod frame first index)))) -
    (1 / 2 : Real) • (∑ row : Index, ∑ column : Index,
      ((ContinuousLinearMap.mul Real C0
        (finiteFrameInverseMetricC0FirstDerivative period hPeriod frame metric last row column variation)).comp
          (jetValue period hPeriod frame column row) +
      (ContinuousLinearMap.mul Real C0
        (finiteFrameInverseMetricC0Coefficient period hPeriod frame metric row column variation)).comp
          (jetFirst period hPeriod frame last column row)))

private theorem deDonderCoefficient_contDiffOn (last : Index) :
    ContDiffOn Real ∞ (deDonderCoefficient period hPeriod frame metric last) Domain := by
  have hConst (operator : Jet →L[Real] C0) :
      ContDiffOn Real ∞ (fun _ : Metric => operator) Domain := contDiffOn_const
  have hWeight (coefficient : Metric → C0) (hCoefficient : ContDiffOn Real ∞ coefficient Domain)
      (operator : Metric → Jet →L[Real] C0) (hOperator : ContDiffOn Real ∞ operator Domain) :
      ContDiffOn Real ∞ (fun variation =>
        (ContinuousLinearMap.mul Real C0 (coefficient variation)).comp (operator variation)) Domain := by
    have hMul : ContDiff Real ∞
        (ContinuousLinearMap.mul Real C0 : C0 → C0 →L[Real] C0) :=
      (ContinuousLinearMap.mul Real C0).contDiff
    exact (hMul.comp_contDiffOn hCoefficient).clm_comp hOperator
  have hInverse := finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame metric
  have hDerivative := finiteFrameInverseMetricC0FirstDerivative_contDiffOn period hPeriod frame metric
  have hGamma := finiteFrameChristoffelC0Coefficient_contDiffOn period hPeriod frame metric
  unfold deDonderCoefficient
  exact (ContDiffOn.sum fun derivative _ => ContDiffOn.sum fun first _ =>
    hWeight _ (hInverse derivative first) _
      (((hConst (jetFirst period hPeriod frame derivative first last)).sub
        (ContDiffOn.sum fun index _ => hWeight _ (hGamma index derivative first) _
          (hConst (jetValue period hPeriod frame index last)))).sub
        (ContDiffOn.sum fun index _ => hWeight _ (hGamma index derivative last) _
          (hConst (jetValue period hPeriod frame first index))))).sub
    ((ContDiffOn.sum fun row _ => ContDiffOn.sum fun column _ =>
      (hWeight _ (hDerivative last row column) _ (hConst (jetValue period hPeriod frame column row))).add
        (hWeight _ (hInverse row column) _ (hConst (jetFirst period hPeriod frame last column row)))).const_smul
          (1 / 2 : Real))

/-- All de Donder covector coefficients, as one bounded operator on the tensor first jet. -/
def frameFreeDiffeomorphismDeDonderOperatorFamily (variation : Metric) : Jet →L[Real] Index → C0 :=
  ContinuousLinearMap.pi (fun last => deDonderCoefficient period hPeriod frame metric last variation)

theorem frameFreeDiffeomorphismDeDonderOperatorFamily_apply
    (variation : Metric) (jet : Jet) (last : Index) :
    frameFreeDiffeomorphismDeDonderOperatorFamily period hPeriod frame metric variation jet last =
      finiteFrameC2DeDonderFirstJetCoefficient period hPeriod frame metric last (variation, jet) := by
  change deDonderCoefficient period hPeriod frame metric last variation jet = _
  simp only [deDonderCoefficient, jetValue, jetFirst, finiteFrameC2DeDonderFirstJetCoefficient,
    sum_apply, _root_.add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

theorem frameFreeDiffeomorphismDeDonderOperatorFamily_contDiffOn :
    ContDiffOn Real ∞ (frameFreeDiffeomorphismDeDonderOperatorFamily period hPeriod frame metric) Domain := by
  exact (ContinuousLinearMap.piEquivL Real Jet (fun _ : Index => C0)).contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr (deDonderCoefficient_contDiffOn period hPeriod frame metric))

theorem frameFreeDiffeomorphismDeDonderOperatorFamily_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeDiffeomorphismDeDonderOperatorFamily period hPeriod frame metric) Domain :=
  (frameFreeDiffeomorphismDeDonderOperatorFamily_contDiffOn period hPeriod frame metric).of_le
    (WithTop.coe_le_coe.mpr le_top)

theorem frameFreeDiffeomorphismDeDonderOperatorFamily_tensor_apply
    (variation tensor : Metric) (last : Index) :
    frameFreeDiffeomorphismDeDonderOperatorFamily period hPeriod frame metric variation
        (finiteFrameTensorC0FirstJetCLM period hPeriod frame metric tensor) last =
      finiteFrameC2DeDonderCoefficient period hPeriod frame metric last (variation, tensor) := by
  rw [frameFreeDiffeomorphismDeDonderOperatorFamily_apply,
    finiteFrameC2DeDonderFirstJetCoefficient_factorization]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismDeDonderOperatorFamily4D
