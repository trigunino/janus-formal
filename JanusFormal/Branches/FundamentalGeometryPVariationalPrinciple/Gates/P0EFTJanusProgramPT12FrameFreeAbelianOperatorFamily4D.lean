import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2AbelianOperators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameCovectorC2Projection4D

/-! Native projected Lorenz and Faddeev--Popov operators as smooth families of
continuous linear maps on the completed finite-frame C² coefficients. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeAbelianOperatorFamily4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D P0EFTJanusFiniteFrameCovectorC2Projection4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
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
local notation "C0" => C(Q period hPeriod, Real)

private def projectedPotentialCoefficient (component : Fin 2) (index : Fin frame.count) :
    FiniteFrameAbelianGaugeC2Core period hPeriod frame →L[Real]
      CanonicalPhysicalScalarC2JetCore period hPeriod :=
  (ContinuousLinearMap.proj index).comp ((ContinuousLinearMap.proj component).comp
    (finiteFrameGaugeC2Projection period hPeriod frame metric))

def frameFreeAbelianLorenzOperatorFamily (component : Fin 2)
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric) :
    FiniteFrameAbelianGaugeC2Core period hPeriod frame →L[Real] C0 :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    (ContinuousLinearMap.mul Real C0
      (finiteFrameInverseMetricC0Coefficient period hPeriod frame metric first second variation)).comp
    ((finiteFrameScalarC2FirstDerivative period hPeriod metric frame first).comp
        (projectedPotentialCoefficient period hPeriod frame metric component second) -
      ∑ upper : Fin frame.count,
        (ContinuousLinearMap.mul Real C0
          (finiteFrameChristoffelC0Coefficient period hPeriod frame metric upper first second variation)).comp
        ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
          (projectedPotentialCoefficient period hPeriod frame metric component upper)))

def frameFreeAbelianFPOperatorFamily (component : Fin 2)
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric) :
    FiniteFrameAbelianGhostC2Core period hPeriod →L[Real] C0 :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    (ContinuousLinearMap.mul Real C0
      (finiteFrameInverseMetricC0Coefficient period hPeriod frame metric first second variation)).comp
    ((finiteFrameScalarC2SecondDerivative period hPeriod metric frame first second).comp
        (ContinuousLinearMap.proj component) -
      ∑ upper : Fin frame.count,
        (ContinuousLinearMap.mul Real C0
          (finiteFrameChristoffelC0Coefficient period hPeriod frame metric upper first second variation)).comp
        ((finiteFrameScalarC2FirstDerivative period hPeriod metric frame upper).comp
          (ContinuousLinearMap.proj component)))

theorem frameFreeAbelianLorenzOperatorFamily_apply (component : Fin 2)
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (potential : FiniteFrameAbelianGaugeC2Core period hPeriod frame) :
    frameFreeAbelianLorenzOperatorFamily period hPeriod frame metric component variation potential =
      finiteFrameC2AbelianLorenzComponentExpression period hPeriod frame metric variation
        (finiteFrameGaugeC2Projection period hPeriod frame metric potential) component := by
  simp only [frameFreeAbelianLorenzOperatorFamily, projectedPotentialCoefficient,
    finiteFrameC2AbelianLorenzComponentExpression, finiteFrameC2AbelianLorenzExpression,
    sum_apply, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.proj_apply]

theorem frameFreeAbelianFPOperatorFamily_apply (component : Fin 2)
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (ghost : FiniteFrameAbelianGhostC2Core period hPeriod) :
    frameFreeAbelianFPOperatorFamily period hPeriod frame metric component variation ghost =
      finiteFrameC2AbelianFPComponentExpression period hPeriod frame metric variation ghost component := by
  simp only [frameFreeAbelianFPOperatorFamily, finiteFrameC2AbelianFPComponentExpression,
    finiteFrameC2AbelianFPExpression, sum_apply, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.mul_apply', ContinuousLinearMap.proj_apply]

theorem frameFreeAbelianLorenzOperatorFamily_contDiffOn (component : Fin 2) :
    ContDiffOn Real ∞ (frameFreeAbelianLorenzOperatorFamily period hPeriod frame metric component)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) := by
  unfold frameFreeAbelianLorenzOperatorFamily
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  apply ((ContinuousLinearMap.mul Real C0).contDiff.comp_contDiffOn
    (finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame metric first second)).clm_comp
  refine contDiffOn_const.sub ?_
  apply ContDiffOn.sum
  intro upper _
  exact ((ContinuousLinearMap.mul Real C0).contDiff.comp_contDiffOn
    (finiteFrameChristoffelC0Coefficient_contDiffOn period hPeriod frame metric upper first second)).clm_comp
      (show ContDiffOn Real ∞
        (fun _ : GeneralMetricRelativeC2Core period hPeriod frame metric =>
          (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
            (projectedPotentialCoefficient period hPeriod frame metric component upper))
        (generalMetricRelativeC2OpenDomain period hPeriod frame metric) from contDiffOn_const)

theorem frameFreeAbelianFPOperatorFamily_contDiffOn (component : Fin 2) :
    ContDiffOn Real ∞ (frameFreeAbelianFPOperatorFamily period hPeriod frame metric component)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) := by
  unfold frameFreeAbelianFPOperatorFamily
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  apply ((ContinuousLinearMap.mul Real C0).contDiff.comp_contDiffOn
    (finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame metric first second)).clm_comp
  refine contDiffOn_const.sub ?_
  apply ContDiffOn.sum
  intro upper _
  exact ((ContinuousLinearMap.mul Real C0).contDiff.comp_contDiffOn
    (finiteFrameChristoffelC0Coefficient_contDiffOn period hPeriod frame metric upper first second)).clm_comp
      (show ContDiffOn Real ∞
        (fun _ : GeneralMetricRelativeC2Core period hPeriod frame metric =>
          (finiteFrameScalarC2FirstDerivative period hPeriod metric frame upper).comp
            (ContinuousLinearMap.proj component : FiniteFrameAbelianGhostC2Core period hPeriod →L[Real]
              CanonicalPhysicalScalarC2JetCore period hPeriod))
        (generalMetricRelativeC2OpenDomain period hPeriod frame metric) from contDiffOn_const)

theorem frameFreeAbelianLorenzOperatorFamily_contDiffOn_two (component : Fin 2) :
    ContDiffOn Real 2 (frameFreeAbelianLorenzOperatorFamily period hPeriod frame metric component)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) :=
  (frameFreeAbelianLorenzOperatorFamily_contDiffOn period hPeriod frame metric component).of_le
    (WithTop.coe_le_coe.mpr le_top)

theorem frameFreeAbelianFPOperatorFamily_contDiffOn_two (component : Fin 2) :
    ContDiffOn Real 2 (frameFreeAbelianFPOperatorFamily period hPeriod frame metric component)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) :=
  (frameFreeAbelianFPOperatorFamily_contDiffOn period hPeriod frame metric component).of_le
    (WithTop.coe_le_coe.mpr le_top)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeAbelianOperatorFamily4D
