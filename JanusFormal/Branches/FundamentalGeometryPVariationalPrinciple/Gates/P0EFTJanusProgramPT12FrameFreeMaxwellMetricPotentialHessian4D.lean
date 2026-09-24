import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MobileMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AffineHessianPullback4D

/-! The actual completed Maxwell metric--potential Hessian vanishes at zero potential.
This is one physical bulk block, with arbitrary admissible C² metric variation. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeMaxwellMetricPotentialHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusProgramPT12AffineHessianPullback4D

private theorem even_second_variable_mixed_hessian_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (action : E × F → Real) (point direction : E) (potential : F)
    (hEven : ∀ x y, action (x, -y) = action (x, y))
    (hC2 : ContDiffAt Real 2 action (point, 0)) :
    fderiv Real (fderiv Real action) (point, 0) (direction, 0) (0, potential) = 0 := by
  let reflection : E × F →L[Real] E × F :=
    (ContinuousLinearMap.fst Real E F).prod (-ContinuousLinearMap.snd Real E F)
  have hFunction : (fun input : E × F => action ((point, 0) + reflection input)) =
      (fun input : E × F => action ((point, 0) + input)) := by
    funext input
    change action (point + input.1, 0 + -input.2) = action (point + input.1, 0 + input.2)
    simpa only [zero_add] using hEven (point + input.1) input.2
  have hFirst : reflection (direction, 0) = (direction, 0) := by simp [reflection]
  have hSecond : reflection (0, potential) = -(0, potential) := by simp [reflection]
  have hIdentity := scaledAffineHessian action (point, 0)
    (ContinuousLinearMap.id Real (E × F)) 1 hC2 (direction, 0) (0, potential)
  simp only [one_mul, ContinuousLinearMap.id_apply] at hIdentity
  have hReflection := scaledAffineHessian action (point, 0) reflection 1 hC2
    (direction, 0) (0, potential)
  simp only [one_mul] at hReflection
  rw [hFunction, hIdentity, hFirst, hSecond,
    (fderiv Real (fderiv Real action) (point, 0) (direction, 0)).map_neg] at hReflection
  linarith

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2MaxwellPairing4D P0EFTJanusFiniteFrameC2MobileMaxwellAction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "MetricCore" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "GaugeCore" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "action" => finiteFrameC2MobileMaxwellAction period hPeriod frame metric

theorem finiteFrameMobileMaxwellAction_potential_neg (variation : MetricCore) (potential : GaugeCore) :
    action (variation, -potential) = action (variation, potential) := by
  unfold finiteFrameC2MobileMaxwellAction finiteFrameC2MobileMaxwellDensity
  rw [finiteFrameMaxwellPairingC0_neg]

theorem finiteFrameMobileMaxwell_metric_potential_hessian_zero
    (variation direction : MetricCore)
    (hVariation : variation ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame metric)
    (potential : GaugeCore) :
    fderiv Real (fderiv Real action) (variation, 0) (direction, 0) (0, potential) = 0 := by
  have hPoint : (variation, (0 : GaugeCore)) ∈
      finiteFrameC2MobileMaxwellDomain period hPeriod frame metric := ⟨hVariation, Set.mem_univ _⟩
  have hC2 : ContDiffAt Real 2 action (variation, 0) :=
    (finiteFrameC2MobileMaxwellAction_contDiffOn_two period hPeriod frame metric _ hPoint).contDiffAt
      ((finiteFrameC2MobileMaxwellDomain_isOpen period hPeriod frame metric).mem_nhds hPoint)
  exact even_second_variable_mixed_hessian_zero action variation direction potential
    (finiteFrameMobileMaxwellAction_potential_neg period hPeriod frame metric) hC2

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeMaxwellMetricPotentialHessian4D
