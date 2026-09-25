import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMaxwellMetricPotentialHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

/-! The complete native Maxwell potential column at zero potential. The
metric--potential cancellation is reused, and the potential pairing is computed. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeMaxwellPotentialColumn4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusProgramPT12AffineHessianPullback4D
open P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
local instance : NormedAddCommGroup (F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] F →L[Real] Real) := inferInstance

private theorem quadratic_slice_hessian
    (action : E × F → Real) (base : E) (B : F →L[Real] F →L[Real] Real)
    (hC2 : ContDiffAt Real 2 action (base, 0)) (hDiagonal : ∀ x, action (base, x) = B x x)
    (first second : F) :
    fderiv Real (fderiv Real action) (base, 0) (0, first) (0, second) = B first second + B second first := by
  have hPull : fderiv Real (fderiv Real (fun x : F => action (base, x))) 0 first second =
      fderiv Real (fderiv Real action) (base, 0) (0, first) (0, second) := by
    simpa only [one_mul, ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply,
      Prod.mk_add_mk, add_zero, zero_add] using
      scaledAffineHessian action (base, 0)
        ((0 : F →L[Real] E).prod (ContinuousLinearMap.id Real F)) 1 hC2 first second
  have hAction : (fun x : F => action (base, x)) = (fun x : F => B x x) := funext hDiagonal
  rw [hAction] at hPull
  exact hPull.symm.trans (bilinearCoefficient_second_fderiv_zero
    (fun _ : F => B) (ContinuousLinearMap.id Real F) (ContinuousLinearMap.id Real F)
    (show ContDiffAt Real 2 (fun _ : F => B) 0 from contDiffAt_const) first second)

private theorem bilinear_product_column
    (H : (E × F) →L[Real] (E × F) →L[Real] Real) (potential : F) (test : E × F)
    (hMetric : H (0, potential) (test.1, 0) = 0) : H (0, potential) test = H (0, potential) (0, test.2) := by
  have hSplit : test = (test.1, 0) + (0, test.2) := by ext <;> simp
  calc
    H (0, potential) test = H (0, potential) ((test.1, 0) + (0, test.2)) :=
      congrArg (H (0, potential)) hSplit
    _ = H (0, potential) (test.1, 0) + H (0, potential) (0, test.2) :=
      (H (0, potential)).map_add _ _
    _ = H (0, potential) (0, test.2) := by rw [hMetric, zero_add]
end Calculus

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2MobileMaxwellAction4D
open P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
open P0EFTJanusProgramPT12FrameFreeMaxwellMetricPotentialHessian4D
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
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
variable (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Metric" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Input" => Metric × Gauge
local notation "action" => finiteFrameC2MobileMaxwellAction period hPeriod frame metric
local instance : NormedAddCommGroup Metric := inferInstance
local instance : NormedSpace Real Metric := inferInstance
local instance : NormedAddCommGroup Gauge := inferInstance
local instance : NormedSpace Real Gauge := inferInstance
local instance : NormedAddCommGroup (Gauge →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Gauge →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Gauge →L[Real] Gauge →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Gauge →L[Real] Gauge →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Input →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Input →L[Real] Real) := inferInstance

private theorem action_contDiffAt_zeroPotential
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (hVariation : variation ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame metric) :
    ContDiffAt Real 2 action (variation, 0) :=
  ((finiteFrameC2MobileMaxwellAction_contDiffOn_two period hPeriod frame metric)
    (variation, 0) ⟨hVariation, Set.mem_univ _⟩).contDiffAt
      ((finiteFrameC2MobileMaxwellDomain_isOpen period hPeriod frame metric).mem_nhds
        ⟨hVariation, Set.mem_univ _⟩)

theorem frameFreeMaxwell_potential_potential_hessian
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (hVariation : variation ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame metric)
    (first second : FiniteFrameAbelianGaugeC2Core period hPeriod frame) :
    fderiv Real (fderiv Real action) (variation, 0) (0, first) (0, second) =
      frameFreeMaxwellBilinear period hPeriod frame metric variation first second +
        frameFreeMaxwellBilinear period hPeriod frame metric variation second first :=
  quadratic_slice_hessian action variation (frameFreeMaxwellBilinear period hPeriod frame metric variation)
    (action_contDiffAt_zeroPotential period hPeriod frame metric variation hVariation)
    (frameFreeMobileMaxwellAction_eq_bilinear period hPeriod frame metric variation) first second

theorem frameFreeMaxwell_potential_hessian_column
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (hVariation : variation ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame metric)
    (potential : FiniteFrameAbelianGaugeC2Core period hPeriod frame)
    (test : GeneralMetricRelativeC2Core period hPeriod frame metric × FiniteFrameAbelianGaugeC2Core period hPeriod frame) :
    fderiv Real (fderiv Real action) (variation, 0) (0, potential) test =
      frameFreeMaxwellBilinear period hPeriod frame metric variation potential test.2 +
        frameFreeMaxwellBilinear period hPeriod frame metric variation test.2 potential := by
  have hMetric := ((action_contDiffAt_zeroPotential period hPeriod frame metric variation hVariation).isSymmSndFDerivAt
    (by norm_num) (0, potential) (test.1, 0)).trans
    (finiteFrameMobileMaxwell_metric_potential_hessian_zero period hPeriod frame metric
      variation test.1 hVariation potential)
  exact (bilinear_product_column (fderiv Real (fderiv Real action) (variation, 0)) potential test hMetric).trans
    (frameFreeMaxwell_potential_potential_hessian period hPeriod frame metric variation hVariation potential test.2)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeMaxwellPotentialColumn4D
