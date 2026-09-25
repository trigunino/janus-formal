import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2CartanFirstJet4D
import Mathlib.Tactic.Abel

/-! The native Cartan first jet is linear in the ghost, and therefore its
partial derivative is its exact bounded operator, smoothly dependent on the metric. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismCartanOperatorFamily4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators

private theorem linear_fderiv_zero_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (f : E → F) (hAdd : ∀ x y, f (x + y) = f x + f y)
    (hSmul : ∀ (scalar : Real) x, f (scalar • x) = scalar • f x)
    (hContinuous : Continuous f) (x : E) : fderiv Real f 0 x = f x := by
  let operator : E →L[Real] F :=
    { toLinearMap := { toFun := f, map_add' := hAdd, map_smul' := hSmul }
      cont := hContinuous }
  exact congrArg (fun derivative : E →L[Real] F => derivative x) (operator.fderiv (x := (0 : E)))

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D P0EFTJanusFiniteFrameC2CartanFirstJet4D
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
local notation "Metric" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "Ghost" => FiniteFrameDiffeomorphismC2Core period hPeriod frame
local notation "Jet" => FiniteFrameCartanC0FirstJet period hPeriod frame
local instance : NormedAddCommGroup Metric := inferInstance
local instance : NormedSpace Real Metric := inferInstance
local instance : NormedAddCommGroup Ghost := inferInstance
local instance : NormedSpace Real Ghost := inferInstance
local instance : NormedAddCommGroup Jet := inferInstance
local instance : NormedSpace Real Jet := inferInstance
local instance : NormedAddCommGroup (Ghost →L[Real] Jet) := inferInstance
local instance : NormedSpace Real (Ghost →L[Real] Jet) := inferInstance

private theorem cartan_add (variation : Metric) (first second : Ghost) :
    finiteFrameC2CartanFirstJet period hPeriod frame metric variation (first + second) =
      finiteFrameC2CartanFirstJet period hPeriod frame metric variation first +
        finiteFrameC2CartanFirstJet period hPeriod frame metric variation second := by
  apply Prod.ext
  · funext row column
    change finiteFrameC2CartanComponentExpression period hPeriod frame metric variation (first + second) row column =
      finiteFrameC2CartanComponentExpression period hPeriod frame metric variation first row column +
        finiteFrameC2CartanComponentExpression period hPeriod frame metric variation second row column
    unfold finiteFrameC2CartanComponentExpression
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  · funext outer row column
    change finiteFrameC2CartanComponentFirstDerivative period hPeriod frame metric variation (first + second) outer row column =
      finiteFrameC2CartanComponentFirstDerivative period hPeriod frame metric variation first outer row column +
        finiteFrameC2CartanComponentFirstDerivative period hPeriod frame metric variation second outer row column
    unfold finiteFrameC2CartanComponentFirstDerivative
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel

private theorem cartan_smul (variation : Metric) (scalar : Real) (ghost : Ghost) :
    finiteFrameC2CartanFirstJet period hPeriod frame metric variation (scalar • ghost) =
      scalar • finiteFrameC2CartanFirstJet period hPeriod frame metric variation ghost := by
  apply Prod.ext
  · funext row column
    change finiteFrameC2CartanComponentExpression period hPeriod frame metric variation (scalar • ghost) row column =
      scalar • finiteFrameC2CartanComponentExpression period hPeriod frame metric variation ghost row column
    unfold finiteFrameC2CartanComponentExpression
    simp only [Pi.smul_apply, map_smul, smul_mul_assoc, smul_add, smul_sub, Finset.smul_sum]
  · funext outer row column
    change finiteFrameC2CartanComponentFirstDerivative period hPeriod frame metric variation (scalar • ghost) outer row column =
      scalar • finiteFrameC2CartanComponentFirstDerivative period hPeriod frame metric variation ghost outer row column
    unfold finiteFrameC2CartanComponentFirstDerivative
    simp only [Pi.smul_apply, map_smul, smul_mul_assoc, smul_add, smul_sub, Finset.smul_sum]

/-- The partial derivative equals the entire native linear ghost operator. -/
def frameFreeDiffeomorphismCartanOperatorFamily (variation : Metric) : Ghost →L[Real] Jet :=
  fderiv Real (finiteFrameC2CartanFirstJet period hPeriod frame metric variation) 0

theorem frameFreeDiffeomorphismCartanOperatorFamily_apply (variation : Metric) (ghost : Ghost) :
    frameFreeDiffeomorphismCartanOperatorFamily period hPeriod frame metric variation ghost =
      finiteFrameC2CartanFirstJet period hPeriod frame metric variation ghost := by
  have hContinuous := (finiteFrameC2CartanFirstJet_contDiff period hPeriod frame metric).continuous.comp
    ((show Continuous (fun _ : Ghost => variation) from continuous_const).prodMk
      (continuous_id : Continuous (fun ghost : Ghost => ghost)))
  exact linear_fderiv_zero_apply
    (finiteFrameC2CartanFirstJet period hPeriod frame metric variation)
    (cartan_add period hPeriod frame metric variation) (cartan_smul period hPeriod frame metric variation)
    hContinuous ghost

theorem frameFreeDiffeomorphismCartanOperatorFamily_contDiff :
    ContDiff Real ∞ (frameFreeDiffeomorphismCartanOperatorFamily period hPeriod frame metric) :=
  (finiteFrameC2CartanFirstJet_contDiff period hPeriod frame metric).fderiv
    (show ContDiff Real ∞ (fun _ : Metric => (0 : Ghost)) from contDiff_const) (by simp)

theorem frameFreeDiffeomorphismCartanOperatorFamily_contDiff_two :
    ContDiff Real 2 (frameFreeDiffeomorphismCartanOperatorFamily period hPeriod frame metric) :=
  (frameFreeDiffeomorphismCartanOperatorFamily_contDiff period hPeriod frame metric).of_le
    (WithTop.coe_le_coe.mpr le_top)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismCartanOperatorFamily4D
