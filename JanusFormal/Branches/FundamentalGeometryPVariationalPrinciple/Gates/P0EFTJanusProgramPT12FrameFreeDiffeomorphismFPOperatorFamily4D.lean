import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismDeDonderOperatorFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismCartanOperatorFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DiffeomorphismFP4D

/-! The native Faddeev--Popov operator is the composition of the de Donder
first-jet contraction and the full Cartan first jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPOperatorFamily4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D P0EFTJanusFiniteFrameC2DiffeomorphismFP4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismDeDonderOperatorFamily4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismCartanOperatorFamily4D
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
local notation "Jet" => P0EFTJanusFiniteFrameC2CartanFirstJet4D.FiniteFrameCartanC0FirstJet period hPeriod frame
local notation "Covectors" => FiniteFrameDiffeomorphismC0Core period hPeriod frame
local instance : NormedAddCommGroup Metric := inferInstance
local instance : NormedSpace Real Metric := inferInstance
local instance : NormedAddCommGroup Ghost := inferInstance
local instance : NormedSpace Real Ghost := inferInstance
local instance : NormedAddCommGroup (Ghost →L[Real] Jet) := inferInstance
local instance : NormedSpace Real (Ghost →L[Real] Jet) := inferInstance
local instance : NormedAddCommGroup (Jet →L[Real] Covectors) := inferInstance
local instance : NormedSpace Real (Jet →L[Real] Covectors) := inferInstance
local instance : NormedAddCommGroup (Ghost →L[Real] Covectors) := inferInstance
local instance : NormedSpace Real (Ghost →L[Real] Covectors) := inferInstance

def frameFreeDiffeomorphismFPOperatorFamily (variation : Metric) : Ghost →L[Real] Covectors :=
  (frameFreeDiffeomorphismDeDonderOperatorFamily period hPeriod frame metric variation).comp
    (frameFreeDiffeomorphismCartanOperatorFamily period hPeriod frame metric variation)

theorem frameFreeDiffeomorphismFPOperatorFamily_apply
    (variation : Metric) (ghost : Ghost) (index : Fin frame.count) :
    frameFreeDiffeomorphismFPOperatorFamily period hPeriod frame metric variation ghost index =
      finiteFrameC2DiffeomorphismFPCoefficient period hPeriod frame metric index (variation, ghost) := by
  unfold frameFreeDiffeomorphismFPOperatorFamily finiteFrameC2DiffeomorphismFPCoefficient
  rw [ContinuousLinearMap.comp_apply, frameFreeDiffeomorphismCartanOperatorFamily_apply,
    frameFreeDiffeomorphismDeDonderOperatorFamily_apply]

theorem frameFreeDiffeomorphismFPOperatorFamily_contDiffOn :
    ContDiffOn Real ∞ (frameFreeDiffeomorphismFPOperatorFamily period hPeriod frame metric)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) :=
  (frameFreeDiffeomorphismDeDonderOperatorFamily_contDiffOn period hPeriod frame metric).clm_comp
    (frameFreeDiffeomorphismCartanOperatorFamily_contDiff period hPeriod frame metric).contDiffOn

theorem frameFreeDiffeomorphismFPOperatorFamily_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeDiffeomorphismFPOperatorFamily period hPeriod frame metric)
      (generalMetricRelativeC2OpenDomain period hPeriod frame metric) :=
  (frameFreeDiffeomorphismFPOperatorFamily_contDiffOn period hPeriod frame metric).of_le
    (WithTop.coe_le_coe.mpr le_top)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPOperatorFamily4D
