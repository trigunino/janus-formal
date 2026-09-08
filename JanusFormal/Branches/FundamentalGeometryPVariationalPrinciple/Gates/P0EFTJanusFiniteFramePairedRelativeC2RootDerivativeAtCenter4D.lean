import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedRelativeC2Root4D

/-! # Sylvester equation for the finite-frame root derivative at the center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedRelativeC2RootDerivativeAtCenter4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D

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
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (C2FiniteFrameCorner period hPeriod frame metric) :=
  (c2FiniteFrameCornerSubmodule period hPeriod frame metric).normedAddCommGroup
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (C2FiniteFrameCorner period hPeriod frame metric) := inferInstance
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric).normedAddCommGroup
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)

private abbrev Model :=
  PairedFiniteFrameMetricC2Core period hPeriod geometry frame
private abbrev Corner :=
  C2FiniteFrameCorner period hPeriod frame geometry.plusMetric

/-- Fréchet derivative at the center of the completed relative target. -/
def pairedFiniteFrameRelativeC2TargetDerivativeAtZero :
    Model period hPeriod geometry frame →L[Real] Corner period hPeriod geometry frame :=
  fderiv Real (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame) 0

theorem pairedFiniteFrameRelativeC2Target_hasFDerivAt_zero :
    HasFDerivAt (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame)
      (pairedFiniteFrameRelativeC2TargetDerivativeAtZero period hPeriod geometry frame) 0 := by
  have hDomain := zero_mem_pairedFiniteFrameRelativeC2Domain period hPeriod geometry frame
  have hOpen := pairedFiniteFrameRelativeC2Domain_isOpen period hPeriod geometry frame
  have hDifferentiable : DifferentiableAt Real
      (pairedFiniteFrameRelativeC2Target period hPeriod geometry frame) 0 :=
    ((pairedFiniteFrameRelativeC2Target_contDiffOn period hPeriod geometry frame 0 hDomain).contDiffAt
      (hOpen.mem_nhds hDomain)).differentiableAt (by norm_num)
  exact hDifferentiable.hasFDerivAt

variable (hRegular : ∀ point, Function.Bijective
  (intrinsicCandidateASylvesterAt period hPeriod geometry point))

/-- Fréchet derivative at the center of the finite local root branch. -/
def pairedFiniteFrameMetricC2RootDerivativeAtZero :
    Model period hPeriod geometry frame →L[Real] Corner period hPeriod geometry frame :=
  fderiv Real (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular) 0

theorem pairedFiniteFrameMetricC2Root_hasFDerivAt_zero :
    HasFDerivAt (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular)
      (pairedFiniteFrameMetricC2RootDerivativeAtZero period hPeriod geometry frame hRegular) 0 := by
  have hDomain :=
    zero_mem_pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular
  have hOpen :=
    pairedFiniteFrameMetricC2RootDomain_isOpen period hPeriod geometry frame hRegular
  have hDifferentiable : DifferentiableAt Real
      (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular) 0 :=
    ((pairedFiniteFrameMetricC2Root_contDiffOn period hPeriod geometry frame hRegular
      0 hDomain).contDiffAt (hOpen.mem_nhds hDomain)).differentiableAt (by norm_num)
  exact hDifferentiable.hasFDerivAt

/-- Differentiating the exact local square identity gives the internal
Sylvester equation for the finite-frame root derivative. -/
theorem pairedFiniteFrameMetricC2RootDerivativeAtZero_sylvester
    (direction : Model period hPeriod geometry frame) :
    c2FiniteFrameCornerSylvester period hPeriod frame geometry.plusMetric
        (c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame)
        (pairedFiniteFrameMetricC2RootDerivativeAtZero period hPeriod geometry frame hRegular
          direction) =
      pairedFiniteFrameRelativeC2TargetDerivativeAtZero period hPeriod geometry frame direction := by
  have hRoot :=
    pairedFiniteFrameMetricC2Root_hasFDerivAt_zero period hPeriod geometry frame hRegular
  have hSquare := c2FiniteFrameCornerSquare_hasFDerivAt period hPeriod frame
    geometry.plusMetric
    (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular 0)
  have hComposed := hSquare.comp 0 hRoot
  have hDomain :=
    zero_mem_pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular
  have hOpen :=
    pairedFiniteFrameMetricC2RootDomain_isOpen period hPeriod geometry frame hRegular
  have hEqual :
      (fun variation => c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
        (pairedFiniteFrameMetricC2Root period hPeriod geometry frame hRegular variation)) =ᶠ[nhds 0]
        pairedFiniteFrameRelativeC2Target period hPeriod geometry frame := by
    filter_upwards [hOpen.mem_nhds hDomain] with variation hVariation
    exact pairedFiniteFrameMetricC2Root_square period hPeriod geometry frame hRegular
      variation hVariation
  have hTarget :=
    pairedFiniteFrameRelativeC2Target_hasFDerivAt_zero period hPeriod geometry frame
  have hDerivativeEquality := (hComposed.congr_of_eventuallyEq hEqual.symm).unique hTarget
  have hApply := congrArg
    (fun derivative : Model period hPeriod geometry frame →L[Real]
        Corner period hPeriod geometry frame => derivative direction)
    hDerivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    pairedFiniteFrameMetricC2Root_zero] using hApply

end
end P0EFTJanusFiniteFramePairedRelativeC2RootDerivativeAtCenter4D
end JanusFormal
