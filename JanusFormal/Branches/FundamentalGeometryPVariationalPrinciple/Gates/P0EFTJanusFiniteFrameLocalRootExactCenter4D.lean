import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameSylvesterLocalRoot4D

/-! # Exact center of the constructed finite-frame local root

On the already specified Sylvester-regular stratum, the actual inverse-function
construction retains the stored root at zero. This extracts its center law;
it does not enlarge the regular stratum or construct a physical atlas.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameLocalRootExactCenter4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Set Topology
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D

/-- The implemented inverse branch returns its actual IFT center at zero. -/
theorem regularLocalC2InverseOpenBranch_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    (map : F → F) (center : F) (derivative : F → F →L[Real] F)
    (equiv : F ≃L[Real] F)
    (hForward : (equiv : F →L[Real] F) = derivative center)
    (hMap : ContDiff Real 2 map)
    (hDerivative : ∀ point, HasFDerivAt map (derivative point) point)
    (hDerivativeContinuous : Continuous derivative) :
    (regularLocalC2InverseOpenBranch map center derivative equiv hForward
      hMap hDerivative hDerivativeContinuous).branch 0 = center := by
  let regularSet : Set F :=
    derivative ⁻¹' Set.range ((↑) : (F ≃L[Real] F) → (F →L[Real] F))
  have hRegularSetOpen : IsOpen regularSet :=
    ContinuousLinearEquiv.isOpen.preimage hDerivativeContinuous
  let baseChart : OpenPartialHomeomorph F F :=
    hMap.contDiffAt.toOpenPartialHomeomorph map
      ((hDerivative center).congr_fderiv hForward.symm) (by norm_num)
  let chart : OpenPartialHomeomorph F F :=
    baseChart.restrOpen regularSet hRegularSetOpen
  have hCenterSource : center ∈ chart.source := by
    rw [show chart = baseChart.restrOpen regularSet hRegularSetOpen by rfl,
      OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hMap.contDiffAt.mem_toOpenPartialHomeomorph_source
      ((hDerivative center).congr_fderiv hForward.symm) (by norm_num),
      ⟨equiv, hForward⟩⟩
  change chart.symm (map center + 0) = center
  rw [add_zero]
  exact chart.left_inv hCenterSource

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameSylvesterLocalRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance c2ScalarNormedSpace : NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance
local instance c2ScalarCompleteSpace : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance cornerNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (C2FiniteFrameCorner period hPeriod frame metric) :=
  (c2FiniteFrameCornerSubmodule period hPeriod frame metric).normedAddCommGroup
local instance cornerNormedSpace
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (C2FiniteFrameCorner period hPeriod frame metric) := inferInstance
local instance cornerCompleteSpace
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (C2FiniteFrameCorner period hPeriod frame metric) :=
  c2FiniteFrameCornerCompleteSpace period hPeriod frame metric

/-- The C² branch is centered on the stored intrinsic root, including regular
branches other than the identity branch. -/
theorem globalCandidateAC2FiniteFrameLocalRootBranch_zero
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    (globalCandidateAC2FiniteFrameLocalRootBranch period hPeriod geometry frame hRegular).branch 0 =
      c2GlobalCandidateAFiniteFrameRootCorner period hPeriod geometry frame := by
  unfold globalCandidateAC2FiniteFrameLocalRootBranch
  exact regularLocalC2InverseOpenBranch_zero _ _ _ _ _ _ _ _

end
end P0EFTJanusFiniteFrameLocalRootExactCenter4D
end JanusFormal
