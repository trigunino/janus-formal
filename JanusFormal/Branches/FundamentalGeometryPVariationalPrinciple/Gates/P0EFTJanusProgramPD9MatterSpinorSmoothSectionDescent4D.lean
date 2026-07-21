import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D

/-!
# Smooth descent of D9 spinor lifts to the actual vector bundle

Every smooth deck-equivariant cover lift defines a genuine smooth section of
the analytic D9 spinor `VectorBundleCore`.  Its coordinate in any covering
trivialization is the original lift evaluated at that chart's local inverse.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D

set_option autoImplicit false
noncomputable section

open Set Topology Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

abbrev D9MatterSpinorFiber (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).Fiber base

private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph (mappingTorusMk (ThroatData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (ThroatData period hPeriod)).isLocalHomeomorph

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance coreIsContMDiff (choice : NormalRootChoice) :
    (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ω :=
  smoothThroatMatterSpinorVectorBundleCore_isContMDiff period hPeriod choice

local instance totalSpaceTopology (choice : NormalRootChoice) :
    TopologicalSpace (Bundle.TotalSpace MatterFiber
      (D9MatterSpinorFiber period hPeriod choice)) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).toTopologicalSpace

local instance fiberBundle (choice : NormalRootChoice) :
    FiberBundle MatterFiber
      (D9MatterSpinorFiber period hPeriod choice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).fiberBundle

local instance vectorBundle (choice : NormalRootChoice) :
    VectorBundle Real MatterFiber
      (D9MatterSpinorFiber period hPeriod choice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).vectorBundle

def d9MatterSpinorSectionFiber
    (choice : NormalRootChoice)
    (lift : SmoothThroatMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    D9MatterSpinorFiber period hPeriod choice base :=
  lift (normalBundleIndexAt period hPeriod base)

def d9MatterSpinorBundleSection
    (choice : NormalRootChoice)
    (lift : SmoothThroatMatterSpinorLift period hPeriod choice) :
    ThroatBase period hPeriod → Bundle.TotalSpace MatterFiber
      (D9MatterSpinorFiber period hPeriod choice) :=
  fun base => ⟨base, d9MatterSpinorSectionFiber period hPeriod choice lift base⟩

@[simp] theorem d9MatterSpinorBundleSection_proj
    (choice : NormalRootChoice)
    (lift : SmoothThroatMatterSpinorLift period hPeriod choice) :
    Bundle.TotalSpace.proj ∘
        d9MatterSpinorBundleSection period hPeriod choice lift = id := by
  rfl

theorem d9MatterSpinorBundleSection_localTriv
    (choice : NormalRootChoice)
    (lift : SmoothThroatMatterSpinorLift period hPeriod choice)
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod anchor) :
    ((smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).localTriv
      anchor (d9MatterSpinorBundleSection period hPeriod choice lift base)).2 =
      lift ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt
        anchor base) := by
  change d9MatterSpinorMonodromy choice
      (localTransitionWinding period hPeriod
        (normalBundleIndexAt period hPeriod base) anchor base)
      (lift (normalBundleIndexAt period hPeriod base)) =
    lift ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt
      anchor base)
  have hIndexLocalInverse :
      (throatProjectionLocalHomeomorph period hPeriod).localInverseAt
          (normalBundleIndexAt period hPeriod base) base =
        normalBundleIndexAt period hPeriod base := by
    have hSelf := (throatProjectionLocalHomeomorph period hPeriod)
      |>.localInverseAt_apply_self
        (x := normalBundleIndexAt period hPeriod base)
    rw [normalBundleIndexAt_projects period hPeriod base] at hSelf
    exact hSelf
  have hTransition := localTransitionWinding_vadd period hPeriod
    (normalBundleIndexAt period hPeriod base) anchor base
    ⟨mem_normalBundleBaseSet_indexAt period hPeriod base, hBase⟩
  rw [hIndexLocalInverse] at hTransition
  rw [← hTransition]
  exact (SmoothThroatMatterSpinorLift.deck_monodromy period hPeriod choice
    lift _ _).symm

theorem throatProjectionLocalInverseAt_contMDiffAt
    (anchor : ThroatCover period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners throatCoverModelWithCorners ∞
      ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor)
      (mappingTorusMk (ThroatData period hPeriod) anchor) := by
  let projection := mappingTorusMk (ThroatData period hPeriod)
  let topologicalInverse :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
  have hProjection : IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ω projection :=
    fixedThroat_projection_isLocalDiffeomorph period hPeriod
  let smoothInverse := (hProjection anchor).localInverse
  have hSmooth : ContMDiffAt throatCoverModelWithCorners
      throatCoverModelWithCorners ∞ smoothInverse (projection anchor) :=
    (hProjection anchor).localInverse_contMDiffAt.of_le (by simp)
  apply hSmooth.congr_of_eventuallyEq
  have hSmoothAt : smoothInverse (projection anchor) = anchor :=
    (hProjection anchor).localInverse_left_inv
      (hProjection anchor).localInverse_mem_target
  have hTopologicalSource : topologicalInverse.source ∈ nhds (projection anchor) :=
    topologicalInverse.open_source.mem_nhds
      ((throatProjectionLocalHomeomorph period hPeriod)
        |>.apply_self_mem_localInverseAt_source)
  have hSmoothIntoTarget : ∀ᶠ nearby in nhds (projection anchor),
      smoothInverse nearby ∈ topologicalInverse.target := by
    have hTarget : topologicalInverse.target ∈ nhds anchor :=
      topologicalInverse.open_target.mem_nhds
        ((throatProjectionLocalHomeomorph period hPeriod)
          |>.self_mem_localInverseAt_target)
    have hTendsto : Filter.Tendsto smoothInverse
        (nhds (projection anchor)) (nhds anchor) := by
      exact (congrArg nhds hSmoothAt) ▸ hSmooth.continuousAt
    exact hTendsto hTarget
  have hSmoothRight := (hProjection anchor).localInverse_eventuallyEq_right
  filter_upwards [hTopologicalSource, hSmoothIntoTarget, hSmoothRight]
    with nearby hSource hTarget hRight
  symm
  apply (throatProjectionLocalHomeomorph period hPeriod)
    |>.injOn_localInverseAt_target hTarget
      (topologicalInverse.map_source hSource)
  exact hRight.trans
    ((throatProjectionLocalHomeomorph period hPeriod)
      |>.apply_localInverseAt_of_mem hSource).symm

theorem d9MatterSpinorBundleSection_contMDiff
    (choice : NormalRootChoice)
    (lift : SmoothThroatMatterSpinorLift period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real MatterFiber)) ∞
      (d9MatterSpinorBundleSection period hPeriod choice lift) := by
  intro base
  let anchor := normalBundleIndexAt period hPeriod base
  let localTriv :=
    (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).localTriv
      anchor
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  have hBase : base ∈ normalBundleBaseSet period hPeriod anchor :=
    mem_normalBundleBaseSet_indexAt period hPeriod base
  have hSource : d9MatterSpinorBundleSection period hPeriod choice lift base ∈
      localTriv.source := by
    rw [localTriv.mem_source]
    exact hBase
  rw [localTriv.contMDiffAt_iff hSource]
  constructor
  · exact contMDiffAt_id
  · have hLocalSmooth : ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real MatterFiber) ∞
        (lift.toFun ∘
          (throatProjectionLocalHomeomorph period hPeriod).localInverseAt
            anchor) base := by
      have hBaseProjection :
          mappingTorusMk (ThroatData period hPeriod) anchor = base :=
        normalBundleIndexAt_projects period hPeriod base
      rw [← hBaseProjection]
      exact lift.contMDiff_toFun.contMDiffAt.comp _
        (throatProjectionLocalInverseAt_contMDiffAt period hPeriod anchor)
    apply hLocalSmooth.congr_of_eventuallyEq
    filter_upwards [(normalBundleBaseSet_isOpen period hPeriod anchor).mem_nhds
      hBase] with nearby hNearby
    exact d9MatterSpinorBundleSection_localTriv period hPeriod choice lift
      anchor nearby hNearby

end
end P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D
end JanusFormal
