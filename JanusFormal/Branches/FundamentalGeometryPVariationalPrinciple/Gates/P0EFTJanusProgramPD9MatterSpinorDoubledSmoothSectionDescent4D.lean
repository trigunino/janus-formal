import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D

/-! # Smooth sections of the doubled D9 matter-spinor bundle -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D

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
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

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

structure SmoothThroatDoubledMatterSpinorLift
    (choice : NormalRootChoice) where
  first : SmoothThroatMatterSpinorLift period hPeriod choice
  second : SmoothThroatMatterSpinorLift period hPeriod (oppositeRoot choice)

instance (choice : NormalRootChoice) :
    CoeFun (SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
      (fun _ => ThroatCover period hPeriod → D9DoubledMatterFiber) :=
  ⟨fun lift anchor => (lift.first anchor, lift.second anchor)⟩

theorem SmoothThroatDoubledMatterSpinorLift.contMDiff_toFun
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real D9DoubledMatterFiber) ∞ lift := by
  rw [contMDiff_prod_module_iff]
  exact ⟨lift.first.contMDiff_toFun, lift.second.contMDiff_toFun⟩

theorem SmoothThroatDoubledMatterSpinorLift.deck_monodromy
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (winding : Int) (anchor : ThroatCover period hPeriod) :
    lift (winding +ᵥ anchor) =
      d9DoubledMatterSpinorMonodromy choice winding (lift anchor) := by
  apply Prod.ext
  · exact SmoothThroatMatterSpinorLift.deck_monodromy
      period hPeriod choice lift.first winding anchor
  · exact SmoothThroatMatterSpinorLift.deck_monodromy
      period hPeriod (oppositeRoot choice) lift.second winding anchor

abbrev D9DoubledMatterSpinorFiber (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).Fiber base

local instance coreIsContMDiff (choice : NormalRootChoice) :
    (smoothThroatDoubledMatterSpinorVectorBundleCore period hPeriod choice)
      |>.IsContMDiff throatCoverModelWithCorners ω :=
  smoothThroatDoubledMatterSpinorVectorBundleCore_isContMDiff
    period hPeriod choice

local instance totalSpaceTopology (choice : NormalRootChoice) :
    TopologicalSpace (Bundle.TotalSpace D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice)) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).toTopologicalSpace

local instance fiberBundle (choice : NormalRootChoice) :
    FiberBundle D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).fiberBundle

local instance vectorBundle (choice : NormalRootChoice) :
    VectorBundle Real D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).vectorBundle

def d9DoubledMatterSpinorSectionFiber
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterSpinorFiber period hPeriod choice base :=
  lift (normalBundleIndexAt period hPeriod base)

def d9DoubledMatterSpinorBundleSection
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    ThroatBase period hPeriod → Bundle.TotalSpace D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) :=
  fun base => ⟨base,
    d9DoubledMatterSpinorSectionFiber period hPeriod choice lift base⟩

@[simp] theorem d9DoubledMatterSpinorBundleSection_proj
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    Bundle.TotalSpace.proj ∘
        d9DoubledMatterSpinorBundleSection period hPeriod choice lift = id := by
  rfl

theorem d9DoubledMatterSpinorBundleSection_localTriv
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod anchor) :
    ((smoothThroatDoubledMatterSpinorVectorBundleCore period hPeriod choice)
      |>.localTriv anchor
        (d9DoubledMatterSpinorBundleSection
          period hPeriod choice lift base)).2 =
      lift ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt
        anchor base) := by
  change d9DoubledMatterSpinorMonodromy choice
      (localTransitionWinding period hPeriod
        (normalBundleIndexAt period hPeriod base) anchor base)
      (lift (normalBundleIndexAt period hPeriod base)) = _
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
  exact (SmoothThroatDoubledMatterSpinorLift.deck_monodromy
    period hPeriod choice lift _ _).symm

theorem d9DoubledMatterSpinorBundleSection_contMDiff
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real D9DoubledMatterFiber)) ∞
      (d9DoubledMatterSpinorBundleSection period hPeriod choice lift) := by
  intro base
  let anchor := normalBundleIndexAt period hPeriod base
  let localTriv :=
    (smoothThroatDoubledMatterSpinorVectorBundleCore
      period hPeriod choice).localTriv anchor
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  have hBase : base ∈ normalBundleBaseSet period hPeriod anchor :=
    mem_normalBundleBaseSet_indexAt period hPeriod base
  have hSource :
      d9DoubledMatterSpinorBundleSection period hPeriod choice lift base ∈
        localTriv.source := by
    rw [localTriv.mem_source]
    exact hBase
  rw [localTriv.contMDiffAt_iff hSource]
  constructor
  · exact contMDiffAt_id
  · have hLocalSmooth : ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real D9DoubledMatterFiber) ∞
        (lift ∘
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
    exact d9DoubledMatterSpinorBundleSection_localTriv
      period hPeriod choice lift anchor nearby hNearby

end
end P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
end JanusFormal
