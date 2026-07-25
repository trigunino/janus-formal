import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D

/-!
# Smooth descent for local primitive SpinC gauges

A smooth local fiber value in every joint throat/monopole chart descends to
a genuine smooth section as soon as the values obey the installed SpinC
coordinate-change cocycle.  This is the gluing theorem needed by explicit
monopole modes; it introduces no choice of global trivialization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D

set_option autoImplicit false
noncomputable section

open Set Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)
private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph
      (mappingTorusMk (ThroatData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (ThroatData period hPeriod)).isLocalHomeomorph

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance primitiveSpinCCoreIsContMDiff
    (choice : NormalRootChoice) :
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ∞ :=
  d9PrimitiveSpinCVectorBundleCore_isContMDiff
    period hPeriod choice

local instance primitiveSpinCTotalSpaceTopology
    (choice : NormalRootChoice) :
    TopologicalSpace
      (Bundle.TotalSpace D9DoubledMatterFiber
        (D9PrimitiveSpinCFiber period hPeriod choice)) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).toTopologicalSpace

local instance primitiveSpinCFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle D9DoubledMatterFiber
      (D9PrimitiveSpinCFiber period hPeriod choice) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).fiberBundle

local instance primitiveSpinCVectorBundle
    (choice : NormalRootChoice) :
    VectorBundle Real D9DoubledMatterFiber
      (D9PrimitiveSpinCFiber period hPeriod choice) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).vectorBundle

private abbrev D9DoubledMatterSpinorFiber
    (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).Fiber base

local instance doubledCoreIsContMDiff
    (choice : NormalRootChoice) :
    (smoothThroatDoubledMatterSpinorVectorBundleCore
      period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ω :=
  smoothThroatDoubledMatterSpinorVectorBundleCore_isContMDiff
    period hPeriod choice

local instance doubledTotalSpaceTopology
    (choice : NormalRootChoice) :
    TopologicalSpace
      (Bundle.TotalSpace D9DoubledMatterFiber
        (D9DoubledMatterSpinorFiber period hPeriod choice)) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).toTopologicalSpace

local instance doubledFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).fiberBundle

local instance doubledVectorBundle
    (choice : NormalRootChoice) :
    VectorBundle Real D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).vectorBundle

/-- Smooth local representatives of a charge-one monopole line section on
the sphere. -/
structure SmoothPrimitiveMonopoleLocalScalarFamily where
  localValue : MonopoleChart → MonopoleSphere → Complex
  contMDiffOn_localValue :
    ∀ chart,
      ContMDiffOn (𝓡 2) 𝓘(Real, Complex) ∞
        (localValue chart) (monopoleChartDomain chart)
  coordChange_localValue :
    ∀ first second point,
      point ∈ monopoleChartDomain first ∩
        monopoleChartDomain second →
      (primitiveMonopoleTransition 1 first second point : Complex) *
          localValue first point =
        localValue second point

/-- Local coordinates of an already smooth doubled-spinor lift in every
normal-root chart. -/
def doubledSpinorLiftLocalValue
    (choice : NormalRootChoice)
    (lift :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterFiber :=
  ((smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).localTriv anchor
      (d9DoubledMatterSpinorBundleSection
        period hPeriod choice lift base)).2

/-- In the chart anchored at a cover point, the local value over that
point's quotient class is the original upstairs lift. -/
theorem doubledSpinorLiftLocalValue_mk
    (choice : NormalRootChoice)
    (lift :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (anchor : ThroatCover period hPeriod) :
    doubledSpinorLiftLocalValue period hPeriod choice lift anchor
        (mappingTorusMk (ThroatData period hPeriod) anchor) =
      lift anchor := by
  unfold doubledSpinorLiftLocalValue
  rw [d9DoubledMatterSpinorBundleSection_localTriv
    period hPeriod choice lift anchor]
  · rw [(throatProjectionLocalHomeomorph period hPeriod)
      |>.localInverseAt_apply_self]
  · exact (throatProjectionLocalHomeomorph period hPeriod)
      |>.apply_self_mem_localInverseAt_source

theorem doubledSpinorLiftLocalValue_contMDiffOn
    (choice : NormalRootChoice)
    (lift :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (anchor : ThroatCover period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real D9DoubledMatterFiber) ∞
      (doubledSpinorLiftLocalValue
        period hPeriod choice lift anchor)
      (normalBundleBaseSet period hPeriod anchor) := by
  let core :=
    smoothThroatDoubledMatterSpinorVectorBundleCore
      period hPeriod choice
  let localTriv := core.localTriv anchor
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  have hMaps :
      MapsTo
        (d9DoubledMatterSpinorBundleSection
          period hPeriod choice lift)
        (normalBundleBaseSet period hPeriod anchor)
        localTriv.source := by
    intro base hBase
    rw [localTriv.mem_source]
    exact hBase
  exact
    (localTriv.contMDiffOn_iff hMaps).mp
      ((d9DoubledMatterSpinorBundleSection_contMDiff
        period hPeriod choice lift).contMDiffOn) |>.2

theorem doubledSpinorLiftLocalValue_coordChange
    (choice : NormalRootChoice)
    (lift :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) :
    d9DoubledMatterSpinorMonodromy choice
        (localTransitionWinding period hPeriod first second base)
        (doubledSpinorLiftLocalValue
          period hPeriod choice lift first base) =
      doubledSpinorLiftLocalValue
        period hPeriod choice lift second base := by
  let core :=
    smoothThroatDoubledMatterSpinorVectorBundleCore
      period hPeriod choice
  change
    core.coordChange first second base
        (core.coordChange (core.indexAt base) first base
          (lift (normalBundleIndexAt period hPeriod base))) =
      core.coordChange (core.indexAt base) second base
        (lift (normalBundleIndexAt period hPeriod base))
  exact core.coordChange_comp
    (core.indexAt base) first second base
      ⟨⟨core.mem_baseSet_at base, hBase.1⟩, hBase.2⟩ _

/-- Local smooth representatives obeying the full normal-root/monopole
coordinate-change law. -/
structure SmoothPrimitiveSpinCLocalGaugeFamily
    (choice : NormalRootChoice) where
  localValue :
    D9PrimitiveSpinCIndex period hPeriod →
      ThroatBase period hPeriod → D9DoubledMatterFiber
  contMDiffOn_localValue :
    ∀ index,
      ContMDiffOn throatCoverModelWithCorners
        (modelWithCornersSelf Real D9DoubledMatterFiber) ∞
        (localValue index)
        (d9PrimitiveSpinCBaseSet period hPeriod index)
  coordChange_localValue :
    ∀ first second base,
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second →
      d9PrimitiveSpinCCoordChange period hPeriod choice
          first second base (localValue first base) =
        localValue second base

/-- Tensor a smooth normal-root spinor lift with a smooth charge-one
monopole line section. -/
def primitiveSpinCTensorLocalGaugeFamily
    (choice : NormalRootChoice)
    (lift :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (monopole : SmoothPrimitiveMonopoleLocalScalarFamily) :
    SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice where
  localValue index base :=
    d9PrimitiveSpinCComplexActionCLM
      (monopole.localValue index.2
        (d9ThroatMonopoleSphereProjection period hPeriod base))
      (doubledSpinorLiftLocalValue
        period hPeriod choice lift index.1 base)
  contMDiffOn_localValue index := by
    have hProjection :
        ContMDiff throatCoverModelWithCorners (𝓡 2) ∞
          (d9ThroatMonopoleSphereProjection period hPeriod) :=
      (d9ThroatMonopoleSphereProjection_contMDiff
        period hPeriod).of_le le_top
    have hScalar :
        ContMDiffOn throatCoverModelWithCorners
          𝓘(Real, Complex) ∞
          (fun base =>
            monopole.localValue index.2
              (d9ThroatMonopoleSphereProjection
                period hPeriod base))
          (d9PrimitiveSpinCBaseSet period hPeriod index) :=
      (monopole.contMDiffOn_localValue index.2).comp
        hProjection.contMDiffOn (by
          intro base hBase
          exact hBase.2)
    have hAction :
        ContMDiffOn throatCoverModelWithCorners
          𝓘(Real,
            D9DoubledMatterFiber →L[Real]
              D9DoubledMatterFiber) ∞
          (fun base =>
            d9PrimitiveSpinCComplexActionCLM
              (monopole.localValue index.2
                (d9ThroatMonopoleSphereProjection
                  period hPeriod base)))
          (d9PrimitiveSpinCBaseSet period hPeriod index) :=
      d9PrimitiveSpinCComplexActionCLM_contMDiff.comp_contMDiffOn
        hScalar
    exact hAction.clm_apply
      ((doubledSpinorLiftLocalValue_contMDiffOn
        period hPeriod choice lift index.1).mono (by
          intro base hBase
          exact hBase.1))
  coordChange_localValue first second base hBase := by
    have hNormal :
        d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding period hPeriod
              first.1 second.1 base)
            (doubledSpinorLiftLocalValue
              period hPeriod choice lift first.1 base) =
          doubledSpinorLiftLocalValue
            period hPeriod choice lift second.1 base :=
      doubledSpinorLiftLocalValue_coordChange
        period hPeriod choice lift first.1 second.1 base
          ⟨hBase.1.1, hBase.2.1⟩
    have hMonopole :
        (d9PrimitiveSpinCPhaseTransition period hPeriod
            first.2 second.2 base : Complex) *
            monopole.localValue first.2
              (d9ThroatMonopoleSphereProjection
                period hPeriod base) =
          monopole.localValue second.2
            (d9ThroatMonopoleSphereProjection
              period hPeriod base) :=
      monopole.coordChange_localValue
        first.2 second.2
        (d9ThroatMonopoleSphereProjection period hPeriod base)
        ⟨hBase.1.2, hBase.2.2⟩
    change
      d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition period hPeriod
            first.2 second.2 base)
          (d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding period hPeriod
              first.1 second.1 base)
            (d9PrimitiveSpinCComplexActionCLM
              (monopole.localValue first.2
                (d9ThroatMonopoleSphereProjection
                  period hPeriod base))
              (doubledSpinorLiftLocalValue
                period hPeriod choice lift first.1 base))) =
        d9PrimitiveSpinCComplexActionCLM
          (monopole.localValue second.2
            (d9ThroatMonopoleSphereProjection
              period hPeriod base))
          (doubledSpinorLiftLocalValue
            period hPeriod choice lift second.1 base)
    rw [d9PrimitiveSpinCPhaseActionCLM_eq_complexAction,
      ← d9PrimitiveSpinCComplexAction_monodromy,
      ← d9PrimitiveSpinCComplexAction_mul,
      hNormal, hMonopole]

/-- Fiber value obtained by selecting the core's preferred chart. -/
def primitiveSpinCSectionFiber
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    D9PrimitiveSpinCFiber period hPeriod choice base :=
  family.localValue
    ((d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).indexAt base) base

/-- Total-space map underlying the descended section. -/
def primitiveSpinCBundleSection
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    ThroatBase period hPeriod →
      Bundle.TotalSpace D9DoubledMatterFiber
        (D9PrimitiveSpinCFiber period hPeriod choice) :=
  fun base =>
    ⟨base, primitiveSpinCSectionFiber
      period hPeriod choice family base⟩

@[simp]
theorem primitiveSpinCBundleSection_proj
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    Bundle.TotalSpace.proj ∘
        primitiveSpinCBundleSection
          period hPeriod choice family =
      id :=
  rfl

/-- In any installed chart, the descended section has exactly the prescribed
local representative. -/
theorem primitiveSpinCBundleSection_localTriv
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      d9PrimitiveSpinCBaseSet period hPeriod index) :
    ((d9PrimitiveSpinCVectorBundleCore period hPeriod choice)
      |>.localTriv index
        (primitiveSpinCBundleSection
          period hPeriod choice family base)).2 =
      family.localValue index base := by
  rw [VectorBundleCore.localTriv_apply]
  exact family.coordChange_localValue
    ((d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).indexAt base)
    index base
    ⟨(d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).mem_baseSet_at base, hBase⟩

/-- The cocycle-compatible local family descends smoothly. -/
theorem primitiveSpinCBundleSection_contMDiff
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real D9DoubledMatterFiber)) ∞
      (primitiveSpinCBundleSection
        period hPeriod choice family) := by
  intro base
  let core :=
    d9PrimitiveSpinCVectorBundleCore period hPeriod choice
  let index := core.indexAt base
  let localTriv := core.localTriv index
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨index, ?_⟩⟩
    rfl
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    core.mem_baseSet_at base
  have hSource :
      primitiveSpinCBundleSection
          period hPeriod choice family base ∈
        localTriv.source := by
    rw [localTriv.mem_source]
    exact hBase
  rw [localTriv.contMDiffAt_iff hSource]
  constructor
  · exact contMDiffAt_id
  · have hLocalSmooth :
        ContMDiffAt throatCoverModelWithCorners
          (modelWithCornersSelf Real D9DoubledMatterFiber) ∞
          (family.localValue index) base :=
      (family.contMDiffOn_localValue index).contMDiffAt
        ((d9PrimitiveSpinCBaseSet_isOpen
          period hPeriod index).mem_nhds hBase)
    apply hLocalSmooth.congr_of_eventuallyEq
    filter_upwards
      [(d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase] with nearby hNearby
    exact primitiveSpinCBundleSection_localTriv
      period hPeriod choice family index nearby hNearby

/-- Bundled genuine smooth section produced by local SpinC gluing. -/
def SmoothPrimitiveSpinCLocalGaugeFamily.toSmoothSection
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice where
  toFun :=
    primitiveSpinCSectionFiber period hPeriod choice family
  contMDiff_toFun :=
    primitiveSpinCBundleSection_contMDiff
      period hPeriod choice family

@[simp]
theorem SmoothPrimitiveSpinCLocalGaugeFamily.toSmoothSection_apply
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    family.toSmoothSection period hPeriod choice base =
      family.localValue
        ((d9PrimitiveSpinCVectorBundleCore
          period hPeriod choice).indexAt base) base :=
  rfl

end
end P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
end JanusFormal
