import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusDifferentialNormalSmoothBundleEquivalence
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth fiberwise normal-bundle comparison

The transported differential-normal atlas already makes the total comparison
an analytic diffeomorphism.  This gate strengthens that statement in the
vector-bundle language: the pointwise continuous linear equivalence and its
inverse are analytic sections of the corresponding hom bundles.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusDifferentialNormalSmoothBundleIsomorphism

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
open P0EFTJanusMappingTorusDifferentialNormalSmoothBundleEquivalence

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance ambientBaseChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

private local instance fixedNormalFiberIsTopologicalAddGroup
    (point : ThroatBase period hPeriod) :
    IsTopologicalAddGroup (FixedThroatNormalFiber period hPeriod point) := by
  change IsTopologicalAddGroup Real
  infer_instance

private local instance fixedNormalFiberContinuousSMul
    (point : ThroatBase period hPeriod) :
    ContinuousSMul Real (FixedThroatNormalFiber period hPeriod point) := by
  change ContinuousSMul Real Real
  infer_instance

/-- The forward fiberwise comparison as a section of the hom bundle. -/
def differentialNormalForwardHomSection (point : ThroatBase period hPeriod) :
    Bundle.TotalSpace (Real →L[Real] Real)
      (fun base ↦ FixedThroatNormalFiber period hPeriod base →L[Real]
        DifferentialNormalFiber period hPeriod base) :=
  ⟨point, differentialNormalFiberContinuousEquiv period hPeriod point⟩

@[simp] theorem differentialNormalForwardHomSection_fst
    (point : ThroatBase period hPeriod) :
    (differentialNormalForwardHomSection period hPeriod point).1 = point :=
  rfl

@[simp] theorem differentialNormalForwardHomSection_snd_apply
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (differentialNormalForwardHomSection period hPeriod point).2 normal =
      differentialNormalFiberEquiv period hPeriod point normal :=
  rfl

private theorem differentialNormalForward_inCoordinates
    (base point : ThroatBase period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod
      (normalBundleIndexAt period hPeriod base)) :
    ContinuousLinearMap.inCoordinates Real
        (FixedThroatNormalFiber period hPeriod) Real
        (DifferentialNormalFiber period hPeriod)
        base point base point
        (differentialNormalFiberContinuousEquiv period hPeriod point) =
      ContinuousLinearMap.id Real Real := by
  apply ContinuousLinearMap.ext
  intro normal
  simp only [ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  simp only [show trivializationAt Real
      (FixedThroatNormalFiber period hPeriod) base =
        (fixedThroatNormalVectorBundleCore period hPeriod).localTriv
          (normalBundleIndexAt period hPeriod base) from rfl]
  simp only [show trivializationAt Real
      (DifferentialNormalFiber period hPeriod) base =
        differentialNormalLocalTriv period hPeriod
          (normalBundleIndexAt period hPeriod base) from rfl]
  simp only [ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := Real)
    (e := differentialNormalLocalTriv period hPeriod
      (normalBundleIndexAt period hPeriod base)) hPoint]
  change
    (differentialNormalLocalTriv period hPeriod
      (normalBundleIndexAt period hPeriod base)
      (differentialNormalTotalDiffeomorph period hPeriod
        ⟨point,
          ((fixedThroatNormalVectorBundleCore period hPeriod).localTriv
            (normalBundleIndexAt period hPeriod base)).symmL Real point normal⟩)).2 =
      normal
  rw [differentialNormalTotalDiffeomorph_localTriv]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := Real)
    (e := (fixedThroatNormalVectorBundleCore period hPeriod).localTriv
      (normalBundleIndexAt period hPeriod base)) hPoint]
  exact Bundle.Trivialization.continuousLinearMapAt_symmL _ hPoint normal

/-- The forward family of quotient maps varies analytically with the base. -/
theorem differentialNormalForwardHomSection_contMDiff :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, Real →L[Real] Real)) ω
      (differentialNormalForwardHomSection period hPeriod) := by
  intro base
  rw [contMDiffAt_hom_bundle]
  constructor
  · exact contMDiffAt_id
  · let anchor := normalBundleIndexAt period hPeriod base
    have hBase : base ∈ normalBundleBaseSet period hPeriod anchor :=
      mem_normalBundleBaseSet_indexAt period hPeriod base
    have hEventually :
        ∀ᶠ point in 𝓝 base,
          point ∈ normalBundleBaseSet period hPeriod anchor :=
      (normalBundleBaseSet_isOpen period hPeriod anchor).mem_nhds hBase
    apply (contMDiffAt_const : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real (Real →L[Real] Real)) ω
      (fun _ : ThroatBase period hPeriod ↦ ContinuousLinearMap.id Real Real)
      base).congr_of_eventuallyEq
    filter_upwards [hEventually] with point hPoint
    exact differentialNormalForward_inCoordinates period hPeriod base point hPoint

/-- The inverse fiberwise comparison as a section of the reverse hom bundle. -/
def differentialNormalBackwardHomSection (point : ThroatBase period hPeriod) :
    Bundle.TotalSpace (Real →L[Real] Real)
      (fun base ↦ DifferentialNormalFiber period hPeriod base →L[Real]
        FixedThroatNormalFiber period hPeriod base) :=
  ⟨point, (differentialNormalFiberContinuousEquiv period hPeriod point).symm⟩

@[simp] theorem differentialNormalBackwardHomSection_fst
    (point : ThroatBase period hPeriod) :
    (differentialNormalBackwardHomSection period hPeriod point).1 = point :=
  rfl

@[simp] theorem differentialNormalBackwardHomSection_snd_apply
    (point : ThroatBase period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    (differentialNormalBackwardHomSection period hPeriod point).2 normal =
      (differentialNormalFiberEquiv period hPeriod point).symm normal :=
  rfl

private theorem differentialNormalBackward_inCoordinates
    (base point : ThroatBase period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod
      (normalBundleIndexAt period hPeriod base)) :
    ContinuousLinearMap.inCoordinates Real
        (DifferentialNormalFiber period hPeriod) Real
        (FixedThroatNormalFiber period hPeriod)
        base point base point
        (differentialNormalFiberContinuousEquiv period hPeriod point).symm =
      ContinuousLinearMap.id Real Real := by
  apply ContinuousLinearMap.ext
  intro normal
  simp only [ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  simp only [show trivializationAt Real
      (DifferentialNormalFiber period hPeriod) base =
        differentialNormalLocalTriv period hPeriod
          (normalBundleIndexAt period hPeriod base) from rfl]
  simp only [show trivializationAt Real
      (FixedThroatNormalFiber period hPeriod) base =
        (fixedThroatNormalVectorBundleCore period hPeriod).localTriv
          (normalBundleIndexAt period hPeriod base) from rfl]
  simp only [ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := Real)
    (e := (fixedThroatNormalVectorBundleCore period hPeriod).localTriv
      (normalBundleIndexAt period hPeriod base)) hPoint]
  let targetTriv := differentialNormalLocalTriv period hPeriod
    (normalBundleIndexAt period hPeriod base)
  let differentialNormal := targetTriv.symmL Real point normal
  let fixedNormal :=
    (differentialNormalFiberContinuousEquiv period hPeriod point).symm
      differentialNormal
  have hForwardFiber :
      differentialNormalTotalDiffeomorph period hPeriod
          (⟨point, fixedNormal⟩ : Bundle.TotalSpace Real
            (FixedThroatNormalFiber period hPeriod)) =
        (⟨point, differentialNormal⟩ : DifferentialNormalTotalSpace period hPeriod) := by
    change
      (⟨point,
        differentialNormalFiberEquiv period hPeriod point
          ((differentialNormalFiberEquiv period hPeriod point).symm
            differentialNormal)⟩ : DifferentialNormalTotalSpace period hPeriod) =
        ⟨point, differentialNormal⟩
    rw [Bundle.TotalSpace.mk_inj]
    exact differentialNormalFiberEquiv_apply_symm_apply period hPeriod
      point differentialNormal
  have hChart := congrArg Prod.snd
    (differentialNormalTotalDiffeomorph_localTriv period hPeriod
      (normalBundleIndexAt period hPeriod base)
      (⟨point, fixedNormal⟩ : Bundle.TotalSpace Real
        (FixedThroatNormalFiber period hPeriod)))
  rw [hForwardFiber] at hChart
  change
    (((fixedThroatNormalVectorBundleCore period hPeriod).localTriv
      (normalBundleIndexAt period hPeriod base))
      ⟨point, fixedNormal⟩).2 = normal
  rw [← hChart]
  change (targetTriv ⟨point, differentialNormal⟩).2 = normal
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := Real) (e := targetTriv) hPoint]
  exact Bundle.Trivialization.continuousLinearMapAt_symmL _ hPoint normal

/-- The inverse family also varies analytically with the base. -/
theorem differentialNormalBackwardHomSection_contMDiff :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, Real →L[Real] Real)) ω
      (differentialNormalBackwardHomSection period hPeriod) := by
  intro base
  rw [contMDiffAt_hom_bundle]
  constructor
  · exact contMDiffAt_id
  · let anchor := normalBundleIndexAt period hPeriod base
    have hBase : base ∈ normalBundleBaseSet period hPeriod anchor :=
      mem_normalBundleBaseSet_indexAt period hPeriod base
    have hEventually :
        ∀ᶠ point in 𝓝 base,
          point ∈ normalBundleBaseSet period hPeriod anchor :=
      (normalBundleBaseSet_isOpen period hPeriod anchor).mem_nhds hBase
    apply (contMDiffAt_const : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real (Real →L[Real] Real)) ω
      (fun _ : ThroatBase period hPeriod ↦ ContinuousLinearMap.id Real Real)
      base).congr_of_eventuallyEq
    filter_upwards [hEventually] with point hPoint
    exact differentialNormalBackward_inCoordinates period hPeriod base point hPoint

end

end P0EFTJanusMappingTorusDifferentialNormalSmoothBundleIsomorphism
end JanusFormal
