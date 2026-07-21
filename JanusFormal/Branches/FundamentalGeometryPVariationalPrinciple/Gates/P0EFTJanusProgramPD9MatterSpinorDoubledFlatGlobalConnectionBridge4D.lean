import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledGlobalCovariantDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D

/-! # Identification of the doubled global and flat-cover D9 connections -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledFlatGlobalConnectionBridge4D

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
open P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalCovariantDerivative4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D
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

local instance fiberIsTopologicalAddGroup (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    IsTopologicalAddGroup
      (D9DoubledMatterSpinorFiber period hPeriod choice base) := by
  change IsTopologicalAddGroup D9DoubledMatterFiber
  infer_instance

local instance fiberContinuousSMul (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    ContinuousSMul Real
      (D9DoubledMatterSpinorFiber period hPeriod choice base) := by
  change ContinuousSMul Real D9DoubledMatterFiber
  infer_instance

private theorem mvfderiv_doubledMatterFiber_eq_mfderiv
    (f : ThroatBase period hPeriod → D9DoubledMatterFiber)
    (base : ThroatBase period hPeriod) :
    mvfderiv throatCoverModelWithCorners f base =
      mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) f base := by
  rfl

theorem d9DoubledMatterSpinorGlobalCovariantDerivative_descended_local
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
        (d9DoubledMatterSpinorSectionFiber
          period hPeriod choice lift) base =
      mvfderiv throatCoverModelWithCorners
        (lift ∘
          (throatProjectionLocalHomeomorph period hPeriod).localInverseAt
            (normalBundleIndexAt period hPeriod base)) base := by
  let core := smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice
  let anchor := normalBundleIndexAt period hPeriod base
  let e := trivializationAt D9DoubledMatterFiber
    (D9DoubledMatterSpinorFiber period hPeriod choice) base
  let localInverse :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
  let hb : base ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' base
  have hBase : base ∈ normalBundleBaseSet period hPeriod anchor :=
    mem_normalBundleBaseSet_indexAt period hPeriod base
  have hCoordinate :
      (fun current : ThroatBase period hPeriod =>
        (e ⟨current, d9DoubledMatterSpinorSectionFiber
          period hPeriod choice lift current⟩).2) =ᶠ[nhds base]
      (lift ∘ localInverse) := by
    filter_upwards [(normalBundleBaseSet_isOpen period hPeriod anchor).mem_nhds
      hBase] with current hCurrent
    exact d9DoubledMatterSpinorBundleSection_localTriv
      period hPeriod choice lift anchor current hCurrent
  have hDerivative :
      mvfderiv throatCoverModelWithCorners
          (fun current : ThroatBase period hPeriod =>
            (e ⟨current, d9DoubledMatterSpinorSectionFiber
              period hPeriod choice lift current⟩).2) base =
        mvfderiv throatCoverModelWithCorners
          (lift ∘ localInverse) base := by
    unfold mvfderiv
    rw [hCoordinate.self_of_nhds, hCoordinate.mfderiv_eq]
  have hSymm (value : D9DoubledMatterFiber) :
      e.symm base value = value := by
    rw [show e = core.localTrivAt base by rfl]
    rw [← core.localTrivAt_def]
    rw [core.localTriv_symm_apply (core.indexAt base)
      (core.mem_baseSet_at base) value]
    exact core.coordChange_self (core.indexAt base) base
      (core.mem_baseSet_at base) value
  change ((e.continuousLinearEquivAt Real base hb).symm :
      D9DoubledMatterFiber →L[Real]
        D9DoubledMatterSpinorFiber period hPeriod choice base).comp
      (mvfderiv throatCoverModelWithCorners
        (fun current : ThroatBase period hPeriod =>
          (e ⟨current, d9DoubledMatterSpinorSectionFiber
            period hPeriod choice lift current⟩).2) base) = _
  rw [hDerivative]
  ext tangent
  exact hSymm _

theorem d9DoubledMatterSpinorGlobalCovariantDerivative_descended_flatCover
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
        (d9DoubledMatterSpinorSectionFiber
          period hPeriod choice lift) base =
      (d9DoubledMatterSpinorFlatCoverDerivative
        period hPeriod choice lift
        (normalBundleIndexAt period hPeriod base)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt
            (normalBundleIndexAt period hPeriod base)) base) := by
  let anchor := normalBundleIndexAt period hPeriod base
  let localInverse :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
  have hInverseBase : localInverse base = anchor := by
    have hSelf := (throatProjectionLocalHomeomorph period hPeriod)
      |>.localInverseAt_apply_self (x := anchor)
    rw [normalBundleIndexAt_projects period hPeriod base] at hSelf
    exact hSelf
  have hLiftAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) lift (localInverse base) :=
    lift.contMDiff_toFun.mdifferentiableAt (by simp)
  have hInverseAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners localInverse base := by
    rw [← normalBundleIndexAt_projects period hPeriod base]
    exact (throatProjectionLocalInverseAt_contMDiffAt period hPeriod anchor)
      |>.mdifferentiableAt (by simp)
  rw [d9DoubledMatterSpinorGlobalCovariantDerivative_descended_local,
    mvfderiv_doubledMatterFiber_eq_mfderiv,
    mfderiv_comp base hLiftAt hInverseAt, hInverseBase]
  rfl

end
end P0EFTJanusProgramPD9MatterSpinorDoubledFlatGlobalConnectionBridge4D
end JanusFormal
