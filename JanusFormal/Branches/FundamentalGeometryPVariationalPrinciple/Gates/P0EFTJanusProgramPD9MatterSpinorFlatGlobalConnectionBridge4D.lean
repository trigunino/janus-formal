import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorGlobalCovariantDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D

/-! # Identification of the global and flat-cover D9 spinor connections -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorFlatGlobalConnectionBridge4D

set_option autoImplicit false
noncomputable section

open Set Topology Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorGlobalCovariantDerivative4D
open P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D
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
    (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ω :=
  smoothThroatMatterSpinorVectorBundleCore_isContMDiff period hPeriod choice

local instance totalSpaceTopology (choice : NormalRootChoice) :
    TopologicalSpace (Bundle.TotalSpace MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice)) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).toTopologicalSpace

local instance fiberBundle (choice : NormalRootChoice) :
    FiberBundle MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).fiberBundle

local instance vectorBundle (choice : NormalRootChoice) :
    VectorBundle Real MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).vectorBundle

local instance fiberIsTopologicalAddGroup (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    IsTopologicalAddGroup
      (SmoothThroatMatterSpinorFiber period hPeriod choice base) := by
  change IsTopologicalAddGroup MatterFiber
  infer_instance

local instance fiberContinuousSMul (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    ContinuousSMul Real
      (SmoothThroatMatterSpinorFiber period hPeriod choice base) := by
  change ContinuousSMul Real MatterFiber
  infer_instance

private theorem mvfderiv_matterFiber_eq_mfderiv
    (f : ThroatBase period hPeriod → MatterFiber)
    (base : ThroatBase period hPeriod) :
    mvfderiv throatCoverModelWithCorners f base =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real MatterFiber) f base := by
  rfl

theorem d9MatterSpinorGlobalCovariantDerivative_descended_local
    (choice : NormalRootChoice)
    (lift : SmoothThroatMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9MatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
        (d9MatterSpinorSectionFiber period hPeriod choice lift) base =
      mvfderiv throatCoverModelWithCorners
        (lift.toFun ∘
          (throatProjectionLocalHomeomorph period hPeriod).localInverseAt
            (normalBundleIndexAt period hPeriod base)) base := by
  let core := smoothThroatMatterSpinorVectorBundleCore period hPeriod choice
  let anchor := normalBundleIndexAt period hPeriod base
  let e := trivializationAt MatterFiber
    (SmoothThroatMatterSpinorFiber period hPeriod choice) base
  let localInverse :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
  let hb : base ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' base
  have hBase : base ∈ normalBundleBaseSet period hPeriod anchor :=
    mem_normalBundleBaseSet_indexAt period hPeriod base
  have hCoordinate :
      (fun current : ThroatBase period hPeriod =>
        (e ⟨current, d9MatterSpinorSectionFiber period hPeriod choice lift
          current⟩).2) =ᶠ[nhds base]
      (lift.toFun ∘ localInverse) := by
    filter_upwards [(normalBundleBaseSet_isOpen period hPeriod anchor).mem_nhds
      hBase] with current hCurrent
    exact d9MatterSpinorBundleSection_localTriv period hPeriod choice lift
      anchor current hCurrent
  have hDerivative :
      mvfderiv throatCoverModelWithCorners
          (fun current : ThroatBase period hPeriod =>
            (e ⟨current, d9MatterSpinorSectionFiber period hPeriod choice lift
              current⟩).2) base =
        mvfderiv throatCoverModelWithCorners
          (lift.toFun ∘ localInverse) base := by
    unfold mvfderiv
    rw [hCoordinate.self_of_nhds, hCoordinate.mfderiv_eq]
  have hSymm (value : MatterFiber) : e.symm base value = value := by
    rw [show e = core.localTrivAt base by rfl]
    rw [← core.localTrivAt_def]
    rw [core.localTriv_symm_apply (core.indexAt base)
      (core.mem_baseSet_at base) value]
    exact core.coordChange_self (core.indexAt base) base
      (core.mem_baseSet_at base) value
  change ((e.continuousLinearEquivAt Real base hb).symm :
      MatterFiber →L[Real]
        SmoothThroatMatterSpinorFiber period hPeriod choice base).comp
      (mvfderiv throatCoverModelWithCorners
        (fun current : ThroatBase period hPeriod =>
          (e ⟨current, d9MatterSpinorSectionFiber period hPeriod choice lift
            current⟩).2) base) = _
  rw [hDerivative]
  ext tangent
  exact hSymm _

theorem d9MatterSpinorGlobalCovariantDerivative_descended_flatCover
    (choice : NormalRootChoice)
    (lift : SmoothThroatMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9MatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
        (d9MatterSpinorSectionFiber period hPeriod choice lift) base =
      (d9MatterSpinorFlatCoverDerivative period hPeriod choice lift
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
      (modelWithCornersSelf Real MatterFiber) lift (localInverse base) :=
    lift.contMDiff_toFun.mdifferentiableAt (by simp)
  have hInverseAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners localInverse base := by
    rw [← normalBundleIndexAt_projects period hPeriod base]
    exact (throatProjectionLocalInverseAt_contMDiffAt period hPeriod anchor)
      |>.mdifferentiableAt (by simp)
  rw [d9MatterSpinorGlobalCovariantDerivative_descended_local,
    mvfderiv_matterFiber_eq_mfderiv,
    mfderiv_comp base hLiftAt hInverseAt, hInverseBase]
  rfl

end
end P0EFTJanusProgramPD9MatterSpinorFlatGlobalConnectionBridge4D
end JanusFormal
