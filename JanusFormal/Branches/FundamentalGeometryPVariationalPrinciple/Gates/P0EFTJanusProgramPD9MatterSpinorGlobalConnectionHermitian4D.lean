import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorFlatGlobalConnectionBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorFlatConnectionHermitian4D

/-! # Hermitian compatibility of the global D9 spinor connection -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorGlobalConnectionHermitian4D

set_option autoImplicit false
noncomputable section

open Set Topology Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorGlobalCovariantDerivative4D
open P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorFlatConnectionHermitian4D
open P0EFTJanusProgramPD9MatterSpinorFlatGlobalConnectionBridge4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
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

private theorem d9MatterSpinorSectionPairing_local
    (choice : NormalRootChoice)
    (first second : SmoothThroatMatterSpinorLift period hPeriod choice)
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod anchor) :
    d9MatterSpinorHermitianPairing
        (d9MatterSpinorSectionFiber period hPeriod choice first base)
        (d9MatterSpinorSectionFiber period hPeriod choice second base) =
      d9MatterSpinorHermitianPairing
        (first ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt
          anchor base))
        (second ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt
          anchor base)) := by
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
  change d9MatterSpinorHermitianPairing
      (first (normalBundleIndexAt period hPeriod base))
      (second (normalBundleIndexAt period hPeriod base)) = _
  rw [← hTransition,
    SmoothThroatMatterSpinorLift.deck_monodromy
      period hPeriod choice first,
    SmoothThroatMatterSpinorLift.deck_monodromy
      period hPeriod choice second]
  exact (d9MatterSpinorMonodromy_preserves_pairing period hPeriod choice
    (localTransitionWinding period hPeriod
      (normalBundleIndexAt period hPeriod base) anchor base)
    (normalBundleIndexAt period hPeriod base)
    (first (normalBundleIndexAt period hPeriod base))
    (second (normalBundleIndexAt period hPeriod base))).symm

theorem d9MatterSpinorGlobalCovariantDerivative_pairing_compatible
    (choice : NormalRootChoice)
    (first second : SmoothThroatMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) (tangent : ThroatCoverCoordinates) :
    mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Complex)
        (fun current => d9MatterSpinorHermitianPairing
          (d9MatterSpinorSectionFiber period hPeriod choice first current)
          (d9MatterSpinorSectionFiber period hPeriod choice second current))
        base tangent =
      d9MatterSpinorHermitianPairing
          (d9MatterSpinorSectionFiber period hPeriod choice first base)
          (d9MatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
            (d9MatterSpinorSectionFiber period hPeriod choice second) base
            tangent) +
        d9MatterSpinorHermitianPairing
          (d9MatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
            (d9MatterSpinorSectionFiber period hPeriod choice first) base
            tangent)
          (d9MatterSpinorSectionFiber period hPeriod choice second base) := by
  let anchor := normalBundleIndexAt period hPeriod base
  let localInverse :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
  have hBase : base ∈ normalBundleBaseSet period hPeriod anchor :=
    mem_normalBundleBaseSet_indexAt period hPeriod base
  have hPairing : Filter.EventuallyEq (nhds base)
      (fun current => d9MatterSpinorHermitianPairing
        (d9MatterSpinorSectionFiber period hPeriod choice first current)
        (d9MatterSpinorSectionFiber period hPeriod choice second current))
      (fun current => d9MatterSpinorHermitianPairing
        (first (localInverse current)) (second (localInverse current))) := by
    filter_upwards [(normalBundleBaseSet_isOpen period hPeriod anchor).mem_nhds
      hBase] with current hCurrent
    exact d9MatterSpinorSectionPairing_local period hPeriod choice first second
      anchor current hCurrent
  have hInverseBase : localInverse base = anchor := by
    have hSelf := (throatProjectionLocalHomeomorph period hPeriod)
      |>.localInverseAt_apply_self (x := anchor)
    rw [normalBundleIndexAt_projects period hPeriod base] at hSelf
    exact hSelf
  have hPairAt : MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Complex)
      (fun point => d9MatterSpinorHermitianPairing (first point) (second point))
      (localInverse base) :=
    (d9MatterSpinorSectionPairing_contMDiff
      period hPeriod choice first second)
      |>.mdifferentiableAt (by simp)
  have hInverseAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners localInverse base := by
    rw [← normalBundleIndexAt_projects period hPeriod base]
    exact (throatProjectionLocalInverseAt_contMDiffAt period hPeriod anchor)
      |>.mdifferentiableAt (by simp)
  have hFirstConnection := congrArg (fun derivative => derivative tangent)
    (d9MatterSpinorGlobalCovariantDerivative_descended_flatCover
      period hPeriod choice first base)
  have hSecondConnection := congrArg (fun derivative => derivative tangent)
    (d9MatterSpinorGlobalCovariantDerivative_descended_flatCover
      period hPeriod choice second base)
  rw [hPairing.mfderiv_eq]
  change (mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real Complex)
      ((fun point => d9MatterSpinorHermitianPairing
        (first point) (second point)) ∘ localInverse) base) tangent =
    d9MatterSpinorHermitianPairing (first anchor)
        (d9MatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
          (d9MatterSpinorSectionFiber period hPeriod choice second) base
          tangent) +
      d9MatterSpinorHermitianPairing
        (d9MatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
          (d9MatterSpinorSectionFiber period hPeriod choice first) base
          tangent)
        (second anchor)
  rw [mfderiv_comp_apply base hPairAt hInverseAt tangent]
  rw [hInverseBase]
  rw [d9MatterSpinorFlatCoverDerivative_pairing_compatible]
  rw [hFirstConnection, hSecondConnection]
  rfl

end
end P0EFTJanusProgramPD9MatterSpinorGlobalConnectionHermitian4D
end JanusFormal
