import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D

/-! # Smooth D9 matter-spinor vector bundle on the throat -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

def d9MatterSpinorMonodromy
    (choice : NormalRootChoice) (winding : Int)
    (matter : MatterFiber) : MatterFiber :=
  matterFiberHalfSpinorLinearEquiv.symm
    ((ambientHalfGammaZ4Representation (winding : ZMod 4) :
        AmbientComplexMatrix2) *ᵥ
      (quarterRootRepresentation choice winding •
        matterFiberHalfSpinorLinearEquiv matter))

@[simp] theorem d9MatterSpinorMonodromy_zero
    (choice : NormalRootChoice) (matter : MatterFiber) :
    d9MatterSpinorMonodromy choice 0 matter = matter := by
  simp [d9MatterSpinorMonodromy]

theorem d9MatterSpinorMonodromy_add
    (choice : NormalRootChoice) (first second : Int)
    (matter : MatterFiber) :
    d9MatterSpinorMonodromy choice (first + second) matter =
      d9MatterSpinorMonodromy choice first
        (d9MatterSpinorMonodromy choice second matter) := by
  apply matterFiberHalfSpinorLinearEquiv.injective
  simp only [d9MatterSpinorMonodromy, LinearEquiv.apply_symm_apply]
  rw [Int.cast_add,
    ambientHalfGammaZ4Representation.map_add_eq_mul,
    quarterRootRepresentation_add]
  simp only [Units.val_mul]
  rw [← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec_smul, mul_smul]

theorem d9MatterSpinorMonodromy_additive
    (choice : NormalRootChoice) (winding : Int)
    (first second : MatterFiber) :
    d9MatterSpinorMonodromy choice winding (first + second) =
      d9MatterSpinorMonodromy choice winding first +
        d9MatterSpinorMonodromy choice winding second := by
  apply matterFiberHalfSpinorLinearEquiv.injective
  simp [d9MatterSpinorMonodromy, Matrix.mulVec_add]

theorem d9MatterSpinorMonodromy_real_smul
    (choice : NormalRootChoice) (winding : Int) (scalar : Real)
    (matter : MatterFiber) :
    d9MatterSpinorMonodromy choice winding (scalar • matter) =
      scalar • d9MatterSpinorMonodromy choice winding matter := by
  apply matterFiberHalfSpinorLinearEquiv.injective
  funext index
  fin_cases index <;>
    simp [d9MatterSpinorMonodromy] <;> ring

def d9MatterSpinorMonodromyLinear
    (choice : NormalRootChoice) (winding : Int) :
    MatterFiber →ₗ[Real] MatterFiber where
  toFun := d9MatterSpinorMonodromy choice winding
  map_add' := d9MatterSpinorMonodromy_additive choice winding
  map_smul' := d9MatterSpinorMonodromy_real_smul choice winding

def d9MatterSpinorMonodromyCLM
    (choice : NormalRootChoice) (winding : Int) :
    MatterFiber →L[Real] MatterFiber :=
  LinearMap.toContinuousLinearMap (d9MatterSpinorMonodromyLinear choice winding)

@[simp] theorem d9MatterSpinorMonodromyCLM_apply
    (choice : NormalRootChoice) (winding : Int) (matter : MatterFiber) :
    d9MatterSpinorMonodromyCLM choice winding matter =
      d9MatterSpinorMonodromy choice winding matter := rfl

def d9MatterSpinorMonodromyCLE
    (choice : NormalRootChoice) (winding : Int) :
    MatterFiber ≃L[Real] MatterFiber where
  toFun := d9MatterSpinorMonodromy choice winding
  invFun := d9MatterSpinorMonodromy choice (-winding)
  left_inv matter := by
    rw [← d9MatterSpinorMonodromy_add]
    simp
  right_inv matter := by
    rw [← d9MatterSpinorMonodromy_add]
    simp
  map_add' := d9MatterSpinorMonodromy_additive choice winding
  map_smul' := d9MatterSpinorMonodromy_real_smul choice winding
  continuous_toFun := (d9MatterSpinorMonodromyCLM choice winding).continuous
  continuous_invFun := (d9MatterSpinorMonodromyCLM choice (-winding)).continuous

@[simp] theorem d9MatterSpinorMonodromyCLE_apply
    (choice : NormalRootChoice) (winding : Int) (matter : MatterFiber) :
    d9MatterSpinorMonodromyCLE choice winding matter =
      d9MatterSpinorMonodromy choice winding matter := rfl

@[simp] theorem d9MatterSpinorMonodromyCLE_symm_apply
    (choice : NormalRootChoice) (winding : Int) (matter : MatterFiber) :
    (d9MatterSpinorMonodromyCLE choice winding).symm matter =
      d9MatterSpinorMonodromy choice (-winding) matter := rfl

private theorem continuousOn_d9MatterSpinorTransition
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod) :
    ContinuousOn
      (fun base => d9MatterSpinorMonodromyCLM choice
        (localTransitionWinding period hPeriod first second base))
      (normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) := by
  intro base hBase
  let overlap := normalBundleBaseSet period hPeriod first ∩
    normalBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (localTransitionWinding period hPeriod first second)
      (fun _ => localTransitionWinding period hPeriod first second base) :=
    (localTransitionWinding_eventuallyEq period hPeriod first second base hBase).filter_mono
      inf_le_left
  exact (continuousWithinAt_const : ContinuousWithinAt
      (fun _ : ThroatBase period hPeriod => d9MatterSpinorMonodromyCLM choice
        (localTransitionWinding period hPeriod first second base)) overlap base).congr_of_eventuallyEq_of_mem
          (hWindingEq.fun_comp (d9MatterSpinorMonodromyCLM choice)) hBase

def smoothThroatMatterSpinorVectorBundleCore
    (choice : NormalRootChoice) :
    VectorBundleCore Real (ThroatBase period hPeriod) MatterFiber
      (ThroatCover period hPeriod) where
  baseSet := normalBundleBaseSet period hPeriod
  isOpen_baseSet := normalBundleBaseSet_isOpen period hPeriod
  indexAt := normalBundleIndexAt period hPeriod
  mem_baseSet_at := mem_normalBundleBaseSet_indexAt period hPeriod
  coordChange first second base := d9MatterSpinorMonodromyCLM choice
    (localTransitionWinding period hPeriod first second base)
  coordChange_self anchor base hBase matter := by
    simp [localTransitionWinding_self period hPeriod anchor base hBase]
  continuousOn_coordChange :=
    continuousOn_d9MatterSpinorTransition period hPeriod choice
  coordChange_comp first second third base hBase matter := by
    simp only [d9MatterSpinorMonodromyCLM_apply]
    rw [← d9MatterSpinorMonodromy_add,
      localTransitionWinding_add period hPeriod first second third base hBase]

private theorem contMDiffOn_d9MatterSpinorTransition
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real (MatterFiber →L[Real] MatterFiber)) ω
      (fun base => d9MatterSpinorMonodromyCLM choice
        (localTransitionWinding period hPeriod first second base))
      (normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) := by
  intro base hBase
  let overlap := normalBundleBaseSet period hPeriod first ∩
    normalBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (localTransitionWinding period hPeriod first second)
      (fun _ => localTransitionWinding period hPeriod first second base) :=
    (localTransitionWinding_eventuallyEq period hPeriod first second base hBase).filter_mono
      inf_le_left
  exact (contMDiffWithinAt_const : ContMDiffWithinAt throatCoverModelWithCorners
      (modelWithCornersSelf Real (MatterFiber →L[Real] MatterFiber)) ω
      (fun _ : ThroatBase period hPeriod => d9MatterSpinorMonodromyCLM choice
        (localTransitionWinding period hPeriod first second base)) overlap base).congr_of_eventuallyEq_of_mem
          (hWindingEq.fun_comp (d9MatterSpinorMonodromyCLM choice)) hBase

theorem smoothThroatMatterSpinorVectorBundleCore_isContMDiff
    (choice : NormalRootChoice) :
    (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ω := by
  constructor
  exact contMDiffOn_d9MatterSpinorTransition period hPeriod choice

abbrev SmoothThroatMatterSpinorFiber (choice : NormalRootChoice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).Fiber

local instance smoothThroatMatterSpinorTotalSpaceTopology
    (choice : NormalRootChoice) :
    TopologicalSpace
      (Bundle.TotalSpace MatterFiber
        (SmoothThroatMatterSpinorFiber period hPeriod choice)) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).toTopologicalSpace

local instance smoothThroatMatterSpinorFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).fiberBundle

local instance smoothThroatMatterSpinorVectorBundle
    (choice : NormalRootChoice) :
    VectorBundle Real MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).vectorBundle

theorem smoothThroatMatterSpinorFiber_isVectorBundle
    (choice : NormalRootChoice) :
    VectorBundle Real MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) :=
  inferInstance

theorem smoothThroatMatterSpinorFiber_isContMDiffVectorBundle
    (choice : NormalRootChoice) :
    letI : (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ω :=
      smoothThroatMatterSpinorVectorBundleCore_isContMDiff period hPeriod choice
    ContMDiffVectorBundle ω MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice)
      throatCoverModelWithCorners := by
  letI : (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ω :=
    smoothThroatMatterSpinorVectorBundleCore_isContMDiff period hPeriod choice
  infer_instance

structure ProgramPD9MatterSpinorSmoothVectorBundleCertificate4D where
  choice : NormalRootChoice
  core : VectorBundleCore Real (ThroatBase period hPeriod) MatterFiber
    (ThroatCover period hPeriod)
  coreCanonical : core =
    smoothThroatMatterSpinorVectorBundleCore period hPeriod choice
  coreSmooth : core.IsContMDiff throatCoverModelWithCorners ω

def programPD9MatterSpinorSmoothVectorBundleCertificate4D :
    ProgramPD9MatterSpinorSmoothVectorBundleCertificate4D period hPeriod where
  choice := .positiveQuarter
  core := smoothThroatMatterSpinorVectorBundleCore
    period hPeriod .positiveQuarter
  coreCanonical := rfl
  coreSmooth := smoothThroatMatterSpinorVectorBundleCore_isContMDiff
    period hPeriod .positiveQuarter

theorem programPD9MatterSpinorSmoothVectorBundleCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorSmoothVectorBundleCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorSmoothVectorBundleCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
end JanusFormal
