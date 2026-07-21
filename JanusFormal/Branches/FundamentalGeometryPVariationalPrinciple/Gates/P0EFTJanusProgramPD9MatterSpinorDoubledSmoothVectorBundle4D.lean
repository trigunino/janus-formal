import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D

/-! # Smooth doubled D9 matter-spinor bundle -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D

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
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

abbrev D9DoubledMatterFiber := MatterFiber × MatterFiber

def d9DoubledMatterFiberHalfSpinorLinearEquiv :
    D9DoubledMatterFiber ≃ₗ[Real] D9DoubledMatterSpinor :=
  matterFiberHalfSpinorLinearEquiv.prodCongr
    matterFiberHalfSpinorLinearEquiv

def d9DoubledMatterSpinorMonodromy
    (choice : NormalRootChoice) (winding : Int)
    (matter : D9DoubledMatterFiber) : D9DoubledMatterFiber :=
  (d9MatterSpinorMonodromy choice winding matter.1,
    d9MatterSpinorMonodromy (oppositeRoot choice) winding matter.2)

@[simp] theorem d9DoubledMatterSpinorMonodromy_zero
    (choice : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorMonodromy choice 0 matter = matter := by
  ext <;> simp [d9DoubledMatterSpinorMonodromy]

theorem d9DoubledMatterSpinorMonodromy_add
    (choice : NormalRootChoice) (first second : Int)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorMonodromy choice (first + second) matter =
      d9DoubledMatterSpinorMonodromy choice first
        (d9DoubledMatterSpinorMonodromy choice second matter) := by
  ext <;> simp only [d9DoubledMatterSpinorMonodromy] <;>
    rw [d9MatterSpinorMonodromy_add]

theorem d9DoubledMatterSpinorMonodromy_additive
    (choice : NormalRootChoice) (winding : Int)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorMonodromy choice winding (first + second) =
      d9DoubledMatterSpinorMonodromy choice winding first +
        d9DoubledMatterSpinorMonodromy choice winding second := by
  ext <;> simp [d9DoubledMatterSpinorMonodromy,
    d9MatterSpinorMonodromy_additive]

theorem d9DoubledMatterSpinorMonodromy_real_smul
    (choice : NormalRootChoice) (winding : Int) (scalar : Real)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorMonodromy choice winding (scalar • matter) =
      scalar • d9DoubledMatterSpinorMonodromy choice winding matter := by
  ext <;> simp [d9DoubledMatterSpinorMonodromy,
    d9MatterSpinorMonodromy_real_smul]

def d9DoubledMatterSpinorMonodromyLinear
    (choice : NormalRootChoice) (winding : Int) :
    D9DoubledMatterFiber →ₗ[Real] D9DoubledMatterFiber where
  toFun := d9DoubledMatterSpinorMonodromy choice winding
  map_add' := d9DoubledMatterSpinorMonodromy_additive choice winding
  map_smul' := d9DoubledMatterSpinorMonodromy_real_smul choice winding

def d9DoubledMatterSpinorMonodromyCLM
    (choice : NormalRootChoice) (winding : Int) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  LinearMap.toContinuousLinearMap
    (d9DoubledMatterSpinorMonodromyLinear choice winding)

@[simp] theorem d9DoubledMatterSpinorMonodromyCLM_apply
    (choice : NormalRootChoice) (winding : Int)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorMonodromyCLM choice winding matter =
      d9DoubledMatterSpinorMonodromy choice winding matter := rfl

theorem d9DoubledMatterSpinorMonodromy_one_eq_deckGenerator
    (choice : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterSpinorMonodromy choice 1 matter) =
      normalRootMultiplier choice •
        d9DoubledMatterSpinorDeckGenerator
          (d9DoubledMatterFiberHalfSpinorLinearEquiv matter) := by
  cases choice <;>
    apply Prod.ext <;> funext index <;> fin_cases index <;>
    simp [d9DoubledMatterFiberHalfSpinorLinearEquiv,
      d9DoubledMatterSpinorMonodromy, d9MatterSpinorMonodromy,
      d9DoubledMatterSpinorDeckGenerator, oppositeRoot,
      normalRootMultiplier, quarterRootRepresentation,
      ambientHalfGammaZ4Representation_one, ambientHalfGammaGeneratorUnit,
      ambientHalfGammaGenerator, dotProduct,
      Fin.sum_univ_succ]

private theorem continuousOn_d9DoubledMatterSpinorTransition
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod) :
    ContinuousOn
      (fun base => d9DoubledMatterSpinorMonodromyCLM choice
        (localTransitionWinding period hPeriod first second base))
      (normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) := by
  intro base hBase
  let overlap := normalBundleBaseSet period hPeriod first ∩
    normalBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (localTransitionWinding period hPeriod first second)
      (fun _ => localTransitionWinding period hPeriod first second base) :=
    (localTransitionWinding_eventuallyEq period hPeriod first second base hBase)
      |>.filter_mono inf_le_left
  exact (continuousWithinAt_const : ContinuousWithinAt
      (fun _ : ThroatBase period hPeriod =>
        d9DoubledMatterSpinorMonodromyCLM choice
          (localTransitionWinding period hPeriod first second base))
      overlap base).congr_of_eventuallyEq_of_mem
        (hWindingEq.fun_comp (d9DoubledMatterSpinorMonodromyCLM choice)) hBase

def smoothThroatDoubledMatterSpinorVectorBundleCore
    (choice : NormalRootChoice) :
    VectorBundleCore Real (ThroatBase period hPeriod) D9DoubledMatterFiber
      (ThroatCover period hPeriod) where
  baseSet := normalBundleBaseSet period hPeriod
  isOpen_baseSet := normalBundleBaseSet_isOpen period hPeriod
  indexAt := normalBundleIndexAt period hPeriod
  mem_baseSet_at := mem_normalBundleBaseSet_indexAt period hPeriod
  coordChange first second base := d9DoubledMatterSpinorMonodromyCLM choice
    (localTransitionWinding period hPeriod first second base)
  coordChange_self anchor base hBase matter := by
    simp [localTransitionWinding_self period hPeriod anchor base hBase]
  continuousOn_coordChange :=
    continuousOn_d9DoubledMatterSpinorTransition period hPeriod choice
  coordChange_comp first second third base hBase matter := by
    simp only [d9DoubledMatterSpinorMonodromyCLM_apply]
    rw [← d9DoubledMatterSpinorMonodromy_add,
      localTransitionWinding_add period hPeriod first second third base hBase]

private theorem contMDiffOn_d9DoubledMatterSpinorTransition
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber)) ω
      (fun base => d9DoubledMatterSpinorMonodromyCLM choice
        (localTransitionWinding period hPeriod first second base))
      (normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) := by
  intro base hBase
  let overlap := normalBundleBaseSet period hPeriod first ∩
    normalBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (localTransitionWinding period hPeriod first second)
      (fun _ => localTransitionWinding period hPeriod first second base) :=
    (localTransitionWinding_eventuallyEq period hPeriod first second base hBase)
      |>.filter_mono inf_le_left
  exact (contMDiffWithinAt_const : ContMDiffWithinAt throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber)) ω
      (fun _ : ThroatBase period hPeriod =>
        d9DoubledMatterSpinorMonodromyCLM choice
          (localTransitionWinding period hPeriod first second base))
      overlap base).congr_of_eventuallyEq_of_mem
        (hWindingEq.fun_comp (d9DoubledMatterSpinorMonodromyCLM choice)) hBase

theorem smoothThroatDoubledMatterSpinorVectorBundleCore_isContMDiff
    (choice : NormalRootChoice) :
    (smoothThroatDoubledMatterSpinorVectorBundleCore period hPeriod choice)
      |>.IsContMDiff throatCoverModelWithCorners ω := by
  constructor
  exact contMDiffOn_d9DoubledMatterSpinorTransition period hPeriod choice

abbrev SmoothThroatDoubledMatterSpinorFiber (choice : NormalRootChoice) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore period hPeriod choice).Fiber

structure ProgramPD9MatterSpinorDoubledSmoothVectorBundleCertificate4D where
  choice : NormalRootChoice
  core : VectorBundleCore Real (ThroatBase period hPeriod)
    D9DoubledMatterFiber (ThroatCover period hPeriod)
  coreCanonical : core =
    smoothThroatDoubledMatterSpinorVectorBundleCore period hPeriod choice
  coreSmooth : core.IsContMDiff throatCoverModelWithCorners ω

def programPD9MatterSpinorDoubledSmoothVectorBundleCertificate4D :
    ProgramPD9MatterSpinorDoubledSmoothVectorBundleCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  core := smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod .positiveQuarter
  coreCanonical := rfl
  coreSmooth := smoothThroatDoubledMatterSpinorVectorBundleCore_isContMDiff
    period hPeriod .positiveQuarter

theorem programPD9MatterSpinorDoubledSmoothVectorBundleCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorDoubledSmoothVectorBundleCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorDoubledSmoothVectorBundleCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
end JanusFormal
