import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Primitive SpinC matter bundle on D9

The primitive circle clutching action is transported to the doubled real
matter fiber through its complex half-spinor realization.  It commutes with
both the normal-root deck monodromy and the Clifford action.  The two
independent cocycles can therefore be combined into one genuine vector-bundle
core on the actual throat.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

/-- Continuous version of the real-linear doubled half-spinor
identification. -/
def d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv :
    D9DoubledMatterFiber ≃L[Real] D9DoubledMatterSpinor :=
  d9DoubledMatterFiberHalfSpinorLinearEquiv.toContinuousLinearEquiv

/-- Arbitrary complex scalar action transported from the doubled
half-spinor model. -/
def d9PrimitiveSpinCComplexActionCLM (scalar : Complex) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.lsmul Real Complex scalar).comp
      d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      scalar • d9DoubledMatterFiberHalfSpinorLinearEquiv matter := by
  simp [d9PrimitiveSpinCComplexActionCLM,
    d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv]

/-- Scalar `U(1)` action transported from the complex doubled spinor. -/
def d9PrimitiveSpinCPhaseActionCLM (phase : Circle) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.lsmul Real Complex (phase : Complex)).comp
      d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv.toContinuousLinearMap)

theorem d9PrimitiveSpinCPhaseActionCLM_eq_complexAction
    (phase : Circle) :
    d9PrimitiveSpinCPhaseActionCLM phase =
      d9PrimitiveSpinCComplexActionCLM (phase : Complex) :=
  rfl

@[simp]
theorem d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction
    (phase : Circle) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9PrimitiveSpinCPhaseActionCLM phase matter) =
      (phase : Complex) •
        d9DoubledMatterFiberHalfSpinorLinearEquiv matter := by
  simp [d9PrimitiveSpinCPhaseActionCLM,
    d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv]

@[simp]
theorem d9PrimitiveSpinCPhaseAction_one
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCPhaseActionCLM 1 matter = matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction]
  exact one_smul Complex
    (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)

theorem d9PrimitiveSpinCPhaseAction_mul
    (first second : Circle) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCPhaseActionCLM (first * second) matter =
      d9PrimitiveSpinCPhaseActionCLM first
        (d9PrimitiveSpinCPhaseActionCLM second matter) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction]
  exact mul_smul (first : Complex) (second : Complex)
    (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)

theorem d9PrimitiveSpinCComplexAction_mul
    (first second : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM (first * second) matter =
      d9PrimitiveSpinCComplexActionCLM first
        (d9PrimitiveSpinCComplexActionCLM second matter) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  exact mul_smul first second
    (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)

@[simp]
theorem d9PrimitiveSpinCComplexAction_one
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM 1 matter = matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  exact one_smul Complex
    (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)

theorem d9PrimitiveSpinCPhaseActionCLM_continuous :
    Continuous
      (d9PrimitiveSpinCPhaseActionCLM :
        Circle →
          D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) := by
  have hScalar :
      Continuous
        (fun phase : Circle =>
          (ContinuousLinearMap.lsmul Real Complex (phase : Complex) :
            D9DoubledMatterSpinor →L[Real] D9DoubledMatterSpinor)) :=
    (ContinuousLinearMap.lsmul Real Complex).continuous.comp
      continuous_subtype_val
  exact
    (hScalar.clm_comp_const
      d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv.toContinuousLinearMap)
      |>.const_clm_comp
        d9DoubledMatterFiberHalfSpinorContinuousLinearEquiv.symm.toContinuousLinearMap

theorem d9MatterSpinorMonodromy_complex_smul
    (choice : NormalRootChoice) (winding : Int) (scalar : Complex)
    (matter : MatterFiber) :
    d9MatterSpinorMonodromy choice winding
        (matterFiberHalfSpinorLinearEquiv.symm
          (scalar • matterFiberHalfSpinorLinearEquiv matter)) =
      matterFiberHalfSpinorLinearEquiv.symm
        (scalar • matterFiberHalfSpinorLinearEquiv
          (d9MatterSpinorMonodromy choice winding matter)) := by
  apply matterFiberHalfSpinorLinearEquiv.injective
  funext index
  fin_cases index <;>
    simp [d9MatterSpinorMonodromy, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

theorem d9PrimitiveSpinCPhaseAction_monodromy
    (choice : NormalRootChoice) (winding : Int) (phase : Circle)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCPhaseActionCLM phase
        (d9DoubledMatterSpinorMonodromy choice winding matter) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9PrimitiveSpinCPhaseActionCLM phase matter) := by
  apply Prod.ext
  · exact
      (d9MatterSpinorMonodromy_complex_smul choice winding
        (phase : Complex) matter.1).symm
  · exact
      (d9MatterSpinorMonodromy_complex_smul
        (oppositeRoot choice) winding
        (phase : Complex) matter.2).symm

theorem d9PrimitiveSpinCComplexAction_monodromy
    (choice : NormalRootChoice) (winding : Int) (scalar : Complex)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM scalar
        (d9DoubledMatterSpinorMonodromy choice winding matter) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9PrimitiveSpinCComplexActionCLM scalar matter) := by
  apply Prod.ext
  · exact
      (d9MatterSpinorMonodromy_complex_smul choice winding
        scalar matter.1).symm
  · exact
      (d9MatterSpinorMonodromy_complex_smul
        (oppositeRoot choice) winding scalar matter.2).symm

theorem d9PrimitiveSpinCPhaseAction_clifford
    (phase : Circle) (direction : Fin 3)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCPhaseActionCLM phase
        (d9DoubledMatterFiberCliffordGamma direction matter) =
      d9DoubledMatterFiberCliffordGamma direction
        (d9PrimitiveSpinCPhaseActionCLM phase matter) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]
  exact
    (d9DoubledMatterSpinorCliffordGamma direction).map_smul
      (phase : Complex)
      (d9DoubledMatterFiberHalfSpinorLinearEquiv matter) |>.symm

/-- Joint chart index for the normal-root and primitive monopole cocycles. -/
abbrev D9PrimitiveSpinCIndex :=
  ThroatCover period hPeriod × MonopoleChart

/-- Common chart domain of the two constituent bundles. -/
def d9PrimitiveSpinCBaseSet
    (index : D9PrimitiveSpinCIndex period hPeriod) :
    Set (ThroatBase period hPeriod) :=
  normalBundleBaseSet period hPeriod index.1 ∩
    d9PrimitiveMonopoleChartDomain period hPeriod index.2

theorem d9PrimitiveSpinCBaseSet_isOpen
    (index : D9PrimitiveSpinCIndex period hPeriod) :
    IsOpen (d9PrimitiveSpinCBaseSet period hPeriod index) :=
  (normalBundleBaseSet_isOpen period hPeriod index.1).inter
    (d9PrimitiveMonopoleChartDomain_isOpen period hPeriod index.2)

/-- Primitive monopole phase on a pair of D9 charts. -/
def d9PrimitiveSpinCPhaseTransition
    (first second : MonopoleChart)
    (base : ThroatBase period hPeriod) : Circle :=
  primitiveMonopoleTransition 1 first second
    (d9ThroatMonopoleSphereProjection period hPeriod base)

private theorem d9PrimitiveSpinCPhaseTransition_continuousOn
    (first second : MonopoleChart) :
    ContinuousOn
      (d9PrimitiveSpinCPhaseTransition period hPeriod first second)
      (d9PrimitiveMonopoleChartDomain period hPeriod first ∩
        d9PrimitiveMonopoleChartDomain period hPeriod second) := by
  cases first <;> cases second
  · exact (continuousOn_const :
      ContinuousOn (fun _ : ThroatBase period hPeriod => (1 : Circle)) _)
        |>.congr (by
          intro base _
          simp [d9PrimitiveSpinCPhaseTransition,
            primitiveMonopoleTransition])
  · have hPhase :
        ContinuousOn
          (fun base : ThroatBase period hPeriod =>
            monopoleSphereXYPhase
              (d9ThroatMonopoleSphereProjection period hPeriod base))
          (d9PrimitiveMonopoleChartDomain period hPeriod .north ∩
            d9PrimitiveMonopoleChartDomain period hPeriod .south) :=
      monopoleSphereXYPhase_continuousOn_overlap.comp'
        (d9ThroatMonopoleSphereProjection_continuous
          period hPeriod).continuousOn (by
            intro base hBase
            exact ⟨hBase.1, hBase.2⟩)
    exact hPhase.congr (by
      intro base _
      simp [d9PrimitiveSpinCPhaseTransition,
        primitiveMonopoleTransition])
  · have hPhase :
      ContinuousOn
        (fun base : ThroatBase period hPeriod =>
          (monopoleSphereXYPhase
            (d9ThroatMonopoleSphereProjection
              period hPeriod base))⁻¹)
        (d9PrimitiveMonopoleChartDomain period hPeriod .south ∩
          d9PrimitiveMonopoleChartDomain period hPeriod .north) := by
      have hOverlap :
          ContinuousOn monopoleSphereXYPhase
            (monopoleChartDomain .south ∩
              monopoleChartDomain .north) := by
        simpa [inter_comm] using
          monopoleSphereXYPhase_continuousOn_overlap
      exact hOverlap.inv.comp'
        (d9ThroatMonopoleSphereProjection_continuous
          period hPeriod).continuousOn (by
            intro base hBase
            exact ⟨hBase.1, hBase.2⟩)
    exact hPhase.congr (by
      intro base _
      simp [d9PrimitiveSpinCPhaseTransition,
        primitiveMonopoleTransition])
  · exact (continuousOn_const :
      ContinuousOn (fun _ : ThroatBase period hPeriod => (1 : Circle)) _)
        |>.congr (by
          intro base _
          simp [d9PrimitiveSpinCPhaseTransition,
            primitiveMonopoleTransition])

private theorem
    d9PrimitiveSpinCPhaseActionTransition_continuousOn
    (first second : MonopoleChart) :
    ContinuousOn
      (fun base : ThroatBase period hPeriod =>
        d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod first second base))
      (d9PrimitiveMonopoleChartDomain period hPeriod first ∩
        d9PrimitiveMonopoleChartDomain period hPeriod second) :=
  d9PrimitiveSpinCPhaseActionCLM_continuous.comp_continuousOn'
    (d9PrimitiveSpinCPhaseTransition_continuousOn
      period hPeriod first second)

/-- Combined SpinC transition: primitive phase followed by the existing
normal-root monodromy. -/
def d9PrimitiveSpinCCoordChange
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  (d9PrimitiveSpinCPhaseActionCLM
    (d9PrimitiveSpinCPhaseTransition
      period hPeriod first.2 second.2 base)).comp
    (d9DoubledMatterSpinorMonodromyCLM choice
      (localTransitionWinding period hPeriod first.1 second.1 base))

private theorem d9PrimitiveSpinCCoordChange_continuousOn
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod) :
    ContinuousOn
      (d9PrimitiveSpinCCoordChange
        period hPeriod choice first second)
      (d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second) := by
  change ContinuousOn
    (fun base : ThroatBase period hPeriod =>
      (d9PrimitiveSpinCPhaseActionCLM
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod first.2 second.2 base)).comp
        (d9DoubledMatterSpinorMonodromyCLM choice
          (localTransitionWinding period hPeriod
            first.1 second.1 base))) _
  have hPhase :=
    d9PrimitiveSpinCPhaseActionTransition_continuousOn
      period hPeriod first.2 second.2
  have hPhase' :
      ContinuousOn
        (fun base : ThroatBase period hPeriod =>
          d9PrimitiveSpinCPhaseActionCLM
            (d9PrimitiveSpinCPhaseTransition
              period hPeriod first.2 second.2 base))
        (d9PrimitiveSpinCBaseSet period hPeriod first ∩
          d9PrimitiveSpinCBaseSet period hPeriod second) :=
    hPhase.mono (by
      intro base hBase
      exact ⟨hBase.1.2, hBase.2.2⟩)
  have hDeck :=
    (smoothThroatDoubledMatterSpinorVectorBundleCore
      period hPeriod choice).continuousOn_coordChange first.1 second.1
  have hDeck' :
      ContinuousOn
        (fun base : ThroatBase period hPeriod =>
          d9DoubledMatterSpinorMonodromyCLM choice
            (localTransitionWinding period hPeriod
              first.1 second.1 base))
        (d9PrimitiveSpinCBaseSet period hPeriod first ∩
          d9PrimitiveSpinCBaseSet period hPeriod second) :=
    hDeck.mono (by
      intro base hBase
      exact ⟨hBase.1.1, hBase.2.1⟩)
  exact hPhase'.clm_comp hDeck'

/-- Genuine primitive SpinC doubled matter vector bundle on the actual D9
throat. -/
def d9PrimitiveSpinCVectorBundleCore
    (choice : NormalRootChoice) :
    VectorBundleCore Real (ThroatBase period hPeriod)
      D9DoubledMatterFiber (D9PrimitiveSpinCIndex period hPeriod) where
  baseSet := d9PrimitiveSpinCBaseSet period hPeriod
  isOpen_baseSet := d9PrimitiveSpinCBaseSet_isOpen period hPeriod
  indexAt base :=
    (normalBundleIndexAt period hPeriod base,
      (d9PrimitiveMonopolePrincipalBundleCore
        period hPeriod 1).indexAt base)
  mem_baseSet_at base :=
    ⟨mem_normalBundleBaseSet_indexAt period hPeriod base,
      (d9PrimitiveMonopolePrincipalBundleCore
        period hPeriod 1).mem_baseSet_at base⟩
  coordChange :=
    d9PrimitiveSpinCCoordChange period hPeriod choice
  coordChange_self index base hBase matter := by
    change
      d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod index.2 index.2 base)
          (d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding
              period hPeriod index.1 index.1 base) matter) =
        matter
    rw [localTransitionWinding_self period hPeriod index.1 base hBase.1]
    simp [d9PrimitiveSpinCPhaseTransition]
  continuousOn_coordChange :=
    d9PrimitiveSpinCCoordChange_continuousOn
      period hPeriod choice
  coordChange_comp first second third base hBase matter := by
    change
      d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod second.2 third.2 base)
          (d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding period hPeriod
              second.1 third.1 base)
            (d9PrimitiveSpinCPhaseActionCLM
              (d9PrimitiveSpinCPhaseTransition
                period hPeriod first.2 second.2 base)
              (d9DoubledMatterSpinorMonodromy choice
                (localTransitionWinding period hPeriod
                  first.1 second.1 base) matter))) =
        d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod first.2 third.2 base)
          (d9DoubledMatterSpinorMonodromy choice
            (localTransitionWinding period hPeriod
              first.1 third.1 base) matter)
    rw [← d9PrimitiveSpinCPhaseAction_monodromy]
    rw [← d9PrimitiveSpinCPhaseAction_mul]
    rw [show
      d9PrimitiveSpinCPhaseTransition
          period hPeriod second.2 third.2 base *
        d9PrimitiveSpinCPhaseTransition
          period hPeriod first.2 second.2 base =
      d9PrimitiveSpinCPhaseTransition
          period hPeriod first.2 third.2 base by
        exact primitiveMonopoleTransition_cocycle
          1 first.2 second.2 third.2
            (d9ThroatMonopoleSphereProjection period hPeriod base)]
    rw [← d9DoubledMatterSpinorMonodromy_add]
    rw [localTransitionWinding_add period hPeriod
      first.1 second.1 third.1 base
      ⟨⟨hBase.1.1.1, hBase.1.2.1⟩, hBase.2.1⟩]

theorem d9PrimitiveSpinCCoordChange_clifford
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) (direction : Fin 3)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGamma direction
        (d9PrimitiveSpinCCoordChange
          period hPeriod choice first second base matter) =
      d9PrimitiveSpinCCoordChange
        period hPeriod choice first second base
        (d9DoubledMatterFiberCliffordGamma direction matter) := by
  change
    d9DoubledMatterFiberCliffordGamma direction
      (d9PrimitiveSpinCPhaseActionCLM
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod first.2 second.2 base)
        (d9DoubledMatterSpinorMonodromy choice
          (localTransitionWinding period hPeriod
            first.1 second.1 base) matter)) =
    d9PrimitiveSpinCPhaseActionCLM
      (d9PrimitiveSpinCPhaseTransition
        period hPeriod first.2 second.2 base)
      (d9DoubledMatterSpinorMonodromy choice
        (localTransitionWinding period hPeriod
          first.1 second.1 base)
        (d9DoubledMatterFiberCliffordGamma direction matter))
  rw [← d9PrimitiveSpinCPhaseAction_clifford]
  rw [d9DoubledMatterFiberCliffordGamma_monodromy]

/-- Construction certificate for the primitive D9 SpinC bundle. -/
structure ProgramPD9PrimitiveSpinCBundleCertificate4D where
  choice : NormalRootChoice
  charge : Int
  charge_eq : charge = 1
  core :
    VectorBundleCore Real (ThroatBase period hPeriod)
      D9DoubledMatterFiber (D9PrimitiveSpinCIndex period hPeriod)
  coreCanonical :
    core = d9PrimitiveSpinCVectorBundleCore period hPeriod choice
  cliffordCompatible :
    ∀ first second base direction matter,
      d9DoubledMatterFiberCliffordGamma direction
          (core.coordChange first second base matter) =
        core.coordChange first second base
          (d9DoubledMatterFiberCliffordGamma direction matter)

def programPD9PrimitiveSpinCBundleCertificate4D :
    ProgramPD9PrimitiveSpinCBundleCertificate4D period hPeriod where
  choice := .positiveQuarter
  charge := 1
  charge_eq := rfl
  core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter
  coreCanonical := rfl
  cliffordCompatible :=
    d9PrimitiveSpinCCoordChange_clifford
      period hPeriod .positiveQuarter

theorem programPD9PrimitiveSpinCBundleCertificate4D_nonempty :
    Nonempty (ProgramPD9PrimitiveSpinCBundleCertificate4D
      period hPeriod) :=
  ⟨programPD9PrimitiveSpinCBundleCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
end JanusFormal
