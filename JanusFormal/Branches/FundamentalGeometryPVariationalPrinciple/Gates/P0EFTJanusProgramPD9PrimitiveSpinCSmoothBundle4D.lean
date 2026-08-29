import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveMonopoleSmoothClutching4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCConnection4D

/-!
# Smooth primitive SpinC bundle on D9

The primitive phase action and the pulled-back clutching phase are smooth.
Together with the already smooth normal-root deck cocycle, this promotes the
primitive SpinC vector-bundle core from a topological bundle to a smooth one.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleSmoothClutching4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance circleChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 1)) Circle :=
  instChartedSpaceEuclideanSpaceRealFinOfNatNatCircle

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D.throatBaseChartedSpace
    period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D.throatBaseIsManifold
    period hPeriod

local instance doubledCoreIsContMDiff (choice : NormalRootChoice) :
    (smoothThroatDoubledMatterSpinorVectorBundleCore
      period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ∞ where
  contMDiffOn_coordChange first second := by
    letI :
        (smoothThroatDoubledMatterSpinorVectorBundleCore
          period hPeriod choice).IsContMDiff
            throatCoverModelWithCorners ω :=
      smoothThroatDoubledMatterSpinorVectorBundleCore_isContMDiff
        period hPeriod choice
    exact
      ((smoothThroatDoubledMatterSpinorVectorBundleCore
        period hPeriod choice).contMDiffOn_coordChange
          throatCoverModelWithCorners first second).of_le
            (show (∞ : ℕ∞ω) ≤ ω from le_top)

private theorem circleCoe_contMDiff :
    ContMDiff (M := Circle) (M' := Complex)
      (𝓡 1) 𝓘(Real, Complex) ∞
      ((↑) : Circle → Complex) := by
  letI : Fact (Module.finrank Real Complex = 1 + 1) :=
    finrank_real_complex_fact'
  exact contMDiff_coe_sphere

/-- Arbitrary complex scalar multiplication on the doubled matter fiber is
smooth as a real map. -/
theorem d9PrimitiveSpinCComplexActionCLM_contMDiff :
    ContMDiff 𝓘(Real, Complex)
      𝓘(Real,
        D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) ∞
      d9PrimitiveSpinCComplexActionCLM := by
  let spinorLsmul :
      Complex →L[Real]
        (D9DoubledMatterSpinor →L[Real] D9DoubledMatterSpinor) :=
    ContinuousLinearMap.lsmul Real Complex
  have hScalar :
      ContMDiff 𝓘(Real, Complex)
        𝓘(Real,
          D9DoubledMatterSpinor →L[Real]
            D9DoubledMatterSpinor) ∞
        (fun scalar : Complex =>
          (ContinuousLinearMap.lsmul Real Complex scalar :
            D9DoubledMatterSpinor →L[Real]
              D9DoubledMatterSpinor)) :=
    spinorLsmul.contDiff.contMDiff
  exact
    contMDiff_const.clm_comp
      (hScalar.clm_comp contMDiff_const)

/-- The scalar phase representation on the doubled matter fiber is smooth. -/
theorem d9PrimitiveSpinCPhaseActionCLM_contMDiff :
    ContMDiff (M := Circle)
      (M' := D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber)
      (𝓡 1)
      𝓘(Real,
        D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) ∞
      d9PrimitiveSpinCPhaseActionCLM := by
  let spinorLsmul :
      Complex →L[Real]
        (D9DoubledMatterSpinor →L[Real] D9DoubledMatterSpinor) :=
    ContinuousLinearMap.lsmul Real Complex
  have hCoe :
      ContMDiff (M := Circle) (M' := Complex)
        (𝓡 1) 𝓘(Real, Complex) ∞
        ((↑) : Circle → Complex) :=
    circleCoe_contMDiff
  have hScalar :
      ContMDiff (M := Circle)
        (M' := D9DoubledMatterSpinor →L[Real]
          D9DoubledMatterSpinor)
        (𝓡 1)
        𝓘(Real,
          D9DoubledMatterSpinor →L[Real] D9DoubledMatterSpinor) ∞
        (fun phase : Circle =>
          (ContinuousLinearMap.lsmul Real Complex (phase : Complex) :
            D9DoubledMatterSpinor →L[Real]
              D9DoubledMatterSpinor)) :=
    spinorLsmul.contDiff.contMDiff.comp hCoe
  exact
    contMDiff_const.clm_comp
      (hScalar.clm_comp contMDiff_const)

/-- The pulled-back primitive phase is smooth on each D9 chart overlap. -/
theorem d9PrimitiveSpinCPhaseTransition_contMDiffOn
    (first second : MonopoleChart) :
    ContMDiffOn throatCoverModelWithCorners (𝓡 1) ∞
      (d9PrimitiveSpinCPhaseTransition period hPeriod first second)
      (d9PrimitiveMonopoleChartDomain period hPeriod first ∩
        d9PrimitiveMonopoleChartDomain period hPeriod second) := by
  cases first <;> cases second
  · refine
      (contMDiff_const.contMDiffOn :
        ContMDiffOn throatCoverModelWithCorners (𝓡 1) ∞
          (fun _ : ThroatBase period hPeriod => (1 : Circle)) _).congr ?_
    intro base _
    simp [d9PrimitiveSpinCPhaseTransition,
      primitiveMonopoleTransition]
  · have hPhase :=
      monopoleSphereXYPhase_contMDiffOn_overlap.comp
        (((d9ThroatMonopoleSphereProjection_contMDiff
          period hPeriod).of_le
            (show (∞ : ℕ∞ω) ≤ ω from le_top)).contMDiffOn :
          ContMDiffOn throatCoverModelWithCorners (𝓡 2) ∞
            (d9ThroatMonopoleSphereProjection period hPeriod)
            (d9PrimitiveMonopoleChartDomain period hPeriod .north ∩
              d9PrimitiveMonopoleChartDomain period hPeriod .south))
        (by
          intro base hBase
          exact ⟨hBase.1, hBase.2⟩)
    exact hPhase.congr (by
      intro base _
      simp [d9PrimitiveSpinCPhaseTransition,
        primitiveMonopoleTransition])
  · have hPhase :
      ContMDiffOn (𝓡 2) (𝓡 1) ∞
        (fun point : MonopoleSphere =>
          (monopoleSphereXYPhase point)⁻¹)
        (monopoleChartDomain .south ∩
          monopoleChartDomain .north) := by
      have hOverlap :
          ContMDiffOn (𝓡 2) (𝓡 1) ∞ monopoleSphereXYPhase
            (monopoleChartDomain .south ∩
              monopoleChartDomain .north) := by
        simpa [inter_comm] using
          monopoleSphereXYPhase_contMDiffOn_overlap
      exact hOverlap.inv
    have hPullback :=
      hPhase.comp
        (((d9ThroatMonopoleSphereProjection_contMDiff
          period hPeriod).of_le
            (show (∞ : ℕ∞ω) ≤ ω from le_top)).contMDiffOn :
          ContMDiffOn throatCoverModelWithCorners (𝓡 2) ∞
            (d9ThroatMonopoleSphereProjection period hPeriod)
            (d9PrimitiveMonopoleChartDomain period hPeriod .south ∩
              d9PrimitiveMonopoleChartDomain period hPeriod .north))
        (by
          intro base hBase
          exact ⟨hBase.1, hBase.2⟩)
    exact hPullback.congr (by
      intro base _
      simp [d9PrimitiveSpinCPhaseTransition,
        primitiveMonopoleTransition])
  · refine
      (contMDiff_const.contMDiffOn :
        ContMDiffOn throatCoverModelWithCorners (𝓡 1) ∞
          (fun _ : ThroatBase period hPeriod => (1 : Circle)) _).congr ?_
    intro base _
    simp [d9PrimitiveSpinCPhaseTransition,
      primitiveMonopoleTransition]

private theorem
    d9PrimitiveSpinCPhaseActionTransition_contMDiffOn
    (first second : MonopoleChart) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real,
        D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) ∞
      (fun base : ThroatBase period hPeriod =>
        d9PrimitiveSpinCPhaseActionCLM
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod first second base))
      (d9PrimitiveMonopoleChartDomain period hPeriod first ∩
        d9PrimitiveMonopoleChartDomain period hPeriod second) :=
  d9PrimitiveSpinCPhaseActionCLM_contMDiff.comp_contMDiffOn
    (d9PrimitiveSpinCPhaseTransition_contMDiffOn
      period hPeriod first second)

/-- The combined primitive SpinC cocycle is smooth. -/
theorem d9PrimitiveSpinCVectorBundleCore_isContMDiff
    (choice : NormalRootChoice) :
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ∞ where
  contMDiffOn_coordChange first second := by
    have hPhase :=
      d9PrimitiveSpinCPhaseActionTransition_contMDiffOn
        period hPeriod first.2 second.2
    have hPhase' :
        ContMDiffOn throatCoverModelWithCorners
          𝓘(Real,
            D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) ∞
          (fun base : ThroatBase period hPeriod =>
            d9PrimitiveSpinCPhaseActionCLM
              (d9PrimitiveSpinCPhaseTransition
                period hPeriod first.2 second.2 base))
          (d9PrimitiveSpinCBaseSet period hPeriod first ∩
            d9PrimitiveSpinCBaseSet period hPeriod second) :=
      hPhase.mono (by
        intro base hBase
        exact ⟨hBase.1.2, hBase.2.2⟩)
    have hDeck :
        ContMDiffOn throatCoverModelWithCorners
          𝓘(Real,
            D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) ∞
          (fun base : ThroatBase period hPeriod =>
            d9DoubledMatterSpinorMonodromyCLM choice
              (localTransitionWinding period hPeriod
                first.1 second.1 base))
          (normalBundleBaseSet period hPeriod first.1 ∩
            normalBundleBaseSet period hPeriod second.1) :=
      (smoothThroatDoubledMatterSpinorVectorBundleCore
        period hPeriod choice).contMDiffOn_coordChange
          throatCoverModelWithCorners first.1 second.1
    have hDeck' :
        ContMDiffOn throatCoverModelWithCorners
          𝓘(Real,
            D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber) ∞
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

/-- Assumption-free smoothness certificate for the canonical primitive
SpinC bundle. -/
structure ProgramPD9PrimitiveSpinCSmoothBundleCertificate4D where
  choice : NormalRootChoice
  smooth :
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ∞

def programPD9PrimitiveSpinCSmoothBundleCertificate4D :
    ProgramPD9PrimitiveSpinCSmoothBundleCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  smooth :=
    d9PrimitiveSpinCVectorBundleCore_isContMDiff
      period hPeriod .positiveQuarter

end
end P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
end JanusFormal
