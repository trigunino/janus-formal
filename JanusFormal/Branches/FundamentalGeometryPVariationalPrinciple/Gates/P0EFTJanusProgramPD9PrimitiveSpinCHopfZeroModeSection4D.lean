import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

/-!
# Complete Hopf zero-mode section of the primitive D9 SpinC bundle

The scalar section used by the first geometric synthesis is only one Hopf
coordinate.  A radial Clifford eigenspinor needs both charge-one coordinates.
This gate constructs the missing complementary component and packages their
sum as a genuine smooth primitive SpinC section in both normal-root sectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- First constant frame vector of the positive radial Clifford eigenline. -/
def d9PrimitiveSpinCHopfFirstFrameCLM
    (_sector : NormalRootChoice) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  ContinuousLinearMap.id Real D9DoubledMatterFiber -
    d9PrimitiveSpinCImaginaryAction.comp
      (d9DoubledMatterFiberCliffordGammaCLM 2)

/-- Second constant frame vector of the positive radial Clifford eigenline. -/
def d9PrimitiveSpinCHopfSecondFrameCLM
    (_sector : NormalRootChoice) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  ContinuousLinearMap.id Real D9DoubledMatterFiber +
    d9PrimitiveSpinCImaginaryAction.comp
      (d9DoubledMatterFiberCliffordGammaCLM 2)

@[simp]
theorem d9PrimitiveSpinCHopfFirstFrameCLM_apply
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCHopfFirstFrameCLM sector matter =
      matter -
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter) := by
  rfl

@[simp]
theorem d9PrimitiveSpinCHopfSecondFrameCLM_apply
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCHopfSecondFrameCLM sector matter =
      matter +
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter) := by
  rfl

theorem d9PrimitiveSpinCHopfFirstFrameCLM_monodromy
    (sector : NormalRootChoice) (winding : Int)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCHopfFirstFrameCLM sector
        (d9DoubledMatterSpinorMonodromy .positiveQuarter winding matter) =
      d9DoubledMatterSpinorMonodromy .positiveQuarter winding
        (d9PrimitiveSpinCHopfFirstFrameCLM sector matter) := by
  have hGamma :
      d9DoubledMatterFiberCliffordGammaCLM 2
          (d9DoubledMatterSpinorMonodromy
            .positiveQuarter winding matter) =
        d9DoubledMatterSpinorMonodromy .positiveQuarter winding
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter) := by
    simpa only [d9DoubledMatterFiberCliffordGammaCLM_apply] using
      d9DoubledMatterFiberCliffordGamma_monodromy
        .positiveQuarter 2 winding matter
  have hImaginary (current : D9DoubledMatterFiber) :
      d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterSpinorMonodromy
            .positiveQuarter winding current) =
        d9DoubledMatterSpinorMonodromy .positiveQuarter winding
          (d9PrimitiveSpinCImaginaryAction current) := by
    exact d9PrimitiveSpinCPhaseAction_monodromy
      .positiveQuarter winding d9PrimitiveSpinCImaginaryPhase current
  simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply]
  rw [hGamma, hImaginary]
  exact
    (d9DoubledMatterSpinorMonodromyCLM
      .positiveQuarter winding).map_sub matter
        (d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) |>.symm

theorem d9PrimitiveSpinCHopfSecondFrameCLM_monodromy
    (sector : NormalRootChoice) (winding : Int)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCHopfSecondFrameCLM sector
        (d9DoubledMatterSpinorMonodromy .positiveQuarter winding matter) =
      d9DoubledMatterSpinorMonodromy .positiveQuarter winding
        (d9PrimitiveSpinCHopfSecondFrameCLM sector matter) := by
  have hGamma :
      d9DoubledMatterFiberCliffordGammaCLM 2
          (d9DoubledMatterSpinorMonodromy
            .positiveQuarter winding matter) =
        d9DoubledMatterSpinorMonodromy .positiveQuarter winding
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter) := by
    simpa only [d9DoubledMatterFiberCliffordGammaCLM_apply] using
      d9DoubledMatterFiberCliffordGamma_monodromy
        .positiveQuarter 2 winding matter
  have hImaginary (current : D9DoubledMatterFiber) :
      d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterSpinorMonodromy
            .positiveQuarter winding current) =
        d9DoubledMatterSpinorMonodromy .positiveQuarter winding
          (d9PrimitiveSpinCImaginaryAction current) := by
    exact d9PrimitiveSpinCPhaseAction_monodromy
      .positiveQuarter winding d9PrimitiveSpinCImaginaryPhase current
  simp only [d9PrimitiveSpinCHopfSecondFrameCLM_apply]
  rw [hGamma, hImaginary]
  exact
    (d9DoubledMatterSpinorMonodromyCLM
      .positiveQuarter winding).map_add matter
        (d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) |>.symm

/-- Apply an equivariant continuous-linear fiber map to a smooth doubled
spinor lift. -/
def d9PrimitiveSpinCMapDoubledLift
    (map : D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber)
    (hMap :
      ∀ winding matter,
        map (d9DoubledMatterSpinorMonodromy
            .positiveQuarter winding matter) =
          d9DoubledMatterSpinorMonodromy .positiveQuarter winding
            (map matter))
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod .positiveQuarter) :
    SmoothThroatDoubledMatterSpinorLift
      period hPeriod .positiveQuarter where
  first :=
    { toFun := fun point => (map (lift point)).1
      contMDiff_toFun := by
        have hMapped :=
          map.contDiff.contMDiff.comp lift.contMDiff_toFun
        rw [contMDiff_prod_module_iff] at hMapped
        exact hMapped.1
      deck_equivariant := by
        intro winding point
        rw [throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
        have h := congrArg Prod.fst (hMap winding (lift point))
        rw [lift.deck_monodromy]
        exact h }
  second :=
    { toFun := fun point => (map (lift point)).2
      contMDiff_toFun := by
        have hMapped :=
          map.contDiff.contMDiff.comp lift.contMDiff_toFun
        rw [contMDiff_prod_module_iff] at hMapped
        exact hMapped.2
      deck_equivariant := by
        intro winding point
        rw [throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
        have h := congrArg Prod.snd (hMap winding (lift point))
        rw [lift.deck_monodromy]
        exact h }

@[simp]
theorem d9PrimitiveSpinCMapDoubledLift_apply
    (map : D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber)
    (hMap :
      ∀ winding matter,
        map (d9DoubledMatterSpinorMonodromy
            .positiveQuarter winding matter) =
          d9DoubledMatterSpinorMonodromy .positiveQuarter winding
            (map matter))
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod .positiveQuarter)
    (point : ThroatCover period hPeriod) :
    d9PrimitiveSpinCMapDoubledLift
        period hPeriod map hMap lift point =
      map (lift point) :=
  Prod.eta _

/-- Add two compatible smooth local gauge families. -/
def d9PrimitiveSpinCAddLocalGaugeFamily
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter) :
    SmoothPrimitiveSpinCLocalGaugeFamily
      period hPeriod .positiveQuarter where
  localValue index base :=
    first.localValue index base + second.localValue index base
  contMDiffOn_localValue index :=
    (first.contMDiffOn_localValue index).add
      (second.contMDiffOn_localValue index)
  coordChange_localValue firstIndex secondIndex base hBase := by
    rw [map_add,
      first.coordChange_localValue firstIndex secondIndex base hBase,
      second.coordChange_localValue firstIndex secondIndex base hBase]

/-- Complete smooth Hopf zero-mode gauges. -/
def primitiveSpinCHopfZeroModeLocalGaugeFamily
    (sector : NormalRootChoice) (mode : Int) :
    SmoothPrimitiveSpinCLocalGaugeFamily
      period hPeriod .positiveQuarter :=
  let normal :=
    primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
  let firstFrame :=
    d9PrimitiveSpinCMapDoubledLift period hPeriod
      (d9PrimitiveSpinCHopfFirstFrameCLM sector)
      (d9PrimitiveSpinCHopfFirstFrameCLM_monodromy sector)
      normal
  let secondFrame :=
    d9PrimitiveSpinCMapDoubledLift period hPeriod
      (d9PrimitiveSpinCHopfSecondFrameCLM sector)
      (d9PrimitiveSpinCHopfSecondFrameCLM_monodromy sector)
      normal
  d9PrimitiveSpinCAddLocalGaugeFamily period hPeriod
    (primitiveSpinCTensorLocalGaugeFamily
      period hPeriod .positiveQuarter
      firstFrame primitiveMonopoleZeroLocalScalarFamily)
    (primitiveSpinCTensorLocalGaugeFamily
      period hPeriod .positiveQuarter
      secondFrame primitiveMonopoleZeroComplementLocalScalarFamily)

/-- Genuine global smooth Hopf zero mode. -/
def primitiveSpinCHopfZeroModeSection
    (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (primitiveSpinCHopfZeroModeLocalGaugeFamily
    period hPeriod sector mode).toSmoothSection
      period hPeriod .positiveQuarter

theorem primitiveSpinCNormalModeDoubledLift_gamma_zero
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    d9DoubledMatterFiberCliffordGammaCLM 0
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]
  unfold d9PrimitiveSpinCImaginaryAction
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction]
  cases sector <;>
    apply Prod.ext <;>
    funext index <;>
    fin_cases index <;>
    simp [primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      d9DoubledMatterSpinorCliffordGamma,
      ambientHalfGammaPositiveEigenvector,
      Complex.I_mul_I]

theorem primitiveSpinCNormalModeDoubledLift_gamma_one
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point) =
      d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]
  unfold d9PrimitiveSpinCImaginaryAction
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]
  cases sector <;>
    apply Prod.ext <;>
    funext index <;>
    fin_cases index <;>
    simp [primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      d9DoubledMatterSpinorCliffordGamma,
      ambientHalfGammaPositiveEigenvector,
      Complex.I_mul_I]

end
end P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
end JanusFormal
