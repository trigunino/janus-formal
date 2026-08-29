import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D

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
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
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

@[simp]
theorem primitiveSpinCHopfZeroModeLocalGaugeFamily_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart) :
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (point, chart) (mappingTorusMk (ThroatData period hPeriod) point) =
      d9PrimitiveSpinCComplexActionCLM
          (primitiveMonopoleZeroLocalValue chart
            (d9MonopoleSphereCoverProjection period hPeriod point))
          (d9PrimitiveSpinCHopfFirstFrameCLM sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)) +
        d9PrimitiveSpinCComplexActionCLM
          (primitiveMonopoleZeroComplementLocalValue chart
            (d9MonopoleSphereCoverProjection period hPeriod point))
          (d9PrimitiveSpinCHopfSecondFrameCLM sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)) := by
  simp [primitiveSpinCHopfZeroModeLocalGaugeFamily,
    d9PrimitiveSpinCAddLocalGaugeFamily,
    primitiveSpinCTensorLocalGaugeFamily,
    primitiveMonopoleZeroLocalScalarFamily,
    primitiveMonopoleZeroComplementLocalScalarFamily,
    d9PrimitiveSpinCMapDoubledLift_apply,
    d9ThroatMonopoleSphereProjection_mk,
    doubledSpinorLiftLocalValue_mk]

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
  have zero_apply (choice : NormalRootChoice) :
      (0 : SmoothThroatMatterSpinorLift period hPeriod choice) point = 0 := rfl
  have imaginary_sq (scalar : Complex) :
      Complex.I * (Complex.I * scalar) = -scalar := by
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  cases sector <;>
    apply Prod.ext <;>
    funext index <;>
    fin_cases index <;>
    simp [primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector,
      zero_apply, imaginary_sq, mul_comm]

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
  have zero_apply (choice : NormalRootChoice) :
      (0 : SmoothThroatMatterSpinorLift period hPeriod choice) point = 0 := rfl
  have imaginary_sq (scalar : Complex) :
      Complex.I * (Complex.I * scalar) = -scalar := by
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  cases sector <;>
    apply Prod.ext <;>
    funext index <;>
    fin_cases index <;>
    simp [primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector,
      zero_apply, imaginary_sq, mul_comm]

theorem d9PrimitiveSpinCComplexAction_clifford
    (scalar : Complex) (direction : Fin 3)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM scalar
        (d9DoubledMatterFiberCliffordGammaCLM direction matter) =
      d9DoubledMatterFiberCliffordGammaCLM direction
        (d9PrimitiveSpinCComplexActionCLM scalar matter) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
    d9DoubledMatterFiberCliffordGammaCLM_apply]
  exact
    ((d9DoubledMatterSpinorCliffordGamma direction).map_smul
      scalar (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)).symm

theorem d9PrimitiveSpinCImaginaryAction_clifford
    (direction : Fin 3) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM direction matter) =
      d9DoubledMatterFiberCliffordGammaCLM direction
        (d9PrimitiveSpinCImaginaryAction matter) := by
  simpa only [d9PrimitiveSpinCImaginaryAction,
    d9DoubledMatterFiberCliffordGammaCLM_apply] using
    d9PrimitiveSpinCPhaseAction_clifford
      d9PrimitiveSpinCImaginaryPhase direction matter

@[simp]
theorem d9PrimitiveSpinCImaginaryAction_sq
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCImaginaryAction
      (d9PrimitiveSpinCImaginaryAction matter) = -matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9PrimitiveSpinCImaginaryAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9PrimitiveSpinCImaginaryPhase_coe, map_neg, smul_smul,
    Complex.I_mul_I, neg_one_smul]

theorem d9DoubledMatterFiberCliffordGammaCLM_sq
    (direction : Fin 3) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGammaCLM direction
        (d9DoubledMatterFiberCliffordGammaCLM direction matter) =
      -matter := by
  simpa only [d9DoubledMatterFiberCliffordGammaCLM_apply] using
    d9DoubledMatterFiberCliffordGamma_sq direction matter

theorem d9DoubledMatterFiberCliffordGammaCLM_anticommute
    (first second : Fin 3) (hDistinct : first ≠ second)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGammaCLM first
        (d9DoubledMatterFiberCliffordGammaCLM second matter) =
      -d9DoubledMatterFiberCliffordGammaCLM second
        (d9DoubledMatterFiberCliffordGammaCLM first matter) := by
  simpa only [d9DoubledMatterFiberCliffordGammaCLM_apply] using
    d9DoubledMatterFiberCliffordGamma_anticommute
      first second hDistinct matter

/-- On the positive radial Clifford eigenline, the radial Levi--Civita
correction has a directionwise closed form. -/
theorem d9LeviCivitaSpinCorrection_of_unitRadial_eigen
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (matter : D9DoubledMatterFiber)
    (hRadial :
      d9UnitRadialClifford period hPeriod point matter =
        d9PrimitiveSpinCImaginaryAction matter) :
    d9LeviCivitaSpinCorrection period hPeriod direction point matter =
      (1 / 2 : Real) •
        (d9PrimitiveSpinCImaginaryAction
            (d9DoubledMatterFiberCliffordGammaCLM direction matter) +
          d9UnitRadialCoordinate period hPeriod direction point • matter) := by
  have hApplied := congrArg
    (d9DoubledMatterFiberCliffordGammaCLM direction) hRadial
  rw [← d9PrimitiveSpinCImaginaryAction_clifford] at hApplied
  fin_cases direction <;>
    simp [d9UnitRadialClifford, d9LeviCivitaSpinCorrection,
      Fin.sum_univ_succ] at hApplied ⊢ <;>
    rw [d9DoubledMatterFiberCliffordGamma_sq] at hApplied <;>
    linear_combination (norm := module) (1 / 2 : Real) • hApplied

theorem d9PrimitiveSpinCHopfFirstFrameCLM_gamma_two
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGammaCLM 2
        (d9PrimitiveSpinCHopfFirstFrameCLM sector matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfFirstFrameCLM sector matter) := by
  simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply, map_sub]
  rw [← d9PrimitiveSpinCImaginaryAction_clifford,
    d9DoubledMatterFiberCliffordGammaCLM_sq,
    d9PrimitiveSpinCImaginaryAction_sq]
  simpa using
    (add_comm
      (d9DoubledMatterFiberCliffordGammaCLM 2 matter)
      (d9PrimitiveSpinCImaginaryAction matter))

theorem d9PrimitiveSpinCHopfSecondFrameCLM_gamma_two
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGammaCLM 2
        (d9PrimitiveSpinCHopfSecondFrameCLM sector matter) =
      -d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfSecondFrameCLM sector matter) := by
  simp only [d9PrimitiveSpinCHopfSecondFrameCLM_apply, map_add]
  rw [← d9PrimitiveSpinCImaginaryAction_clifford,
    d9DoubledMatterFiberCliffordGammaCLM_sq,
    d9PrimitiveSpinCImaginaryAction_sq]
  simp

theorem d9PrimitiveSpinCHopfFirstFrameCLM_gamma_zero_of
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (hZero :
      d9DoubledMatterFiberCliffordGammaCLM 0 matter =
        d9PrimitiveSpinCImaginaryAction matter) :
    d9DoubledMatterFiberCliffordGammaCLM 0
        (d9PrimitiveSpinCHopfFirstFrameCLM sector matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfSecondFrameCLM sector matter) := by
  simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply, map_sub, map_add]
  rw [hZero,
    ← d9PrimitiveSpinCImaginaryAction_clifford 0,
    d9DoubledMatterFiberCliffordGammaCLM_anticommute 0 2 (by decide),
    hZero,
    ← d9PrimitiveSpinCImaginaryAction_clifford 2]
  simp [sub_eq_add_neg]

theorem d9PrimitiveSpinCHopfSecondFrameCLM_gamma_zero_of
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (hZero :
      d9DoubledMatterFiberCliffordGammaCLM 0 matter =
        d9PrimitiveSpinCImaginaryAction matter) :
    d9DoubledMatterFiberCliffordGammaCLM 0
        (d9PrimitiveSpinCHopfSecondFrameCLM sector matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfFirstFrameCLM sector matter) := by
  simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply, map_sub, map_add]
  rw [hZero,
    ← d9PrimitiveSpinCImaginaryAction_clifford 0,
    d9DoubledMatterFiberCliffordGammaCLM_anticommute 0 2 (by decide),
    hZero,
    ← d9PrimitiveSpinCImaginaryAction_clifford 2]
  simp [sub_eq_add_neg]

theorem d9PrimitiveSpinCHopfFirstFrameCLM_gamma_one_of
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (hOne :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (d9PrimitiveSpinCHopfFirstFrameCLM sector matter) =
      d9PrimitiveSpinCHopfSecondFrameCLM sector matter := by
  simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply, map_sub]
  rw [hOne,
    ← d9PrimitiveSpinCImaginaryAction_clifford 1,
    d9DoubledMatterFiberCliffordGammaCLM_anticommute 1 2 (by decide),
    hOne,
    ← d9PrimitiveSpinCImaginaryAction_clifford 2,
    d9DoubledMatterFiberCliffordGammaCLM_sq]
  simp [sub_eq_add_neg, add_comm]

theorem d9PrimitiveSpinCHopfSecondFrameCLM_gamma_one_of
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (hOne :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (d9PrimitiveSpinCHopfSecondFrameCLM sector matter) =
      -d9PrimitiveSpinCHopfFirstFrameCLM sector matter := by
  simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply, map_add, map_neg]
  rw [hOne,
    ← d9PrimitiveSpinCImaginaryAction_clifford 1,
    d9DoubledMatterFiberCliffordGammaCLM_anticommute 1 2 (by decide),
    hOne,
    ← d9PrimitiveSpinCImaginaryAction_clifford 2,
    d9DoubledMatterFiberCliffordGammaCLM_sq]
  simp [sub_eq_add_neg, add_comm]

theorem d9PrimitiveSpinCHopf_first_coefficient
    (x y z : Real) (firstScalar secondScalar : Complex)
    (hHopf :
      (Complex.ofReal x + Complex.I * Complex.ofReal y) * secondScalar =
        Complex.ofReal (1 - z) * firstScalar) :
    Complex.ofReal x * (Complex.I * secondScalar) -
          Complex.ofReal y * secondScalar +
        Complex.ofReal z * (Complex.I * firstScalar) =
      Complex.I * firstScalar := by
  calc
    _ =
        Complex.I *
            (((Complex.ofReal x + Complex.I * Complex.ofReal y) *
                secondScalar) -
              Complex.ofReal (1 - z) * firstScalar) +
          Complex.I * firstScalar := by
      push_cast
      ring_nf
      simp [sub_eq_add_neg, Complex.I_mul_I]
    _ = _ := by rw [hHopf]; simp

theorem d9PrimitiveSpinCHopf_second_coefficient
    (x y z : Real) (firstScalar secondScalar : Complex)
    (hHopf :
      (Complex.ofReal x - Complex.I * Complex.ofReal y) * firstScalar =
        Complex.ofReal (1 + z) * secondScalar) :
    Complex.ofReal x * (Complex.I * firstScalar) +
          Complex.ofReal y * firstScalar -
        Complex.ofReal z * (Complex.I * secondScalar) =
      Complex.I * secondScalar := by
  calc
    _ =
        Complex.I *
            (((Complex.ofReal x - Complex.I * Complex.ofReal y) *
                firstScalar) -
              Complex.ofReal (1 + z) * secondScalar) +
          Complex.I * secondScalar := by
      push_cast
      ring_nf
      simp [sub_eq_add_neg, Complex.I_mul_I]
    _ = _ := by rw [hHopf]; simp

theorem d9DoubledMatterSpinor_real_smul_eq_complex
    (scalar : Real) (spinor : D9DoubledMatterSpinor) :
    scalar • spinor = Complex.ofReal scalar • spinor := by
  apply Prod.ext <;> funext index <;>
    simp [Complex.real_smul]

/-- Complex linear combination of the two constant Hopf frame vectors. -/
def d9PrimitiveSpinCHopfFrameCombination
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (firstScalar secondScalar : Complex) : D9DoubledMatterFiber :=
  d9PrimitiveSpinCComplexActionCLM firstScalar
      (d9PrimitiveSpinCHopfFirstFrameCLM sector matter) +
    d9PrimitiveSpinCComplexActionCLM secondScalar
      (d9PrimitiveSpinCHopfSecondFrameCLM sector matter)

theorem d9PrimitiveSpinCHopfFrameCombination_radial_eigen_of
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (x y z : Real) (firstScalar secondScalar : Complex)
    (hZero :
      d9DoubledMatterFiberCliffordGammaCLM 0 matter =
        d9PrimitiveSpinCImaginaryAction matter)
    (hOne :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter))
    (hFirst :
      (Complex.ofReal x + Complex.I * Complex.ofReal y) * secondScalar =
        Complex.ofReal (1 - z) * firstScalar)
    (hSecond :
      (Complex.ofReal x - Complex.I * Complex.ofReal y) * firstScalar =
        Complex.ofReal (1 + z) * secondScalar) :
    x • d9DoubledMatterFiberCliffordGammaCLM 0
          (d9PrimitiveSpinCHopfFrameCombination
            sector matter firstScalar secondScalar) +
        y • d9DoubledMatterFiberCliffordGammaCLM 1
          (d9PrimitiveSpinCHopfFrameCombination
            sector matter firstScalar secondScalar) +
      z • d9DoubledMatterFiberCliffordGammaCLM 2
          (d9PrimitiveSpinCHopfFrameCombination
            sector matter firstScalar secondScalar) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfFrameCombination
          sector matter firstScalar secondScalar) := by
  have hZeroFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_zero_of
      sector matter hZero
  have hZeroSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_zero_of
      sector matter hZero
  have hOneFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_one_of
      sector matter hOne
  have hOneSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_one_of
      sector matter hOne
  have hTwoFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_two sector matter
  have hTwoSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_two sector matter
  unfold d9PrimitiveSpinCHopfFrameCombination
  simp only [map_add]
  rw [← d9PrimitiveSpinCComplexAction_clifford firstScalar 0,
    ← d9PrimitiveSpinCComplexAction_clifford secondScalar 0,
    hZeroFirst, hZeroSecond,
    ← d9PrimitiveSpinCComplexAction_clifford firstScalar 1,
    ← d9PrimitiveSpinCComplexAction_clifford secondScalar 1,
    hOneFirst, hOneSecond,
    ← d9PrimitiveSpinCComplexAction_clifford firstScalar 2,
    ← d9PrimitiveSpinCComplexAction_clifford secondScalar 2,
    hTwoFirst, hTwoSecond]
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [map_add, map_smul, map_neg,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9PrimitiveSpinCImaginaryAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9PrimitiveSpinCImaginaryPhase_coe]
  simp_rw [d9DoubledMatterSpinor_real_smul_eq_complex]
  let firstImage :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv
      (d9PrimitiveSpinCHopfFirstFrameCLM sector matter)
  let secondImage :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv
      (d9PrimitiveSpinCHopfSecondFrameCLM sector matter)
  change
    Complex.ofReal x •
          (firstScalar • (Complex.I • secondImage) +
            secondScalar • (Complex.I • firstImage)) +
        Complex.ofReal y •
          (firstScalar • secondImage + -(secondScalar • firstImage)) +
      Complex.ofReal z •
          (firstScalar • (Complex.I • firstImage) +
            -(secondScalar • (Complex.I • secondImage))) =
      Complex.I • firstScalar • firstImage +
        Complex.I • secondScalar • secondImage
  have hFirstCoefficient :=
    d9PrimitiveSpinCHopf_first_coefficient
      x y z firstScalar secondScalar hFirst
  have hSecondCoefficient :=
    d9PrimitiveSpinCHopf_second_coefficient
      x y z firstScalar secondScalar hSecond
  calc
    _ =
        (Complex.ofReal x * (Complex.I * secondScalar) -
              Complex.ofReal y * secondScalar +
            Complex.ofReal z * (Complex.I * firstScalar)) • firstImage +
          (Complex.ofReal x * (Complex.I * firstScalar) +
                Complex.ofReal y * firstScalar -
              Complex.ofReal z * (Complex.I * secondScalar)) •
            secondImage := by
      module
    _ =
        (Complex.I * firstScalar) • firstImage +
          (Complex.I * secondScalar) • secondImage := by
      rw [hFirstCoefficient, hSecondCoefficient]
    _ = _ := by module

@[simp]
theorem monopoleSphereCoordinate_d9MonopoleSphereCoverProjection
    (point : ThroatCover period hPeriod) (direction : Fin 3) :
    monopoleSphereCoordinate
        (d9MonopoleSphereCoverProjection period hPeriod point) direction =
      d9UnitRadialCoordinate period hPeriod direction point := rfl

theorem monopoleSphereXY_d9MonopoleSphereCoverProjection
    (point : ThroatCover period hPeriod) :
    monopoleSphereXY
        (d9MonopoleSphereCoverProjection period hPeriod point) =
      Complex.ofReal (d9UnitRadialCoordinate period hPeriod 0 point) +
        Complex.I *
          Complex.ofReal
            (d9UnitRadialCoordinate period hPeriod 1 point) := by
  apply Complex.ext <;>
    simp [monopoleSphereXY, d9UnitRadialCoordinate,
      d9MonopoleSphereCoverProjection, monopoleSphereCoordinate]

theorem star_monopoleSphereXY_d9MonopoleSphereCoverProjection
    (point : ThroatCover period hPeriod) :
    star
        (monopoleSphereXY
          (d9MonopoleSphereCoverProjection period hPeriod point)) =
      Complex.ofReal (d9UnitRadialCoordinate period hPeriod 0 point) -
        Complex.I *
          Complex.ofReal
            (d9UnitRadialCoordinate period hPeriod 1 point) := by
  apply Complex.ext <;>
    simp [monopoleSphereXY, d9UnitRadialCoordinate,
      d9MonopoleSphereCoverProjection, monopoleSphereCoordinate]

theorem primitiveSpinCHopfFrameCombination_unitRadial_eigen
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9UnitRadialClifford period hPeriod point
        (d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (primitiveMonopoleZeroLocalValue chart
            (d9MonopoleSphereCoverProjection period hPeriod point))
          (primitiveMonopoleZeroComplementLocalValue chart
            (d9MonopoleSphereCoverProjection period hPeriod point))) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (primitiveMonopoleZeroLocalValue chart
            (d9MonopoleSphereCoverProjection period hPeriod point))
          (primitiveMonopoleZeroComplementLocalValue chart
            (d9MonopoleSphereCoverProjection period hPeriod point))) := by
  cases chart with
  | north =>
      have hFirst :
          (Complex.ofReal
                (d9UnitRadialCoordinate period hPeriod 0 point) +
              Complex.I *
                Complex.ofReal
                  (d9UnitRadialCoordinate period hPeriod 1 point)) *
              primitiveMonopoleZeroComplementNorthValue
                (d9MonopoleSphereCoverProjection period hPeriod point) =
            Complex.ofReal
                (1 - d9UnitRadialCoordinate period hPeriod 2 point) *
              primitiveMonopoleZeroNorthValue
                (d9MonopoleSphereCoverProjection period hPeriod point) := by
        rw [← monopoleSphereXY_d9MonopoleSphereCoverProjection]
        simpa only [
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] using
          primitiveMonopoleHopfNorth_xy_mul_complement
            (d9MonopoleSphereCoverProjection period hPeriod point) hChart
      have hSecond :
          (Complex.ofReal
                (d9UnitRadialCoordinate period hPeriod 0 point) -
              Complex.I *
                Complex.ofReal
                  (d9UnitRadialCoordinate period hPeriod 1 point)) *
              primitiveMonopoleZeroNorthValue
                (d9MonopoleSphereCoverProjection period hPeriod point) =
            Complex.ofReal
                (1 + d9UnitRadialCoordinate period hPeriod 2 point) *
              primitiveMonopoleZeroComplementNorthValue
                (d9MonopoleSphereCoverProjection period hPeriod point) := by
        rw [← star_monopoleSphereXY_d9MonopoleSphereCoverProjection]
        simpa only [
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] using
          primitiveMonopoleHopfNorth_star_mul_first
            (d9MonopoleSphereCoverProjection period hPeriod point) hChart
      simpa [d9UnitRadialClifford, Fin.sum_univ_succ, add_assoc,
        primitiveMonopoleZeroLocalValue,
        primitiveMonopoleZeroComplementLocalValue] using
        d9PrimitiveSpinCHopfFrameCombination_radial_eigen_of
          sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9UnitRadialCoordinate period hPeriod 0 point)
          (d9UnitRadialCoordinate period hPeriod 1 point)
          (d9UnitRadialCoordinate period hPeriod 2 point)
          (primitiveMonopoleZeroNorthValue
            (d9MonopoleSphereCoverProjection period hPeriod point))
          (primitiveMonopoleZeroComplementNorthValue
            (d9MonopoleSphereCoverProjection period hPeriod point))
          (primitiveSpinCNormalModeDoubledLift_gamma_zero
            period hPeriod sector mode point)
          (primitiveSpinCNormalModeDoubledLift_gamma_one
            period hPeriod sector mode point)
          hFirst hSecond
  | south =>
      have hFirst :
          (Complex.ofReal
                (d9UnitRadialCoordinate period hPeriod 0 point) +
              Complex.I *
                Complex.ofReal
                  (d9UnitRadialCoordinate period hPeriod 1 point)) *
              primitiveMonopoleZeroComplementSouthValue
                (d9MonopoleSphereCoverProjection period hPeriod point) =
            Complex.ofReal
                (1 - d9UnitRadialCoordinate period hPeriod 2 point) *
              primitiveMonopoleZeroSouthValue
                (d9MonopoleSphereCoverProjection period hPeriod point) := by
        rw [← monopoleSphereXY_d9MonopoleSphereCoverProjection]
        simpa only [
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] using
          primitiveMonopoleHopfSouth_xy_mul_second
            (d9MonopoleSphereCoverProjection period hPeriod point) hChart
      have hSecond :
          (Complex.ofReal
                (d9UnitRadialCoordinate period hPeriod 0 point) -
              Complex.I *
                Complex.ofReal
                  (d9UnitRadialCoordinate period hPeriod 1 point)) *
              primitiveMonopoleZeroSouthValue
                (d9MonopoleSphereCoverProjection period hPeriod point) =
            Complex.ofReal
                (1 + d9UnitRadialCoordinate period hPeriod 2 point) *
              primitiveMonopoleZeroComplementSouthValue
                (d9MonopoleSphereCoverProjection period hPeriod point) := by
        rw [← star_monopoleSphereXY_d9MonopoleSphereCoverProjection]
        simpa only [
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] using
          primitiveMonopoleHopfSouth_star_mul_first
            (d9MonopoleSphereCoverProjection period hPeriod point) hChart
      simpa [d9UnitRadialClifford, Fin.sum_univ_succ, add_assoc,
        primitiveMonopoleZeroLocalValue,
        primitiveMonopoleZeroComplementLocalValue] using
        d9PrimitiveSpinCHopfFrameCombination_radial_eigen_of
          sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9UnitRadialCoordinate period hPeriod 0 point)
          (d9UnitRadialCoordinate period hPeriod 1 point)
          (d9UnitRadialCoordinate period hPeriod 2 point)
          (primitiveMonopoleZeroSouthValue
            (d9MonopoleSphereCoverProjection period hPeriod point))
          (primitiveMonopoleZeroComplementSouthValue
            (d9MonopoleSphereCoverProjection period hPeriod point))
          (primitiveSpinCNormalModeDoubledLift_gamma_zero
            period hPeriod sector mode point)
          (primitiveSpinCNormalModeDoubledLift_gamma_one
            period hPeriod sector mode point)
          hFirst hSecond

theorem primitiveSpinCHopfZeroModeLocalGaugeFamily_unitRadial_eigen
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9UnitRadialClifford period hPeriod point
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (point, chart)
            (mappingTorusMk (ThroatData period hPeriod) point)) =
      d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (point, chart)
            (mappingTorusMk (ThroatData period hPeriod) point)) := by
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk]
  simpa only [d9PrimitiveSpinCHopfFrameCombination] using
    primitiveSpinCHopfFrameCombination_unitRadial_eigen
      period hPeriod sector mode point chart hChart

end
end P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
end JanusFormal
