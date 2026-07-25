import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D

/-!
# Levi--Civita spin connection in the intrinsic radial frame

For the product throat metric written on `ℝ³ \ {0}` as
`g = ‖x‖⁻² g_Euclidean`, the orthonormal radial frame is
`eᵢ = ‖x‖ ∂ᵢ`.  Its Levi--Civita coefficients are

`ωᵢⱼₖ = δᵢⱼ nₖ - δᵢₖ nⱼ`,

where `n = x / ‖x‖`.  The associated spin correction is

`Ωᵢ = 1/2 ∑_{k ≠ i} nₖ γᵢγₖ`.

This file adds that genuine zero-order correction to the already constructed
flat-cover derivative.  Clifford contraction reduces it exactly to
`-γ(n)`, without changing the elliptic principal symbol.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D

set_option autoImplicit false
noncomputable section

open Set Bundle Module
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance euclideanR3Finrank :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

/-- Component of the unit radial vector `n` in the Euclidean frame. -/
def d9UnitRadialCoordinate
    (direction : Fin 3) (point : ThroatCover period hPeriod) : Real :=
  (equatorialTwoSphereHomeomorph point.fiber).1 direction

theorem d9UnitRadialCoordinate_contMDiff (direction : Fin 3) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real) ∞
      (d9UnitRadialCoordinate period hPeriod direction) := by
  have hToProduct :
      ContMDiff throatCoverModelWithCorners
        ((𝓡 2).prod 𝓘(Real)) ∞
        (coverHomeomorphProd (ThroatData period hPeriod)) :=
    chartedSpacePullback_toFun_contMDiff
      throatCoverModelWithCorners ∞
      (coverHomeomorphProd (ThroatData period hPeriod))
  have hFiber :
      ContMDiff throatCoverModelWithCorners (𝓡 2) ∞
        (fun point : ThroatCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hToProduct
  have hSphere :
      ContMDiff throatCoverModelWithCorners (𝓡 2) ∞
        (fun point : ThroatCover period hPeriod =>
          equatorialTwoSphereHomeomorph point.fiber) :=
    (chartedSpacePullback_toFun_contMDiff
      (𝓡 2) ∞ equatorialTwoSphereHomeomorph).comp hFiber
  have hAmbient :
      ContMDiff throatCoverModelWithCorners
        𝓘(Real, EuclideanSpace Real (Fin 3)) ∞
        (fun point : ThroatCover period hPeriod =>
          (equatorialTwoSphereHomeomorph point.fiber).1) :=
    contMDiff_coe_sphere.comp hSphere
  exact (EuclideanSpace.proj direction).contDiff.contMDiff.comp hAmbient

theorem d9UnitRadialCoordinate_deck
    (direction : Fin 3) (winding : Int)
    (point : ThroatCover period hPeriod) :
    d9UnitRadialCoordinate period hPeriod direction (winding +ᵥ point) =
      d9UnitRadialCoordinate period hPeriod direction point := by
  change
    (equatorialTwoSphereHomeomorph
      (((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber)).1
        direction =
      (equatorialTwoSphereHomeomorph point.fiber).1 direction
  rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber =
      ((Homeomorph.refl EquatorialTwoSphere) ^ winding).toEquiv
        point.fiber from rfl,
    homeomorph_toEquiv_zpow,
    show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl,
    one_zpow]
  rfl

theorem d9UnitRadialCoordinate_norm_sq
    (point : ThroatCover period hPeriod) :
    ∑ direction : Fin 3,
        d9UnitRadialCoordinate period hPeriod direction point ^ 2 = 1 := by
  have hNorm :
      ‖(equatorialTwoSphereHomeomorph point.fiber).1‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using
      (equatorialTwoSphereHomeomorph point.fiber).2
  have hSq := congrArg (fun value : Real => value ^ 2) hNorm
  rw [EuclideanSpace.real_norm_sq_eq] at hSq
  simpa [d9UnitRadialCoordinate] using hSq

/-- Kronecker coefficient in the intrinsic frame. -/
def d9KroneckerDelta (first second : Fin 3) : Real :=
  if first = second then 1 else 0

/-- Levi--Civita coefficients of `eᵢ = ‖x‖ ∂ᵢ`. -/
def d9RadialLeviCivitaCoefficient
    (first second third : Fin 3)
    (point : ThroatCover period hPeriod) : Real :=
  d9KroneckerDelta first second *
      d9UnitRadialCoordinate period hPeriod third point -
    d9KroneckerDelta first third *
      d9UnitRadialCoordinate period hPeriod second point

theorem d9RadialLeviCivitaCoefficient_skew
    (first second third : Fin 3)
    (point : ThroatCover period hPeriod) :
    d9RadialLeviCivitaCoefficient period hPeriod
        first second third point =
      -d9RadialLeviCivitaCoefficient period hPeriod
        first third second point := by
  unfold d9RadialLeviCivitaCoefficient
  ring

theorem d9RadialLeviCivitaCoefficient_contMDiff
    (first second third : Fin 3) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real) ∞
      (d9RadialLeviCivitaCoefficient period hPeriod
        first second third) := by
  exact
    (contMDiff_const.mul
      (d9UnitRadialCoordinate_contMDiff
        period hPeriod third)).sub
      (contMDiff_const.mul
        (d9UnitRadialCoordinate_contMDiff
          period hPeriod second))

/-- Spin lift of the radial Levi--Civita connection in its simplified
antisymmetric form. -/
def d9LeviCivitaSpinCorrection
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (matter : D9DoubledMatterFiber) : D9DoubledMatterFiber :=
  ∑ other : Fin 3,
    if other = direction then 0
    else
      ((1 : Real) / 2 *
        d9UnitRadialCoordinate period hPeriod other point) •
          d9DoubledMatterFiberCliffordGammaCLM direction
            (d9DoubledMatterFiberCliffordGammaCLM other matter)

/-- Clifford multiplication by the unit radial vector. -/
def d9UnitRadialClifford
    (point : ThroatCover period hPeriod)
    (matter : D9DoubledMatterFiber) : D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9UnitRadialCoordinate period hPeriod direction point •
      d9DoubledMatterFiberCliffordGammaCLM direction matter

/-- Clifford contraction of the Levi--Civita spin correction is exactly
`-γ(n)`. -/
theorem d9LeviCivitaSpinCorrection_contraction
    (point : ThroatCover period hPeriod)
    (matter : D9DoubledMatterFiber) :
    (∑ direction : Fin 3,
      d9DoubledMatterFiberCliffordGammaCLM direction
        (d9LeviCivitaSpinCorrection
          period hPeriod direction point matter)) =
      -d9UnitRadialClifford period hPeriod point matter := by
  simp [d9LeviCivitaSpinCorrection, d9UnitRadialClifford,
    Fin.sum_univ_succ, d9DoubledMatterFiberCliffordGammaCLM_apply,
    d9DoubledMatterFiberCliffordGamma_sq, smul_add, add_smul]
  module

theorem d9LeviCivitaSpinCorrection_contMDiff
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (fun point =>
        d9LeviCivitaSpinCorrection
          period hPeriod direction point (lift point)) := by
  apply ContMDiff.sum
  intro other _
  by_cases hSame : other = direction
  · simp only [hSame, ↓reduceIte]
    exact contMDiff_const
  · simp only [d9LeviCivitaSpinCorrection, hSame, ↓reduceIte]
    exact
      (contMDiff_const.mul
        (d9UnitRadialCoordinate_contMDiff
          period hPeriod other)).smul
        ((d9DoubledMatterFiberCliffordGammaCLM direction).contDiff.contMDiff.comp
          ((d9DoubledMatterFiberCliffordGammaCLM other).contDiff.contMDiff.comp
            lift.contMDiff_toFun))

theorem d9LeviCivitaSpinCorrection_deck
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) (winding : Int)
    (point : ThroatCover period hPeriod) :
    d9LeviCivitaSpinCorrection period hPeriod direction
        (winding +ᵥ point) (lift (winding +ᵥ point)) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9LeviCivitaSpinCorrection
          period hPeriod direction point (lift point)) := by
  unfold d9LeviCivitaSpinCorrection
  change
    (∑ other : Fin 3,
      if other = direction then 0
      else
        ((1 : Real) / 2 *
          d9UnitRadialCoordinate period hPeriod other (winding +ᵥ point)) •
            d9DoubledMatterFiberCliffordGammaCLM direction
              (d9DoubledMatterFiberCliffordGammaCLM other
                (lift (winding +ᵥ point)))) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (∑ other : Fin 3,
          if other = direction then 0
          else
            ((1 : Real) / 2 *
              d9UnitRadialCoordinate period hPeriod other point) •
                d9DoubledMatterFiberCliffordGammaCLM direction
                  (d9DoubledMatterFiberCliffordGammaCLM other
                    (lift point)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro other _
  by_cases hSame : other = direction
  · simp only [hSame, ↓reduceIte]
    exact
      (map_zero
        (d9DoubledMatterSpinorMonodromyCLM choice winding)).symm
  · simp only [hSame, ↓reduceIte]
    change
      ((1 : Real) / 2 *
        d9UnitRadialCoordinate period hPeriod other (winding +ᵥ point)) •
          d9DoubledMatterFiberCliffordGammaCLM direction
            (d9DoubledMatterFiberCliffordGammaCLM other
              (lift (winding +ᵥ point))) =
        d9DoubledMatterSpinorMonodromyCLM choice winding
          (((1 : Real) / 2 *
            d9UnitRadialCoordinate period hPeriod other point) •
              d9DoubledMatterFiberCliffordGammaCLM direction
                (d9DoubledMatterFiberCliffordGammaCLM other
                  (lift point)))
    rw [d9UnitRadialCoordinate_deck,
      lift.deck_monodromy]
    simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
    rw [d9DoubledMatterFiberCliffordGamma_monodromy
        choice other winding (lift point),
      d9DoubledMatterFiberCliffordGamma_monodromy
        choice direction winding
          (d9DoubledMatterFiberCliffordGamma other (lift point)),
      ← d9DoubledMatterSpinorMonodromy_real_smul]
    rfl

/-- Levi--Civita spin covariant derivative along one intrinsic frame
direction. -/
def d9LeviCivitaSpinFrameDerivative
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    D9DoubledMatterFiber :=
  d9IntrinsicDoubledMatterFlatFrameDerivative
      period hPeriod choice lift direction point +
    d9LeviCivitaSpinCorrection
      period hPeriod direction point (lift point)

/-- Dirac contraction of the Levi--Civita spin connection. -/
def d9LeviCivitaSpinCoverDirac
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGammaCLM direction
      (d9LeviCivitaSpinFrameDerivative
        period hPeriod choice lift direction point)

theorem d9LeviCivitaSpinCoverDirac_eq
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    d9LeviCivitaSpinCoverDirac period hPeriod choice lift point =
      d9IntrinsicDoubledMatterSpinorCoverDirac
          period hPeriod choice lift point -
        d9UnitRadialClifford period hPeriod point (lift point) := by
  unfold d9LeviCivitaSpinCoverDirac
    d9LeviCivitaSpinFrameDerivative
    d9IntrinsicDoubledMatterSpinorCoverDirac
  rw [show
      (∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9IntrinsicDoubledMatterFlatFrameDerivative
              period hPeriod choice lift direction point +
            d9LeviCivitaSpinCorrection
              period hPeriod direction point (lift point))) =
        (∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGammaCLM direction
            (d9IntrinsicDoubledMatterFlatFrameDerivative
              period hPeriod choice lift direction point)) +
        ∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGammaCLM direction
            (d9LeviCivitaSpinCorrection
              period hPeriod direction point (lift point)) by
        simp only [map_add, Finset.sum_add_distrib]]
  rw [d9LeviCivitaSpinCorrection_contraction]
  rfl

theorem d9UnitRadialClifford_contMDiff
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (fun point =>
        d9UnitRadialClifford period hPeriod point (lift point)) := by
  apply ContMDiff.sum
  intro direction _
  exact
    (d9UnitRadialCoordinate_contMDiff
      period hPeriod direction).smul
      ((d9DoubledMatterFiberCliffordGammaCLM direction).contDiff.contMDiff.comp
        lift.contMDiff_toFun)

theorem d9UnitRadialClifford_deck
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (winding : Int) (point : ThroatCover period hPeriod) :
    d9UnitRadialClifford period hPeriod
        (winding +ᵥ point) (lift (winding +ᵥ point)) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9UnitRadialClifford period hPeriod point (lift point)) := by
  unfold d9UnitRadialClifford
  change
    (∑ direction : Fin 3,
      d9UnitRadialCoordinate period hPeriod direction (winding +ᵥ point) •
        d9DoubledMatterFiberCliffordGammaCLM direction
          (lift (winding +ᵥ point))) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (∑ direction : Fin 3,
          d9UnitRadialCoordinate period hPeriod direction point •
            d9DoubledMatterFiberCliffordGammaCLM direction
              (lift point))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  change
    d9UnitRadialCoordinate period hPeriod direction (winding +ᵥ point) •
        d9DoubledMatterFiberCliffordGammaCLM direction
          (lift (winding +ᵥ point)) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (d9UnitRadialCoordinate period hPeriod direction point •
          d9DoubledMatterFiberCliffordGammaCLM direction
            (lift point))
  rw [d9UnitRadialCoordinate_deck,
    lift.deck_monodromy,
    d9DoubledMatterFiberCliffordGammaCLM_apply,
    d9DoubledMatterFiberCliffordGamma_monodromy,
    ← d9DoubledMatterSpinorMonodromy_real_smul]
  rfl

theorem d9LeviCivitaSpinCoverDirac_contMDiff
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (d9LeviCivitaSpinCoverDirac period hPeriod choice lift) := by
  rw [show d9LeviCivitaSpinCoverDirac period hPeriod choice lift =
      fun point =>
        d9IntrinsicDoubledMatterSpinorCoverDirac
            period hPeriod choice lift point -
          d9UnitRadialClifford period hPeriod point (lift point) by
        funext point
        exact d9LeviCivitaSpinCoverDirac_eq
          period hPeriod choice lift point]
  exact
    (d9IntrinsicDoubledMatterSpinorCoverDirac_contMDiff
      period hPeriod choice lift).sub
      (d9UnitRadialClifford_contMDiff
        period hPeriod choice lift)

theorem d9LeviCivitaSpinCoverDirac_deck
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (winding : Int) (point : ThroatCover period hPeriod) :
    d9LeviCivitaSpinCoverDirac period hPeriod choice lift
        (winding +ᵥ point) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9LeviCivitaSpinCoverDirac
          period hPeriod choice lift point) := by
  rw [d9LeviCivitaSpinCoverDirac_eq,
    d9LeviCivitaSpinCoverDirac_eq,
    d9IntrinsicDoubledMatterSpinorCoverDirac_deck,
    d9UnitRadialClifford_deck]
  exact
    (map_sub
      (d9DoubledMatterSpinorMonodromyCLM choice winding) _ _).symm

/-- Corrected cover operator packaged as a smooth doubled spinor lift. -/
def d9LeviCivitaSpinDiracLift
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice where
  first :=
    { toFun := fun point =>
        (d9LeviCivitaSpinCoverDirac
          period hPeriod choice lift point).1
      contMDiff_toFun := by
        have hSmooth :=
          d9LeviCivitaSpinCoverDirac_contMDiff
            period hPeriod choice lift
        rw [contMDiff_prod_module_iff] at hSmooth
        exact hSmooth.1
      deck_equivariant := by
        intro winding point
        rw [throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
        have hDeck := congrArg Prod.fst
          (d9LeviCivitaSpinCoverDirac_deck
            period hPeriod choice lift winding point)
        simpa [d9DoubledMatterSpinorMonodromy] using hDeck }
  second :=
    { toFun := fun point =>
        (d9LeviCivitaSpinCoverDirac
          period hPeriod choice lift point).2
      contMDiff_toFun := by
        have hSmooth :=
          d9LeviCivitaSpinCoverDirac_contMDiff
            period hPeriod choice lift
        rw [contMDiff_prod_module_iff] at hSmooth
        exact hSmooth.2
      deck_equivariant := by
        intro winding point
        rw [throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
        have hDeck := congrArg Prod.snd
          (d9LeviCivitaSpinCoverDirac_deck
            period hPeriod choice lift winding point)
        simpa [d9DoubledMatterSpinorMonodromy] using hDeck }

@[simp]
theorem d9LeviCivitaSpinDiracLift_apply
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    d9LeviCivitaSpinDiracLift period hPeriod choice lift point =
      d9LeviCivitaSpinCoverDirac period hPeriod choice lift point :=
  rfl

structure ProgramPD9MatterSpinorLeviCivitaConnectionCertificate4D where
  choice : NormalRootChoice
  radialCoordinate : Fin 3 → ThroatCover period hPeriod → Real
  radialCoordinateCanonical :
    radialCoordinate = d9UnitRadialCoordinate period hPeriod
  radialCoordinateSmooth :
    ∀ direction,
      ContMDiff throatCoverModelWithCorners 𝓘(Real) ∞
        (radialCoordinate direction)
  radialUnit : ∀ point,
    ∑ direction : Fin 3, radialCoordinate direction point ^ 2 = 1
  connectionCoefficient :
    Fin 3 → Fin 3 → Fin 3 → ThroatCover period hPeriod → Real
  connectionCoefficientCanonical :
    connectionCoefficient =
      d9RadialLeviCivitaCoefficient period hPeriod
  metricCompatible : ∀ first second third point,
    connectionCoefficient first second third point =
      -connectionCoefficient first third second point
  operator :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice
  operatorCanonical :
    operator = d9LeviCivitaSpinDiracLift period hPeriod choice
  coverReduction : ∀ lift point,
    operator lift point =
      d9IntrinsicDoubledMatterSpinorCoverDirac
          period hPeriod choice lift point -
        d9UnitRadialClifford period hPeriod point (lift point)

def programPD9MatterSpinorLeviCivitaConnectionCertificate4D :
    ProgramPD9MatterSpinorLeviCivitaConnectionCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  radialCoordinate := d9UnitRadialCoordinate period hPeriod
  radialCoordinateCanonical := rfl
  radialCoordinateSmooth :=
    d9UnitRadialCoordinate_contMDiff period hPeriod
  radialUnit := d9UnitRadialCoordinate_norm_sq period hPeriod
  connectionCoefficient :=
    d9RadialLeviCivitaCoefficient period hPeriod
  connectionCoefficientCanonical := rfl
  metricCompatible :=
    d9RadialLeviCivitaCoefficient_skew period hPeriod
  operator :=
    d9LeviCivitaSpinDiracLift period hPeriod .positiveQuarter
  operatorCanonical := rfl
  coverReduction := by
    intro lift point
    exact d9LeviCivitaSpinCoverDirac_eq
      period hPeriod .positiveQuarter lift point

theorem
    programPD9MatterSpinorLeviCivitaConnectionCertificate4D_nonempty :
    Nonempty
      (ProgramPD9MatterSpinorLeviCivitaConnectionCertificate4D
        period hPeriod) :=
  ⟨programPD9MatterSpinorLeviCivitaConnectionCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
end JanusFormal
