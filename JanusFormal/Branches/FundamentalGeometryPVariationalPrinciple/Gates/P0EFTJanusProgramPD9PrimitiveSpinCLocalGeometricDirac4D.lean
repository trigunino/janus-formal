import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D

/-!
# Differential local Dirac operator on the primitive D9 SpinC bundle

This gate applies the genuine manifold derivative of a smooth local gauge
representative to the global intrinsic throat frame, adds the radial
Levi--Civita spin correction and the pulled-back primitive monopole
connection, and contracts with the three Clifford generators.

The remaining overlap calculation is isolated as the ordinary Leibniz law
for the derivative of the explicit clutching phase.  Once that identity is
supplied, gauge covariance of the complete local operator follows here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Unit radial coordinate written directly on the quotient throat. -/
def d9PrimitiveSpinCBaseUnitRadialCoordinate
    (direction : Fin 3) (base : ThroatBase period hPeriod) : Real :=
  d9PrimitiveMonopoleBaseCoordinate period hPeriod direction base

/-- The quotient radial coordinate agrees with the established cover
coordinate under the mapping-torus projection. -/
@[simp]
theorem d9PrimitiveSpinCBaseUnitRadialCoordinate_mk
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction
        (mappingTorusMk (ThroatData period hPeriod) point) =
      P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D.d9UnitRadialCoordinate
        period hPeriod direction point :=
  rfl

/-- Flat central connection of the rotating normal spin frame. -/
def d9PrimitiveSpinCNormalFrameConnectionCoefficient
    (direction : Fin 3) (base : ThroatBase period hPeriod) : Real :=
  -(Real.pi / (2 * period)) *
    d9PrimitiveSpinCBaseUnitRadialCoordinate
      period hPeriod direction base

/-- Total charge-one connection: monopole plus normal spin-frame term. -/
def d9PrimitiveSpinCTotalConnectionFrameCoefficient
    (chart : MonopoleChart) (direction : Fin 3)
    (base : ThroatBase period hPeriod) : Real :=
  d9PrimitiveMonopoleConnectionFrameCoefficient
      period hPeriod 1 chart direction base +
    d9PrimitiveSpinCNormalFrameConnectionCoefficient
      period hPeriod direction base

theorem d9PrimitiveSpinCTotalConnectionFrameCoefficient_gauge_difference
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    d9PrimitiveSpinCTotalConnectionFrameCoefficient
          period hPeriod .north direction base -
        d9PrimitiveSpinCTotalConnectionFrameCoefficient
          period hPeriod .south direction base =
      d9PrimitiveMonopoleAngularFrameCoefficient
        period hPeriod direction base := by
  have hDifference :=
    d9PrimitiveMonopoleConnectionFrameCoefficient_gauge_difference
      period hPeriod 1 direction base hNorth hSouth
  norm_num at hDifference
  unfold d9PrimitiveSpinCTotalConnectionFrameCoefficient
  linarith

/-- Radial Levi--Civita spin correction on a local quotient gauge. -/
def d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) : D9DoubledMatterFiber :=
  ∑ other : Fin 3,
    if other = direction then 0
    else
      ((1 : Real) / 2 *
        d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod other base) •
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9DoubledMatterFiberCliffordGammaCLM other matter)

/-- The Levi--Civita correction commutes with the primitive phase action. -/
theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_phase
    (phase : Circle) (direction : Fin 3)
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base
        (d9PrimitiveSpinCPhaseActionCLM phase matter) =
      d9PrimitiveSpinCPhaseActionCLM phase
        (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base matter) := by
  unfold d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro other _
  by_cases hSame : other = direction
  · simp [hSame]
  · simp only [hSame, ↓reduceIte, map_smul]
    simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
    rw [d9PrimitiveSpinCPhaseAction_clifford,
      d9PrimitiveSpinCPhaseAction_clifford]

/-- Genuine manifold derivative of one local gauge representative along one
global intrinsic frame direction. -/
def d9PrimitiveSpinCLocalFlatFrameDerivative
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod) :
    D9DoubledMatterFiber :=
  mfderiv throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber)
      (family.localValue index) base
      (d9IntrinsicThroatFrame period hPeriod direction base)

/-- Local Levi--Civita spin derivative of a primitive SpinC representative. -/
def d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCLocalFlatFrameDerivative
      period hPeriod choice family index direction base +
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
      period hPeriod direction base (family.localValue index base)

/-- Actual local differential SpinC Dirac expression in one joint
normal-root/monopole chart. -/
def d9PrimitiveSpinCLocalGeometricDirac
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCLocalDirac
    (fun direction =>
      d9PrimitiveSpinCTotalConnectionFrameCoefficient
        period hPeriod index.2 direction base)
    (fun direction =>
      d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice family index direction base)
    (family.localValue index base)

/-- The coupled connection is zeroth order: the principal response to a
derivative increment is the bare intrinsic Clifford contraction. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_principal_increment
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (increment : Fin 3 → D9DoubledMatterFiber) :
    d9PrimitiveSpinCLocalDirac
        (fun direction =>
          d9PrimitiveSpinCTotalConnectionFrameCoefficient
            period hPeriod index.2 direction base)
        (fun direction =>
          d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
              period hPeriod choice family index direction base +
            increment direction)
        (family.localValue index base) =
      d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family index base +
        ∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGammaCLM direction
            (increment direction) := by
  exact d9PrimitiveSpinCLocalDirac_partial_add
    (fun direction =>
      d9PrimitiveSpinCTotalConnectionFrameCoefficient
        period hPeriod index.2 direction base)
    (fun direction =>
      d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice family index direction base)
    increment (family.localValue index base)

/-- North/south local values are related by the explicit primitive phase
when the normal-root chart is held fixed. -/
theorem d9PrimitiveSpinCLocalValue_north_south
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (normalIndex : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hNormal : base ∈ normalBundleBaseSet period hPeriod normalIndex)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    family.localValue (normalIndex, .south) base =
      d9PrimitiveSpinCPhaseActionCLM
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod .north .south base)
        (family.localValue (normalIndex, .north) base) := by
  have hChange := family.coordChange_localValue
    (normalIndex, .north) (normalIndex, .south) base
    ⟨⟨hNormal, hNorth⟩, ⟨hNormal, hSouth⟩⟩
  change
    d9PrimitiveSpinCPhaseActionCLM
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod .north .south base)
        (d9DoubledMatterSpinorMonodromy choice
          (localTransitionWinding
            period hPeriod normalIndex normalIndex base)
          (family.localValue (normalIndex, .north) base)) =
      family.localValue (normalIndex, .south) base at hChange
  rw [localTransitionWinding_self
    period hPeriod normalIndex base hNormal] at hChange
  simpa using hChange.symm

/-- If the ordinary derivative obeys the explicit clutching Leibniz rule,
then adding Levi--Civita preserves that rule. -/
theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_north_south
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (normalIndex : ThroatCover period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hNormal : base ∈ normalBundleBaseSet period hPeriod normalIndex)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south)
    (hFlat :
      d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family
          (normalIndex, .south) direction base =
        d9PrimitiveSpinCGaugeTransformedDirectionalPartial
          (d9PrimitiveMonopoleAngularFrameCoefficient
            period hPeriod direction base)
          (d9PrimitiveSpinCPhaseTransition
            period hPeriod .north .south base)
          (d9PrimitiveSpinCLocalFlatFrameDerivative
            period hPeriod choice family
            (normalIndex, .north) direction base)
          (family.localValue (normalIndex, .north) base)) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice family
        (normalIndex, .south) direction base =
      d9PrimitiveSpinCGaugeTransformedDirectionalPartial
        (d9PrimitiveMonopoleAngularFrameCoefficient
          period hPeriod direction base)
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod .north .south base)
        (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice family
          (normalIndex, .north) direction base)
        (family.localValue (normalIndex, .north) base) := by
  have hValue := d9PrimitiveSpinCLocalValue_north_south
    period hPeriod choice family normalIndex base
    hNormal hNorth hSouth
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [hFlat, hValue,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_phase]
  unfold d9PrimitiveSpinCGaugeTransformedDirectionalPartial
  rw [map_add]
  abel

/-- Gauge covariance of the complete differential local Dirac follows from
the sole remaining first-derivative clutching identity. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_north_south
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (normalIndex : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hNormal : base ∈ normalBundleBaseSet period hPeriod normalIndex)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south)
    (hFlat :
      ∀ direction,
        d9PrimitiveSpinCLocalFlatFrameDerivative
            period hPeriod choice family
            (normalIndex, .south) direction base =
          d9PrimitiveSpinCGaugeTransformedDirectionalPartial
            (d9PrimitiveMonopoleAngularFrameCoefficient
              period hPeriod direction base)
            (d9PrimitiveSpinCPhaseTransition
              period hPeriod .north .south base)
            (d9PrimitiveSpinCLocalFlatFrameDerivative
              period hPeriod choice family
              (normalIndex, .north) direction base)
            (family.localValue (normalIndex, .north) base)) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice family (normalIndex, .south) base =
      d9PrimitiveSpinCPhaseActionCLM
        (d9PrimitiveSpinCPhaseTransition
          period hPeriod .north .south base)
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family (normalIndex, .north) base) := by
  let phase :=
    d9PrimitiveSpinCPhaseTransition
      period hPeriod .north .south base
  let northMatter := family.localValue (normalIndex, .north) base
  have hValue :
      family.localValue (normalIndex, .south) base =
        d9PrimitiveSpinCPhaseActionCLM phase northMatter :=
    d9PrimitiveSpinCLocalValue_north_south
      period hPeriod choice family normalIndex base
      hNormal hNorth hSouth
  have hDerivatives :
      (fun direction =>
        d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice family
          (normalIndex, .south) direction base) =
        (fun direction =>
          d9PrimitiveSpinCGaugeTransformedDirectionalPartial
            (d9PrimitiveMonopoleAngularFrameCoefficient
              period hPeriod direction base)
            phase
            (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
              period hPeriod choice family
              (normalIndex, .north) direction base)
            northMatter) := by
    funext direction
    exact d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_north_south
      period hPeriod choice family normalIndex direction base
      hNormal hNorth hSouth (hFlat direction)
  unfold d9PrimitiveSpinCLocalGeometricDirac
  rw [hValue, hDerivatives]
  apply d9PrimitiveSpinCLocalDirac_gauge
  intro direction
  have hDifference :=
    d9PrimitiveSpinCTotalConnectionFrameCoefficient_gauge_difference
      period hPeriod direction base hNorth hSouth
  linarith

end
end P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
end JanusFormal
