import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D

/-!
# Leibniz rule for the geometric primitive SpinC Dirac operator

This gate proves the local first-order product rule needed to generate the
positive monopole tower from the geometric Hopf zero mode.  The multiplier
is an arbitrary globally smooth real scalar on the quotient throat.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D

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
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Multiply every local representative of a primitive SpinC section by a
globally defined smooth real scalar. -/
def d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice where
  localValue index base := scalar base • family.localValue index base
  contMDiffOn_localValue index :=
    hScalar.contMDiffOn.smul (family.contMDiffOn_localValue index)
  coordChange_localValue first second base hBase := by
    rw [map_smul,
      family.coordChange_localValue first second base hBase]

@[simp]
theorem d9PrimitiveSpinCRealScalarMulLocalGaugeFamily_localValue
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
      period hPeriod choice scalar hScalar family).localValue index base =
      scalar base • family.localValue index base :=
  rfl

/-- Exact manifold-derivative product rule in an intrinsic throat-frame
direction. -/
theorem d9PrimitiveSpinCLocalFlatFrameDerivative_realScalarMul
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod choice
        (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
          period hPeriod choice scalar hScalar family)
        index direction base =
      scalar base •
          d9PrimitiveSpinCLocalFlatFrameDerivative
            period hPeriod choice family index direction base +
        (mvfderiv throatCoverModelWithCorners scalar base
          (d9IntrinsicThroatFrame
            period hPeriod direction base)) •
          family.localValue index base := by
  let field := family.localValue index
  let tangent := d9IntrinsicThroatFrame period hPeriod direction base
  have hScalarDiff :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Real) scalar base :=
    hScalar.mdifferentiableAt (by simp)
  have hFieldDiff :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) field base :=
    ((family.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase)).mdifferentiableAt (by simp)
  have hProduct := mvfderiv_smul hScalarDiff hFieldDiff
  have hApply := congrArg (fun derivative => derivative tangent) hProduct
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  change
    mvfderiv throatCoverModelWithCorners
        (scalar • field) base tangent =
      scalar base •
          mvfderiv throatCoverModelWithCorners field base tangent +
        mvfderiv throatCoverModelWithCorners scalar base tangent •
          field base
  simpa [tangent] using hApply

/-- The algebraic Levi--Civita spin correction is real-linear in the
spinor variable. -/
theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_real_smul
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (scalar : Real) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base (scalar • matter) =
      scalar •
        d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base matter := by
  unfold d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro other _
  by_cases hSame : other = direction
  · simp [hSame]
  · simp only [hSame, ↓reduceIte, map_smul]
    module

/-- One coupled directional derivative is homogeneous when both its
ordinary derivative and spinor value are scaled by the same real number. -/
theorem d9PrimitiveSpinCLocalDirectionalDerivative_real_smul
    (connectionCoefficient scalar : Real)
    (ordinaryDerivative matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCLocalDirectionalDerivative connectionCoefficient
        (scalar • ordinaryDerivative) (scalar • matter) =
      scalar •
        d9PrimitiveSpinCLocalDirectionalDerivative
          connectionCoefficient ordinaryDerivative matter := by
  unfold d9PrimitiveSpinCLocalDirectionalDerivative
  rw [map_smul]
  module

/-- The algebraic local Dirac contraction is homogeneous in its derivative
and spinor arguments. -/
theorem d9PrimitiveSpinCLocalDirac_real_smul
    (connectionCoefficient : Fin 3 → Real)
    (ordinaryDerivative : Fin 3 → D9DoubledMatterFiber)
    (scalar : Real) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCLocalDirac connectionCoefficient
        (fun direction => scalar • ordinaryDerivative direction)
        (scalar • matter) =
      scalar •
        d9PrimitiveSpinCLocalDirac
          connectionCoefficient ordinaryDerivative matter := by
  unfold d9PrimitiveSpinCLocalDirac
  simp_rw [d9PrimitiveSpinCLocalDirectionalDerivative_real_smul,
    map_smul]
  exact Finset.smul_sum.symm

/-- Exact Levi--Civita derivative product rule. -/
theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_realScalarMul
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice
        (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
          period hPeriod choice scalar hScalar family)
        index direction base =
      scalar base •
          d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
            period hPeriod choice family index direction base +
        (mvfderiv throatCoverModelWithCorners scalar base
          (d9IntrinsicThroatFrame
            period hPeriod direction base)) •
          family.localValue index base := by
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [d9PrimitiveSpinCLocalFlatFrameDerivative_realScalarMul
      (hBase := hBase),
    d9PrimitiveSpinCRealScalarMulLocalGaugeFamily_localValue,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_real_smul]
  module

/-- Clifford contraction of the scalar differential against a local
primitive SpinC representative. -/
def d9PrimitiveSpinCScalarCliffordGradientAt
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGammaCLM direction
      ((mvfderiv throatCoverModelWithCorners scalar base
          (d9IntrinsicThroatFrame
            period hPeriod direction base)) •
        family.localValue index base)

/-- Clifford contraction by one scalar differential is pointwise linear in a
second scalar multiplier of the spinor. -/
theorem d9PrimitiveSpinCScalarCliffordGradientAt_realScalarMul
    (choice : NormalRootChoice)
    (scalar multiplier : ThroatBase period hPeriod → Real)
    (hMultiplier :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ multiplier)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCScalarCliffordGradientAt
        period hPeriod choice scalar
        (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
          period hPeriod choice multiplier hMultiplier family)
        index base =
      multiplier base •
        d9PrimitiveSpinCScalarCliffordGradientAt
          period hPeriod choice scalar family index base := by
  unfold d9PrimitiveSpinCScalarCliffordGradientAt
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  rw [d9PrimitiveSpinCRealScalarMulLocalGaugeFamily_localValue,
    smul_smul]
  simp_rw [map_smul]
  module

/-- Exact local first-order Leibniz rule for the complete coupled geometric
Dirac operator. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_realScalarMul
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice
        (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
          period hPeriod choice scalar hScalar family)
        index base =
      scalar base •
          d9PrimitiveSpinCLocalGeometricDirac
            period hPeriod choice family index base +
        d9PrimitiveSpinCScalarCliffordGradientAt
          period hPeriod choice scalar family index base := by
  unfold d9PrimitiveSpinCLocalGeometricDirac
  simp_rw [
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_realScalarMul
      (hBase := hBase)]
  rw [d9PrimitiveSpinCRealScalarMulLocalGaugeFamily_localValue,
    d9PrimitiveSpinCLocalDirac_partial_add,
    d9PrimitiveSpinCLocalDirac_real_smul]
  rfl

/-- Genuine global smooth section obtained by multiplying an arbitrary
primitive SpinC section by a globally smooth real scalar. -/
def d9PrimitiveSpinCRealScalarMulSection
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
    period hPeriod choice scalar hScalar
    (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state)).toSmoothSection
        period hPeriod choice

/-- At the preferred index, recovering local gauges from a genuine section
returns its actual fiber value. -/
theorem d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_indexAt
    (choice : NormalRootChoice)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
        period hPeriod choice state).localValue
          ((d9PrimitiveSpinCVectorBundleCore
            period hPeriod choice).indexAt base) base =
      state base := by
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state
  have hRecover :
      family.toSmoothSection period hPeriod choice = state :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection
      period hPeriod choice state
  exact congrArg
    (fun current : D9PrimitiveSpinCSmoothSection period hPeriod choice =>
      current base) hRecover

@[simp]
theorem d9PrimitiveSpinCRealScalarMulSection_apply
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCRealScalarMulSection
        period hPeriod choice scalar hScalar state base =
      scalar base • state base := by
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state
  change scalar base • family.localValue
      ((d9PrimitiveSpinCVectorBundleCore
        period hPeriod choice).indexAt base) base =
    scalar base • state base
  rw [← d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection
    period hPeriod choice state]
  rfl

/-- Multiplication by a smooth scalar commutes with a constant real
coefficient on genuine smooth sections. -/
theorem d9PrimitiveSpinCRealScalarMulSection_real_smul
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (coefficient : Real)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCRealScalarMulSection
        period hPeriod choice scalar hScalar (coefficient • state) =
      coefficient •
        d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice scalar hScalar state := by
  ext base
  rw [d9PrimitiveSpinCRealScalarMulSection_apply]
  have hStateSmul :
      (coefficient • state) base = coefficient • state base :=
    rfl
  have hResultSmul :
      (coefficient •
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod choice scalar hScalar state) base =
        coefficient •
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod choice scalar hScalar state base :=
    rfl
  rw [hStateSmul, hResultSmul,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  module

/-- Global Clifford-gradient remainder in the scalar Leibniz rule.  It is
defined as a difference of genuine smooth sections, hence carries no local
gluing assumption. -/
def d9PrimitiveSpinCScalarCliffordGradientSection
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  d9PrimitiveSpinCGeometricDiracOperator
      period hPeriod choice
      (d9PrimitiveSpinCRealScalarMulSection
        period hPeriod choice scalar hScalar state) -
    d9PrimitiveSpinCRealScalarMulSection
      period hPeriod choice scalar hScalar
      (d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod choice state)

/-- Exact global smooth-section Leibniz rule. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_realScalarMul
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod choice
        (d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice scalar hScalar state) =
      d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice scalar hScalar
          (d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod choice state) +
        d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod choice scalar hScalar state := by
  unfold d9PrimitiveSpinCScalarCliffordGradientSection
  module

/-- The globally packaged remainder is exactly the local Clifford contraction
of the scalar differential in the preferred gauge. -/
theorem d9PrimitiveSpinCScalarCliffordGradientSection_apply
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCScalarCliffordGradientSection
        period hPeriod choice scalar hScalar state base :
      D9DoubledMatterFiber) =
      d9PrimitiveSpinCScalarCliffordGradientAt
        period hPeriod choice scalar
        (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
          period hPeriod choice state)
        ((d9PrimitiveSpinCVectorBundleCore
          period hPeriod choice).indexAt base) base := by
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state
  let multiplied :=
    d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
      period hPeriod choice scalar hScalar family
  let index :=
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).indexAt base
  let gradientValue :
      D9PrimitiveSpinCFiber period hPeriod choice base :=
    d9PrimitiveSpinCScalarCliffordGradientSection
      period hPeriod choice scalar hScalar state base
  let remainderValue :
      D9PrimitiveSpinCFiber period hPeriod choice base :=
    d9PrimitiveSpinCScalarCliffordGradientAt
      period hPeriod choice scalar family index base
  let multipliedDiracValue :
      D9PrimitiveSpinCFiber period hPeriod choice base :=
    d9PrimitiveSpinCLocalGeometricDirac
      period hPeriod choice multiplied index base
  let scaledDiracValue :
      D9PrimitiveSpinCFiber period hPeriod choice base :=
    scalar base •
      d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice family index base
  change
    gradientValue = remainderValue
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).mem_baseSet_at base
  have hDiracMultiplied :=
    congrArg
      (fun smoothSection :
        D9PrimitiveSpinCSmoothSection period hPeriod choice =>
        smoothSection base)
      (d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection
        period hPeriod choice multiplied)
  have hLeibniz :=
    d9PrimitiveSpinCLocalGeometricDirac_realScalarMul
      period hPeriod choice scalar hScalar family index base hBase
  have hGlobal :=
    congrArg
      (fun smoothSection :
        D9PrimitiveSpinCSmoothSection period hPeriod choice =>
        smoothSection base)
      (d9PrimitiveSpinCGeometricDiracOperator_realScalarMul
        period hPeriod choice scalar hScalar state)
  change
    d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod choice
          (multiplied.toSmoothSection period hPeriod choice) base =
      d9PrimitiveSpinCRealScalarMulSection
              period hPeriod choice scalar hScalar
              (d9PrimitiveSpinCGeometricDiracOperator
                period hPeriod choice state) base +
        d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod choice scalar hScalar state base at hGlobal
  rw [hDiracMultiplied,
    d9PrimitiveSpinCGeometricDiracSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply] at hGlobal
  change
    multipliedDiracValue = scaledDiracValue + gradientValue at hGlobal
  have hLeibnizFiber :
      multipliedDiracValue = scaledDiracValue + remainderValue :=
    hLeibniz
  rw [hLeibnizFiber] at hGlobal
  exact (add_left_cancel hGlobal).symm

/-- Clifford multiplication by the differential of one scalar is pointwise
linear in a second smooth real scalar multiplier. -/
theorem d9PrimitiveSpinCScalarCliffordGradientSection_realScalarMul
    (choice : NormalRootChoice)
    (scalar multiplier : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (hMultiplier :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ multiplier)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCScalarCliffordGradientSection
        period hPeriod choice scalar hScalar
        (d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice multiplier hMultiplier state) =
      d9PrimitiveSpinCRealScalarMulSection
        period hPeriod choice multiplier hMultiplier
        (d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod choice scalar hScalar state) := by
  ext base
  rw [d9PrimitiveSpinCRealScalarMulSection_apply]
  change
    (d9PrimitiveSpinCScalarCliffordGradientSection
        period hPeriod choice scalar hScalar
        (d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice multiplier hMultiplier state) base :
      D9DoubledMatterFiber) =
    multiplier base •
      (d9PrimitiveSpinCScalarCliffordGradientSection
        period hPeriod choice scalar hScalar state base :
      D9DoubledMatterFiber)
  rw [d9PrimitiveSpinCScalarCliffordGradientSection_apply,
    d9PrimitiveSpinCScalarCliffordGradientSection_apply]
  unfold d9PrimitiveSpinCScalarCliffordGradientAt
  simp_rw [d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_indexAt,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  let matter : D9DoubledMatterFiber := state base
  change
    (∑ direction : Fin 3,
      d9DoubledMatterFiberCliffordGammaCLM direction
        (mvfderiv throatCoverModelWithCorners scalar base
            (d9IntrinsicThroatFrame period hPeriod direction base) •
          (multiplier base • matter))) =
      multiplier base •
        ∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGammaCLM direction
            (mvfderiv throatCoverModelWithCorners scalar base
                (d9IntrinsicThroatFrame
                  period hPeriod direction base) •
              matter)
  calc
    _ = ∑ direction : Fin 3,
        multiplier base •
          d9DoubledMatterFiberCliffordGammaCLM direction
            (mvfderiv throatCoverModelWithCorners scalar base
                (d9IntrinsicThroatFrame
                  period hPeriod direction base) •
              matter) := by
      apply Finset.sum_congr rfl
      intro direction _
      rw [
        (d9DoubledMatterFiberCliffordGammaCLM direction).map_smul,
        (d9DoubledMatterFiberCliffordGammaCLM direction).map_smul,
        (d9DoubledMatterFiberCliffordGammaCLM direction).map_smul]
      simp only [smul_smul, mul_comm]
    _ = _ := by
      exact (Finset.smul_sum (r := multiplier base)
        (f := fun direction : Fin 3 =>
          d9DoubledMatterFiberCliffordGammaCLM direction
            (mvfderiv throatCoverModelWithCorners scalar base
                (d9IntrinsicThroatFrame
                  period hPeriod direction base) •
              matter))
        (s := Finset.univ)).symm

/-- Global form of the tangential-projector formula for a pulled-back sphere
coordinate. -/
theorem d9PrimitiveMonopoleCoordinateFrameDerivative_eq_projector
    (coordinate direction : Fin 3)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveMonopoleCoordinateFrameDerivative
        period hPeriod coordinate direction base =
      d9KroneckerDelta direction coordinate -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod direction base *
          d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base := by
  let point := normalBundleIndexAt period hPeriod base
  have hProject :
      mappingTorusMk (ThroatData period hPeriod) point = base :=
    normalBundleIndexAt_projects period hPeriod base
  rw [← hProject]
  exact d9PrimitiveMonopoleCoordinateFrameDerivative_mk
    period hPeriod coordinate direction point

/-- The `mvfderiv` form of the same coordinate derivative, used directly
by the Leibniz rule. -/
theorem d9PrimitiveMonopoleBaseCoordinate_mvfderiv_intrinsicFrame
    (coordinate direction : Fin 3)
    (base : ThroatBase period hPeriod) :
    mvfderiv throatCoverModelWithCorners
        (d9PrimitiveMonopoleBaseCoordinate
          period hPeriod coordinate) base
        (d9IntrinsicThroatFrame period hPeriod direction base) =
      d9PrimitiveMonopoleCoordinateFrameDerivative
        period hPeriod coordinate direction base := by
  rfl

/-- Actual smooth section candidate obtained by multiplying the Hopf zero
mode by one global sphere coordinate.  These three sections are the
geometric seeds of the first positive sphere level. -/
def primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    SmoothPrimitiveSpinCLocalGaugeFamily
      period hPeriod .positiveQuarter :=
  d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
    period hPeriod .positiveQuarter
    (d9PrimitiveMonopoleBaseCoordinate
      period hPeriod coordinate)
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod coordinate)
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode)

/-- The complete local Dirac action on a first-level coordinate seed.  The
new term is exactly Clifford multiplication by the tangential derivative
`δᵢⱼ - nᵢ nⱼ`; no spectral assumption is used. -/
theorem primitiveSpinCHopfFirstSphereCoordinateLocalGeometricDirac_mk
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (point : MappingTorusCover (ThroatData period hPeriod))
    (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9UnitRadialCoordinate period hPeriod coordinate point •
          (-normalRootLeviCivitaCorrectedFrequency
              period sector mode •
            (primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point)) +
        ∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGammaCLM direction
            ((d9KroneckerDelta direction coordinate -
                d9UnitRadialCoordinate
                    period hPeriod direction point *
                  d9UnitRadialCoordinate
                    period hPeriod coordinate point) •
              (primitiveSpinCHopfZeroModeLocalGaugeFamily
                period hPeriod sector mode).localValue
                  (point, chart)
                  (mappingTorusMk
                    (ThroatData period hPeriod) point)) := by
  let base := mappingTorusMk (ThroatData period hPeriod) point
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet
        period hPeriod (point, chart) := by
    constructor
    · exact mappingTorusMk_mem_normalBundleBaseSet
        period hPeriod point
    · exact hChart
  rw [primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily]
  rw [d9PrimitiveSpinCLocalGeometricDirac_realScalarMul
      (hBase := hBase)]
  rw [primitiveSpinCHopfZeroModeLocalGeometricDirac_mk
      (hChart := hChart)]
  unfold d9PrimitiveSpinCScalarCliffordGradientAt
  simp_rw [
    d9PrimitiveMonopoleBaseCoordinate_mvfderiv_intrinsicFrame,
    d9PrimitiveMonopoleCoordinateFrameDerivative_eq_projector]
  rfl

/-- Clifford contraction of the coordinate projector simplifies to
`γⱼ - nⱼ γ(n)` on the Hopf radial eigenspinor. -/
theorem primitiveSpinCHopfTangentialCoordinateClifford_mk
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (point : MappingTorusCover (ThroatData period hPeriod))
    (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    (∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          ((d9KroneckerDelta direction coordinate -
              d9UnitRadialCoordinate
                  period hPeriod direction point *
                d9UnitRadialCoordinate
                  period hPeriod coordinate point) •
            (primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point))) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart)
              (mappingTorusMk
                (ThroatData period hPeriod) point)) -
        d9UnitRadialCoordinate
            period hPeriod coordinate point •
          d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point)) := by
  let matter :=
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point)
  have hRadial :
      d9UnitRadialClifford period hPeriod point matter =
        d9PrimitiveSpinCImaginaryAction matter :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily_unitRadial_eigen
      period hPeriod sector mode point chart hChart
  rw [← hRadial]
  fin_cases coordinate <;>
    simp [Fin.sum_univ_succ, d9KroneckerDelta,
      d9UnitRadialClifford, matter, map_smul] <;>
    module

/-- Simplified local first-level equation. -/
theorem primitiveSpinCHopfFirstSphereCoordinateLocalGeometricDirac_mk'
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (point : MappingTorusCover (ThroatData period hPeriod))
    (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9UnitRadialCoordinate period hPeriod coordinate point •
          (-normalRootLeviCivitaCorrectedFrequency
              period sector mode •
            (primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point)) +
        d9DoubledMatterFiberCliffordGammaCLM coordinate
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart)
              (mappingTorusMk
                (ThroatData period hPeriod) point)) -
        d9UnitRadialCoordinate period hPeriod coordinate point •
          d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point)) := by
  rw [primitiveSpinCHopfFirstSphereCoordinateLocalGeometricDirac_mk
      (hChart := hChart),
    primitiveSpinCHopfTangentialCoordinateClifford_mk
      (hChart := hChart)]
  abel

/-- Global smooth first-level coordinate seed. -/
def primitiveSpinCHopfFirstSphereCoordinateSection
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
    period hPeriod coordinate sector mode).toSmoothSection
      period hPeriod .positiveQuarter

@[simp]
theorem primitiveSpinCHopfFirstSphereCoordinateSection_apply
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (base : ThroatBase period hPeriod) :
    primitiveSpinCHopfFirstSphereCoordinateSection
        period hPeriod coordinate sector mode base =
      d9PrimitiveMonopoleBaseCoordinate
          period hPeriod coordinate base •
        primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode base := by
  rfl

/-- Pointwise Clifford-gradient remainder of one coordinate seed, expressed
in the preferred local gauge at each base point. -/
def primitiveSpinCHopfFirstSphereCoordinateCliffordGradientAt
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (base : ThroatBase period hPeriod) :
    D9PrimitiveSpinCFiber
      period hPeriod .positiveQuarter base :=
  d9PrimitiveSpinCScalarCliffordGradientAt
    period hPeriod .positiveQuarter
    (d9PrimitiveMonopoleBaseCoordinate
      period hPeriod coordinate)
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode)
    ((d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter).indexAt base)
    base

/-- The global preferred-gauge gradient remainder is the intrinsic
`γⱼ - nⱼJ` expression. -/
theorem primitiveSpinCHopfFirstSphereCoordinateCliffordGradientAt_eq
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (base : ThroatBase period hPeriod) :
    primitiveSpinCHopfFirstSphereCoordinateCliffordGradientAt
        period hPeriod coordinate sector mode base =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode base) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector mode base) := by
  let point := normalBundleIndexAt period hPeriod base
  let chart :=
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod 1).indexAt base
  let core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter
  have hProject :
      mappingTorusMk (ThroatData period hPeriod) point = base :=
    normalBundleIndexAt_projects period hPeriod base
  have hChartBase :
      base ∈ d9PrimitiveMonopoleChartDomain
        period hPeriod chart :=
    (core.mem_baseSet_at base).2
  have hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart := by
    unfold d9PrimitiveMonopoleChartDomain at hChartBase
    rw [← hProject] at hChartBase
    exact hChartBase
  have hLocal :=
    primitiveSpinCHopfTangentialCoordinateClifford_mk
      period hPeriod coordinate sector mode point chart hChart
  change
    (∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          ((d9PrimitiveMonopoleCoordinateFrameDerivative
              period hPeriod coordinate direction base) •
            (primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart) base)) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart) base) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base •
          d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart) base)
  rw [← hProject]
  simp_rw [
    d9PrimitiveMonopoleCoordinateFrameDerivative_eq_projector]
  exact hLocal

/-- Intrinsic `γⱼ - nⱼJ` tangent value, packaged in the actual SpinC fiber. -/
def primitiveSpinCHopfFirstSphereCoordinateTangentialAt
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (base : ThroatBase period hPeriod) :
    D9PrimitiveSpinCFiber
      period hPeriod .positiveQuarter base :=
  d9DoubledMatterFiberCliffordGammaCLM coordinate
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector mode base) -
    d9PrimitiveSpinCBaseUnitRadialCoordinate
        period hPeriod coordinate base •
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode base)

/-- Operator-level first-order identity for each of the three genuine
first-positive-level geometric seeds. -/
theorem primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_apply
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) base =
      d9PrimitiveMonopoleBaseCoordinate
          period hPeriod coordinate base •
          (-normalRootLeviCivitaCorrectedFrequency
              period sector mode •
            primitiveSpinCHopfZeroModeSection
              period hPeriod sector mode base) +
        primitiveSpinCHopfFirstSphereCoordinateCliffordGradientAt
          period hPeriod coordinate sector mode base := by
  let family :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode
  let multiplied :=
    primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
      period hPeriod coordinate sector mode
  let core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter
  let index := core.indexAt base
  let point := normalBundleIndexAt period hPeriod base
  let chart :=
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod 1).indexAt base
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    core.mem_baseSet_at base
  have hLeibniz :=
    d9PrimitiveSpinCLocalGeometricDirac_realScalarMul
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate
        period hPeriod coordinate)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod coordinate)
      family index base hBase
  have hProject :
      mappingTorusMk (ThroatData period hPeriod) point = base :=
    normalBundleIndexAt_projects period hPeriod base
  have hChartBase :
      base ∈ d9PrimitiveMonopoleChartDomain
        period hPeriod chart :=
    (core.mem_baseSet_at base).2
  have hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart := by
    unfold d9PrimitiveMonopoleChartDomain at hChartBase
    rw [← hProject] at hChartBase
    exact hChartBase
  have hZeroAtAnchor :=
    primitiveSpinCHopfZeroModeLocalGeometricDirac_mk
      period hPeriod sector mode point chart hChart
  have hZeroLocal :
      d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod .positiveQuarter family index base =
        -normalRootLeviCivitaCorrectedFrequency
            period sector mode •
          family.localValue index base := by
    change
      d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod .positiveQuarter family
            (point, chart) base =
        -normalRootLeviCivitaCorrectedFrequency
            period sector mode •
          family.localValue (point, chart) base
    rw [← hProject]
    exact hZeroAtAnchor
  unfold primitiveSpinCHopfFirstSphereCoordinateSection
  rw [d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection]
  rw [d9PrimitiveSpinCGeometricDiracSection_apply]
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter multiplied index base = _
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod coordinate)
          family)
        index base = _
  rw [hLeibniz]
  rw [hZeroLocal]
  rfl

/-- Simplified global first-order equation for a coordinate seed. -/
theorem primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_apply'
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) base =
      d9PrimitiveMonopoleBaseCoordinate
          period hPeriod coordinate base •
          (-normalRootLeviCivitaCorrectedFrequency
              period sector mode •
            primitiveSpinCHopfZeroModeSection
              period hPeriod sector mode base) +
        primitiveSpinCHopfFirstSphereCoordinateTangentialAt
          period hPeriod coordinate sector mode base := by
  rw [primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_apply,
    primitiveSpinCHopfFirstSphereCoordinateCliffordGradientAt_eq]
  rfl

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
end JanusFormal
