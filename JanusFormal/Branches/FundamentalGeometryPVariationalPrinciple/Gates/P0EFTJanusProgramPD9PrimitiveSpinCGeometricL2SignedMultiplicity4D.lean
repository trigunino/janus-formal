import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D

/-!
# Exact geometric multiplicity of the signed primitive SpinC blocks

The null-harmonic scalar packet lies in the positive radial Clifford
eigenbundle, while its Clifford-gradient packet lies in the negative radial
eigenbundle.  This separates the two components pointwise and proves that
each first-order signed family has the expected physical multiplicity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Module
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

local instance signedMultiplicityComplexSMul :
    SMul Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexSMul period hPeriod

local instance signedMultiplicityComplexModule :
    Module Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexModule period hPeriod

/-- Radial Clifford multiplication at one base point, bundled linearly. -/
private def radialCliffordLinearMap
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterFiber →ₗ[Real] D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9PrimitiveSpinCBaseUnitRadialCoordinate
        period hPeriod direction base •
      d9DoubledMatterFiberCliffordGammaCLM direction

@[simp]
private theorem radialCliffordLinearMap_apply
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    radialCliffordLinearMap period hPeriod base matter =
      d9PrimitiveSpinCBaseUnitRadialClifford
        period hPeriod base matter := by
  simp [radialCliffordLinearMap,
    d9PrimitiveSpinCBaseUnitRadialClifford]

private theorem d9PrimitiveSpinCBaseUnitRadialClifford_zero
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (0 : D9DoubledMatterFiber) = 0 := by
  rw [← radialCliffordLinearMap_apply, map_zero]

private theorem d9PrimitiveSpinCBaseUnitRadialClifford_add
    (base : ThroatBase period hPeriod)
    (first second : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (first + second) =
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base first +
        d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base second := by
  rw [← radialCliffordLinearMap_apply, map_add,
    radialCliffordLinearMap_apply, radialCliffordLinearMap_apply]

/-- The fiber complex action commutes with the radial Clifford action. -/
theorem d9PrimitiveSpinCBaseUnitRadialClifford_complexAction
    (base : ThroatBase period hPeriod)
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base matter) := by
  rw [d9PrimitiveSpinCComplexAction_eq_re_add_im,
    ← radialCliffordLinearMap_apply,
    map_add, map_smul, map_smul,
    radialCliffordLinearMap_apply,
    radialCliffordLinearMap_apply,
    d9PrimitiveSpinCBaseUnitRadialClifford_imaginary,
    d9PrimitiveSpinCComplexAction_eq_re_add_im]

/-- The fiber complex action commutes with the intrinsic imaginary action. -/
theorem d9PrimitiveSpinCImaginaryAction_complexAction
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCImaginaryAction matter) := by
  unfold d9PrimitiveSpinCImaginaryAction
  rw [d9PrimitiveSpinCPhaseActionCLM_eq_complexAction,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul, mul_comm]

/-- A first-sphere tangential partner has the opposite radial eigenvalue
from its scalar Hopf seed. -/
theorem primitiveSpinCHopfFirstSphereTangential_baseUnitRadial_anti_eigen
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode base) =
      -d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode base) := by
  rw [primitiveSpinCHopfFirstSphereTangential_baseUnitRadial]
  rw [primitiveSpinCHopfFirstSphereTangentialSection_apply]
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt
  rw [map_sub, d9PrimitiveSpinCImaginaryAction_clifford,
    map_smul, d9PrimitiveSpinCImaginaryAction_sq]
  module

/-- Clifford contraction by a null differential sends the Hopf zero mode
to the negative radial eigenbundle. -/
theorem primitiveSpinCNullGradient_zeroMode_baseUnitRadial_anti_eigen
    (parameter : Complex) (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        ((primitiveSpinCNullGradientLinearMap
          period hPeriod parameter
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode)) base) =
      -d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCNullGradientLinearMap
          period hPeriod parameter
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode)) base) := by
  rw [primitiveSpinCNullGradientLinearMap_apply]
  change
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (∑ coordinate : Fin 3,
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSolidNullVector parameter coordinate)
            (primitiveSpinCCoordinateGradientLinearMap
              period hPeriod coordinate
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode)) base :
            D9DoubledMatterFiber)) =
      -d9PrimitiveSpinCImaginaryAction
        (∑ coordinate : Fin 3,
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSolidNullVector parameter coordinate)
            (primitiveSpinCCoordinateGradientLinearMap
              period hPeriod coordinate
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode)) base :
            D9DoubledMatterFiber))
  rw [← radialCliffordLinearMap_apply]
  simp_rw [d9PrimitiveSpinCComplexScalarSection_apply,
    ← d9PrimitiveSpinCComplexAction_eq_re_add_im]
  rw [map_sum, map_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [radialCliffordLinearMap_apply,
    d9PrimitiveSpinCBaseUnitRadialClifford_complexAction,
    primitiveSpinCCoordinateGradient_zeroMode,
    primitiveSpinCHopfFirstSphereTangential_baseUnitRadial_anti_eigen,
    map_neg,
    d9PrimitiveSpinCImaginaryAction_complexAction]

/-- A complex scalar times a real scalar multiple preserves positive radial
parity. -/
private theorem radialClifford_complexAction_real_smul_eigen
    (base : ThroatBase period hPeriod) (scalar : Complex) (real : Real)
    (matter : D9DoubledMatterFiber)
    (hMatter :
      d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base matter =
        d9PrimitiveSpinCImaginaryAction matter) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (d9PrimitiveSpinCComplexActionCLM scalar (real • matter)) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCComplexActionCLM scalar (real • matter)) := by
  rw [d9PrimitiveSpinCBaseUnitRadialClifford_complexAction,
    ← radialCliffordLinearMap_apply, map_smul,
    radialCliffordLinearMap_apply, hMatter,
    d9PrimitiveSpinCImaginaryAction_complexAction]
  simp only [map_smul]

/-- A complex scalar times a real scalar multiple preserves negative radial
parity. -/
private theorem radialClifford_complexAction_real_smul_anti_eigen
    (base : ThroatBase period hPeriod) (scalar : Complex) (real : Real)
    (matter : D9DoubledMatterFiber)
    (hMatter :
      d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base matter =
        -d9PrimitiveSpinCImaginaryAction matter) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (d9PrimitiveSpinCComplexActionCLM scalar (real • matter)) =
      -d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCComplexActionCLM scalar (real • matter)) := by
  rw [d9PrimitiveSpinCBaseUnitRadialClifford_complexAction,
    ← radialCliffordLinearMap_apply, map_smul,
    radialCliffordLinearMap_apply, hMatter, smul_neg, map_neg,
    d9PrimitiveSpinCImaginaryAction_complexAction]
  simp only [map_smul]

/-- Null-form multiplication preserves positive radial parity. -/
theorem primitiveSpinCNullMultiplication_baseUnitRadial_eigen
    (parameter : Complex) (state : SmoothSection period hPeriod)
    (base : ThroatBase period hPeriod)
    (hState :
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          (state base) =
        d9PrimitiveSpinCImaginaryAction (state base)) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        ((primitiveSpinCNullMultiplicationLinearMap
          period hPeriod parameter state) base) =
      d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCNullMultiplicationLinearMap
          period hPeriod parameter state) base) := by
  rw [primitiveSpinCNullMultiplicationLinearMap_apply]
  change
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (∑ coordinate : Fin 3,
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSolidNullVector parameter coordinate)
            (primitiveSpinCCoordinateMultiplicationLinearMap
              period hPeriod coordinate state) base :
            D9DoubledMatterFiber)) =
      d9PrimitiveSpinCImaginaryAction
        (∑ coordinate : Fin 3,
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSolidNullVector parameter coordinate)
            (primitiveSpinCCoordinateMultiplicationLinearMap
              period hPeriod coordinate state) base :
            D9DoubledMatterFiber))
  rw [← radialCliffordLinearMap_apply]
  simp_rw [d9PrimitiveSpinCComplexScalarSection_apply,
    ← d9PrimitiveSpinCComplexAction_eq_re_add_im]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  exact radialClifford_complexAction_real_smul_eigen
    period hPeriod base
    (primitiveSpinCSolidNullVector parameter coordinate)
    (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate base)
    (state base) hState

/-- Null-form multiplication preserves negative radial parity. -/
theorem primitiveSpinCNullMultiplication_baseUnitRadial_anti_eigen
    (parameter : Complex) (state : SmoothSection period hPeriod)
    (base : ThroatBase period hPeriod)
    (hState :
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          (state base) =
        -d9PrimitiveSpinCImaginaryAction (state base)) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        ((primitiveSpinCNullMultiplicationLinearMap
          period hPeriod parameter state) base) =
      -d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCNullMultiplicationLinearMap
          period hPeriod parameter state) base) := by
  rw [primitiveSpinCNullMultiplicationLinearMap_apply]
  change
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (∑ coordinate : Fin 3,
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSolidNullVector parameter coordinate)
            (primitiveSpinCCoordinateMultiplicationLinearMap
              period hPeriod coordinate state) base :
            D9DoubledMatterFiber)) =
      -d9PrimitiveSpinCImaginaryAction
        (∑ coordinate : Fin 3,
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSolidNullVector parameter coordinate)
            (primitiveSpinCCoordinateMultiplicationLinearMap
              period hPeriod coordinate state) base :
            D9DoubledMatterFiber))
  rw [← radialCliffordLinearMap_apply]
  simp_rw [d9PrimitiveSpinCComplexScalarSection_apply,
    ← d9PrimitiveSpinCComplexAction_eq_re_add_im]
  rw [map_sum, map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  exact radialClifford_complexAction_real_smul_anti_eigen
    period hPeriod base
    (primitiveSpinCSolidNullVector parameter coordinate)
    (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate base)
    (state base) hState

/-- Every scalar null power remains in the positive radial eigenbundle. -/
theorem primitiveSpinCNullPowerSection_baseUnitRadial_eigen
    (parameter : Complex) (sector : NormalRootChoice) (circleMode : Int)
    (degree : Nat) (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (primitiveSpinCNullPowerSection
          period hPeriod parameter sector circleMode degree base) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCNullPowerSection
          period hPeriod parameter sector circleMode degree base) := by
  induction degree with
  | zero =>
      rw [primitiveSpinCNullPowerSection_zero]
      exact primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen
        period hPeriod sector circleMode base
  | succ degree ih =>
      rw [primitiveSpinCNullPowerSection_succ]
      exact primitiveSpinCNullMultiplication_baseUnitRadial_eigen
        period hPeriod parameter
        (primitiveSpinCNullPowerSection
          period hPeriod parameter sector circleMode degree)
        base ih

/-- Every null-gradient power remains in the negative radial eigenbundle. -/
theorem primitiveSpinCNullGradientPowerSection_baseUnitRadial_anti_eigen
    (parameter : Complex) (sector : NormalRootChoice) (circleMode : Int)
    (degree : Nat) (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (primitiveSpinCNullGradientPowerSection
          period hPeriod parameter sector circleMode degree base) =
      -d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCNullGradientPowerSection
          period hPeriod parameter sector circleMode degree base) := by
  induction degree with
  | zero =>
      rw [primitiveSpinCNullGradientPowerSection_zero]
      exact
        primitiveSpinCNullGradient_zeroMode_baseUnitRadial_anti_eigen
          period hPeriod parameter sector circleMode base
  | succ degree ih =>
      rw [primitiveSpinCNullGradientPowerSection_succ]
      exact primitiveSpinCNullMultiplication_baseUnitRadial_anti_eigen
        period hPeriod parameter
        (primitiveSpinCNullGradientPowerSection
          period hPeriod parameter sector circleMode degree)
        base ih

/-- The scalar member of every physical null-harmonic seed has positive
radial parity. -/
theorem primitiveSpinCAllLevelNullHarmonicScalar_baseUnitRadial_eigen
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.scalarSection base) =
      d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.scalarSection base) := by
  change
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (primitiveSpinCNullPowerSection
          period hPeriod
          (primitiveSpinCNullGeometricParameter positiveLevel multiplicity)
          sector circleMode (positiveLevel + 1) base) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCNullPowerSection
          period hPeriod
          (primitiveSpinCNullGeometricParameter positiveLevel multiplicity)
          sector circleMode (positiveLevel + 1) base)
  exact primitiveSpinCNullPowerSection_baseUnitRadial_eigen
    period hPeriod
    (primitiveSpinCNullGeometricParameter positiveLevel multiplicity)
    sector circleMode (positiveLevel + 1) base

/-- The Clifford-gradient member of every physical null-harmonic seed has
negative radial parity. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_baseUnitRadial_anti_eigen
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.gradientSection base) =
      -d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.gradientSection base) := by
  rw [show
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel multiplicity sector circleMode).gradientSection =
      (primitiveSpinCAllLevelNullHarmonicSquaredSeed
        period hPeriod positiveLevel multiplicity sector circleMode
        ).gradientSection by rfl]
  rw [primitiveSpinCAllLevelNullHarmonicSquaredSeed_gradientSection]
  change
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (((positiveLevel + 1 : Nat) : Real) •
          (show D9DoubledMatterFiber from
            primitiveSpinCNullGradientPowerSection
            period hPeriod
            (primitiveSpinCNullGeometricParameter positiveLevel multiplicity)
            sector circleMode positiveLevel base)) =
      -d9PrimitiveSpinCImaginaryAction
        (((positiveLevel + 1 : Nat) : Real) •
          (show D9DoubledMatterFiber from
            primitiveSpinCNullGradientPowerSection
            period hPeriod
            (primitiveSpinCNullGeometricParameter positiveLevel multiplicity)
            sector circleMode positiveLevel base))
  rw [d9PrimitiveSpinCBaseUnitRadialClifford_real_smul,
    primitiveSpinCNullGradientPowerSection_baseUnitRadial_anti_eigen,
    smul_neg, map_smul]

/-- Smooth sections with positive radial Clifford parity. -/
def primitiveSpinCGeometricL2PositiveRadialSubmodule :
    Submodule Complex (SmoothSection period hPeriod) where
  carrier := {state | ∀ base,
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (state base) =
      d9PrimitiveSpinCImaginaryAction (state base)}
  zero_mem' := by
    intro base
    change
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          (0 : D9DoubledMatterFiber) =
        d9PrimitiveSpinCImaginaryAction (0 : D9DoubledMatterFiber)
    rw [d9PrimitiveSpinCBaseUnitRadialClifford_zero, map_zero]
  add_mem' := by
    intro first second hFirst hSecond base
    change
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          ((show D9DoubledMatterFiber from first base) +
            (show D9DoubledMatterFiber from second base)) =
        d9PrimitiveSpinCImaginaryAction
          ((show D9DoubledMatterFiber from first base) +
            (show D9DoubledMatterFiber from second base))
    rw [d9PrimitiveSpinCBaseUnitRadialClifford_add,
      hFirst base, hSecond base, map_add]
  smul_mem' := by
    intro scalar state hState base
    change
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state base) =
        d9PrimitiveSpinCImaginaryAction
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state base)
    rw [d9PrimitiveSpinCComplexScalarSection_apply,
      ← d9PrimitiveSpinCComplexAction_eq_re_add_im,
      d9PrimitiveSpinCBaseUnitRadialClifford_complexAction,
      hState base, d9PrimitiveSpinCImaginaryAction_complexAction]

/-- Smooth sections with negative radial Clifford parity. -/
def primitiveSpinCGeometricL2NegativeRadialSubmodule :
    Submodule Complex (SmoothSection period hPeriod) where
  carrier := {state | ∀ base,
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (state base) =
      -d9PrimitiveSpinCImaginaryAction (state base)}
  zero_mem' := by
    intro base
    change
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          (0 : D9DoubledMatterFiber) =
        -d9PrimitiveSpinCImaginaryAction (0 : D9DoubledMatterFiber)
    rw [d9PrimitiveSpinCBaseUnitRadialClifford_zero, map_zero, neg_zero]
  add_mem' := by
    intro first second hFirst hSecond base
    change
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          ((show D9DoubledMatterFiber from first base) +
            (show D9DoubledMatterFiber from second base)) =
        -d9PrimitiveSpinCImaginaryAction
          ((show D9DoubledMatterFiber from first base) +
            (show D9DoubledMatterFiber from second base))
    rw [d9PrimitiveSpinCBaseUnitRadialClifford_add,
      hFirst base, hSecond base, map_add, neg_add]
  smul_mem' := by
    intro scalar state hState base
    change
      d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state base) =
        -d9PrimitiveSpinCImaginaryAction
          (d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state base)
    rw [d9PrimitiveSpinCComplexScalarSection_apply,
      ← d9PrimitiveSpinCComplexAction_eq_re_add_im,
      d9PrimitiveSpinCBaseUnitRadialClifford_complexAction,
      hState base, map_neg,
      d9PrimitiveSpinCImaginaryAction_complexAction]

/-- The two pointwise radial parity submodules are algebraically disjoint. -/
theorem primitiveSpinCGeometricL2RadialSubmodules_disjoint :
    Disjoint
      (primitiveSpinCGeometricL2PositiveRadialSubmodule period hPeriod)
      (primitiveSpinCGeometricL2NegativeRadialSubmodule
        period hPeriod) := by
  rw [Submodule.disjoint_def]
  intro state hPositive hNegative
  apply DFunLike.ext state 0
  intro base
  let matter : D9DoubledMatterFiber :=
    show D9DoubledMatterFiber from state base
  have hOpposite :
      d9PrimitiveSpinCImaginaryAction matter =
        -d9PrimitiveSpinCImaginaryAction matter := by
    simpa only [matter] using
      (hPositive base).symm.trans (hNegative base)
  have hSum :
      d9PrimitiveSpinCImaginaryAction matter +
          d9PrimitiveSpinCImaginaryAction matter = 0 := by
    exact
      (congrArg
        (fun current =>
          current + d9PrimitiveSpinCImaginaryAction matter)
        hOpposite).trans
        (neg_add_cancel (d9PrimitiveSpinCImaginaryAction matter))
  have hTwice :
      (2 : Real) •
          d9PrimitiveSpinCImaginaryAction matter = 0 := by
    simpa only [two_smul] using hSum
  have hImaginary :
      d9PrimitiveSpinCImaginaryAction matter = 0 :=
    (smul_eq_zero.mp hTwice).resolve_left (by norm_num)
  have hApplied := congrArg d9PrimitiveSpinCImaginaryAction hImaginary
  rw [d9PrimitiveSpinCImaginaryAction_sq, map_zero] at hApplied
  change matter = 0
  exact neg_eq_zero.mp hApplied

/-- Every scalar null-harmonic seed lies in positive radial parity. -/
theorem primitiveSpinCAllLevelNullHarmonicScalar_mem_positiveRadial
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel multiplicity sector circleMode).scalarSection ∈
        primitiveSpinCGeometricL2PositiveRadialSubmodule
          period hPeriod :=
  primitiveSpinCAllLevelNullHarmonicScalar_baseUnitRadial_eigen
    period hPeriod positiveLevel multiplicity sector circleMode

/-- Every Clifford-gradient null-harmonic seed lies in negative radial
parity. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_mem_negativeRadial
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        positiveLevel multiplicity sector circleMode).gradientSection ∈
        primitiveSpinCGeometricL2NegativeRadialSubmodule
          period hPeriod :=
  primitiveSpinCAllLevelNullHarmonicGradient_baseUnitRadial_anti_eigen
    period hPeriod positiveLevel multiplicity sector circleMode

/-- Scalar coefficient of the radial-positive component in one signed
first-order branch. -/
def primitiveSpinCGeometricL2SignedBranchScalarCoefficient
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) : Complex :=
  ((primitiveSpinCDiracBranchSign branch *
        primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode -
      normalRootLeviCivitaCorrectedFrequency
        period sector circleMode : Real) : Complex)

/-- The scalar component of either signed branch is nonzero at every
positive sphere level. -/
theorem primitiveSpinCGeometricL2SignedBranchScalarCoefficient_ne_zero
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCGeometricL2SignedBranchScalarCoefficient
        period positiveLevel branch sector circleMode ≠ 0 := by
  unfold primitiveSpinCGeometricL2SignedBranchScalarCoefficient
  apply Complex.ofReal_ne_zero.mpr
  have hSquare :=
    primitiveSpinCHarmonicDiracFrequency_sq
      period positiveLevel sector circleMode
  have hEnergy :=
    primitiveSpinCHarmonicSphereEnergy_pos positiveLevel
  cases branch with
  | positive =>
      simp only [primitiveSpinCDiracBranchSign_positive, one_mul]
      intro hZero
      have hEqual :
          primitiveSpinCHarmonicDiracFrequency
              period positiveLevel sector circleMode =
            normalRootLeviCivitaCorrectedFrequency
              period sector circleMode :=
        sub_eq_zero.mp hZero
      rw [hEqual] at hSquare
      linarith
  | negative =>
      simp only [primitiveSpinCDiracBranchSign_negative, neg_one_mul]
      intro hZero
      have hEqual :
          primitiveSpinCHarmonicDiracFrequency
              period positiveLevel sector circleMode =
            -normalRootLeviCivitaCorrectedFrequency
              period sector circleMode := by
        linarith
      rw [hEqual] at hSquare
      nlinarith

/-- The raw signed section is exactly its nonzero scalar radial component
plus its Clifford-gradient radial component. -/
theorem primitiveSpinCGeometricL2SignedBranchRawFamily_eq_radial_components
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    primitiveSpinCGeometricL2SignedBranchRawFamily
        period hPeriod positiveLevel branch sector circleMode multiplicity =
      primitiveSpinCGeometricL2SignedBranchScalarCoefficient
          period positiveLevel branch sector circleMode •
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode).scalarSection +
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode).gradientSection := by
  cases branch <;>
    simp [primitiveSpinCGeometricL2SignedBranchRawFamily,
      primitiveSpinCGeometricL2SignedBranchMode,
      primitiveSpinCAllLevelSignedGeometricSection,
      primitiveSpinCAllLevelSignedGeometricSeed,
      primitiveSpinCGeometricL2SignedBranchScalarCoefficient,
      primitiveSpinCDiracBranchSign,
      PrimitiveSpinCHarmonicDiracSeed4D.positiveSection,
      PrimitiveSpinCHarmonicDiracSeed4D.negativeSection]

/-- Every signed branch realizes all of its expected physical multiplicity:
its canonical raw family is complex-linearly independent. -/
theorem primitiveSpinCGeometricL2SignedBranchRawFamily_linearIndependent
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    LinearIndependent Complex
      (primitiveSpinCGeometricL2SignedBranchRawFamily
        period hPeriod positiveLevel branch sector circleMode) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hRelation multiplicity
  let branchCoefficient : Complex :=
    primitiveSpinCGeometricL2SignedBranchScalarCoefficient
      period positiveLevel branch sector circleMode
  let scalarState : SmoothSection period hPeriod :=
    ∑ index,
      coefficients index •
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel index sector circleMode).scalarSection
  let gradientState : SmoothSection period hPeriod :=
    ∑ index,
      coefficients index •
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel index sector circleMode).gradientSection
  have hScalarMem :
      scalarState ∈
        primitiveSpinCGeometricL2PositiveRadialSubmodule
          period hPeriod := by
    dsimp only [scalarState]
    apply Submodule.sum_mem
    intro index _
    exact Submodule.smul_mem _ _
      (primitiveSpinCAllLevelNullHarmonicScalar_mem_positiveRadial
        period hPeriod positiveLevel index sector circleMode)
  have hGradientMem :
      gradientState ∈
        primitiveSpinCGeometricL2NegativeRadialSubmodule
          period hPeriod := by
    dsimp only [gradientState]
    apply Submodule.sum_mem
    intro index _
    exact Submodule.smul_mem _ _
      (primitiveSpinCAllLevelNullHarmonicGradient_mem_negativeRadial
        period hPeriod positiveLevel index sector circleMode)
  have hDecompose :
      branchCoefficient • scalarState + gradientState = 0 := by
    calc
      branchCoefficient • scalarState + gradientState =
          ∑ index,
            coefficients index •
              (branchCoefficient •
                  ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
                    period hPeriod).seed
                      positiveLevel index sector circleMode).scalarSection +
                ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
                  period hPeriod).seed
                    positiveLevel index sector circleMode).gradientSection) := by
        dsimp only [scalarState, gradientState]
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro index _
        rw [smul_add, smul_smul, smul_smul,
          mul_comm branchCoefficient (coefficients index)]
      _ =
          ∑ index,
            coefficients index •
              primitiveSpinCGeometricL2SignedBranchRawFamily
                period hPeriod positiveLevel branch sector circleMode
                index := by
        apply Finset.sum_congr rfl
        intro index _
        rw [
          primitiveSpinCGeometricL2SignedBranchRawFamily_eq_radial_components]
      _ = 0 := hRelation
  have hEqual :
      branchCoefficient • scalarState = -gradientState := by
    rw [eq_neg_iff_add_eq_zero]
    exact hDecompose
  have hPositive :
      branchCoefficient • scalarState ∈
        primitiveSpinCGeometricL2PositiveRadialSubmodule
          period hPeriod :=
    Submodule.smul_mem _ _ hScalarMem
  have hNegative :
      branchCoefficient • scalarState ∈
        primitiveSpinCGeometricL2NegativeRadialSubmodule
          period hPeriod := by
    rw [hEqual]
    exact Submodule.neg_mem _ hGradientMem
  have hScaledZero : branchCoefficient • scalarState = 0 :=
    Submodule.disjoint_def.mp
      (primitiveSpinCGeometricL2RadialSubmodules_disjoint
        period hPeriod)
      (branchCoefficient • scalarState)
      hPositive hNegative
  have hScalarZero : scalarState = 0 :=
    (smul_eq_zero.mp hScaledZero).resolve_left
      (primitiveSpinCGeometricL2SignedBranchScalarCoefficient_ne_zero
        period positiveLevel branch sector circleMode)
  have hScalarRelation :
      ∑ index,
          coefficients index •
            (primitiveSpinCAllLevelNullHarmonicSquaredSeed
              period hPeriod positiveLevel index sector circleMode
            ).scalarSection = 0 := by
    change scalarState = 0
    exact hScalarZero
  exact
    Fintype.linearIndependent_iff.mp
      (primitiveSpinCAllLevelNullHarmonicSquaredSeed_linearIndependent
        period hPeriod positiveLevel sector circleMode)
      coefficients hScalarRelation multiplicity

/-- Every signed branch has exactly the expected sphere multiplicity. -/
theorem primitiveSpinCGeometricL2SignedBranchBlock_finrank
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    finrank Complex
        (primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel branch sector circleMode) =
      primitiveSphereModeDegeneracy (positiveLevel + 1) := by
  unfold primitiveSpinCGeometricL2SignedBranchBlock
  simpa using
    finrank_span_eq_card
      (primitiveSpinCGeometricL2SignedBranchRawFamily_linearIndependent
        period hPeriod positiveLevel branch sector circleMode)

/-- The complete two-sign block has twice the expected sphere
multiplicity. -/
theorem primitiveSpinCGeometricL2SignedBlock_finrank
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    finrank Complex
        (primitiveSpinCGeometricL2SignedBlock
          period hPeriod positiveLevel sector circleMode) =
      2 * primitiveSphereModeDegeneracy (positiveLevel + 1) := by
  let positive :=
    primitiveSpinCGeometricL2SignedBranchBlock
      period hPeriod positiveLevel .positive sector circleMode
  let negative :=
    primitiveSpinCGeometricL2SignedBranchBlock
      period hPeriod positiveLevel .negative sector circleMode
  letI : FiniteDimensional Complex positive := by
    dsimp only [positive]
    infer_instance
  letI : FiniteDimensional Complex negative := by
    dsimp only [negative]
    infer_instance
  have hDimension :=
    Submodule.finrank_sup_add_finrank_inf_eq positive negative
  have hDisjoint : Disjoint positive negative := by
    dsimp only [positive, negative]
    exact
      primitiveSpinCGeometricL2SignedBranchBlocks_disjoint
        period hPeriod positiveLevel sector circleMode
  have hDisjointEq : positive ⊓ negative = ⊥ :=
    hDisjoint.eq_bot
  dsimp only [positive, negative] at hDimension hDisjointEq
  rw [hDisjointEq, finrank_bot,
    primitiveSpinCGeometricL2SignedBranchBlock_finrank,
    primitiveSpinCGeometricL2SignedBranchBlock_finrank] at hDimension
  rw [primitiveSpinCGeometricL2SignedBlock]
  omega

/-- Assumption-free certificate for the exact signed multiplicities. -/
structure ProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicityCertificate4D
    where
  radialSubmodulesDisjoint :
    Disjoint
      (primitiveSpinCGeometricL2PositiveRadialSubmodule period hPeriod)
      (primitiveSpinCGeometricL2NegativeRadialSubmodule period hPeriod)
  branchIndependent :
    ∀ positiveLevel branch sector circleMode,
      LinearIndependent Complex
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod positiveLevel branch sector circleMode)
  branchFinrank :
    ∀ positiveLevel branch sector circleMode,
      finrank Complex
          (primitiveSpinCGeometricL2SignedBranchBlock
            period hPeriod positiveLevel branch sector circleMode) =
        primitiveSphereModeDegeneracy (positiveLevel + 1)
  signedBlockFinrank :
    ∀ positiveLevel sector circleMode,
      finrank Complex
          (primitiveSpinCGeometricL2SignedBlock
            period hPeriod positiveLevel sector circleMode) =
        2 * primitiveSphereModeDegeneracy (positiveLevel + 1)

def programPD9PrimitiveSpinCGeometricL2SignedMultiplicityCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicityCertificate4D
      period hPeriod where
  radialSubmodulesDisjoint :=
    primitiveSpinCGeometricL2RadialSubmodules_disjoint period hPeriod
  branchIndependent :=
    primitiveSpinCGeometricL2SignedBranchRawFamily_linearIndependent
      period hPeriod
  branchFinrank :=
    primitiveSpinCGeometricL2SignedBranchBlock_finrank period hPeriod
  signedBlockFinrank :=
    primitiveSpinCGeometricL2SignedBlock_finrank period hPeriod

theorem primitiveSpinCGeometricL2SignedMultiplicity_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicityCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2SignedMultiplicityCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D
end JanusFormal
