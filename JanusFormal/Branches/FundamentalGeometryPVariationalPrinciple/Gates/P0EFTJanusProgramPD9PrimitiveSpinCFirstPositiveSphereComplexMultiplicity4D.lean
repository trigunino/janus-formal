import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalLocal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexWitnessNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereTwoWitnessAlgebra4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
import Mathlib.Tactic

/-!
# Complex multiplicity of the positive first-sphere Dirac block

The three positive first-sphere eigensections were previously proved linearly
independent over `ℝ`.  A single equatorial evaluation cannot prove complex
independence because its two tangential values are related by `Γ₁ ψ = JΓ₂ ψ`.

This gate combines two genuine geometric evaluations:

* the original phase-zero witness, which yields `c₁ - i c₂ = 0`;
* the antipodal phase-`π` witness, which yields `c₁ + i c₂ = 0`.

The radial coefficient is separated at the original witness by the occupied
normal-root component.  Faithfulness of the complex fiber action and the
injective two-witness transform then force all three complex coefficients to
vanish.  Thus the simultaneous positive synthesis `ℂ³ → Γ∞(S)` is genuinely
injective.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexWitnessNoGo4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereTwoWitnessAlgebra4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexLocalCoordinate4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
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

/-- Public phase-zero witness chart. -/
abbrev primitiveSpinCHopfPositiveWitnessIndex :
    D9PrimitiveSpinCIndex period hPeriod :=
  primitiveSpinCGeometricZeroModeWitnessIndex period hPeriod 0

/-- Public phase-zero witness quotient point. -/
abbrev primitiveSpinCHopfPositiveWitnessBase :
    ThroatBase period hPeriod :=
  primitiveSpinCGeometricZeroModeWitnessBase period hPeriod 0

/-- Local value of one positive first-sphere eigensection at the original
phase-zero witness. -/
def primitiveSpinCHopfFirstSpherePositiveWitnessLocal
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9DoubledMatterFiber :=
  primitiveSpinCGeometricSectionLocalCoordinate
    period hPeriod
    (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
    (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
    (primitiveSpinCHopfFirstSpherePositiveSection
      period hPeriod coordinate sector mode)

/-- Local value of one positive first-sphere eigensection at the antipodal
witness. -/
def primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9DoubledMatterFiber :=
  primitiveSpinCGeometricSectionLocalCoordinate
    period hPeriod
    (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
    (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
    (primitiveSpinCHopfFirstSpherePositiveSection
      period hPeriod coordinate sector mode)

/-- The occupied normal-root coefficient is complex-linear under the
transported fiber scalar action. -/
theorem primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction
    (sector : NormalRootChoice) (scalar : Complex)
    (matter : D9DoubledMatterFiber) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      scalar *
        primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          matter := by
  have hAction :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction scalar matter
  cases sector with
  | positiveQuarter =>
      have hCoordinate := congrArg
        (fun pair : AmbientHalfSpinor2 × AmbientHalfSpinor2 => pair.1 0)
        hAction
      simpa [primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap,
        d9MatterGammaPositiveCoefficientLinearMap] using hCoordinate
  | negativeQuarter =>
      have hCoordinate := congrArg
        (fun pair : AmbientHalfSpinor2 × AmbientHalfSpinor2 => pair.2 0)
        hAction
      simpa [primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap,
        d9MatterGammaPositiveCoefficientLinearMap] using hCoordinate

@[simp]
theorem d9PrimitiveSpinCComplexAction_zero_scalar
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM 0 matter = 0 := by
  rw [d9PrimitiveSpinCComplexAction_eq_re_add_im]
  simp

@[simp]
theorem d9PrimitiveSpinCComplexAction_I
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM Complex.I matter =
      d9PrimitiveSpinCImaginaryAction matter := by
  rw [d9PrimitiveSpinCComplexAction_eq_re_add_im]
  simp

@[simp]
theorem d9PrimitiveSpinCComplexAction_neg_I
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM (-Complex.I) matter =
      -d9PrimitiveSpinCImaginaryAction matter := by
  rw [d9PrimitiveSpinCComplexAction_eq_re_add_im]
  simp

/-- Local phase-zero value of the complete positive complex packet. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexPacket_local_positive
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
        (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM (coefficients 0)
          (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
            period hPeriod 0 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
            period hPeriod 2 sector mode) := by
  rw [primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_apply,
    map_sum]
  simp_rw [primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap,
    primitiveSpinCGeometricSectionLocalCoordinate_complexLine_eq_action
    period hPeriod
    (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
    (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
    (primitiveSpinCGeometricZeroModeWitnessBase_mem period hPeriod 0)]
  simp [primitiveSpinCHopfFirstSpherePositiveWitnessLocal,
    Fin.sum_univ_succ]
  abel

/-- Local antipodal value of the complete positive complex packet. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexPacket_local_antipodal
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM (coefficients 0)
          (primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
            period hPeriod 0 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
            period hPeriod 2 sector mode) := by
  rw [primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_apply,
    map_sum]
  simp_rw [primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap,
    primitiveSpinCGeometricSectionLocalCoordinate_complexLine_eq_action
    period hPeriod
    (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
    (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
    (primitiveSpinCHopfAntipodalWitnessBase_mem period hPeriod 0)]
  simp [primitiveSpinCHopfFirstSpherePositiveAntipodalLocal,
    Fin.sum_univ_succ]
  abel

/-- The original witness identifies the first tangential local value with
multiplication by `i` of the second. -/
theorem primitiveSpinCHopfFirstSpherePositiveWitnessLocal_one_eq_I_two
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSpherePositiveWitnessLocal
        period hPeriod 1 sector mode =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
          period hPeriod 2 sector mode) := by
  simpa [primitiveSpinCHopfFirstSpherePositiveWitnessLocal,
    primitiveSpinCHopfPositiveWitnessIndex,
    primitiveSpinCHopfPositiveWitnessBase] using
    (firstSpherePositiveComplexWitness_tangential_collinear
      period hPeriod sector mode)

/-- The antipodal witness identifies the first tangential local value with
multiplication by `-i` of the second. -/
theorem primitiveSpinCHopfFirstSpherePositiveAntipodalLocal_one_eq_neg_I_two
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
        period hPeriod 1 sector mode =
      d9PrimitiveSpinCComplexActionCLM (-Complex.I)
        (primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
          period hPeriod 2 sector mode) := by
  rw [primitiveSpinCHopfFirstSpherePositiveAntipodalLocal,
    primitiveSpinCHopfFirstSpherePositiveAntipodalLocal,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_one_antipodal,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_two_antipodal,
    d9PrimitiveSpinCComplexAction_neg_I]
  exact primitiveSpinCHopfFirstSphereAntipodalTangential_relation
    period hPeriod sector mode

/-- The second tangential local value at the original witness is nonzero. -/
theorem primitiveSpinCHopfFirstSpherePositiveWitnessLocal_two_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSpherePositiveWitnessLocal
        period hPeriod 2 sector mode ≠ 0 := by
  rw [primitiveSpinCHopfFirstSpherePositiveWitnessLocal,
    primitiveSpinCHopfPositiveWitnessIndex,
    primitiveSpinCHopfPositiveWitnessBase,
    firstSpherePositiveLocalCoordinate_two]
  exact clifford_witnessMode_ne_zero period hPeriod 2 sector mode

/-- The second tangential local value at the antipodal witness is nonzero. -/
theorem primitiveSpinCHopfFirstSpherePositiveAntipodalLocal_two_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
        period hPeriod 2 sector mode ≠ 0 := by
  rw [primitiveSpinCHopfFirstSpherePositiveAntipodalLocal,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_two_antipodal]
  exact primitiveSpinCHopfAntipodalValue_gammaTwo_ne_zero
    period hPeriod sector mode

/-- Vanishing at the phase and antipodal local witnesses already separates
all three positive complex multiplicity coefficients. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexPacketLocal_eq_zero_coefficients
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients)
    (hPositiveLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
          (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
          (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode coefficients) = 0)
    (hAntipodalLocal :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
          (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode coefficients) = 0) :
    coefficients = 0 := by
  rw [primitiveSpinCHopfFirstSpherePositiveComplexPacket_local_positive]
    at hPositiveLocal
  rw [primitiveSpinCHopfFirstSpherePositiveComplexPacket_local_antipodal]
    at hAntipodalLocal
  have hSector := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector)
    hPositiveLocal
  simp only [map_add, map_zero,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction]
    at hSector
  have hRadialValue :
      primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
            period hPeriod 0 sector mode) =
        (primitiveSpinCHopfFirstSpherePositiveRadialCoefficient
          period sector mode : Complex) := by
    rw [primitiveSpinCHopfFirstSpherePositiveWitnessLocal,
      primitiveSpinCHopfPositiveWitnessIndex,
      primitiveSpinCHopfPositiveWitnessBase,
      firstSpherePositiveLocalCoordinate_zero,
      map_smul, map_smul, witnessMode_sectorCoefficient]
    norm_num [primitiveSpinCHopfFirstSpherePositiveRadialCoefficient]
    ring
  have hOneValue :
      primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
            period hPeriod 1 sector mode) = 0 := by
    rw [primitiveSpinCHopfFirstSpherePositiveWitnessLocal,
      primitiveSpinCHopfPositiveWitnessIndex,
      primitiveSpinCHopfPositiveWitnessBase,
      firstSpherePositiveLocalCoordinate_one,
      map_smul, map_smul, witnessMode_gamma_one_sectorCoefficient]
    simp
  have hTwoValue :
      primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
            period hPeriod 2 sector mode) = 0 := by
    rw [primitiveSpinCHopfFirstSpherePositiveWitnessLocal,
      primitiveSpinCHopfPositiveWitnessIndex,
      primitiveSpinCHopfPositiveWitnessBase,
      firstSpherePositiveLocalCoordinate_two,
      map_smul, map_smul, witnessMode_gamma_two_sectorCoefficient]
    simp
  have hRadialProduct :
      coefficients 0 *
          (primitiveSpinCHopfFirstSpherePositiveRadialCoefficient
            period sector mode : Complex) = 0 := by
    rw [hRadialValue, hOneValue, hTwoValue] at hSector
    simpa using hSector
  have hRadialNonzero :
      (primitiveSpinCHopfFirstSpherePositiveRadialCoefficient
        period sector mode : Complex) ≠ 0 := by
    exact_mod_cast
      primitiveSpinCHopfFirstSpherePositiveRadialCoefficient_ne_zero
        period sector mode
  have hZero : coefficients 0 = 0 :=
    (mul_eq_zero.mp hRadialProduct).resolve_right hRadialNonzero
  have hPositiveTangential :
      d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
            period hPeriod 2 sector mode) = 0 := by
    simpa [hZero] using hPositiveLocal
  rw [primitiveSpinCHopfFirstSpherePositiveWitnessLocal_one_eq_I_two,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_add_scalar] at hPositiveTangential
  have hPositiveScalar :
      coefficients 1 * Complex.I + coefficients 2 = 0 :=
    (d9PrimitiveSpinCComplexAction_eq_zero_iff
      (coefficients 1 * Complex.I + coefficients 2)
      (primitiveSpinCHopfFirstSpherePositiveWitnessLocal
        period hPeriod 2 sector mode)
      (primitiveSpinCHopfFirstSpherePositiveWitnessLocal_two_ne_zero
        period hPeriod sector mode)).mp hPositiveTangential
  have hMinus :
      coefficients 1 - Complex.I * coefficients 2 = 0 := by
    calc
      coefficients 1 - Complex.I * coefficients 2 =
          (-Complex.I) *
            (coefficients 1 * Complex.I + coefficients 2) := by
        ring_nf <;> simp [Complex.I_sq]
      _ = 0 := by rw [hPositiveScalar]; ring
  have hAntipodalTangential :
      d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
            period hPeriod 2 sector mode) = 0 := by
    simpa [hZero] using hAntipodalLocal
  rw [primitiveSpinCHopfFirstSpherePositiveAntipodalLocal_one_eq_neg_I_two,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_add_scalar] at hAntipodalTangential
  have hAntipodalScalar :
      coefficients 1 * (-Complex.I) + coefficients 2 = 0 :=
    (d9PrimitiveSpinCComplexAction_eq_zero_iff
      (coefficients 1 * (-Complex.I) + coefficients 2)
      (primitiveSpinCHopfFirstSpherePositiveAntipodalLocal
        period hPeriod 2 sector mode)
      (primitiveSpinCHopfFirstSpherePositiveAntipodalLocal_two_ne_zero
        period hPeriod sector mode)).mp hAntipodalTangential
  have hPlus :
      coefficients 1 + Complex.I * coefficients 2 = 0 := by
    calc
      coefficients 1 + Complex.I * coefficients 2 =
          Complex.I *
            (coefficients 1 * (-Complex.I) + coefficients 2) := by
        ring_nf <;> simp [Complex.I_sq]
      _ = 0 := by rw [hAntipodalScalar]; ring
  exact primitiveSpinCFirstSphereTwoWitness_vanishing
    coefficients hZero hPlus hMinus

/-- Vanishing of the positive complex packet forces every complex
multiplicity coefficient to vanish. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_eq_zero_coefficients
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients)
    (hSynthesis :
      primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
        period hPeriod sector mode coefficients = 0) :
    coefficients = 0 := by
  apply
    primitiveSpinCHopfFirstSpherePositiveComplexPacketLocal_eq_zero_coefficients
      period hPeriod sector mode coefficients
  · rw [hSynthesis, map_zero]
  · rw [hSynthesis, map_zero]

/-- The complete positive first-sphere complex synthesis is injective. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_injective
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
      (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
        period hPeriod sector mode) := by
  intro first second hEqual
  apply sub_eq_zero.mp
  apply
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_eq_zero_coefficients
      period hPeriod sector mode (first - second)
  rw [map_sub, hEqual, sub_self]

/-- The positive first-sphere eigenspace now has three faithful complex
geometric coordinates, not merely three real coordinates. -/
def primitiveSpinCHopfFirstSpherePositiveComplexCoordinateEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCFirstSphereComplexCoefficients ≃ₗ[Real]
      LinearMap.range
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode) :=
  LinearEquiv.ofInjective
    (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
      period hPeriod sector mode)
    (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_injective
      period hPeriod sector mode)

/-- Consolidated positive complex multiplicity theorem. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexMultiplicity_closed
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode) ∧
      (∀ coefficients,
        primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode coefficients = 0 →
          coefficients = 0) :=
  ⟨primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_injective
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_eq_zero_coefficients
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
end JanusFormal
