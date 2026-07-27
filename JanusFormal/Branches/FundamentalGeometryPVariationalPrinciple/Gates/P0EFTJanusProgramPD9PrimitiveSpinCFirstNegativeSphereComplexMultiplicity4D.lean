import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D

/-!
# Complex multiplicity of the negative first-sphere Dirac block

The negative internal Dirac branch has the same two tangential witness values
as the positive branch.  Its only changed local coefficient is the radial
factor `2(-λ-k)`, already proved nonzero.  The phase-zero and antipodal
witnesses therefore yield the same two opposite complex equations and force
all three complex multiplicity coefficients to vanish.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstNegativeSphereComplexMultiplicity4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
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

/-- Local value of one negative first-sphere eigensection at the original
phase-zero witness. -/
def primitiveSpinCHopfFirstSphereNegativeWitnessLocal
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9DoubledMatterFiber :=
  primitiveSpinCGeometricSectionLocalCoordinate
    period hPeriod
    (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
    (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
    (primitiveSpinCHopfFirstSphereNegativeSection
      period hPeriod coordinate sector mode)

/-- Local value of one negative first-sphere eigensection at the antipodal
witness. -/
def primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9DoubledMatterFiber :=
  primitiveSpinCGeometricSectionLocalCoordinate
    period hPeriod
    (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
    (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
    (primitiveSpinCHopfFirstSphereNegativeSection
      period hPeriod coordinate sector mode)

/-- Local phase-zero value of the complete negative complex packet. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexPacket_local_positive
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
        (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM (coefficients 0)
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 0 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 2 sector mode) := by
  rw [primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_apply,
    map_sum]
  simp_rw [primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap,
    primitiveSpinCGeometricSectionLocalCoordinate_complexLine_eq_action
    period hPeriod
    (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
    (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
    (primitiveSpinCGeometricZeroModeWitnessBase_mem period hPeriod 0)]
  simp [primitiveSpinCHopfFirstSphereNegativeWitnessLocal,
    Fin.sum_univ_succ]
  abel

/-- Local antipodal value of the complete negative complex packet. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexPacket_local_antipodal
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      d9PrimitiveSpinCComplexActionCLM (coefficients 0)
          (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
            period hPeriod 0 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
            period hPeriod 2 sector mode) := by
  rw [primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_apply,
    map_sum]
  simp_rw [primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap,
    primitiveSpinCGeometricSectionLocalCoordinate_complexLine_eq_action
    period hPeriod
    (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
    (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
    (primitiveSpinCHopfAntipodalWitnessBase_mem period hPeriod 0)]
  simp [primitiveSpinCHopfFirstSphereNegativeAntipodalLocal,
    Fin.sum_univ_succ]
  abel

/-- The original witness identifies the first negative tangential local value
with multiplication by `i` of the second. -/
theorem primitiveSpinCHopfFirstSphereNegativeWitnessLocal_one_eq_I_two
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereNegativeWitnessLocal
        period hPeriod 1 sector mode =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
          period hPeriod 2 sector mode) := by
  simpa [primitiveSpinCHopfFirstSphereNegativeWitnessLocal,
    primitiveSpinCHopfPositiveWitnessIndex,
    primitiveSpinCHopfPositiveWitnessBase] using
    (firstSphereNegativeComplexWitness_tangential_collinear
      period hPeriod sector mode)

/-- The antipodal witness identifies the first negative tangential local value
with multiplication by `-i` of the second. -/
theorem primitiveSpinCHopfFirstSphereNegativeAntipodalLocal_one_eq_neg_I_two
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
        period hPeriod 1 sector mode =
      d9PrimitiveSpinCComplexActionCLM (-Complex.I)
        (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
          period hPeriod 2 sector mode) := by
  rw [primitiveSpinCHopfFirstSphereNegativeAntipodalLocal,
    primitiveSpinCHopfFirstSphereNegativeAntipodalLocal,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_one_antipodal,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_two_antipodal,
    d9PrimitiveSpinCComplexAction_neg_I]
  exact primitiveSpinCHopfFirstSphereAntipodalTangential_relation
    period hPeriod sector mode

/-- The second negative tangential local value at the original witness is
nonzero. -/
theorem primitiveSpinCHopfFirstSphereNegativeWitnessLocal_two_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereNegativeWitnessLocal
        period hPeriod 2 sector mode ≠ 0 := by
  rw [primitiveSpinCHopfFirstSphereNegativeWitnessLocal,
    primitiveSpinCHopfPositiveWitnessIndex,
    primitiveSpinCHopfPositiveWitnessBase,
    firstSphereNegativeLocalCoordinate_two]
  exact clifford_witnessMode_ne_zero period hPeriod 2 sector mode

/-- The second negative tangential local value at the antipodal witness is
nonzero. -/
theorem primitiveSpinCHopfFirstSphereNegativeAntipodalLocal_two_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
        period hPeriod 2 sector mode ≠ 0 := by
  rw [primitiveSpinCHopfFirstSphereNegativeAntipodalLocal,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_two_antipodal]
  exact primitiveSpinCHopfAntipodalValue_gammaTwo_ne_zero
    period hPeriod sector mode

/-- Vanishing at the phase and antipodal local witnesses already separates
all three negative complex multiplicity coefficients. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexPacketLocal_eq_zero_coefficients
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients)
    (hPositiveEvaluation :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfPositiveWitnessIndex period hPeriod)
          (primitiveSpinCHopfPositiveWitnessBase period hPeriod)
          (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode coefficients) = 0)
    (hAntipodalEvaluation :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
          (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode coefficients) = 0) :
    coefficients = 0 := by
  have hPositiveLocal :
      d9PrimitiveSpinCComplexActionCLM (coefficients 0)
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 0 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 2 sector mode) = 0 := by
    simpa only [
      primitiveSpinCHopfFirstSphereNegativeComplexPacket_local_positive]
      using hPositiveEvaluation
  have hSector := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector)
    hPositiveLocal
  simp only [map_add, map_zero,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction]
    at hSector
  have hRadialValue :
      primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 0 sector mode) =
        (primitiveSpinCHopfFirstSphereNegativeRadialCoefficient
          period sector mode : Complex) := by
    rw [primitiveSpinCHopfFirstSphereNegativeWitnessLocal,
      primitiveSpinCHopfPositiveWitnessIndex,
      primitiveSpinCHopfPositiveWitnessBase,
      firstSphereNegativeLocalCoordinate_zero,
      map_smul, map_smul, witnessMode_sectorCoefficient]
    norm_num [primitiveSpinCHopfFirstSphereNegativeRadialCoefficient]
    ring
  have hOneValue :
      primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 1 sector mode) = 0 := by
    rw [primitiveSpinCHopfFirstSphereNegativeWitnessLocal,
      primitiveSpinCHopfPositiveWitnessIndex,
      primitiveSpinCHopfPositiveWitnessBase,
      firstSphereNegativeLocalCoordinate_one,
      map_smul, map_smul, witnessMode_gamma_one_sectorCoefficient]
    simp
  have hTwoValue :
      primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 2 sector mode) = 0 := by
    rw [primitiveSpinCHopfFirstSphereNegativeWitnessLocal,
      primitiveSpinCHopfPositiveWitnessIndex,
      primitiveSpinCHopfPositiveWitnessBase,
      firstSphereNegativeLocalCoordinate_two,
      map_smul, map_smul, witnessMode_gamma_two_sectorCoefficient]
    simp
  have hRadialProduct :
      coefficients 0 *
          (primitiveSpinCHopfFirstSphereNegativeRadialCoefficient
            period sector mode : Complex) = 0 := by
    rw [hRadialValue, hOneValue, hTwoValue] at hSector
    simpa using hSector
  have hRadialNonzero :
      (primitiveSpinCHopfFirstSphereNegativeRadialCoefficient
        period sector mode : Complex) ≠ 0 := by
    exact_mod_cast
      primitiveSpinCHopfFirstSphereNegativeRadialCoefficient_ne_zero
        period sector mode
  have hZero : coefficients 0 = 0 :=
    (mul_eq_zero.mp hRadialProduct).resolve_right hRadialNonzero
  have hPositiveTangential :
      d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
            period hPeriod 2 sector mode) = 0 := by
    simpa [hZero] using hPositiveLocal
  rw [primitiveSpinCHopfFirstSphereNegativeWitnessLocal_one_eq_I_two,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_add_scalar] at hPositiveTangential
  have hPositiveScalar :
      coefficients 1 * Complex.I + coefficients 2 = 0 :=
    (d9PrimitiveSpinCComplexAction_eq_zero_iff
      (coefficients 1 * Complex.I + coefficients 2)
      (primitiveSpinCHopfFirstSphereNegativeWitnessLocal
        period hPeriod 2 sector mode)
      (primitiveSpinCHopfFirstSphereNegativeWitnessLocal_two_ne_zero
        period hPeriod sector mode)).mp hPositiveTangential
  have hMinus :
      coefficients 1 - Complex.I * coefficients 2 = 0 := by
    calc
      coefficients 1 - Complex.I * coefficients 2 =
          (-Complex.I) *
            (coefficients 1 * Complex.I + coefficients 2) := by
        ring_nf <;> simp [Complex.I_sq]
      _ = 0 := by rw [hPositiveScalar]; ring
  have hAntipodalLocal :
      d9PrimitiveSpinCComplexActionCLM (coefficients 0)
          (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
            period hPeriod 0 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
            period hPeriod 2 sector mode) = 0 := by
    simpa only [
      primitiveSpinCHopfFirstSphereNegativeComplexPacket_local_antipodal]
      using hAntipodalEvaluation
  have hAntipodalTangential :
      d9PrimitiveSpinCComplexActionCLM (coefficients 1)
          (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
            period hPeriod 1 sector mode) +
        d9PrimitiveSpinCComplexActionCLM (coefficients 2)
          (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
            period hPeriod 2 sector mode) = 0 := by
    simpa [hZero] using hAntipodalLocal
  rw [primitiveSpinCHopfFirstSphereNegativeAntipodalLocal_one_eq_neg_I_two,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_add_scalar] at hAntipodalTangential
  have hAntipodalScalar :
      coefficients 1 * (-Complex.I) + coefficients 2 = 0 :=
    (d9PrimitiveSpinCComplexAction_eq_zero_iff
      (coefficients 1 * (-Complex.I) + coefficients 2)
      (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal
        period hPeriod 2 sector mode)
      (primitiveSpinCHopfFirstSphereNegativeAntipodalLocal_two_ne_zero
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

/-- Vanishing of the negative complex packet forces every complex
multiplicity coefficient to vanish. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_eq_zero_coefficients
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients)
    (hSynthesis :
      primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
        period hPeriod sector mode coefficients = 0) :
    coefficients = 0 := by
  apply
    primitiveSpinCHopfFirstSphereNegativeComplexPacketLocal_eq_zero_coefficients
      period hPeriod sector mode coefficients
  · rw [hSynthesis, map_zero]
  · rw [hSynthesis, map_zero]

/-- The complete negative first-sphere complex synthesis is injective. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_injective
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
      (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
        period hPeriod sector mode) := by
  intro first second hEqual
  apply sub_eq_zero.mp
  apply
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_eq_zero_coefficients
      period hPeriod sector mode (first - second)
  rw [map_sub, hEqual, sub_self]

/-- The negative first-sphere eigenspace has three faithful complex geometric
coordinates. -/
def primitiveSpinCHopfFirstSphereNegativeComplexCoordinateEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCFirstSphereComplexCoefficients ≃ₗ[Real]
      LinearMap.range
        (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode) :=
  LinearEquiv.ofInjective
    (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
      period hPeriod sector mode)
    (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_injective
      period hPeriod sector mode)

/-- Consolidated negative complex multiplicity theorem. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexMultiplicity_closed
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
        (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode) ∧
      (∀ coefficients,
        primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode coefficients = 0 →
          coefficients = 0) :=
  ⟨primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_injective
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_eq_zero_coefficients
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstNegativeSphereComplexMultiplicity4D
end JanusFormal
