import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

/-!
# Complex signed packet for the first positive sphere level

The global complex structure supplies one faithful complex line for each of
the three positive and three negative geometric coordinate eigensections.
This gate assembles those lines into finite complex packets and proves exact
intertwining with the genuine differential Dirac operator.

No injectivity of the simultaneous three-coordinate complex synthesis is
asserted: that remaining statement is precisely the joint complex
independence problem, stronger than the coordinatewise faithfulness proved in
the preceding gate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Complex coefficients for the three constructed multiplicities of one
internal Dirac sign. -/
abbrev PrimitiveSpinCFirstSphereComplexCoefficients :=
  Fin 3 → Complex

/-- The actual positive-quarter geometric Dirac operator distributes over
every finite sum of genuine smooth sections. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_finset_sum
    {ι : Type} [DecidableEq ι]
    (states : ι →
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter)
    (indices : Finset ι) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (∑ index ∈ indices, states index) =
      ∑ index ∈ indices,
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter (states index) := by
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty,
        d9PrimitiveSpinCGeometricDiracOperator_zero]
  | @insert index tail hIndex inductionHypothesis =>
      simp only [Finset.sum_insert hIndex,
        d9PrimitiveSpinCGeometricDiracOperator_add,
        inductionHypothesis]

/-- Simultaneous positive-branch synthesis of the three complex coordinate
lines. -/
def primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCFirstSphereComplexCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter where
  toFun coefficients :=
    ∑ coordinate : Fin 3,
      primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
        period hPeriod coordinate sector mode (coefficients coordinate)
  map_add' first second := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_apply
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
        period hPeriod sector mode coefficients =
      ∑ coordinate : Fin 3,
        primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
          period hPeriod coordinate sector mode (coefficients coordinate) :=
  rfl

/-- Simultaneous negative-branch synthesis of the three complex coordinate
lines. -/
def primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCFirstSphereComplexCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter where
  toFun coefficients :=
    ∑ coordinate : Fin 3,
      primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
        period hPeriod coordinate sector mode (coefficients coordinate)
  map_add' first second := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_apply
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
        period hPeriod sector mode coefficients =
      ∑ coordinate : Fin 3,
        primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
          period hPeriod coordinate sector mode (coefficients coordinate) :=
  rfl

/-- Every finite positive complex packet is an actual eigensection with the
positive first-sphere eigenvalue. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_eigen
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
        primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode coefficients := by
  rw [primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_apply,
    d9PrimitiveSpinCGeometricDiracOperator_finset_sum]
  simp_rw [
    primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap_eigen]
  rw [Finset.smul_sum]

/-- Every finite negative complex packet is an actual eigensection with the
negative first-sphere eigenvalue. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_eigen
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
        primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode coefficients := by
  rw [primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_apply,
    d9PrimitiveSpinCGeometricDiracOperator_finset_sum]
  simp_rw [
    primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap_eigen]
  rw [Finset.smul_sum]

/-- Complex coefficients for both internal Dirac signs. -/
abbrev PrimitiveSpinCFirstSphereSignedComplexCoefficients :=
  PrimitiveSpinCFirstSphereComplexCoefficients ×
    PrimitiveSpinCFirstSphereComplexCoefficients

/-- Simultaneous complex synthesis of both first-sphere internal signs. -/
def primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCFirstSphereSignedComplexCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter where
  toFun coefficients :=
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
        period hPeriod sector mode coefficients.1 +
      primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
        period hPeriod sector mode coefficients.2
  map_add' first second := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    module
  map_smul' scalar coefficients := by
    change
      primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode (scalar • coefficients.1) +
          primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode (scalar • coefficients.2) =
        scalar •
          (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
              period hPeriod sector mode coefficients.1 +
            primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
              period hPeriod sector mode coefficients.2)
    rw [map_smul, map_smul, smul_add]

@[simp]
theorem primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
        period hPeriod sector mode coefficients =
      primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode coefficients.1 +
        primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode coefficients.2 :=
  rfl

/-- Explicit signed Dirac diagonal on the complex first-sphere coefficient
packet. -/
def primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCFirstSphereSignedComplexCoefficients →ₗ[Real]
      PrimitiveSpinCFirstSphereSignedComplexCoefficients where
  toFun coefficients :=
    (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
        coefficients.1,
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
        coefficients.2)
  map_add' first second := by
    apply Prod.ext
    · change
        primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
            (first.1 + second.1) =
          primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
              first.1 +
            primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
              second.1
      exact smul_add _ _ _
    · change
        (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
            (first.2 + second.2) =
          (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
              first.2 +
            (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
              second.2
      exact smul_add _ _ _
  map_smul' scalar coefficients := by
    apply Prod.ext
    · change
        primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
            (scalar • coefficients.1) =
          scalar •
            (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
              coefficients.1)
      rw [smul_smul, smul_smul, mul_comm]
    · change
        (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
            (scalar • coefficients.2) =
          scalar •
            ((-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
              coefficients.2)
      rw [smul_smul, smul_smul, mul_comm]

@[simp]
theorem primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_apply
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
        period sector mode coefficients =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
          coefficients.1,
        (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
          coefficients.2) :=
  rfl

/-- The genuine differential Dirac operator intertwines the simultaneous
complex synthesis with the explicit signed coefficient diagonal. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode coefficients) =
      primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
        period hPeriod sector mode
        (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode coefficients) := by
  rw [primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_eigen,
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_eigen,
    primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_apply,
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    map_smul, map_smul]

/-- Squaring the signed complex coefficient diagonal removes the internal
sign and gives the actual first-sphere squared eigenvalue. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_sq
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode
          (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode coefficients) =
      (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2) •
        coefficients := by
  let frequency :=
    primitiveSpinCHopfFirstSphereDiracFrequency period sector mode
  have hFrequencySq :
      frequency ^ 2 =
        normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2 := by
    simpa [frequency] using
      primitiveSpinCHopfFirstSphereDiracFrequency_sq period sector mode
  apply Prod.ext
  · change frequency • (frequency • coefficients.1) =
      (normalRootLeviCivitaCorrectedFrequency
        period sector mode ^ 2 + 2) • coefficients.1
    rw [smul_smul]
    rw [← pow_two, hFrequencySq]
  · change (-frequency) • ((-frequency) • coefficients.2) =
      (normalRootLeviCivitaCorrectedFrequency
        period sector mode ^ 2 + 2) • coefficients.2
    rw [smul_smul]
    have hNegativeSq : (-frequency) * (-frequency) = frequency ^ 2 := by
      ring
    rw [hNegativeSq, hFrequencySq]

/-- The square of the genuine differential Dirac operator intertwines with
the unsigned first-sphere diagonal on every complex packet. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac_sq
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients)) =
      primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
        period hPeriod sector mode
        ((normalRootLeviCivitaCorrectedFrequency
          period sector mode ^ 2 + 2) • coefficients) := by
  rw [primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac,
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac,
    primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_sq]

/-- The geometric range of the simultaneous complex first-sphere synthesis. -/
abbrev PrimitiveSpinCHopfFirstSphereSignedComplexSpan
    (sector : NormalRootChoice) (mode : Int) :=
  LinearMap.range
    (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
      period hPeriod sector mode)

/-- The actual Dirac operator preserves the complex first-sphere span. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexSpan_dirac_mem
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1 ∈
      PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode := by
  rcases state.property with ⟨coefficients, hCoefficients⟩
  refine ⟨primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
    period sector mode coefficients, ?_⟩
  rw [← hCoefficients]
  exact
    (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac
      period hPeriod sector mode coefficients).symm

/-- Restricted actual Dirac operator on the invariant complex packet range. -/
def primitiveSpinCHopfFirstSphereSignedComplexActualDirac
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode →ₗ[Real]
      PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode where
  toFun state :=
    ⟨d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1,
      primitiveSpinCHopfFirstSphereSignedComplexSpan_dirac_mem
        period hPeriod sector mode state⟩
  map_add' first second := by
    apply Subtype.ext
    change
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter (first.1 + second.1) =
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter first.1 +
          d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter second.1
    exact d9PrimitiveSpinCGeometricDiracOperator_add
      period hPeriod first.1 second.1
  map_smul' scalar state := by
    apply Subtype.ext
    change
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter (scalar • state.1) =
        scalar •
          d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter state.1
    exact d9PrimitiveSpinCGeometricDiracOperator_real_smul
      period hPeriod .positiveQuarter scalar state.1

/-- Consolidated complex first-sphere packet result.  The synthesis and its
range are geometrically correct and Dirac-invariant; joint coefficient
faithfulness remains the next explicit theorem. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexPacket_closed
    (sector : NormalRootChoice) (mode : Int) :
    (∀ coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients,
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients) =
        primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode
          (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode coefficients)) ∧
      (∀ state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
          period hPeriod sector mode,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter state.1 ∈
          PrimitiveSpinCHopfFirstSphereSignedComplexSpan
            period hPeriod sector mode) :=
  ⟨primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSphereSignedComplexSpan_dirac_mem
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
end JanusFormal
