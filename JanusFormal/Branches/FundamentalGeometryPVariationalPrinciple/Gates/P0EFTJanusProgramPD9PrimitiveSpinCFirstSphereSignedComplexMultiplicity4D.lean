import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstNegativeSphereComplexMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexAutomorphism4D

/-!
# Signed complex multiplicity of the first primitive SpinC sphere level

The two internal Dirac signs now each have a faithful geometric synthesis from
`ℂ³`.  Their actual smooth-section ranges have eigenvalues `+λ` and `-λ`, and
`λ > 0`; hence the ranges are disjoint even though each has twice the real
dimension of the earlier real seed block.

Adding the two ranges therefore gives a faithful signed synthesis

`ℂ³ × ℂ³ → Γ∞(S)`.

The resulting linear equivalence identifies the actual restricted
differential Dirac operator with the explicit signed coefficient diagonal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereSignedComplexMultiplicity4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstNegativeSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Actual smooth-section range of the positive complex packet. -/
abbrev PrimitiveSpinCHopfFirstSpherePositiveComplexSpan
    (sector : NormalRootChoice) (mode : Int) :=
  LinearMap.range
    (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
      period hPeriod sector mode)

/-- Actual smooth-section range of the negative complex packet. -/
abbrev PrimitiveSpinCHopfFirstSphereNegativeComplexSpan
    (sector : NormalRootChoice) (mode : Int) :=
  LinearMap.range
    (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
      period hPeriod sector mode)

/-- Every state in the positive complex range is a genuine positive
first-order Dirac eigensection. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexSpan_eigen
    {sector : NormalRootChoice} {mode : Int}
    (state : PrimitiveSpinCHopfFirstSpherePositiveComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1 =
      primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
        state.1 := by
  rcases state.property with ⟨coefficients, hCoefficients⟩
  rw [← hCoefficients]
  exact primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_eigen
    period hPeriod sector mode coefficients

/-- Every state in the negative complex range is a genuine negative
first-order Dirac eigensection. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexSpan_eigen
    {sector : NormalRootChoice} {mode : Int}
    (state : PrimitiveSpinCHopfFirstSphereNegativeComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1 =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
        state.1 := by
  rcases state.property with ⟨coefficients, hCoefficients⟩
  rw [← hCoefficients]
  exact primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_eigen
    period hPeriod sector mode coefficients

/-- The positive and negative complex geometric ranges are disjoint because
their first-order eigenvalues are opposite and nonzero. -/
theorem primitiveSpinCHopfFirstSpherePositiveNegativeComplex_disjoint
    (sector : NormalRootChoice) (mode : Int) :
    Disjoint
      (PrimitiveSpinCHopfFirstSpherePositiveComplexSpan
        period hPeriod sector mode)
      (PrimitiveSpinCHopfFirstSphereNegativeComplexSpan
        period hPeriod sector mode) := by
  apply Submodule.disjoint_def.mpr
  intro state hPositive hNegative
  let positiveState : PrimitiveSpinCHopfFirstSpherePositiveComplexSpan
      period hPeriod sector mode := ⟨state, hPositive⟩
  let negativeState : PrimitiveSpinCHopfFirstSphereNegativeComplexSpan
      period hPeriod sector mode := ⟨state, hNegative⟩
  have hPositiveEigen :=
    primitiveSpinCHopfFirstSpherePositiveComplexSpan_eigen
      period hPeriod positiveState
  have hNegativeEigen :=
    primitiveSpinCHopfFirstSphereNegativeComplexSpan_eigen
      period hPeriod negativeState
  let frequency :=
    primitiveSpinCHopfFirstSphereDiracFrequency period sector mode
  have hFrequency : frequency ≠ 0 :=
    ne_of_gt
      (primitiveSpinCHopfFirstSphereDiracFrequency_pos
        period sector mode)
  have hTwiceFrequency : (2 * frequency) ≠ 0 :=
    mul_ne_zero (by norm_num) hFrequency
  have hScaled : (2 * frequency) • state = 0 := by
    calc
      (2 * frequency) • state =
          frequency • state - (-frequency) • state := by module
      _ = 0 := by
        change
          frequency • positiveState.1 -
            (-frequency) • negativeState.1 = 0
        rw [← hPositiveEigen, ← hNegativeEigen]
        exact sub_self _
  exact (smul_eq_zero.mp hScaled).resolve_left hTwiceFrequency

/-- The complete simultaneous signed complex synthesis is injective. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_injective
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
      (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
        period hPeriod sector mode) := by
  intro first second hEqual
  let firstPositive :=
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
      period hPeriod sector mode first.1
  let secondPositive :=
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
      period hPeriod sector mode second.1
  let firstNegative :=
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
      period hPeriod sector mode first.2
  let secondNegative :=
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
      period hPeriod sector mode second.2
  have hDifference : firstPositive - secondPositive =
      secondNegative - firstNegative := by
    change firstPositive + firstNegative = secondPositive + secondNegative
      at hEqual
    calc
      firstPositive - secondPositive =
          (firstPositive + firstNegative) -
            (secondPositive + firstNegative) := by abel
      _ = (secondPositive + secondNegative) -
            (secondPositive + firstNegative) := by rw [hEqual]
      _ = secondNegative - firstNegative := by abel
  have hPositiveMem : firstPositive - secondPositive ∈
      PrimitiveSpinCHopfFirstSpherePositiveComplexSpan
        period hPeriod sector mode := by
    exact Submodule.sub_mem _
      ⟨first.1, rfl⟩ ⟨second.1, rfl⟩
  have hNegativeMem : firstPositive - secondPositive ∈
      PrimitiveSpinCHopfFirstSphereNegativeComplexSpan
        period hPeriod sector mode := by
    rw [hDifference]
    exact Submodule.sub_mem _
      ⟨second.2, rfl⟩ ⟨first.2, rfl⟩
  have hPositiveZero : firstPositive - secondPositive = 0 :=
    (Submodule.disjoint_def.mp
      (primitiveSpinCHopfFirstSpherePositiveNegativeComplex_disjoint
        period hPeriod sector mode))
      (firstPositive - secondPositive) hPositiveMem hNegativeMem
  have hNegativeZero : secondNegative - firstNegative = 0 := by
    rw [← hDifference]
    exact hPositiveZero
  have hFirst : first.1 = second.1 := by
    apply primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_injective
      period hPeriod sector mode
    exact sub_eq_zero.mp hPositiveZero
  have hSecond : first.2 = second.2 := by
    apply primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_injective
      period hPeriod sector mode
    exact (sub_eq_zero.mp hNegativeZero).symm
  exact Prod.ext hFirst hSecond

/-- Exact signed complex coordinates on the actual geometric first-sphere
range. -/
def primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCFirstSphereSignedComplexCoefficients ≃ₗ[Real]
      PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode :=
  LinearEquiv.ofInjective
    (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
      period hPeriod sector mode)
    (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_injective
      period hPeriod sector mode)

@[simp]
theorem primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv_coe
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    ((primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
        period hPeriod sector mode coefficients :
      PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode) :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) =
      primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
        period hPeriod sector mode coefficients :=
  rfl

/-- On exact signed complex coordinates, the actual restricted differential
Dirac operator is the explicit signed coefficient diagonal. -/
@[simp]
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDirac_synthesisEquiv
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac
        period hPeriod sector mode
        (primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
          period hPeriod sector mode coefficients) =
      primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
        period hPeriod sector mode
        (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode coefficients) := by
  apply Subtype.ext
  exact
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac
      period hPeriod sector mode coefficients

/-- Exact conjugacy of the actual first-sphere Dirac restriction with the
signed complex coefficient diagonal. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexActualDirac_conjugate
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac
        period hPeriod sector mode =
      (primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
          period hPeriod sector mode).toLinearMap.comp
        ((primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode).comp
          (primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
            period hPeriod sector mode).symm.toLinearMap) := by
  apply LinearMap.ext
  intro state
  rcases (primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
    period hPeriod sector mode).surjective state with ⟨coefficients, rfl⟩
  rw [primitiveSpinCHopfFirstSphereSignedComplexActualDirac_synthesisEquiv]
  simp

/-- Consolidated signed complex multiplicity and operator theorem. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexMultiplicity_closed
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
        (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode) ∧
      Disjoint
        (PrimitiveSpinCHopfFirstSpherePositiveComplexSpan
          period hPeriod sector mode)
        (PrimitiveSpinCHopfFirstSphereNegativeComplexSpan
          period hPeriod sector mode) ∧
      primitiveSpinCHopfFirstSphereSignedComplexActualDirac
          period hPeriod sector mode =
        (primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
            period hPeriod sector mode).toLinearMap.comp
          ((primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode).comp
            (primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
              period hPeriod sector mode).symm.toLinearMap) :=
  ⟨primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_injective
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSpherePositiveNegativeComplex_disjoint
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSphereSignedComplexActualDirac_conjugate
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereSignedComplexMultiplicity4D
end JanusFormal
