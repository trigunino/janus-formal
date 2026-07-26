import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereExhaustion4D

/-!
# Faithful six-mode signed first-sphere packet

The two three-dimensional geometric eigenspaces are assembled into one
faithful six-coordinate synthesis.  The genuine differential Dirac operator
intertwines this synthesis with the explicit signed diagonal coefficient
operator, whose square is the geometric first-sphere squared eigenvalue.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereExhaustion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Three coordinates for each internal Dirac sign. -/
abbrev PrimitiveSpinCFirstSphereSignedCoefficients :=
  (Fin 3 → Real) × (Fin 3 → Real)

/-- Simultaneous synthesis of the positive and negative geometric blocks. -/
def primitiveSpinCHopfFirstSphereSignedPacketSynthesis
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCFirstSphereSignedCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter where
  toFun coefficients :=
    (primitiveSpinCHopfFirstSpherePositiveCoordinateEquiv
      period hPeriod sector circleMode coefficients.1 : _) +
    (primitiveSpinCHopfFirstSphereNegativeCoordinateEquiv
      period hPeriod sector circleMode coefficients.2 : _)
  map_add' first second := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
    module
  map_smul' scalar coefficients := by
    change
      ((primitiveSpinCHopfFirstSpherePositiveCoordinateEquiv
          period hPeriod sector circleMode (scalar • coefficients.1) :
            primitiveSpinCHopfFirstSpherePositiveBlock
              period hPeriod sector circleMode) :
          D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) +
          ((primitiveSpinCHopfFirstSphereNegativeCoordinateEquiv
            period hPeriod sector circleMode (scalar • coefficients.2) :
              primitiveSpinCHopfFirstSphereNegativeBlock
                period hPeriod sector circleMode) :
            D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) =
        scalar •
          (((primitiveSpinCHopfFirstSpherePositiveCoordinateEquiv
              period hPeriod sector circleMode coefficients.1 :
                primitiveSpinCHopfFirstSpherePositiveBlock
                  period hPeriod sector circleMode) :
              D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) +
            ((primitiveSpinCHopfFirstSphereNegativeCoordinateEquiv
              period hPeriod sector circleMode coefficients.2 :
                primitiveSpinCHopfFirstSphereNegativeBlock
                  period hPeriod sector circleMode) :
              D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter))
    rw [map_smul, map_smul, Submodule.coe_smul, Submodule.coe_smul, smul_add]

@[simp]
theorem primitiveSpinCHopfFirstSphereSignedPacketSynthesis_apply
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedCoefficients) :
    primitiveSpinCHopfFirstSphereSignedPacketSynthesis
        period hPeriod sector circleMode coefficients =
      (primitiveSpinCHopfFirstSpherePositiveCoordinateEquiv
        period hPeriod sector circleMode coefficients.1 : _) +
      (primitiveSpinCHopfFirstSphereNegativeCoordinateEquiv
        period hPeriod sector circleMode coefficients.2 : _) :=
  rfl

/-- The six-coordinate synthesis is faithful; disjointness of the two signed
eigenspaces prevents cancellation between branches. -/
theorem primitiveSpinCHopfFirstSphereSignedPacketSynthesis_injective
    (sector : NormalRootChoice) (circleMode : Int) :
    Function.Injective
      (primitiveSpinCHopfFirstSphereSignedPacketSynthesis
        period hPeriod sector circleMode) := by
  intro first second hEqual
  let firstPositive :=
    primitiveSpinCHopfFirstSpherePositiveCoordinateEquiv
      period hPeriod sector circleMode first.1
  let secondPositive :=
    primitiveSpinCHopfFirstSpherePositiveCoordinateEquiv
      period hPeriod sector circleMode second.1
  let firstNegative :=
    primitiveSpinCHopfFirstSphereNegativeCoordinateEquiv
      period hPeriod sector circleMode first.2
  let secondNegative :=
    primitiveSpinCHopfFirstSphereNegativeCoordinateEquiv
      period hPeriod sector circleMode second.2
  have hDifference :
      (firstPositive : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) -
          secondPositive =
        (secondNegative : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) -
          firstNegative := by
    change
      (firstPositive : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) +
          firstNegative =
        secondPositive + secondNegative at hEqual
    calc
      (firstPositive : D9PrimitiveSpinCSmoothSection
            period hPeriod .positiveQuarter) -
          secondPositive =
        (firstPositive + firstNegative) -
          (secondPositive + firstNegative) := by module
      _ = (secondPositive + secondNegative) -
          (secondPositive + firstNegative) := by rw [hEqual]
      _ = secondNegative - firstNegative := by module
  have hPositiveMem :
      (firstPositive : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) -
          secondPositive ∈
        primitiveSpinCHopfFirstSpherePositiveBlock
          period hPeriod sector circleMode :=
    Submodule.sub_mem _ firstPositive.property secondPositive.property
  have hNegativeMem :
      (firstPositive : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) -
          secondPositive ∈
        primitiveSpinCHopfFirstSphereNegativeBlock
          period hPeriod sector circleMode := by
    rw [hDifference]
    exact Submodule.sub_mem _ secondNegative.property firstNegative.property
  have hPositiveZero :
      (firstPositive : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) -
          secondPositive = 0 :=
    (Submodule.disjoint_def.mp
      (primitiveSpinCHopfFirstSpherePositiveNegative_disjoint
        period hPeriod sector circleMode))
      ((firstPositive : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) - secondPositive)
      hPositiveMem hNegativeMem
  have hNegativeZero :
      (secondNegative : D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter) -
          firstNegative = 0 := by
    rw [← hDifference]
    exact hPositiveZero
  have hFirstCoordinate : first.1 = second.1 := by
    apply
      (primitiveSpinCHopfFirstSpherePositiveCoordinateEquiv
        period hPeriod sector circleMode).injective
    apply Subtype.ext
    exact sub_eq_zero.mp hPositiveZero
  have hSecondCoordinate : first.2 = second.2 := by
    apply
      (primitiveSpinCHopfFirstSphereNegativeCoordinateEquiv
        period hPeriod sector circleMode).injective
    apply Subtype.ext
    exact (sub_eq_zero.mp hNegativeZero).symm
  exact Prod.ext hFirstCoordinate hSecondCoordinate

/-- Explicit signed diagonal on the six coefficient coordinates. -/
def primitiveSpinCHopfFirstSphereSignedCoefficientOperator
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCFirstSphereSignedCoefficients →ₗ[Real]
      PrimitiveSpinCFirstSphereSignedCoefficients where
  toFun coefficients :=
    (primitiveSpinCHopfFirstSphereDiracFrequency period sector circleMode •
        coefficients.1,
      (-primitiveSpinCHopfFirstSphereDiracFrequency
          period sector circleMode) • coefficients.2)
  map_add' first second := by
    ext coordinate <;> dsimp <;> ring
  map_smul' scalar coefficients := by
    ext coordinate <;> dsimp <;> ring

@[simp]
theorem primitiveSpinCHopfFirstSphereSignedCoefficientOperator_apply
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedCoefficients) :
    primitiveSpinCHopfFirstSphereSignedCoefficientOperator
        period sector circleMode coefficients =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector circleMode •
          coefficients.1,
        (-primitiveSpinCHopfFirstSphereDiracFrequency
            period sector circleMode) • coefficients.2) :=
  rfl

/-- The genuine first-order Dirac operator is exactly the signed diagonal
operator after faithful six-mode synthesis. -/
theorem primitiveSpinCHopfFirstSphereSignedPacketSynthesis_intertwines_dirac
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereSignedPacketSynthesis
          period hPeriod sector circleMode coefficients) =
      primitiveSpinCHopfFirstSphereSignedPacketSynthesis
        period hPeriod sector circleMode
        (primitiveSpinCHopfFirstSphereSignedCoefficientOperator
          period sector circleMode coefficients) := by
  let positive :=
    primitiveSpinCHopfFirstSpherePositiveCoordinateEquiv
      period hPeriod sector circleMode coefficients.1
  let negative :=
    primitiveSpinCHopfFirstSphereNegativeCoordinateEquiv
      period hPeriod sector circleMode coefficients.2
  have hPositive :=
    primitiveSpinCHopfFirstSpherePositiveBlock_eigen
      period hPeriod positive.property
  have hNegative :=
    primitiveSpinCHopfFirstSphereNegativeBlock_eigen
      period hPeriod negative.property
  rw [primitiveSpinCHopfFirstSphereSignedPacketSynthesis_apply,
    d9PrimitiveSpinCGeometricDiracOperator_add, hPositive, hNegative,
    primitiveSpinCHopfFirstSphereSignedCoefficientOperator_apply,
    primitiveSpinCHopfFirstSphereSignedPacketSynthesis_apply]
  simp only [map_smul, Submodule.coe_smul]
  rfl

/-- Squaring the signed coefficient diagonal removes the internal sign and
returns the genuine first-sphere squared eigenvalue. -/
theorem primitiveSpinCHopfFirstSphereSignedCoefficientOperator_sq
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedCoefficients) :
    primitiveSpinCHopfFirstSphereSignedCoefficientOperator period sector
        circleMode
        (primitiveSpinCHopfFirstSphereSignedCoefficientOperator period sector
          circleMode coefficients) =
      (normalRootLeviCivitaCorrectedFrequency period sector circleMode ^ 2 +
          2) • coefficients := by
  let frequency :=
    primitiveSpinCHopfFirstSphereDiracFrequency period sector circleMode
  have hFrequencySq :
      frequency ^ 2 =
        normalRootLeviCivitaCorrectedFrequency period sector circleMode ^ 2 +
          2 := by
    simpa [frequency] using
      primitiveSpinCHopfFirstSphereDiracFrequency_sq
        period sector circleMode
  apply Prod.ext
  · funext coordinate
    change
      frequency * (frequency * coefficients.1 coordinate) =
        (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 2) * coefficients.1 coordinate
    rw [← hFrequencySq]
    ring
  · funext coordinate
    change
      (-frequency) * ((-frequency) * coefficients.2 coordinate) =
        (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 2) * coefficients.2 coordinate
    rw [← hFrequencySq]
    ring

/-- Consequently the square of the genuine differential Dirac operator
intertwines with the unsigned geometric diagonal on the packet. -/
theorem primitiveSpinCHopfFirstSphereSignedPacketSynthesis_intertwines_dirac_sq
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCFirstSphereSignedCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfFirstSphereSignedPacketSynthesis
            period hPeriod sector circleMode coefficients)) =
      primitiveSpinCHopfFirstSphereSignedPacketSynthesis
        period hPeriod sector circleMode
        ((normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 2) • coefficients) := by
  rw [primitiveSpinCHopfFirstSphereSignedPacketSynthesis_intertwines_dirac,
    primitiveSpinCHopfFirstSphereSignedPacketSynthesis_intertwines_dirac,
    primitiveSpinCHopfFirstSphereSignedCoefficientOperator_sq]

end
end P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D
end JanusFormal
