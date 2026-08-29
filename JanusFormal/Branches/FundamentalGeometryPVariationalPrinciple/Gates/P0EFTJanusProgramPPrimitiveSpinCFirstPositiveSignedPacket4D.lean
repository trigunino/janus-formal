import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereExhaustion4D

/-!
# Faithful six-mode signed first-sphere packet

The two three-dimensional geometric eigenspaces are assembled into one
faithful six-coordinate synthesis.  The genuine differential Dirac operator
intertwines this synthesis with the explicit signed diagonal coefficient
operator, whose square is the geometric first-sphere squared eigenvalue.

The final section adjoins the genuine complex Hopf zero coefficient at the
same normal-root/circle label.  The resulting eight-real-dimensional packet
is faithful because the zero block and the signed first-sphere block have
squared eigenvalues separated by the exact gap `2`.  The actual geometric
Dirac operator preserves this finite smooth span and is conjugate there to
the explicit coefficient diagonal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereExhaustion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
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

/-- One complex Hopf zero coefficient together with the two signed
three-coordinate first-sphere packets at the same root/circle label. -/
abbrev PrimitiveSpinCLowEnergySignedCoefficients :=
  Complex × PrimitiveSpinCFirstSphereSignedCoefficients

/-- Simultaneous geometric synthesis of the zero block and the complete
signed first-sphere block. -/
def primitiveSpinCHopfLowEnergySignedSynthesis
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCLowEnergySignedCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter where
  toFun coefficients :=
    primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod (sector, circleMode) coefficients.1 +
      primitiveSpinCHopfFirstSphereSignedPacketSynthesis
        period hPeriod sector circleMode coefficients.2
  map_add' first second := by
    change
      primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, circleMode) (first.1 + second.1) +
          primitiveSpinCHopfFirstSphereSignedPacketSynthesis
            period hPeriod sector circleMode (first.2 + second.2) =
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
              period hPeriod (sector, circleMode) first.1 +
            primitiveSpinCHopfFirstSphereSignedPacketSynthesis
              period hPeriod sector circleMode first.2) +
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
              period hPeriod (sector, circleMode) second.1 +
            primitiveSpinCHopfFirstSphereSignedPacketSynthesis
              period hPeriod sector circleMode second.2)
    rw [map_add, map_add]
    module
  map_smul' scalar coefficients := by
    change
      primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, circleMode) (scalar • coefficients.1) +
          primitiveSpinCHopfFirstSphereSignedPacketSynthesis
            period hPeriod sector circleMode (scalar • coefficients.2) =
        scalar •
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
              period hPeriod (sector, circleMode) coefficients.1 +
            primitiveSpinCHopfFirstSphereSignedPacketSynthesis
              period hPeriod sector circleMode coefficients.2)
    rw [map_smul, map_smul, smul_add]

@[simp]
theorem primitiveSpinCHopfLowEnergySignedSynthesis_apply
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCLowEnergySignedCoefficients) :
    primitiveSpinCHopfLowEnergySignedSynthesis
        period hPeriod sector circleMode coefficients =
      primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, circleMode) coefficients.1 +
        primitiveSpinCHopfFirstSphereSignedPacketSynthesis
          period hPeriod sector circleMode coefficients.2 :=
  rfl

/-- Explicit coefficient Dirac operator on the low-energy packet.  Its zero
coordinate has eigenvalue `-k`; its first-sphere coordinates have the two
internal eigenvalues `±sqrt (k² + 2)`. -/
def primitiveSpinCHopfLowEnergySignedCoefficientOperator
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCLowEnergySignedCoefficients →ₗ[Real]
      PrimitiveSpinCLowEnergySignedCoefficients where
  toFun coefficients :=
    ((-normalRootLeviCivitaCorrectedFrequency
        period sector circleMode) • coefficients.1,
      primitiveSpinCHopfFirstSphereSignedCoefficientOperator
        period sector circleMode coefficients.2)
  map_add' first second := by
    apply Prod.ext
    · change
        (-normalRootLeviCivitaCorrectedFrequency
            period sector circleMode) • (first.1 + second.1) =
          (-normalRootLeviCivitaCorrectedFrequency
              period sector circleMode) • first.1 +
            (-normalRootLeviCivitaCorrectedFrequency
              period sector circleMode) • second.1
      rw [smul_add]
    · change
        primitiveSpinCHopfFirstSphereSignedCoefficientOperator
            period sector circleMode (first.2 + second.2) =
          primitiveSpinCHopfFirstSphereSignedCoefficientOperator
              period sector circleMode first.2 +
            primitiveSpinCHopfFirstSphereSignedCoefficientOperator
              period sector circleMode second.2
      rw [map_add]
  map_smul' scalar coefficients := by
    apply Prod.ext
    · change
        (-normalRootLeviCivitaCorrectedFrequency
            period sector circleMode) • (scalar • coefficients.1) =
          scalar •
            ((-normalRootLeviCivitaCorrectedFrequency
              period sector circleMode) • coefficients.1)
      module
    · change
        primitiveSpinCHopfFirstSphereSignedCoefficientOperator
            period sector circleMode (scalar • coefficients.2) =
          scalar •
            primitiveSpinCHopfFirstSphereSignedCoefficientOperator
              period sector circleMode coefficients.2
      rw [map_smul]

@[simp]
theorem primitiveSpinCHopfLowEnergySignedCoefficientOperator_apply
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCLowEnergySignedCoefficients) :
    primitiveSpinCHopfLowEnergySignedCoefficientOperator
        period sector circleMode coefficients =
      ((-normalRootLeviCivitaCorrectedFrequency
          period sector circleMode) • coefficients.1,
        primitiveSpinCHopfFirstSphereSignedCoefficientOperator
          period sector circleMode coefficients.2) :=
  rfl

/-- A single complex Hopf coefficient is faithfully represented by its two
real global eigenspinors. -/
theorem primitiveSpinCHopfZeroModeCoefficientLinearMap_injective
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Function.Injective
      (primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod label) := by
  intro first second hEqual
  have hSynthesis :
      primitiveSpinCHopfFiniteZeroModeSynthesis period hPeriod
          (Finsupp.single label first) =
        primitiveSpinCHopfFiniteZeroModeSynthesis period hPeriod
          (Finsupp.single label second) := by
    simpa only [primitiveSpinCHopfFiniteZeroModeSynthesis_single]
      using hEqual
  have hSingle :=
    primitiveSpinCHopfFiniteZeroModeSynthesis_injective
      period hPeriod hSynthesis
  have hAt := congrArg
    (fun coefficients : PrimitiveSpinCGeometricFiniteZeroModeCoefficients =>
      coefficients label) hSingle
  simpa using hAt

/-- The actual differential Dirac operator intertwines the complete
low-energy synthesis with its explicit coefficient diagonal. -/
theorem primitiveSpinCHopfLowEnergySignedSynthesis_intertwines_dirac
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCLowEnergySignedCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode coefficients) =
      primitiveSpinCHopfLowEnergySignedSynthesis
        period hPeriod sector circleMode
        (primitiveSpinCHopfLowEnergySignedCoefficientOperator
          period sector circleMode coefficients) := by
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, circleMode) coefficients.1 +
          primitiveSpinCHopfFirstSphereSignedPacketSynthesis
            period hPeriod sector circleMode coefficients.2) =
      primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, circleMode)
          ((-normalRootLeviCivitaCorrectedFrequency
            period sector circleMode) • coefficients.1) +
        primitiveSpinCHopfFirstSphereSignedPacketSynthesis
          period hPeriod sector circleMode
          (primitiveSpinCHopfFirstSphereSignedCoefficientOperator
            period sector circleMode coefficients.2)
  rw [d9PrimitiveSpinCGeometricDiracOperator_add,
    primitiveSpinCHopfZeroModeCoefficientGeometricDiracOperator_eigen,
    primitiveSpinCHopfFirstSphereSignedPacketSynthesis_intertwines_dirac,
    map_smul]

/-- The square of the low-energy coefficient operator differs from the
first-sphere squared eigenvalue by exactly `-2` on the Hopf zero coordinate
and vanishes on all six first-sphere coordinates. -/
theorem primitiveSpinCHopfLowEnergySignedCoefficientOperator_square_gap
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCLowEnergySignedCoefficients) :
    primitiveSpinCHopfLowEnergySignedCoefficientOperator
          period sector circleMode
          (primitiveSpinCHopfLowEnergySignedCoefficientOperator
            period sector circleMode coefficients) -
        (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 2) • coefficients =
      ((-2 : Real) • coefficients.1, 0) := by
  apply Prod.ext
  · change
      (-normalRootLeviCivitaCorrectedFrequency
          period sector circleMode) •
          ((-normalRootLeviCivitaCorrectedFrequency
            period sector circleMode) • coefficients.1) -
        (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 2) • coefficients.1 =
      (-2 : Real) • coefficients.1
    module
  · change
      primitiveSpinCHopfFirstSphereSignedCoefficientOperator
          period sector circleMode
          (primitiveSpinCHopfFirstSphereSignedCoefficientOperator
            period sector circleMode coefficients.2) -
        (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 2) • coefficients.2 = 0
    rw [primitiveSpinCHopfFirstSphereSignedCoefficientOperator_sq]
    exact sub_self _

/-- The eight-real-coordinate low-energy synthesis is faithful.  The proof
uses the exact squared spectral gap `2` to isolate the Hopf coefficient, then
the already established faithfulness of the zero and signed first-level
syntheses. -/
theorem primitiveSpinCHopfLowEnergySignedSynthesis_injective
    (sector : NormalRootChoice) (circleMode : Int) :
    Function.Injective
      (primitiveSpinCHopfLowEnergySignedSynthesis
        period hPeriod sector circleMode) := by
  intro first second hEqual
  let delta : PrimitiveSpinCLowEnergySignedCoefficients := first - second
  have hDelta :
      primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode delta = 0 := by
    change
      primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode (first - second) = 0
    rw [map_sub, hEqual, sub_self]
  have hDirac :
      primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode
          (primitiveSpinCHopfLowEnergySignedCoefficientOperator
            period sector circleMode delta) = 0 := by
    have hApplied := congrArg
      (d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter) hDelta
    rw [primitiveSpinCHopfLowEnergySignedSynthesis_intertwines_dirac,
      d9PrimitiveSpinCGeometricDiracOperator_zero] at hApplied
    exact hApplied
  have hDiracSq :
      primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode
          (primitiveSpinCHopfLowEnergySignedCoefficientOperator
            period sector circleMode
            (primitiveSpinCHopfLowEnergySignedCoefficientOperator
              period sector circleMode delta)) = 0 := by
    have hApplied := congrArg
      (d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter) hDirac
    rw [primitiveSpinCHopfLowEnergySignedSynthesis_intertwines_dirac,
      d9PrimitiveSpinCGeometricDiracOperator_zero] at hApplied
    exact hApplied
  have hIsolated :
      primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode
          (primitiveSpinCHopfLowEnergySignedCoefficientOperator
                period sector circleMode
                (primitiveSpinCHopfLowEnergySignedCoefficientOperator
                  period sector circleMode delta) -
            (normalRootLeviCivitaCorrectedFrequency
                period sector circleMode ^ 2 + 2) • delta) = 0 := by
    rw [map_sub, hDiracSq, map_smul, hDelta, smul_zero, sub_zero]
  rw [primitiveSpinCHopfLowEnergySignedCoefficientOperator_square_gap]
    at hIsolated
  have hZeroImage :
      primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, circleMode)
          ((-2 : Real) • delta.1) = 0 := by
    change
      primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, circleMode)
            ((-2 : Real) • delta.1) +
          primitiveSpinCHopfFirstSphereSignedPacketSynthesis
            period hPeriod sector circleMode
            (0 : PrimitiveSpinCFirstSphereSignedCoefficients) = 0
      at hIsolated
    simpa only [map_zero, add_zero] using hIsolated
  have hFirstScaled : (-2 : Real) • delta.1 = 0 := by
    apply primitiveSpinCHopfZeroModeCoefficientLinearMap_injective
      period hPeriod (sector, circleMode)
    simpa only [map_zero] using hZeroImage
  have hDeltaFirst : delta.1 = 0 :=
    (smul_eq_zero.mp hFirstScaled).resolve_left (by norm_num)
  have hPacketImage :
      primitiveSpinCHopfFirstSphereSignedPacketSynthesis
          period hPeriod sector circleMode delta.2 = 0 := by
    change
      primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, circleMode) delta.1 +
          primitiveSpinCHopfFirstSphereSignedPacketSynthesis
            period hPeriod sector circleMode delta.2 = 0
      at hDelta
    rw [hDeltaFirst, map_zero, zero_add] at hDelta
    exact hDelta
  have hDeltaSecond : delta.2 = 0 := by
    apply primitiveSpinCHopfFirstSphereSignedPacketSynthesis_injective
      period hPeriod sector circleMode
    simpa only [map_zero] using hPacketImage
  have hDeltaZero : delta = 0 := by
    apply Prod.ext
    · exact hDeltaFirst
    · exact hDeltaSecond
  exact sub_eq_zero.mp (by simpa [delta] using hDeltaZero)

/-- The genuine finite smooth low-energy invariant span. -/
abbrev PrimitiveSpinCHopfLowEnergySignedSpan
    (sector : NormalRootChoice) (circleMode : Int) :=
  LinearMap.range
    (primitiveSpinCHopfLowEnergySignedSynthesis
      period hPeriod sector circleMode)

/-- Faithful low-energy coefficients as exact coordinates on their geometric
smooth-section range. -/
def primitiveSpinCHopfLowEnergySignedSynthesisEquiv
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCLowEnergySignedCoefficients ≃ₗ[Real]
      PrimitiveSpinCHopfLowEnergySignedSpan
        period hPeriod sector circleMode :=
  LinearEquiv.ofInjective
    (primitiveSpinCHopfLowEnergySignedSynthesis
      period hPeriod sector circleMode)
    (primitiveSpinCHopfLowEnergySignedSynthesis_injective
      period hPeriod sector circleMode)

@[simp]
theorem primitiveSpinCHopfLowEnergySignedSynthesisEquiv_coe
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCLowEnergySignedCoefficients) :
    ((primitiveSpinCHopfLowEnergySignedSynthesisEquiv
          period hPeriod sector circleMode coefficients :
        PrimitiveSpinCHopfLowEnergySignedSpan
          period hPeriod sector circleMode) :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) =
      primitiveSpinCHopfLowEnergySignedSynthesis
        period hPeriod sector circleMode coefficients :=
  rfl

/-- The actual differential Dirac operator preserves the low-energy smooth
span. -/
theorem primitiveSpinCHopfLowEnergySignedSpan_dirac_mem
    (sector : NormalRootChoice) (circleMode : Int)
    (state : PrimitiveSpinCHopfLowEnergySignedSpan
      period hPeriod sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1 ∈
      PrimitiveSpinCHopfLowEnergySignedSpan
        period hPeriod sector circleMode := by
  rcases state.property with ⟨coefficients, hCoefficients⟩
  refine ⟨primitiveSpinCHopfLowEnergySignedCoefficientOperator
    period sector circleMode coefficients, ?_⟩
  rw [← hCoefficients]
  exact
    (primitiveSpinCHopfLowEnergySignedSynthesis_intertwines_dirac
      period hPeriod sector circleMode coefficients).symm

/-- Restriction of the actual geometric Dirac operator to the invariant
low-energy smooth span. -/
def primitiveSpinCHopfLowEnergySignedActualDirac
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCHopfLowEnergySignedSpan
        period hPeriod sector circleMode →ₗ[Real]
      PrimitiveSpinCHopfLowEnergySignedSpan
        period hPeriod sector circleMode where
  toFun state :=
    ⟨d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1,
      primitiveSpinCHopfLowEnergySignedSpan_dirac_mem
        period hPeriod sector circleMode state⟩
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

/-- On exact low-energy coordinates, the restricted actual Dirac operator is
the explicit coefficient diagonal. -/
@[simp]
theorem primitiveSpinCHopfLowEnergySignedActualDirac_synthesisEquiv
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients : PrimitiveSpinCLowEnergySignedCoefficients) :
    primitiveSpinCHopfLowEnergySignedActualDirac
        period hPeriod sector circleMode
        (primitiveSpinCHopfLowEnergySignedSynthesisEquiv
          period hPeriod sector circleMode coefficients) =
      primitiveSpinCHopfLowEnergySignedSynthesisEquiv
        period hPeriod sector circleMode
        (primitiveSpinCHopfLowEnergySignedCoefficientOperator
          period sector circleMode coefficients) := by
  apply Subtype.ext
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode coefficients) =
      primitiveSpinCHopfLowEnergySignedSynthesis
        period hPeriod sector circleMode
        (primitiveSpinCHopfLowEnergySignedCoefficientOperator
          period sector circleMode coefficients)
  exact primitiveSpinCHopfLowEnergySignedSynthesis_intertwines_dirac
    period hPeriod sector circleMode coefficients

/-- Exact conjugacy of the restricted differential Dirac operator with the
low-energy coefficient diagonal. -/
theorem primitiveSpinCHopfLowEnergySignedActualDirac_conjugate
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCHopfLowEnergySignedActualDirac
        period hPeriod sector circleMode =
      (primitiveSpinCHopfLowEnergySignedSynthesisEquiv
          period hPeriod sector circleMode).toLinearMap.comp
        ((primitiveSpinCHopfLowEnergySignedCoefficientOperator
            period sector circleMode).comp
          (primitiveSpinCHopfLowEnergySignedSynthesisEquiv
            period hPeriod sector circleMode).symm.toLinearMap) := by
  apply LinearMap.ext
  intro state
  rcases (primitiveSpinCHopfLowEnergySignedSynthesisEquiv
    period hPeriod sector circleMode).surjective state with
    ⟨coefficients, rfl⟩
  rw [primitiveSpinCHopfLowEnergySignedActualDirac_synthesisEquiv]
  simp

/-- Consolidated low-energy geometric spectral bridge.  This closes the
faithful zero-plus-first-level packet, not the arbitrary-level geometric
Fourier theorem. -/
theorem primitiveSpinCHopfLowEnergySignedGeometricRealization_closed
    (sector : NormalRootChoice) (circleMode : Int) :
    Function.Injective
        (primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode) ∧
      (∀ coefficients : PrimitiveSpinCLowEnergySignedCoefficients,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCHopfLowEnergySignedSynthesis
              period hPeriod sector circleMode coefficients) =
          primitiveSpinCHopfLowEnergySignedSynthesis
            period hPeriod sector circleMode
            (primitiveSpinCHopfLowEnergySignedCoefficientOperator
              period sector circleMode coefficients)) ∧
      primitiveSpinCHopfLowEnergySignedActualDirac
          period hPeriod sector circleMode =
        (primitiveSpinCHopfLowEnergySignedSynthesisEquiv
            period hPeriod sector circleMode).toLinearMap.comp
          ((primitiveSpinCHopfLowEnergySignedCoefficientOperator
              period sector circleMode).comp
            (primitiveSpinCHopfLowEnergySignedSynthesisEquiv
              period hPeriod sector circleMode).symm.toLinearMap) :=
  ⟨primitiveSpinCHopfLowEnergySignedSynthesis_injective
      period hPeriod sector circleMode,
    primitiveSpinCHopfLowEnergySignedSynthesis_intertwines_dirac
      period hPeriod sector circleMode,
    primitiveSpinCHopfLowEnergySignedActualDirac_conjugate
      period hPeriod sector circleMode⟩

end
end P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D
end JanusFormal
