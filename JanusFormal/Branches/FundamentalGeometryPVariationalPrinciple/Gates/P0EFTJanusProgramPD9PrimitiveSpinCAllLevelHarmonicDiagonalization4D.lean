import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereExhaustion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

/-!
# All-level harmonic diagonalization of the primitive SpinC Dirac operator

For a scalar spherical harmonic of positive level `p`, multiplication of the
Hopf zero mode and Clifford multiplication by its gradient form a two-component
Dirac block

`D X = -k X + T`, `D T = p(p+1) X + k T`.

This file diagonalizes that block uniformly, proves exact agreement with the
complete D9/D10 squared spectrum, and verifies that the already constructed
first positive sphere level is literally the `p = 1` instance.  The global
scalar Leibniz rule now constructs the first block equation from any smooth
scalar, and the remaining differential input is isolated as one
Lichnerowicz/squared-Dirac identity. Consequently the remaining geometric
input is the construction, independence and completeness of the higher scalar
harmonic packets together with that identity; no further first-order SpinC
diagonalization is required.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

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

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

/-- Sphere contribution at the positive level numbered from zero.  Thus
`positiveLevel = 0` is the physical sphere level `p = 1`. -/
def primitiveSpinCHarmonicSphereEnergy
    (positiveLevel : Nat) : Real :=
  primitiveSpinCFullSphereEigenvalueSquared (positiveLevel + 1)

theorem primitiveSpinCHarmonicSphereEnergy_eq
    (positiveLevel : Nat) :
    primitiveSpinCHarmonicSphereEnergy positiveLevel =
      ((positiveLevel + 1 : Nat) : Real) *
        ((positiveLevel + 2 : Nat) : Real) := by
  unfold primitiveSpinCHarmonicSphereEnergy
    primitiveSpinCFullSphereEigenvalueSquared
  congr 1

theorem primitiveSpinCHarmonicSphereEnergy_pos
    (positiveLevel : Nat) :
    0 < primitiveSpinCHarmonicSphereEnergy positiveLevel := by
  rw [primitiveSpinCHarmonicSphereEnergy_eq]
  positivity

/-- Distinct positive sphere levels have distinct squared energies. -/
theorem primitiveSpinCHarmonicSphereEnergy_strictMono :
    StrictMono primitiveSpinCHarmonicSphereEnergy := by
  apply strictMono_nat_of_lt_succ
  intro positiveLevel
  rw [primitiveSpinCHarmonicSphereEnergy_eq,
    primitiveSpinCHarmonicSphereEnergy_eq]
  norm_num [Nat.cast_add, Nat.cast_one]
  have hNonnegative : (0 : Real) ≤ positiveLevel := by positivity
  nlinarith

/-- Exact positive frequency of one all-level harmonic Dirac block. -/
def primitiveSpinCHarmonicDiracFrequency
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) : Real :=
  Real.sqrt
    (normalRootLeviCivitaCorrectedFrequency
        period sector circleMode ^ 2 +
      primitiveSpinCHarmonicSphereEnergy positiveLevel)

theorem primitiveSpinCHarmonicDiracFrequency_sq
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode ^ 2 =
      normalRootLeviCivitaCorrectedFrequency
          period sector circleMode ^ 2 +
        primitiveSpinCHarmonicSphereEnergy positiveLevel := by
  unfold primitiveSpinCHarmonicDiracFrequency
  exact Real.sq_sqrt
    (add_nonneg (sq_nonneg _)
      (le_of_lt
        (primitiveSpinCHarmonicSphereEnergy_pos positiveLevel)))

theorem primitiveSpinCHarmonicDiracFrequency_pos
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    0 <
      primitiveSpinCHarmonicDiracFrequency
        period positiveLevel sector circleMode := by
  unfold primitiveSpinCHarmonicDiracFrequency
  exact Real.sqrt_pos.2
    (add_pos_of_nonneg_of_pos (sq_nonneg _)
      (primitiveSpinCHarmonicSphereEnergy_pos positiveLevel))

/-- The actual smooth geometric data attached to one scalar harmonic.
The two equations are the global Dirac form of the scalar harmonic and its
Clifford gradient. -/
structure PrimitiveSpinCHarmonicDiracSeed4D
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) where
  scalarSection : SmoothSection period hPeriod
  gradientSection : SmoothSection period hPeriod
  dirac_scalar :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter scalarSection =
      (-normalRootLeviCivitaCorrectedFrequency
          period sector circleMode) • scalarSection +
        gradientSection
  dirac_gradient :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter gradientSection =
      primitiveSpinCHarmonicSphereEnergy positiveLevel • scalarSection +
        normalRootLeviCivitaCorrectedFrequency
          period sector circleMode • gradientSection

namespace PrimitiveSpinCHarmonicDiracSeed4D

variable {period hPeriod}
variable {positiveLevel : Nat} {sector : NormalRootChoice}
variable {circleMode : Int}

/-- Positive eigensection obtained by the uniform two-by-two
diagonalization. -/
def positiveSection
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    SmoothSection period hPeriod :=
  (primitiveSpinCHarmonicDiracFrequency
        period positiveLevel sector circleMode -
      normalRootLeviCivitaCorrectedFrequency
        period sector circleMode) • seed.scalarSection +
    seed.gradientSection

/-- Negative eigensection obtained from the same harmonic seed. -/
def negativeSection
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    SmoothSection period hPeriod :=
  (-primitiveSpinCHarmonicDiracFrequency
        period positiveLevel sector circleMode -
      normalRootLeviCivitaCorrectedFrequency
        period sector circleMode) • seed.scalarSection +
    seed.gradientSection

theorem positiveSection_eigen
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter seed.positiveSection =
      primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode • seed.positiveSection := by
  rw [positiveSection,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    seed.dirac_scalar, seed.dirac_gradient]
  have hSquare :=
    primitiveSpinCHarmonicDiracFrequency_sq
      period positiveLevel sector circleMode
  let frequency :=
    primitiveSpinCHarmonicDiracFrequency
      period positiveLevel sector circleMode
  let normal :=
    normalRootLeviCivitaCorrectedFrequency period sector circleMode
  let energy := primitiveSpinCHarmonicSphereEnergy positiveLevel
  have hSquare' : frequency ^ 2 = normal ^ 2 + energy := by
    simpa [frequency, normal, energy] using hSquare
  change
    (frequency - normal) •
          ((-normal) • seed.scalarSection + seed.gradientSection) +
        (energy • seed.scalarSection + normal • seed.gradientSection) =
      frequency •
        ((frequency - normal) • seed.scalarSection + seed.gradientSection)
  calc
    _ =
        (normal ^ 2 + energy - normal * frequency) •
            seed.scalarSection +
          frequency • seed.gradientSection := by
      module
    _ =
        (frequency ^ 2 - normal * frequency) •
            seed.scalarSection +
          frequency • seed.gradientSection := by
      rw [hSquare']
    _ = _ := by
      module

theorem negativeSection_eigen
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter seed.negativeSection =
      (-primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode) • seed.negativeSection := by
  rw [negativeSection,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    seed.dirac_scalar, seed.dirac_gradient]
  let frequency :=
    primitiveSpinCHarmonicDiracFrequency
      period positiveLevel sector circleMode
  let normal :=
    normalRootLeviCivitaCorrectedFrequency period sector circleMode
  let energy := primitiveSpinCHarmonicSphereEnergy positiveLevel
  have hSquare : frequency ^ 2 = normal ^ 2 + energy := by
    simpa [frequency, normal, energy] using
      primitiveSpinCHarmonicDiracFrequency_sq
        period positiveLevel sector circleMode
  change
    (-frequency - normal) •
          ((-normal) • seed.scalarSection + seed.gradientSection) +
        (energy • seed.scalarSection + normal • seed.gradientSection) =
      (-frequency) •
        ((-frequency - normal) • seed.scalarSection + seed.gradientSection)
  calc
    _ =
        (normal ^ 2 + energy + normal * frequency) •
            seed.scalarSection +
          (-frequency) • seed.gradientSection := by
      module
    _ =
        (frequency ^ 2 + normal * frequency) •
            seed.scalarSection +
          (-frequency) • seed.gradientSection := by
      rw [hSquare]
    _ = _ := by
      module

theorem dirac_sq_scalar
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter seed.scalarSection) =
      (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 +
          primitiveSpinCHarmonicSphereEnergy positiveLevel) •
        seed.scalarSection := by
  rw [seed.dirac_scalar,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    seed.dirac_scalar, seed.dirac_gradient]
  module

theorem dirac_sq_gradient
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter seed.gradientSection) =
      (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 +
          primitiveSpinCHarmonicSphereEnergy positiveLevel) •
        seed.gradientSection := by
  rw [seed.dirac_gradient,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    seed.dirac_scalar, seed.dirac_gradient]
  module

theorem positiveSection_sub_negativeSection
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    seed.positiveSection - seed.negativeSection =
      (2 *
        primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode) • seed.scalarSection := by
  unfold positiveSection negativeSection
  module

/-- The signed eigensections span exactly the original scalar/gradient
geometric seed block. -/
theorem eigen_span_eq_seed_span
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    Submodule.span Real
        ({seed.positiveSection, seed.negativeSection} :
          Set (SmoothSection period hPeriod)) =
      Submodule.span Real
        ({seed.scalarSection, seed.gradientSection} :
          Set (SmoothSection period hPeriod)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro state hState
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hState
    rcases hState with rfl | rfl
    · unfold positiveSection
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    · unfold negativeSection
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  · rw [Submodule.span_le]
    intro state hState
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hState
    have hFrequency :
        (2 *
          primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode) ≠ 0 := by
      exact mul_ne_zero (by norm_num)
        (ne_of_gt (primitiveSpinCHarmonicDiracFrequency_pos
          period positiveLevel sector circleMode))
    have hPositive :
        seed.positiveSection ∈
          Submodule.span Real
            ({seed.positiveSection, seed.negativeSection} :
              Set (SmoothSection period hPeriod)) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hNegative :
        seed.negativeSection ∈
          Submodule.span Real
            ({seed.positiveSection, seed.negativeSection} :
              Set (SmoothSection period hPeriod)) :=
      Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    have hScalar :
        seed.scalarSection ∈
          Submodule.span Real
            ({seed.positiveSection, seed.negativeSection} :
              Set (SmoothSection period hPeriod)) := by
      have hDifference :
          seed.positiveSection - seed.negativeSection ∈
            Submodule.span Real
              ({seed.positiveSection, seed.negativeSection} :
                Set (SmoothSection period hPeriod)) :=
        Submodule.sub_mem _ hPositive hNegative
      rw [seed.positiveSection_sub_negativeSection] at hDifference
      have hRecover :
          seed.scalarSection =
            (2 *
              primitiveSpinCHarmonicDiracFrequency
                period positiveLevel sector circleMode)⁻¹ •
              ((2 *
                primitiveSpinCHarmonicDiracFrequency
                  period positiveLevel sector circleMode) •
                seed.scalarSection) := by
        rw [smul_smul, inv_mul_cancel₀ hFrequency, one_smul]
      rw [hRecover]
      exact Submodule.smul_mem _ _ hDifference
    rcases hState with rfl | rfl
    · exact hScalar
    · have hIdentity :
          seed.gradientSection =
            seed.positiveSection -
              (primitiveSpinCHarmonicDiracFrequency
                    period positiveLevel sector circleMode -
                normalRootLeviCivitaCorrectedFrequency
                  period sector circleMode) • seed.scalarSection := by
        unfold positiveSection
        module
      rw [hIdentity]
      exact Submodule.sub_mem _ hPositive
        (Submodule.smul_mem _ _ hScalar)

/-- Full real-linear complex coordinate generated by the positive
eigensection. -/
def positiveComplexLine
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    Complex →ₗ[Real] SmoothSection period hPeriod :=
  d9PrimitiveSpinCComplexLineLinearMap
    period hPeriod .positiveQuarter seed.positiveSection

/-- Full real-linear complex coordinate generated by the negative
eigensection. -/
def negativeComplexLine
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode) :
    Complex →ₗ[Real] SmoothSection period hPeriod :=
  d9PrimitiveSpinCComplexLineLinearMap
    period hPeriod .positiveQuarter seed.negativeSection

theorem positiveComplexLine_eigen
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode)
    (coefficient : Complex) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (seed.positiveComplexLine coefficient) =
      primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode •
        seed.positiveComplexLine coefficient :=
  d9PrimitiveSpinCComplexLineLinearMap_eigen
    period hPeriod seed.positiveSection
    (primitiveSpinCHarmonicDiracFrequency
      period positiveLevel sector circleMode)
    seed.positiveSection_eigen coefficient

theorem negativeComplexLine_eigen
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode)
    (coefficient : Complex) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (seed.negativeComplexLine coefficient) =
      (-primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode) •
        seed.negativeComplexLine coefficient :=
  d9PrimitiveSpinCComplexLineLinearMap_eigen
    period hPeriod seed.negativeSection
    (-primitiveSpinCHarmonicDiracFrequency
      period positiveLevel sector circleMode)
    seed.negativeSection_eigen coefficient

theorem positiveComplexLine_injective
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode)
    (hNonzero : seed.positiveSection ≠ 0) :
    Function.Injective seed.positiveComplexLine :=
  d9PrimitiveSpinCComplexLineLinearMap_injective
    period hPeriod .positiveQuarter seed.positiveSection hNonzero

theorem negativeComplexLine_injective
    (seed :
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode)
    (hNonzero : seed.negativeSection ≠ 0) :
    Function.Injective seed.negativeComplexLine :=
  d9PrimitiveSpinCComplexLineLinearMap_injective
    period hPeriod .positiveQuarter seed.negativeSection hNonzero

end PrimitiveSpinCHarmonicDiracSeed4D

/-- A still smaller geometric input: one smooth section satisfying only the
expected squared-Dirac eigen-equation. -/
structure PrimitiveSpinCHarmonicSquaredSeed4D
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) where
  scalarSection : SmoothSection period hPeriod
  dirac_sq_scalar :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter scalarSection) =
      (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 +
          primitiveSpinCHarmonicSphereEnergy positiveLevel) • scalarSection

namespace PrimitiveSpinCHarmonicSquaredSeed4D

variable {period hPeriod}
variable {positiveLevel : Nat} {sector : NormalRootChoice}
variable {circleMode : Int}

/-- The Clifford-gradient partner is recovered canonically from the first
Dirac image. -/
def gradientSection
    (seed :
      PrimitiveSpinCHarmonicSquaredSeed4D
        period hPeriod positiveLevel sector circleMode) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCGeometricDiracOperator
      period hPeriod .positiveQuarter seed.scalarSection +
    normalRootLeviCivitaCorrectedFrequency
      period sector circleMode • seed.scalarSection

/-- A squared eigensection canonically generates the full first-order Dirac
block.  Thus the two first-order identities are not independent geometric
obligations. -/
def toDiracSeed
    (seed :
      PrimitiveSpinCHarmonicSquaredSeed4D
        period hPeriod positiveLevel sector circleMode) :
    PrimitiveSpinCHarmonicDiracSeed4D
      period hPeriod positiveLevel sector circleMode where
  scalarSection := seed.scalarSection
  gradientSection := seed.gradientSection
  dirac_scalar := by
    unfold gradientSection
    module
  dirac_gradient := by
    unfold gradientSection
    rw [d9PrimitiveSpinCGeometricDiracOperator_add,
      d9PrimitiveSpinCGeometricDiracOperator_real_smul,
      seed.dirac_sq_scalar]
    module

theorem positiveSection_eigen
    (seed :
      PrimitiveSpinCHarmonicSquaredSeed4D
        period hPeriod positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter seed.toDiracSeed.positiveSection =
      primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode •
        seed.toDiracSeed.positiveSection :=
  seed.toDiracSeed.positiveSection_eigen

theorem negativeSection_eigen
    (seed :
      PrimitiveSpinCHarmonicSquaredSeed4D
        period hPeriod positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter seed.toDiracSeed.negativeSection =
      (-primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode) •
        seed.toDiracSeed.negativeSection :=
  seed.toDiracSeed.negativeSection_eigen

end PrimitiveSpinCHarmonicSquaredSeed4D

/-- Genuine smooth SpinC section obtained by multiplying a Hopf zero mode by
a globally smooth real scalar. -/
def primitiveSpinCScalarHarmonicSection
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCRealScalarMulSection
    period hPeriod .positiveQuarter scalar hScalar
    (primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode)

/-- Genuine global Clifford-gradient remainder attached to the same scalar
multiplier and Hopf zero mode. -/
def primitiveSpinCScalarHarmonicGradientSection
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCScalarCliffordGradientSection
    period hPeriod .positiveQuarter scalar hScalar
    (primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode)

/-- The first equation of every scalar-harmonic Dirac block follows
unconditionally from the global scalar Leibniz rule and the Hopf zero-mode
equation. -/
theorem primitiveSpinCScalarHarmonicSection_dirac
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCScalarHarmonicSection
          period hPeriod scalar hScalar sector circleMode) =
      (-normalRootLeviCivitaCorrectedFrequency
          period sector circleMode) •
          primitiveSpinCScalarHarmonicSection
            period hPeriod scalar hScalar sector circleMode +
        primitiveSpinCScalarHarmonicGradientSection
          period hPeriod scalar hScalar sector circleMode := by
  unfold primitiveSpinCScalarHarmonicSection
    primitiveSpinCScalarHarmonicGradientSection
  rw [d9PrimitiveSpinCGeometricDiracOperator_realScalarMul,
    primitiveSpinCHopfZeroModeGeometricDiracOperator_eigen,
    d9PrimitiveSpinCRealScalarMulSection_real_smul]

/-- Exact remaining geometric input for one scalar harmonic: the scalar is
globally smooth and its genuine SpinC multiplier satisfies the expected
Lichnerowicz/squared-Dirac equation for every normal-root Fourier mode. -/
structure PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
    (positiveLevel : Nat) where
  scalar : ThroatBase period hPeriod → Real
  scalar_contMDiff :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar
  dirac_sq_scalar :
    ∀ (sector : NormalRootChoice) (circleMode : Int),
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCScalarHarmonicSection
              period hPeriod scalar scalar_contMDiff sector circleMode)) =
        (normalRootLeviCivitaCorrectedFrequency
              period sector circleMode ^ 2 +
            primitiveSpinCHarmonicSphereEnergy positiveLevel) •
          primitiveSpinCScalarHarmonicSection
            period hPeriod scalar scalar_contMDiff sector circleMode

namespace PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D

variable {period hPeriod}
variable {positiveLevel : Nat}

/-- Canonical squared seed carried by one genuine smooth scalar harmonic. -/
def toSquaredSeed
    (harmonic :
      PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod positiveLevel)
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCHarmonicSquaredSeed4D
      period hPeriod positiveLevel sector circleMode where
  scalarSection :=
    primitiveSpinCScalarHarmonicSection
      period hPeriod harmonic.scalar harmonic.scalar_contMDiff
      sector circleMode
  dirac_sq_scalar := harmonic.dirac_sq_scalar sector circleMode

/-- Canonical first-order Dirac block carried by the same scalar harmonic. -/
def toDiracSeed
    (harmonic :
      PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod positiveLevel)
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCHarmonicDiracSeed4D
      period hPeriod positiveLevel sector circleMode :=
  (harmonic.toSquaredSeed sector circleMode).toDiracSeed

/-- The gradient reconstructed from the squared seed is exactly the global
Clifford-gradient remainder, so the reduction preserves the geometric
meaning of the two-component block. -/
theorem toDiracSeed_gradientSection_eq
    (harmonic :
      PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod positiveLevel)
    (sector : NormalRootChoice) (circleMode : Int) :
    (harmonic.toDiracSeed sector circleMode).gradientSection =
      primitiveSpinCScalarHarmonicGradientSection
        period hPeriod harmonic.scalar harmonic.scalar_contMDiff
        sector circleMode := by
  change
    d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCScalarHarmonicSection
            period hPeriod harmonic.scalar harmonic.scalar_contMDiff
            sector circleMode) +
        normalRootLeviCivitaCorrectedFrequency
            period sector circleMode •
          primitiveSpinCScalarHarmonicSection
            period hPeriod harmonic.scalar harmonic.scalar_contMDiff
            sector circleMode =
      primitiveSpinCScalarHarmonicGradientSection
        period hPeriod harmonic.scalar harmonic.scalar_contMDiff
        sector circleMode
  rw [primitiveSpinCScalarHarmonicSection_dirac]
  module

/-- The single squared-Dirac input yields the second geometric block equation
for the actual global Clifford-gradient remainder. -/
theorem gradientSection_dirac
    (harmonic :
      PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod positiveLevel)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCScalarHarmonicGradientSection
          period hPeriod harmonic.scalar harmonic.scalar_contMDiff
          sector circleMode) =
      primitiveSpinCHarmonicSphereEnergy positiveLevel •
          primitiveSpinCScalarHarmonicSection
            period hPeriod harmonic.scalar harmonic.scalar_contMDiff
            sector circleMode +
        normalRootLeviCivitaCorrectedFrequency
            period sector circleMode •
          primitiveSpinCScalarHarmonicGradientSection
            period hPeriod harmonic.scalar harmonic.scalar_contMDiff
            sector circleMode := by
  rw [← harmonic.toDiracSeed_gradientSection_eq sector circleMode]
  exact (harmonic.toDiracSeed sector circleMode).dirac_gradient

end PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D

/-- Complete coefficient label corresponding to one positive harmonic. -/
def primitiveSpinCHarmonicGeometricMode
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCGeometricFullMode :=
  (sector, (⟨positiveLevel + 1, multiplicity⟩, circleMode))

/-- Uniform harmonic diagonalization has exactly the complete geometric
D9/D10 squared eigenvalue. -/
theorem primitiveSpinCHarmonicDiracFrequency_sq_eq_geometricSpectrum
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode ^ 2 =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod
        (primitiveSpinCHarmonicGeometricMode
          positiveLevel multiplicity sector circleMode) := by
  rw [primitiveSpinCHarmonicDiracFrequency_sq]
  unfold primitiveSpinCHarmonicGeometricMode
    primitiveSpinCGeometricSquaredEigenvalue
    primitiveSpinCHarmonicSphereEnergy
  rw [normalRootLeviCivitaCorrectedFrequency_sq_eq_circle
    period hPeriod sector circleMode]
  ring

/-- A full family of scalar-harmonic Dirac seeds.  Once this purely spherical
packet is constructed, all positive geometric SpinC eigensections are
canonical. -/
structure PrimitiveSpinCAllPositiveHarmonicSeedTower4D where
  seed :
    ∀ (positiveLevel : Nat)
      (_multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
      (sector : NormalRootChoice) (circleMode : Int),
      PrimitiveSpinCHarmonicDiracSeed4D
        period hPeriod positiveLevel sector circleMode

/-- All-level input reduced to squared eigensections only. -/
structure PrimitiveSpinCAllPositiveHarmonicSquaredSeedTower4D where
  seed :
    ∀ (positiveLevel : Nat)
      (_multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
      (sector : NormalRootChoice) (circleMode : Int),
      PrimitiveSpinCHarmonicSquaredSeed4D
        period hPeriod positiveLevel sector circleMode

namespace PrimitiveSpinCAllPositiveHarmonicSquaredSeedTower4D

variable
  (tower :
    PrimitiveSpinCAllPositiveHarmonicSquaredSeedTower4D period hPeriod)

/-- Canonical promotion from the squared harmonic tower to the full
first-order seed tower. -/
def toDiracSeedTower :
    PrimitiveSpinCAllPositiveHarmonicSeedTower4D period hPeriod where
  seed := fun positiveLevel multiplicity sector circleMode =>
    (tower.seed positiveLevel multiplicity sector circleMode).toDiracSeed

end PrimitiveSpinCAllPositiveHarmonicSquaredSeedTower4D

/-- Full scalar-harmonic packet.  This is the precise geometric construction
whose existence promotes automatically to every signed SpinC eigensection. -/
structure PrimitiveSpinCAllPositiveScalarHarmonicTower4D where
  harmonic :
    ∀ (positiveLevel : Nat)
      (_multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))),
      PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod positiveLevel

namespace PrimitiveSpinCAllPositiveScalarHarmonicTower4D

variable
  (tower :
    PrimitiveSpinCAllPositiveScalarHarmonicTower4D period hPeriod)

/-- Forget only the scalar origin and retain the complete squared-seed
packet. -/
def toSquaredSeedTower :
    PrimitiveSpinCAllPositiveHarmonicSquaredSeedTower4D period hPeriod where
  seed := fun positiveLevel multiplicity sector circleMode =>
    (tower.harmonic positiveLevel multiplicity).toSquaredSeed
      sector circleMode

/-- Canonical all-level first-order Dirac tower generated from scalar
harmonics. -/
def toDiracSeedTower :
    PrimitiveSpinCAllPositiveHarmonicSeedTower4D period hPeriod :=
  tower.toSquaredSeedTower.toDiracSeedTower

end PrimitiveSpinCAllPositiveScalarHarmonicTower4D

namespace PrimitiveSpinCAllPositiveHarmonicSeedTower4D

variable
  (tower :
    PrimitiveSpinCAllPositiveHarmonicSeedTower4D period hPeriod)

def positiveModeSection
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  (tower.seed positiveLevel multiplicity sector circleMode).positiveSection

def negativeModeSection
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  (tower.seed positiveLevel multiplicity sector circleMode).negativeSection

theorem positiveModeSection_eigen
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (positiveModeSection period hPeriod tower positiveLevel multiplicity
          sector circleMode) =
      primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode •
        positiveModeSection period hPeriod tower positiveLevel multiplicity
          sector circleMode :=
  (PrimitiveSpinCAllPositiveHarmonicSeedTower4D.seed
    tower positiveLevel multiplicity sector circleMode).positiveSection_eigen

theorem negativeModeSection_eigen
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (negativeModeSection period hPeriod tower positiveLevel multiplicity
          sector circleMode) =
      (-primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode) •
        negativeModeSection period hPeriod tower positiveLevel multiplicity
          sector circleMode :=
  (PrimitiveSpinCAllPositiveHarmonicSeedTower4D.seed
    tower positiveLevel multiplicity sector circleMode).negativeSection_eigen

/-- Scalar part of one fixed all-multiplicity harmonic packet. -/
def scalarHarmonicBlock
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Submodule Real (SmoothSection period hPeriod) :=
  Submodule.span Real
    (Set.range fun multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) =>
      (tower.seed positiveLevel multiplicity sector circleMode).scalarSection)

/-- Clifford-gradient part of the same packet. -/
def gradientHarmonicBlock
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Submodule Real (SmoothSection period hPeriod) :=
  Submodule.span Real
    (Set.range fun multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) =>
      (tower.seed positiveLevel multiplicity sector circleMode).gradientSection)

/-- Original scalar/gradient seed packet before diagonalization. -/
def geometricHarmonicSeedBlock
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Submodule Real (SmoothSection period hPeriod) :=
  scalarHarmonicBlock period hPeriod tower positiveLevel sector circleMode ⊔
    gradientHarmonicBlock period hPeriod tower positiveLevel sector circleMode

/-- Positive eigenspace generated by one all-multiplicity packet. -/
def positiveHarmonicEigenblock
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Submodule Real (SmoothSection period hPeriod) :=
  Submodule.span Real
    (Set.range fun multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) =>
      (tower.seed positiveLevel multiplicity sector circleMode).positiveSection)

/-- Negative eigenspace generated by the same packet. -/
def negativeHarmonicEigenblock
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Submodule Real (SmoothSection period hPeriod) :=
  Submodule.span Real
    (Set.range fun multiplicity :
        Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) =>
      (tower.seed positiveLevel multiplicity sector circleMode).negativeSection)

theorem positiveHarmonicEigenblock_eigen
    {positiveLevel : Nat} {sector : NormalRootChoice}
    {circleMode : Int} {state : SmoothSection period hPeriod}
    (hState :
      state ∈
        positiveHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state =
      primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode • state := by
  rw [positiveHarmonicEigenblock] at hState
  refine Submodule.span_induction
    (p := fun state _ =>
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state =
        primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode • state)
    ?_ ?_ ?_ ?_ hState
  · rintro _ ⟨multiplicity, rfl⟩
    exact
      (tower.seed
        positiveLevel multiplicity sector circleMode).positiveSection_eigen
  · rw [d9PrimitiveSpinCGeometricDiracOperator_zero, smul_zero]
  · intro first second _ _ hFirst hSecond
    rw [d9PrimitiveSpinCGeometricDiracOperator_add,
      hFirst, hSecond, smul_add]
  · intro scalar sectionState _ hSection
    rw [d9PrimitiveSpinCGeometricDiracOperator_real_smul,
      hSection, smul_smul, smul_smul, mul_comm scalar]

theorem negativeHarmonicEigenblock_eigen
    {positiveLevel : Nat} {sector : NormalRootChoice}
    {circleMode : Int} {state : SmoothSection period hPeriod}
    (hState :
      state ∈
        negativeHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state =
      (-primitiveSpinCHarmonicDiracFrequency
          period positiveLevel sector circleMode) • state := by
  rw [negativeHarmonicEigenblock] at hState
  refine Submodule.span_induction
    (p := fun state _ =>
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state =
        (-primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode) • state)
    ?_ ?_ ?_ ?_ hState
  · rintro _ ⟨multiplicity, rfl⟩
    exact
      (tower.seed
        positiveLevel multiplicity sector circleMode).negativeSection_eigen
  · rw [d9PrimitiveSpinCGeometricDiracOperator_zero, smul_zero]
  · intro first second _ _ hFirst hSecond
    rw [d9PrimitiveSpinCGeometricDiracOperator_add,
      hFirst, hSecond, smul_add]
  · intro scalar sectionState _ hSection
    rw [d9PrimitiveSpinCGeometricDiracOperator_real_smul,
      hSection, smul_smul, smul_smul, mul_comm scalar]

theorem positive_negativeHarmonicEigenblocks_disjoint
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Disjoint
      (positiveHarmonicEigenblock
        period hPeriod tower positiveLevel sector circleMode)
      (negativeHarmonicEigenblock
        period hPeriod tower positiveLevel sector circleMode) := by
  refine Submodule.disjoint_def.mpr ?_
  intro state hPositive hNegative
  have hPositiveEigen :=
    positiveHarmonicEigenblock_eigen
      period hPeriod tower hPositive
  have hNegativeEigen :=
    negativeHarmonicEigenblock_eigen
      period hPeriod tower hNegative
  let frequency :=
    primitiveSpinCHarmonicDiracFrequency
      period positiveLevel sector circleMode
  have hFrequency : frequency ≠ 0 :=
    ne_of_gt
      (primitiveSpinCHarmonicDiracFrequency_pos
        period positiveLevel sector circleMode)
  have hTwiceFrequency : (2 * frequency) ≠ 0 :=
    mul_ne_zero (by norm_num) hFrequency
  have hScaled : (2 * frequency) • state = 0 := by
    calc
      (2 * frequency) • state =
          frequency • state - (-frequency) • state := by
        module
      _ = 0 := by
        rw [← hPositiveEigen, ← hNegativeEigen]
        exact sub_self _
  exact (smul_eq_zero.mp hScaled).resolve_left hTwiceFrequency

theorem positiveHarmonicEigenblock_le_seed
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    positiveHarmonicEigenblock
        period hPeriod tower positiveLevel sector circleMode ≤
      geometricHarmonicSeedBlock
        period hPeriod tower positiveLevel sector circleMode := by
  rw [positiveHarmonicEigenblock, Submodule.span_le]
  rintro state ⟨multiplicity, rfl⟩
  unfold PrimitiveSpinCHarmonicDiracSeed4D.positiveSection
    geometricHarmonicSeedBlock
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _
      (Submodule.mem_sup_left
        (Submodule.subset_span ⟨multiplicity, rfl⟩))
  · exact Submodule.mem_sup_right
      (Submodule.subset_span ⟨multiplicity, rfl⟩)

theorem negativeHarmonicEigenblock_le_seed
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    negativeHarmonicEigenblock
        period hPeriod tower positiveLevel sector circleMode ≤
      geometricHarmonicSeedBlock
        period hPeriod tower positiveLevel sector circleMode := by
  rw [negativeHarmonicEigenblock, Submodule.span_le]
  rintro state ⟨multiplicity, rfl⟩
  unfold PrimitiveSpinCHarmonicDiracSeed4D.negativeSection
    geometricHarmonicSeedBlock
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _
      (Submodule.mem_sup_left
        (Submodule.subset_span ⟨multiplicity, rfl⟩))
  · exact Submodule.mem_sup_right
      (Submodule.subset_span ⟨multiplicity, rfl⟩)

theorem scalarSection_mem_harmonicEigenblocks
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    (tower.seed positiveLevel multiplicity sector circleMode).scalarSection ∈
      positiveHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode ⊔
        negativeHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode := by
  let seed := tower.seed positiveLevel multiplicity sector circleMode
  let frequency :=
    primitiveSpinCHarmonicDiracFrequency
      period positiveLevel sector circleMode
  have hTwiceFrequency : (2 * frequency) ≠ 0 :=
    mul_ne_zero (by norm_num)
      (ne_of_gt
        (primitiveSpinCHarmonicDiracFrequency_pos
          period positiveLevel sector circleMode))
  have hPositive : seed.positiveSection ∈
      positiveHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode ⊔
        negativeHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode :=
    Submodule.mem_sup_left
      (Submodule.subset_span ⟨multiplicity, rfl⟩)
  have hNegative : seed.negativeSection ∈
      positiveHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode ⊔
        negativeHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode :=
    Submodule.mem_sup_right
      (Submodule.subset_span ⟨multiplicity, rfl⟩)
  have hScaled : (2 * frequency) • seed.scalarSection ∈
      positiveHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode ⊔
        negativeHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode := by
    rw [← seed.positiveSection_sub_negativeSection]
    exact Submodule.sub_mem _ hPositive hNegative
  have hRecover :
      seed.scalarSection =
        (2 * frequency)⁻¹ • ((2 * frequency) • seed.scalarSection) := by
    rw [smul_smul, inv_mul_cancel₀ hTwiceFrequency, one_smul]
  rw [show
    (tower.seed positiveLevel multiplicity sector circleMode).scalarSection =
      seed.scalarSection by rfl, hRecover]
  exact Submodule.smul_mem _ _ hScaled

theorem gradientSection_mem_harmonicEigenblocks
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    (tower.seed positiveLevel multiplicity sector circleMode).gradientSection ∈
      positiveHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode ⊔
        negativeHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode := by
  let seed := tower.seed positiveLevel multiplicity sector circleMode
  have hPositive : seed.positiveSection ∈
      positiveHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode ⊔
        negativeHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode :=
    Submodule.mem_sup_left
      (Submodule.subset_span ⟨multiplicity, rfl⟩)
  have hScalar :=
    scalarSection_mem_harmonicEigenblocks
      period hPeriod tower positiveLevel multiplicity sector circleMode
  have hIdentity :
      seed.gradientSection =
        seed.positiveSection -
          (primitiveSpinCHarmonicDiracFrequency
                period positiveLevel sector circleMode -
            normalRootLeviCivitaCorrectedFrequency
              period sector circleMode) • seed.scalarSection := by
    unfold PrimitiveSpinCHarmonicDiracSeed4D.positiveSection
    module
  rw [show
    (tower.seed positiveLevel multiplicity sector circleMode).gradientSection =
      seed.gradientSection by rfl, hIdentity]
  exact Submodule.sub_mem _ hPositive
    (Submodule.smul_mem _ _ hScalar)

/-- At every positive level the two signed eigenspaces are disjoint and
exhaust exactly the original all-multiplicity scalar/gradient packet. -/
theorem harmonicEigenblocks_sup_eq_seed
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    positiveHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode ⊔
        negativeHarmonicEigenblock
          period hPeriod tower positiveLevel sector circleMode =
      geometricHarmonicSeedBlock
        period hPeriod tower positiveLevel sector circleMode := by
  apply le_antisymm
  · exact sup_le
      (positiveHarmonicEigenblock_le_seed
        period hPeriod tower positiveLevel sector circleMode)
      (negativeHarmonicEigenblock_le_seed
        period hPeriod tower positiveLevel sector circleMode)
  · unfold geometricHarmonicSeedBlock
    apply sup_le
    · rw [scalarHarmonicBlock, Submodule.span_le]
      rintro state ⟨multiplicity, rfl⟩
      exact scalarSection_mem_harmonicEigenblocks
        period hPeriod tower positiveLevel multiplicity sector circleMode
    · rw [gradientHarmonicBlock, Submodule.span_le]
      rintro state ⟨multiplicity, rfl⟩
      exact gradientSection_mem_harmonicEigenblocks
        period hPeriod tower positiveLevel multiplicity sector circleMode

end PrimitiveSpinCAllPositiveHarmonicSeedTower4D

/-- The existing first positive geometric block is the first inhabitant of
the uniform all-level seed interface. -/
def primitiveSpinCFirstPositiveHarmonicSeed
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCHarmonicDiracSeed4D
      period hPeriod 0 sector circleMode where
  scalarSection :=
    primitiveSpinCHopfFirstSphereCoordinateSection
      period hPeriod coordinate sector circleMode
  gradientSection :=
    primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector circleMode
  dirac_scalar :=
    primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_eq
      period hPeriod coordinate sector circleMode
  dirac_gradient := by
    simpa [primitiveSpinCHarmonicSphereEnergy,
      primitiveSpinCFullSphereEigenvalueSquared] using
      primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_eq
        period hPeriod coordinate sector circleMode

/-- The constructed first positive level also inhabits the reduced
squared-seed interface. -/
def primitiveSpinCFirstPositiveHarmonicSquaredSeed
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCHarmonicSquaredSeed4D
      period hPeriod 0 sector circleMode where
  scalarSection :=
    (primitiveSpinCFirstPositiveHarmonicSeed
      period hPeriod coordinate sector circleMode).scalarSection
  dirac_sq_scalar := by
    simpa [primitiveSpinCHarmonicSphereEnergy,
      primitiveSpinCFullSphereEigenvalueSquared] using
      (primitiveSpinCFirstPositiveHarmonicSeed
        period hPeriod coordinate sector circleMode).dirac_sq_scalar

/-- The generic smooth-scalar construction specializes exactly to the
already constructed first sphere-coordinate section. -/
theorem primitiveSpinCFirstPositiveScalarHarmonicSection_eq
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCScalarHarmonicSection
        period hPeriod
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod coordinate)
        sector circleMode =
      primitiveSpinCHopfFirstSphereCoordinateSection
        period hPeriod coordinate sector circleMode := by
  ext base
  unfold primitiveSpinCScalarHarmonicSection
  rw [d9PrimitiveSpinCRealScalarMulSection_apply,
    primitiveSpinCHopfFirstSphereCoordinateSection_apply]

/-- The first positive scalar coordinate satisfies the exact
Lichnerowicz-seed interface, with no new spectral assumption. -/
def primitiveSpinCFirstPositiveScalarHarmonicLichnerowiczSeed
    (coordinate : Fin 3) :
    PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
      period hPeriod 0 where
  scalar := d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
  scalar_contMDiff :=
    d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod coordinate
  dirac_sq_scalar := by
    intro sector circleMode
    rw [primitiveSpinCFirstPositiveScalarHarmonicSection_eq]
    exact
      (primitiveSpinCFirstPositiveHarmonicSquaredSeed
        period hPeriod coordinate sector circleMode).dirac_sq_scalar

theorem primitiveSpinCHarmonicDiracFrequency_zero
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCHarmonicDiracFrequency period 0 sector circleMode =
      primitiveSpinCHopfFirstSphereDiracFrequency
        period sector circleMode := by
  simp [primitiveSpinCHarmonicDiracFrequency,
    primitiveSpinCHarmonicSphereEnergy,
    primitiveSpinCFullSphereEigenvalueSquared,
    primitiveSpinCHopfFirstSphereDiracFrequency]

theorem primitiveSpinCFirstPositiveHarmonicSeed_positiveSection
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int) :
    (primitiveSpinCFirstPositiveHarmonicSeed
        period hPeriod coordinate sector circleMode).positiveSection =
      primitiveSpinCHopfFirstSpherePositiveSection
        period hPeriod coordinate sector circleMode := by
  simp [PrimitiveSpinCHarmonicDiracSeed4D.positiveSection,
    primitiveSpinCFirstPositiveHarmonicSeed,
    primitiveSpinCHarmonicDiracFrequency_zero,
    primitiveSpinCHopfFirstSpherePositiveSection]

theorem primitiveSpinCFirstPositiveHarmonicSeed_negativeSection
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int) :
    (primitiveSpinCFirstPositiveHarmonicSeed
        period hPeriod coordinate sector circleMode).negativeSection =
      primitiveSpinCHopfFirstSphereNegativeSection
        period hPeriod coordinate sector circleMode := by
  simp [PrimitiveSpinCHarmonicDiracSeed4D.negativeSection,
    primitiveSpinCFirstPositiveHarmonicSeed,
    primitiveSpinCHarmonicDiracFrequency_zero,
    primitiveSpinCHopfFirstSphereNegativeSection]

/-- Unconditional certificate that all SpinC-specific all-level
diagonalization is complete.  Its quantified seed is precisely the remaining
scalar-harmonic input. -/
structure PrimitiveSpinCAllLevelHarmonicDiagonalizationCertificate4D :
    Prop where
  frequencyPositive :
    ∀ positiveLevel sector circleMode,
      0 < primitiveSpinCHarmonicDiracFrequency
        period positiveLevel sector circleMode
  spectralAgreement :
    ∀ positiveLevel multiplicity sector circleMode,
      primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode ^ 2 =
        primitiveSpinCGeometricSquaredEigenvalue period hPeriod
          (primitiveSpinCHarmonicGeometricMode
            positiveLevel multiplicity sector circleMode)
  diagonalizes :
    ∀ positiveLevel sector circleMode
      (seed :
        PrimitiveSpinCHarmonicDiracSeed4D
          period hPeriod positiveLevel sector circleMode),
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter seed.positiveSection =
        primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode • seed.positiveSection ∧
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter seed.negativeSection =
        (-primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode) • seed.negativeSection ∧
      Submodule.span Real
          ({seed.positiveSection, seed.negativeSection} :
            Set (SmoothSection period hPeriod)) =
        Submodule.span Real
          ({seed.scalarSection, seed.gradientSection} :
            Set (SmoothSection period hPeriod))
  firstLevelRealized :
    ∀ coordinate sector circleMode,
      (primitiveSpinCFirstPositiveHarmonicSeed
          period hPeriod coordinate sector circleMode).positiveSection =
        primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector circleMode ∧
      (primitiveSpinCFirstPositiveHarmonicSeed
          period hPeriod coordinate sector circleMode).negativeSection =
        primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector circleMode
  packetDecomposition :
    ∀ (tower :
        PrimitiveSpinCAllPositiveHarmonicSeedTower4D period hPeriod)
      positiveLevel sector circleMode,
      Disjoint
        (tower.positiveHarmonicEigenblock
          period hPeriod positiveLevel sector circleMode)
        (tower.negativeHarmonicEigenblock
          period hPeriod positiveLevel sector circleMode) ∧
      tower.positiveHarmonicEigenblock
            period hPeriod positiveLevel sector circleMode ⊔
          tower.negativeHarmonicEigenblock
            period hPeriod positiveLevel sector circleMode =
        tower.geometricHarmonicSeedBlock
          period hPeriod positiveLevel sector circleMode
  squaredSeedReduction :
    ∀ positiveLevel sector circleMode
      (seed :
        PrimitiveSpinCHarmonicSquaredSeed4D
          period hPeriod positiveLevel sector circleMode),
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter seed.toDiracSeed.positiveSection =
        primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode •
          seed.toDiracSeed.positiveSection ∧
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter seed.toDiracSeed.negativeSection =
        (-primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode) •
          seed.toDiracSeed.negativeSection
  scalarLeibnizReduction :
    ∀ scalar
      (hScalar :
        ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
      sector circleMode,
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCScalarHarmonicSection
            period hPeriod scalar hScalar sector circleMode) =
        (-normalRootLeviCivitaCorrectedFrequency
            period sector circleMode) •
            primitiveSpinCScalarHarmonicSection
              period hPeriod scalar hScalar sector circleMode +
          primitiveSpinCScalarHarmonicGradientSection
            period hPeriod scalar hScalar sector circleMode
  scalarLichnerowiczReduction :
    ∀ positiveLevel
      (harmonic :
        PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
          period hPeriod positiveLevel)
      sector circleMode,
      (harmonic.toDiracSeed sector circleMode).scalarSection =
          primitiveSpinCScalarHarmonicSection
            period hPeriod harmonic.scalar harmonic.scalar_contMDiff
            sector circleMode ∧
        (harmonic.toDiracSeed sector circleMode).gradientSection =
          primitiveSpinCScalarHarmonicGradientSection
            period hPeriod harmonic.scalar harmonic.scalar_contMDiff
            sector circleMode
  firstScalarHarmonicRealized :
    ∀ coordinate sector circleMode,
      primitiveSpinCScalarHarmonicSection
          period hPeriod
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod coordinate)
          sector circleMode =
        primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector circleMode
  complexLineDiagonalization :
    ∀ positiveLevel sector circleMode
      (seed :
        PrimitiveSpinCHarmonicDiracSeed4D
          period hPeriod positiveLevel sector circleMode)
      coefficient,
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (seed.positiveComplexLine coefficient) =
        primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode •
          seed.positiveComplexLine coefficient ∧
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (seed.negativeComplexLine coefficient) =
        (-primitiveSpinCHarmonicDiracFrequency
            period positiveLevel sector circleMode) •
          seed.negativeComplexLine coefficient

def primitiveSpinCAllLevelHarmonicDiagonalizationCertificate4D :
    PrimitiveSpinCAllLevelHarmonicDiagonalizationCertificate4D
      period hPeriod where
  frequencyPositive :=
    primitiveSpinCHarmonicDiracFrequency_pos period
  spectralAgreement :=
    primitiveSpinCHarmonicDiracFrequency_sq_eq_geometricSpectrum
      period hPeriod
  diagonalizes := by
    intro positiveLevel sector circleMode seed
    exact ⟨seed.positiveSection_eigen, seed.negativeSection_eigen,
      seed.eigen_span_eq_seed_span⟩
  firstLevelRealized := by
    intro coordinate sector circleMode
    exact
      ⟨primitiveSpinCFirstPositiveHarmonicSeed_positiveSection
          period hPeriod coordinate sector circleMode,
        primitiveSpinCFirstPositiveHarmonicSeed_negativeSection
          period hPeriod coordinate sector circleMode⟩
  packetDecomposition := by
    intro tower positiveLevel sector circleMode
    exact
      ⟨tower.positive_negativeHarmonicEigenblocks_disjoint
          period hPeriod positiveLevel sector circleMode,
        tower.harmonicEigenblocks_sup_eq_seed
          period hPeriod positiveLevel sector circleMode⟩
  squaredSeedReduction := by
    intro positiveLevel sector circleMode seed
    exact ⟨seed.positiveSection_eigen, seed.negativeSection_eigen⟩
  scalarLeibnizReduction :=
    primitiveSpinCScalarHarmonicSection_dirac period hPeriod
  scalarLichnerowiczReduction := by
    intro positiveLevel harmonic sector circleMode
    exact ⟨rfl, harmonic.toDiracSeed_gradientSection_eq sector circleMode⟩
  firstScalarHarmonicRealized :=
    primitiveSpinCFirstPositiveScalarHarmonicSection_eq period hPeriod
  complexLineDiagonalization := by
    intro positiveLevel sector circleMode seed coefficient
    exact
      ⟨seed.positiveComplexLine_eigen coefficient,
        seed.negativeComplexLine_eigen coefficient⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
end JanusFormal
