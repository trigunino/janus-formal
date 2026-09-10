import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalMultiindexJetTower4D

/-!
# Affine local variational complex for T06

This gate constructs a genuine local calculation before integration for the
explicitly bounded class of autonomous affine first-order densities.  Formal
total derivatives come from the four-dimensional multi-index jet tower.  The
kernel of the local Euler map is exactly constants plus horizontal
divergences.  A square-zero linear field differential commutes with the local
horizontal differential.

The affine class is a support result; it does not contain the complete
nonlinear Candidate-A density and does not close T06.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AffineLocalVariationalComplex4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPPhysicalMultiindexJetTower4D

universe u

variable (FieldFiber : Type u)
  [NormedAddCommGroup FieldFiber] [NormedSpace Real FieldFiber]

/-- Constant, field-linear and first-derivative-linear coefficients of an
autonomous affine first-order density. -/
abbrev ProgramPT06AffineFirstOrderDensity4D :=
  Real × ((FieldFiber →L[Real] Real) ×
    (Fin 4 → FieldFiber →L[Real] Real))

/-- A zeroth-order horizontal current, one component per spacetime
direction. -/
abbrev ProgramPT06AffineZerothOrderCurrent4D :=
  Fin 4 → FieldFiber →L[Real] Real

/-- Value component of a zero-order multi-index jet. -/
def programPT06ZeroJetValue
    (jet : TruncatedMultiindexJet4D FieldFiber 0) : FieldFiber :=
  jet ⟨0, by simp⟩

/-- Value component of a first-order multi-index jet. -/
def programPT06FirstJetValue
    (jet : TruncatedMultiindexJet4D FieldFiber 1) : FieldFiber :=
  jet ⟨0, by simp⟩

/-- Directional first derivative stored by a first-order jet. -/
def programPT06FirstJetDerivative
    (jet : TruncatedMultiindexJet4D FieldFiber 1)
    (direction : Fin 4) : FieldFiber :=
  jet ⟨coordinateMultiIndex direction, by simp⟩

/-- Taking one formal total derivative and then its value component extracts
the corresponding first-jet derivative. -/
@[simp] theorem programPT06ZeroJetValue_totalDerivative
    (jet : TruncatedMultiindexJet4D FieldFiber 1)
    (direction : Fin 4) :
    programPT06ZeroJetValue FieldFiber (totalDerivative direction jet) =
      programPT06FirstJetDerivative FieldFiber jet direction := by
  unfold programPT06ZeroJetValue programPT06FirstJetDerivative totalDerivative
  apply congrArg jet
  apply Subtype.ext
  simp

/-- Pointwise evaluation of an affine first-order local density. -/
def programPT06AffineDensityEvaluation
    (density : ProgramPT06AffineFirstOrderDensity4D FieldFiber)
    (jet : TruncatedMultiindexJet4D FieldFiber 1) : Real :=
  density.1 + density.2.1 (programPT06FirstJetValue FieldFiber jet) +
    ∑ direction : Fin 4,
      density.2.2 direction
        (programPT06FirstJetDerivative FieldFiber jet direction)

/-- Formal horizontal divergence of a zeroth-order current, evaluated by the
actual multi-index total derivative. -/
def programPT06AffineCurrentTotalDivergence
    (current : ProgramPT06AffineZerothOrderCurrent4D FieldFiber)
    (jet : TruncatedMultiindexJet4D FieldFiber 1) : Real :=
  ∑ direction : Fin 4,
    current direction
      (programPT06ZeroJetValue FieldFiber (totalDerivative direction jet))

/-- Local horizontal differential from affine currents to affine
first-order densities. -/
def programPT06AffineCurrentLocalDH :
    ProgramPT06AffineZerothOrderCurrent4D FieldFiber →ₗ[Real]
      ProgramPT06AffineFirstOrderDensity4D FieldFiber where
  toFun current := (0, (0, current))
  map_add' first second := by
    simp
  map_smul' scalar current := by
    simp

/-- Evaluation of `dH` is exactly the formal total divergence, before any
integration or Stokes theorem. -/
theorem programPT06AffineCurrentLocalDH_evaluation
    (current : ProgramPT06AffineZerothOrderCurrent4D FieldFiber)
    (jet : TruncatedMultiindexJet4D FieldFiber 1) :
    programPT06AffineDensityEvaluation FieldFiber
        (programPT06AffineCurrentLocalDH FieldFiber current) jet =
      programPT06AffineCurrentTotalDivergence FieldFiber current jet := by
  simp [programPT06AffineDensityEvaluation,
    programPT06AffineCurrentLocalDH,
    programPT06AffineCurrentTotalDivergence]

/-- Formal Euler operator for autonomous affine first-order densities.  The
constant derivative coefficients have zero total derivative, leaving the
field coefficient. -/
def programPT06AffineLocalEuler :
    ProgramPT06AffineFirstOrderDensity4D FieldFiber →ₗ[Real]
      (FieldFiber →L[Real] Real) where
  toFun density := density.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Simultaneous inclusion of the constant density and a horizontal
divergence. -/
def programPT06AffineAugmentedDH :
    (Real × ProgramPT06AffineZerothOrderCurrent4D FieldFiber) →ₗ[Real]
      ProgramPT06AffineFirstOrderDensity4D FieldFiber where
  toFun input := (input.1, (0, input.2))
  map_add' first second := by
    simp
  map_smul' scalar input := by
    simp

/-- Exact affine local null-Lagrangian theorem:
`ker Euler = constants + range dH`. -/
theorem programPT06_affineLocalEuler_ker_eq_augmentedDH_range :
    LinearMap.ker (programPT06AffineLocalEuler FieldFiber) =
      LinearMap.range (programPT06AffineAugmentedDH FieldFiber) := by
  ext density
  constructor
  · intro hNull
    change density.2.1 = 0 at hNull
    refine ⟨(density.1, density.2.2), ?_⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hNull.symm
      · rfl
  · rintro ⟨input, rfl⟩
    rfl

/-- A linear BRST-type differential on the field fiber. -/
structure ProgramPT06SquareZeroFieldDifferential4D where
  differential : FieldFiber →L[Real] FieldFiber
  square_zero : differential.comp differential = 0

/-- Induced differential on affine boundary currents. -/
def programPT06AffineCurrentBRST
    (brst : ProgramPT06SquareZeroFieldDifferential4D FieldFiber)
    (current : ProgramPT06AffineZerothOrderCurrent4D FieldFiber) :
    ProgramPT06AffineZerothOrderCurrent4D FieldFiber :=
  fun direction => (current direction).comp brst.differential

/-- Induced differential on affine first-order densities. -/
def programPT06AffineDensityBRST
    (brst : ProgramPT06SquareZeroFieldDifferential4D FieldFiber)
    (density : ProgramPT06AffineFirstOrderDensity4D FieldFiber) :
    ProgramPT06AffineFirstOrderDensity4D FieldFiber :=
  (0, (density.2.1.comp brst.differential,
    fun direction => (density.2.2 direction).comp brst.differential))

/-- The induced BRST differential commutes with the local horizontal
differential. -/
theorem programPT06AffineBRST_commutes_localDH
    (brst : ProgramPT06SquareZeroFieldDifferential4D FieldFiber)
    (current : ProgramPT06AffineZerothOrderCurrent4D FieldFiber) :
    programPT06AffineDensityBRST FieldFiber brst
        (programPT06AffineCurrentLocalDH FieldFiber current) =
      programPT06AffineCurrentLocalDH FieldFiber
        (programPT06AffineCurrentBRST FieldFiber brst current) := by
  rfl

/-- The induced BRST differential squares to zero on every affine density. -/
theorem programPT06AffineDensityBRST_square_zero
    (brst : ProgramPT06SquareZeroFieldDifferential4D FieldFiber)
    (density : ProgramPT06AffineFirstOrderDensity4D FieldFiber) :
    programPT06AffineDensityBRST FieldFiber brst
        (programPT06AffineDensityBRST FieldFiber brst density) = 0 := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro field
      have hSquare := DFunLike.congr_fun brst.square_zero field
      change density.2.1 (brst.differential (brst.differential field)) = 0
      change brst.differential (brst.differential field) = 0 at hSquare
      rw [hSquare]
      exact map_zero density.2.1
    · funext direction
      apply ContinuousLinearMap.ext
      intro field
      have hSquare := DFunLike.congr_fun brst.square_zero field
      change density.2.2 direction
          (brst.differential (brst.differential field)) = 0
      change brst.differential (brst.differential field) = 0 at hSquare
      rw [hSquare]
      exact map_zero (density.2.2 direction)

end

end P0EFTJanusProgramPT06AffineLocalVariationalComplex4D
end JanusFormal
