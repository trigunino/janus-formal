import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Exact bulk/boundary cancellation on a finite three-dimensional box

An arbitrary, position-dependent flux is placed on every coordinate-normal
face of a finite rectangular lattice.  Summing its forward divergence over
all cells telescopes exactly to the outward flux through the six faces.  The
negative faces carry the opposite orientation.  Consequently, a boundary
counterterm equal to minus that six-face flux cancels the bulk-divergence
first variation exactly, sector by sector.

This is a finite-network Stokes theorem.  It does not construct a manifold
embedding, a continuum GHY term, null boundaries, joints, or corner terms.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteBoxBulkBoundaryStokes

set_option autoImplicit false

open scoped BigOperators

/-- Numbers of cells in the three coordinate directions. -/
structure BoxShape3 where
  xCells : ℕ
  yCells : ℕ
  zCells : ℕ

/-- Arbitrary variable fluxes through the coordinate-normal cell faces.
The first coordinate of `xFlux`, the second of `yFlux`, and the third of
`zFlux` label the corresponding face position. -/
structure VariableFlux3 where
  xFlux : ℕ → ℕ → ℕ → ℝ
  yFlux : ℕ → ℕ → ℕ → ℝ
  zFlux : ℕ → ℕ → ℕ → ℝ

/-- Sum of a cell density over the finite box. -/
def boxSum (shape : BoxShape3) (density : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range shape.xCells,
    ∑ j ∈ Finset.range shape.yCells,
      ∑ k ∈ Finset.range shape.zCells, density i j k

/-- Forward discrete divergence in one cell. -/
def cellDivergence (flux : VariableFlux3) (i j k : ℕ) : ℝ :=
  (flux.xFlux (i + 1) j k - flux.xFlux i j k) +
  (flux.yFlux i (j + 1) k - flux.yFlux i j k) +
  (flux.zFlux i j (k + 1) - flux.zFlux i j k)

/-- Integrated bulk divergence on the box. -/
def bulkDivergence (shape : BoxShape3) (flux : VariableFlux3) : ℝ :=
  boxSum shape (cellDivergence flux)

/-- Outward flux on the negative `x` face. -/
def xNegativeFaceFlux (shape : BoxShape3) (flux : VariableFlux3) : ℝ :=
  -∑ j ∈ Finset.range shape.yCells,
    ∑ k ∈ Finset.range shape.zCells, flux.xFlux 0 j k

/-- Outward flux on the positive `x` face. -/
def xPositiveFaceFlux (shape : BoxShape3) (flux : VariableFlux3) : ℝ :=
  ∑ j ∈ Finset.range shape.yCells,
    ∑ k ∈ Finset.range shape.zCells, flux.xFlux shape.xCells j k

/-- Outward flux on the negative `y` face. -/
def yNegativeFaceFlux (shape : BoxShape3) (flux : VariableFlux3) : ℝ :=
  -∑ i ∈ Finset.range shape.xCells,
    ∑ k ∈ Finset.range shape.zCells, flux.yFlux i 0 k

/-- Outward flux on the positive `y` face. -/
def yPositiveFaceFlux (shape : BoxShape3) (flux : VariableFlux3) : ℝ :=
  ∑ i ∈ Finset.range shape.xCells,
    ∑ k ∈ Finset.range shape.zCells, flux.yFlux i shape.yCells k

/-- Outward flux on the negative `z` face. -/
def zNegativeFaceFlux (shape : BoxShape3) (flux : VariableFlux3) : ℝ :=
  -∑ i ∈ Finset.range shape.xCells,
    ∑ j ∈ Finset.range shape.yCells, flux.zFlux i j 0

/-- Outward flux on the positive `z` face. -/
def zPositiveFaceFlux (shape : BoxShape3) (flux : VariableFlux3) : ℝ :=
  ∑ i ∈ Finset.range shape.xCells,
    ∑ j ∈ Finset.range shape.yCells, flux.zFlux i j shape.zCells

/-- The six oriented faces of the finite box. -/
def orientedBoundaryFlux (shape : BoxShape3) (flux : VariableFlux3) : ℝ :=
  xNegativeFaceFlux shape flux + xPositiveFaceFlux shape flux +
  yNegativeFaceFlux shape flux + yPositiveFaceFlux shape flux +
  zNegativeFaceFlux shape flux + zPositiveFaceFlux shape flux

theorem orientedBoundaryFlux_eq_six_faces
    (shape : BoxShape3) (flux : VariableFlux3) :
    orientedBoundaryFlux shape flux =
      xNegativeFaceFlux shape flux + xPositiveFaceFlux shape flux +
      yNegativeFaceFlux shape flux + yPositiveFaceFlux shape flux +
      zNegativeFaceFlux shape flux + zPositiveFaceFlux shape flux := by
  rfl

/-- The one-dimensional telescoping identity used in each coordinate. -/
theorem sum_forwardDifference (count : ℕ) (field : ℕ → ℝ) :
    (∑ index ∈ Finset.range count,
      (field (index + 1) - field index)) =
    field count - field 0 := by
  exact Finset.sum_range_sub field count

/-- Telescoping in the first coordinate, with arbitrary transverse
dependence. -/
theorem boxSum_forwardDifference_x
    (shape : BoxShape3) (field : ℕ → ℕ → ℕ → ℝ) :
    boxSum shape (fun i j k ↦ field (i + 1) j k - field i j k) =
      (∑ j ∈ Finset.range shape.yCells,
        ∑ k ∈ Finset.range shape.zCells, field shape.xCells j k) -
      (∑ j ∈ Finset.range shape.yCells,
        ∑ k ∈ Finset.range shape.zCells, field 0 j k) := by
  calc
    boxSum shape (fun i j k ↦ field (i + 1) j k - field i j k) =
        ∑ i ∈ Finset.range shape.xCells,
          ((∑ j ∈ Finset.range shape.yCells,
              ∑ k ∈ Finset.range shape.zCells, field (i + 1) j k) -
            (∑ j ∈ Finset.range shape.yCells,
              ∑ k ∈ Finset.range shape.zCells, field i j k)) := by
      unfold boxSum
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.sum_sub_distrib]
    _ = _ := by
      exact sum_forwardDifference shape.xCells
        (fun i ↦ ∑ j ∈ Finset.range shape.yCells,
          ∑ k ∈ Finset.range shape.zCells, field i j k)

/-- Telescoping in the second coordinate, with arbitrary transverse
dependence. -/
theorem boxSum_forwardDifference_y
    (shape : BoxShape3) (field : ℕ → ℕ → ℕ → ℝ) :
    boxSum shape (fun i j k ↦ field i (j + 1) k - field i j k) =
      (∑ i ∈ Finset.range shape.xCells,
        ∑ k ∈ Finset.range shape.zCells, field i shape.yCells k) -
      (∑ i ∈ Finset.range shape.xCells,
        ∑ k ∈ Finset.range shape.zCells, field i 0 k) := by
  calc
    boxSum shape (fun i j k ↦ field i (j + 1) k - field i j k) =
        ∑ i ∈ Finset.range shape.xCells,
          ((∑ k ∈ Finset.range shape.zCells,
              field i shape.yCells k) -
            (∑ k ∈ Finset.range shape.zCells, field i 0 k)) := by
      unfold boxSum
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j ∈ Finset.range shape.yCells,
            ∑ k ∈ Finset.range shape.zCells,
              (field i (j + 1) k - field i j k)) =
            ∑ j ∈ Finset.range shape.yCells,
              ((∑ k ∈ Finset.range shape.zCells,
                  field i (j + 1) k) -
                (∑ k ∈ Finset.range shape.zCells,
                  field i j k)) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.sum_sub_distrib]
        _ = _ := by
          exact sum_forwardDifference shape.yCells
            (fun j ↦ ∑ k ∈ Finset.range shape.zCells, field i j k)
    _ = _ := by
      simp only [Finset.sum_sub_distrib]

/-- Telescoping in the third coordinate, with arbitrary transverse
dependence. -/
theorem boxSum_forwardDifference_z
    (shape : BoxShape3) (field : ℕ → ℕ → ℕ → ℝ) :
    boxSum shape (fun i j k ↦ field i j (k + 1) - field i j k) =
      (∑ i ∈ Finset.range shape.xCells,
        ∑ j ∈ Finset.range shape.yCells, field i j shape.zCells) -
      (∑ i ∈ Finset.range shape.xCells,
        ∑ j ∈ Finset.range shape.yCells, field i j 0) := by
  calc
    boxSum shape (fun i j k ↦ field i j (k + 1) - field i j k) =
        ∑ i ∈ Finset.range shape.xCells,
          ∑ j ∈ Finset.range shape.yCells,
            (field i j shape.zCells - field i j 0) := by
      unfold boxSum
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_forwardDifference shape.zCells (fun k ↦ field i j k)
    _ = _ := by
      simp only [Finset.sum_sub_distrib]

/-- Exact finite-box divergence theorem for arbitrary variable fluxes. -/
theorem bulkDivergence_eq_orientedBoundaryFlux
    (shape : BoxShape3) (flux : VariableFlux3) :
    bulkDivergence shape flux = orientedBoundaryFlux shape flux := by
  calc
    bulkDivergence shape flux =
        boxSum shape
            (fun i j k ↦ flux.xFlux (i + 1) j k - flux.xFlux i j k) +
        boxSum shape
            (fun i j k ↦ flux.yFlux i (j + 1) k - flux.yFlux i j k) +
        boxSum shape
            (fun i j k ↦ flux.zFlux i j (k + 1) - flux.zFlux i j k) := by
      simp [bulkDivergence, cellDivergence, boxSum,
        Finset.sum_add_distrib]
    _ =
        ((∑ j ∈ Finset.range shape.yCells,
            ∑ k ∈ Finset.range shape.zCells,
              flux.xFlux shape.xCells j k) -
          (∑ j ∈ Finset.range shape.yCells,
            ∑ k ∈ Finset.range shape.zCells, flux.xFlux 0 j k)) +
        ((∑ i ∈ Finset.range shape.xCells,
            ∑ k ∈ Finset.range shape.zCells,
              flux.yFlux i shape.yCells k) -
          (∑ i ∈ Finset.range shape.xCells,
            ∑ k ∈ Finset.range shape.zCells, flux.yFlux i 0 k)) +
        ((∑ i ∈ Finset.range shape.xCells,
            ∑ j ∈ Finset.range shape.yCells,
              flux.zFlux i j shape.zCells) -
          (∑ i ∈ Finset.range shape.xCells,
            ∑ j ∈ Finset.range shape.yCells, flux.zFlux i j 0)) := by
      rw [boxSum_forwardDifference_x, boxSum_forwardDifference_y,
        boxSum_forwardDifference_z]
    _ = orientedBoundaryFlux shape flux := by
      simp [orientedBoundaryFlux, xNegativeFaceFlux, xPositiveFaceFlux,
        yNegativeFaceFlux, yPositiveFaceFlux,
        zNegativeFaceFlux, zPositiveFaceFlux]
      ring

/-- The bulk part of the first-variation ledger. -/
def bulkDivergenceFirstVariation
    (shape : BoxShape3) (fluxVariation : VariableFlux3) : ℝ :=
  bulkDivergence shape fluxVariation

/-- Boundary counterterm with the sign opposite to the outward flux. -/
def boundaryCountertermFirstVariation
    (shape : BoxShape3) (fluxVariation : VariableFlux3) : ℝ :=
  -orientedBoundaryFlux shape fluxVariation

/-- Full matched bulk-plus-boundary first variation. -/
def matchedBulkBoundaryFirstVariation
    (shape : BoxShape3) (fluxVariation : VariableFlux3) : ℝ :=
  bulkDivergenceFirstVariation shape fluxVariation +
    boundaryCountertermFirstVariation shape fluxVariation

/-- The six-face counterterm cancels the bulk divergence exactly. -/
theorem matchedBulkBoundaryFirstVariation_eq_zero
    (shape : BoxShape3) (fluxVariation : VariableFlux3) :
    matchedBulkBoundaryFirstVariation shape fluxVariation = 0 := by
  rw [matchedBulkBoundaryFirstVariation,
    bulkDivergenceFirstVariation, boundaryCountertermFirstVariation,
    bulkDivergence_eq_orientedBoundaryFlux]
  ring

/-- Independent sum of the two Janus-sector ledgers. -/
def twoSectorBulkBoundaryFirstVariation
    (shape : BoxShape3)
    (plusFluxVariation minusFluxVariation : VariableFlux3) : ℝ :=
  matchedBulkBoundaryFirstVariation shape plusFluxVariation +
    matchedBulkBoundaryFirstVariation shape minusFluxVariation

theorem twoSectorBulkBoundaryFirstVariation_eq_zero
    (shape : BoxShape3)
    (plusFluxVariation minusFluxVariation : VariableFlux3) :
    twoSectorBulkBoundaryFirstVariation shape
      plusFluxVariation minusFluxVariation = 0 := by
  simp [twoSectorBulkBoundaryFirstVariation,
    matchedBulkBoundaryFirstVariation_eq_zero]

/-- Exchanging the two independently cancelled sectors leaves the ledger
unchanged; no stronger physical PT identification is assumed here. -/
theorem twoSectorBulkBoundaryFirstVariation_sectorExchange
    (shape : BoxShape3)
    (plusFluxVariation minusFluxVariation : VariableFlux3) :
    twoSectorBulkBoundaryFirstVariation shape
        plusFluxVariation minusFluxVariation =
      twoSectorBulkBoundaryFirstVariation shape
        minusFluxVariation plusFluxVariation := by
  rw [twoSectorBulkBoundaryFirstVariation_eq_zero,
    twoSectorBulkBoundaryFirstVariation_eq_zero]

end P0EFTJanusFiniteBoxBulkBoundaryStokes
end JanusFormal
