import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2LinearIsometryResolution4D

/-!
# Five-sector L² Hilbert coordinates

Minimal Hilbert-coordinate facade built from one isometry to the nested L²
five-sector product.  All projector facts are delegated to the orthogonal
product resolution obtained after the continuous forgetting equivalence.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D
open P0EFTJanusProgramPFiveSectorL2LinearIsometryResolution4D

variable
  {E Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]

/-- One genuine Hilbert coordinate decomposition into the nested L² product. -/
structure FiveSectorL2HilbertCoordinates where
  decomposition : E ≃ₗᵢ[Real]
    FiveSectorL2Product Metric Abelian Matter Longitudinal Boundary

namespace FiveSectorL2HilbertCoordinates

variable (coordinates : FiveSectorL2HilbertCoordinates
  (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
  (Longitudinal := Longitudinal) (Boundary := Boundary))

/-- Raw-product orthogonal decomposition associated to the L² coordinates. -/
def orthogonalProductDecomposition :
    FiveSectorOrthogonalProductDecomposition
      (E := E)
      (MetricDiffeomorphism := Metric)
      (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter)
      (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary) :=
  fiveSectorOrthogonalProductDecompositionOfL2Isometry
    coordinates.decomposition

/-- Uniform transported projector for the five physical slots. -/
def sectorProjector (sector : FiveSectorSlot) : E →L[Real] E :=
  coordinates.orthogonalProductDecomposition.projection sector

/-- Transported metric/diffeomorphism projector. -/
def metricProjector : E →L[Real] E :=
  coordinates.sectorProjector .metricDiffeomorphism

/-- Transported Abelian-gauge projector. -/
def abelianProjector : E →L[Real] E :=
  coordinates.sectorProjector .abelianGauge

/-- Transported primitive-SpinC-matter projector. -/
def matterProjector : E →L[Real] E :=
  coordinates.sectorProjector .primitiveSpinCMatter

/-- Transported longitudinal/LL projector. -/
def longitudinalProjector : E →L[Real] E :=
  coordinates.sectorProjector .longitudinalLL

/-- Transported boundary/finite-BV projector. -/
def boundaryProjector : E →L[Real] E :=
  coordinates.sectorProjector .boundaryFiniteBV

/-- Every transported projector is idempotent. -/
theorem sectorProjector_idempotent (sector : FiveSectorSlot) (state : E) :
    coordinates.sectorProjector sector
        (coordinates.sectorProjector sector state) =
      coordinates.sectorProjector sector state :=
  coordinates.orthogonalProductDecomposition.projection_idempotent sector state

/-- Distinct transported projectors compose to zero. -/
theorem sectorProjector_comp_zero
    (first second : FiveSectorSlot) (hDistinct : first ≠ second) :
    (coordinates.sectorProjector first).comp
        (coordinates.sectorProjector second) = 0 :=
  coordinates.orthogonalProductDecomposition.projection_comp_zero
    first second hDistinct

/-- Every transported projector is self-adjoint. -/
theorem sectorProjector_selfAdjoint
    (sector : FiveSectorSlot) (first second : E) :
    inner Real (coordinates.sectorProjector sector first) second =
      inner Real first (coordinates.sectorProjector sector second) :=
  coordinates.orthogonalProductDecomposition.projection_selfAdjoint
    sector first second

/-- Images of distinct transported projectors are orthogonal. -/
theorem sectorProjector_orthogonal
    (first second : FiveSectorSlot) (hDistinct : first ≠ second)
    (x y : E) :
    inner Real (coordinates.sectorProjector first x)
        (coordinates.sectorProjector second y) = 0 :=
  coordinates.orthogonalProductDecomposition.projection_orthogonal
    first second hDistinct x y

/-- The five transported projectors reconstruct every state. -/
theorem projectors_reconstruct (state : E) :
    (∑ sector : FiveSectorSlot, coordinates.sectorProjector sector state) =
      state :=
  coordinates.orthogonalProductDecomposition.sum_projection_apply state

private theorem five_sector_slot_univ :
    (Finset.univ : Finset FiveSectorSlot) =
      { .metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
        .longitudinalLL, .boundaryFiniteBV } := by
  decide

/-- Named-coordinate form of the reconstruction identity. -/
theorem projectors_decompose (state : E) :
    coordinates.metricProjector state +
        coordinates.abelianProjector state +
        coordinates.matterProjector state +
        coordinates.longitudinalProjector state +
        coordinates.boundaryProjector state = state := by
  have hReconstruct := coordinates.projectors_reconstruct state
  rw [five_sector_slot_univ] at hReconstruct
  simpa [metricProjector, abelianProjector, matterProjector,
    longitudinalProjector, boundaryProjector, add_assoc] using hReconstruct

/-- Exact Pythagorean decomposition generated by the L² coordinates. -/
theorem norm_sq_decomposition (state : E) :
    ‖state‖ ^ 2 =
      ∑ sector : FiveSectorSlot,
        ‖coordinates.sectorProjector sector state‖ ^ 2 :=
  fiveSectorProjection_norm_sq_sum
    coordinates.orthogonalProductDecomposition state

/-- Public checkpoint for the L² five-sector facade. -/
theorem five_sector_l2_hilbert_coordinates_gate :
    (∀ sector state,
      coordinates.sectorProjector sector
          (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector state) ∧
    (∀ first second, first ≠ second → ∀ x y,
      inner Real (coordinates.sectorProjector first x)
          (coordinates.sectorProjector second y) = 0) ∧
    (∀ state,
      (∑ sector : FiveSectorSlot,
        coordinates.sectorProjector sector state) = state) ∧
    (∀ state,
      ‖state‖ ^ 2 =
        ∑ sector : FiveSectorSlot,
          ‖coordinates.sectorProjector sector state‖ ^ 2) :=
  ⟨coordinates.sectorProjector_idempotent,
    fun _ _ hDistinct => coordinates.sectorProjector_orthogonal _ _ hDistinct,
    coordinates.projectors_reconstruct,
    coordinates.norm_sq_decomposition⟩

end FiveSectorL2HilbertCoordinates

end

end P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D
end JanusFormal
