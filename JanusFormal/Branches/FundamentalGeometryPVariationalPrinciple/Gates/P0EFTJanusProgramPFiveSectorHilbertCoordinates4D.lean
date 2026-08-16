import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Five-sector Hilbert coordinates

A single linear isometry from a Hilbert space to a right-associated product of
five sector Hilbert spaces determines canonical bounded sector injections,
coordinate maps and mutually annihilating projectors.  This is the algebraic
core needed to replace five independently supplied subspaces by one genuine
coordinate decomposition.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorHilbertCoordinates4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace BigOperators

/-- The D10-free physical sector order used by the global Candidate-A Hessian. -/
inductive FivePhysicalSector
  | metricDiffeomorphism
  | abelianGauge
  | primitiveSpinCMatter
  | longitudinalLL
  | boundaryFiniteBV
  deriving DecidableEq, Fintype

/-- Right-associated product used for explicit coordinate calculations. -/
abbrev FiveSectorProduct
    (Metric Abelian Matter Longitudinal Boundary : Type*) :=
  Metric × (Abelian × (Matter × (Longitudinal × Boundary)))

section ProductCoordinates

variable
  {Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup Metric] [NormedSpace Real Metric]
  [NormedAddCommGroup Abelian] [NormedSpace Real Abelian]
  [NormedAddCommGroup Matter] [NormedSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [NormedSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [NormedSpace Real Boundary]

/-- Metric/diffeomorphism coordinate axis. -/
def fiveSectorMetricAxis :
    Metric →L[Real]
      FiveSectorProduct Metric Abelian Matter Longitudinal Boundary :=
  ContinuousLinearMap.inl Real Metric
    (Abelian × (Matter × (Longitudinal × Boundary)))

/-- Abelian coordinate axis. -/
def fiveSectorAbelianAxis :
    Abelian →L[Real]
      FiveSectorProduct Metric Abelian Matter Longitudinal Boundary :=
  (ContinuousLinearMap.inr Real Metric
      (Abelian × (Matter × (Longitudinal × Boundary)))).comp
    (ContinuousLinearMap.inl Real Abelian
      (Matter × (Longitudinal × Boundary)))

/-- Primitive SpinC matter coordinate axis. -/
def fiveSectorMatterAxis :
    Matter →L[Real]
      FiveSectorProduct Metric Abelian Matter Longitudinal Boundary :=
  (ContinuousLinearMap.inr Real Metric
      (Abelian × (Matter × (Longitudinal × Boundary)))).comp
    ((ContinuousLinearMap.inr Real Abelian
        (Matter × (Longitudinal × Boundary))).comp
      (ContinuousLinearMap.inl Real Matter (Longitudinal × Boundary)))

/-- Longitudinal/LL coordinate axis. -/
def fiveSectorLongitudinalAxis :
    Longitudinal →L[Real]
      FiveSectorProduct Metric Abelian Matter Longitudinal Boundary :=
  (ContinuousLinearMap.inr Real Metric
      (Abelian × (Matter × (Longitudinal × Boundary)))).comp
    ((ContinuousLinearMap.inr Real Abelian
        (Matter × (Longitudinal × Boundary))).comp
      ((ContinuousLinearMap.inr Real Matter (Longitudinal × Boundary)).comp
        (ContinuousLinearMap.inl Real Longitudinal Boundary)))

/-- Finite-boundary/BV coordinate axis. -/
def fiveSectorBoundaryAxis :
    Boundary →L[Real]
      FiveSectorProduct Metric Abelian Matter Longitudinal Boundary :=
  (ContinuousLinearMap.inr Real Metric
      (Abelian × (Matter × (Longitudinal × Boundary)))).comp
    ((ContinuousLinearMap.inr Real Abelian
        (Matter × (Longitudinal × Boundary))).comp
      ((ContinuousLinearMap.inr Real Matter (Longitudinal × Boundary)).comp
        (ContinuousLinearMap.inr Real Longitudinal Boundary)))

/-- Metric coordinate extraction. -/
def fiveSectorMetricCoordinate :
    FiveSectorProduct Metric Abelian Matter Longitudinal Boundary →L[Real]
      Metric :=
  ContinuousLinearMap.fst Real Metric
    (Abelian × (Matter × (Longitudinal × Boundary)))

/-- Abelian coordinate extraction. -/
def fiveSectorAbelianCoordinate :
    FiveSectorProduct Metric Abelian Matter Longitudinal Boundary →L[Real]
      Abelian :=
  (ContinuousLinearMap.fst Real Abelian
      (Matter × (Longitudinal × Boundary))).comp
    (ContinuousLinearMap.snd Real Metric
      (Abelian × (Matter × (Longitudinal × Boundary))))

/-- Matter coordinate extraction. -/
def fiveSectorMatterCoordinate :
    FiveSectorProduct Metric Abelian Matter Longitudinal Boundary →L[Real]
      Matter :=
  (ContinuousLinearMap.fst Real Matter (Longitudinal × Boundary)).comp
    ((ContinuousLinearMap.snd Real Abelian
        (Matter × (Longitudinal × Boundary))).comp
      (ContinuousLinearMap.snd Real Metric
        (Abelian × (Matter × (Longitudinal × Boundary)))))

/-- Longitudinal coordinate extraction. -/
def fiveSectorLongitudinalCoordinate :
    FiveSectorProduct Metric Abelian Matter Longitudinal Boundary →L[Real]
      Longitudinal :=
  (ContinuousLinearMap.fst Real Longitudinal Boundary).comp
    ((ContinuousLinearMap.snd Real Matter (Longitudinal × Boundary)).comp
      ((ContinuousLinearMap.snd Real Abelian
          (Matter × (Longitudinal × Boundary))).comp
        (ContinuousLinearMap.snd Real Metric
          (Abelian × (Matter × (Longitudinal × Boundary))))))

/-- Boundary/BV coordinate extraction. -/
def fiveSectorBoundaryCoordinate :
    FiveSectorProduct Metric Abelian Matter Longitudinal Boundary →L[Real]
      Boundary :=
  (ContinuousLinearMap.snd Real Longitudinal Boundary).comp
    ((ContinuousLinearMap.snd Real Matter (Longitudinal × Boundary)).comp
      ((ContinuousLinearMap.snd Real Abelian
          (Matter × (Longitudinal × Boundary))).comp
        (ContinuousLinearMap.snd Real Metric
          (Abelian × (Matter × (Longitudinal × Boundary))))))

@[simp] theorem fiveSectorMetricCoordinate_axis (x : Metric) :
    fiveSectorMetricCoordinate
        (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
        (Longitudinal := Longitudinal) (Boundary := Boundary)
        (fiveSectorMetricAxis
          (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
          (Longitudinal := Longitudinal) (Boundary := Boundary) x) = x := rfl
@[simp] theorem fiveSectorAbelianCoordinate_axis (x : Abelian) :
    fiveSectorAbelianCoordinate
        (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
        (Longitudinal := Longitudinal) (Boundary := Boundary)
        (fiveSectorAbelianAxis
          (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
          (Longitudinal := Longitudinal) (Boundary := Boundary) x) = x := rfl
@[simp] theorem fiveSectorMatterCoordinate_axis (x : Matter) :
    fiveSectorMatterCoordinate
        (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
        (Longitudinal := Longitudinal) (Boundary := Boundary)
        (fiveSectorMatterAxis
          (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
          (Longitudinal := Longitudinal) (Boundary := Boundary) x) = x := rfl
@[simp] theorem fiveSectorLongitudinalCoordinate_axis (x : Longitudinal) :
    fiveSectorLongitudinalCoordinate
        (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
        (Longitudinal := Longitudinal) (Boundary := Boundary)
        (fiveSectorLongitudinalAxis
          (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
          (Longitudinal := Longitudinal) (Boundary := Boundary) x) = x := rfl
@[simp] theorem fiveSectorBoundaryCoordinate_axis (x : Boundary) :
    fiveSectorBoundaryCoordinate
        (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
        (Longitudinal := Longitudinal) (Boundary := Boundary)
        (fiveSectorBoundaryAxis
          (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
          (Longitudinal := Longitudinal) (Boundary := Boundary) x) = x := rfl

/-- Every product vector is the exact sum of its five coordinate axes. -/
theorem fiveSector_axis_decomposition
    (x : FiveSectorProduct Metric Abelian Matter Longitudinal Boundary) :
    fiveSectorMetricAxis (fiveSectorMetricCoordinate x) +
      fiveSectorAbelianAxis (fiveSectorAbelianCoordinate x) +
      fiveSectorMatterAxis (fiveSectorMatterCoordinate x) +
      fiveSectorLongitudinalAxis (fiveSectorLongitudinalCoordinate x) +
      fiveSectorBoundaryAxis (fiveSectorBoundaryCoordinate x) = x := by
  rcases x with ⟨metric, abelian, matter, longitudinal, boundary⟩
  simp [fiveSectorMetricAxis, fiveSectorAbelianAxis, fiveSectorMatterAxis,
    fiveSectorLongitudinalAxis, fiveSectorBoundaryAxis,
    fiveSectorMetricCoordinate, fiveSectorAbelianCoordinate,
    fiveSectorMatterCoordinate, fiveSectorLongitudinalCoordinate,
    fiveSectorBoundaryCoordinate]

end ProductCoordinates

section HilbertCoordinates

variable
  {E Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]

/-- One isometric coordinate decomposition replaces five unrelated subspace
choices. -/
structure FiveSectorHilbertCoordinates where
  decomposition : E ≃ₗᵢ[Real]
    FiveSectorProduct Metric Abelian Matter Longitudinal Boundary

namespace FiveSectorHilbertCoordinates

variable (coordinates : FiveSectorHilbertCoordinates
  (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
  (Longitudinal := Longitudinal) (Boundary := Boundary))

private def forward : E →L[Real]
    FiveSectorProduct Metric Abelian Matter Longitudinal Boundary :=
  coordinates.decomposition.toLinearIsometry.toContinuousLinearMap

private def backward :
    FiveSectorProduct Metric Abelian Matter Longitudinal Boundary →L[Real] E :=
  coordinates.decomposition.symm.toLinearIsometry.toContinuousLinearMap

/-- Canonical metric-sector projector. -/
def metricProjector : E →L[Real] E :=
  (backward coordinates).comp
    ((fiveSectorMetricAxis.comp fiveSectorMetricCoordinate).comp
      (forward coordinates))

/-- Canonical Abelian-sector projector. -/
def abelianProjector : E →L[Real] E :=
  (backward coordinates).comp
    ((fiveSectorAbelianAxis.comp fiveSectorAbelianCoordinate).comp
      (forward coordinates))

/-- Canonical primitive-matter projector. -/
def matterProjector : E →L[Real] E :=
  (backward coordinates).comp
    ((fiveSectorMatterAxis.comp fiveSectorMatterCoordinate).comp
      (forward coordinates))

/-- Canonical longitudinal/LL projector. -/
def longitudinalProjector : E →L[Real] E :=
  (backward coordinates).comp
    ((fiveSectorLongitudinalAxis.comp fiveSectorLongitudinalCoordinate).comp
      (forward coordinates))

/-- Canonical finite-boundary/BV projector. -/
def boundaryProjector : E →L[Real] E :=
  (backward coordinates).comp
    ((fiveSectorBoundaryAxis.comp fiveSectorBoundaryCoordinate).comp
      (forward coordinates))

/-- Uniform sector-projector interface. -/
def sectorProjector : FivePhysicalSector → E →L[Real] E
  | .metricDiffeomorphism => coordinates.metricProjector
  | .abelianGauge => coordinates.abelianProjector
  | .primitiveSpinCMatter => coordinates.matterProjector
  | .longitudinalLL => coordinates.longitudinalProjector
  | .boundaryFiniteBV => coordinates.boundaryProjector

/-- Every canonical sector projector is idempotent. -/
theorem sectorProjector_idempotent
    (sector : FivePhysicalSector) (x : E) :
    coordinates.sectorProjector sector
        (coordinates.sectorProjector sector x) =
      coordinates.sectorProjector sector x := by
  apply coordinates.decomposition.injective
  cases sector <;>
    simp [sectorProjector, metricProjector, abelianProjector, matterProjector,
      longitudinalProjector, boundaryProjector, forward, backward,
      fiveSectorMetricAxis, fiveSectorAbelianAxis, fiveSectorMatterAxis,
      fiveSectorLongitudinalAxis, fiveSectorBoundaryAxis,
      fiveSectorMetricCoordinate, fiveSectorAbelianCoordinate,
      fiveSectorMatterCoordinate, fiveSectorLongitudinalCoordinate,
      fiveSectorBoundaryCoordinate]

/-- Distinct canonical coordinate projectors annihilate one another. -/
theorem sectorProjector_comp_zero
    {first second : FivePhysicalSector} (h : first ≠ second) (x : E) :
    coordinates.sectorProjector first
        (coordinates.sectorProjector second x) = 0 := by
  apply coordinates.decomposition.injective
  cases first <;> cases second <;>
    simp [sectorProjector, metricProjector, abelianProjector, matterProjector,
      longitudinalProjector, boundaryProjector, forward, backward,
      fiveSectorMetricAxis, fiveSectorAbelianAxis, fiveSectorMatterAxis,
      fiveSectorLongitudinalAxis, fiveSectorBoundaryAxis,
      fiveSectorMetricCoordinate, fiveSectorAbelianCoordinate,
      fiveSectorMatterCoordinate, fiveSectorLongitudinalCoordinate,
      fiveSectorBoundaryCoordinate] at h ⊢

/-- The five canonical projectors resolve the identity. -/
theorem projectors_decompose (x : E) :
    coordinates.metricProjector x + coordinates.abelianProjector x +
      coordinates.matterProjector x + coordinates.longitudinalProjector x +
      coordinates.boundaryProjector x = x := by
  apply coordinates.decomposition.injective
  simpa [metricProjector, abelianProjector, matterProjector,
    longitudinalProjector, boundaryProjector, forward, backward] using
    fiveSector_axis_decomposition (coordinates.decomposition x)

/-- Canonical closed-coordinate subspace represented as the projector range. -/
def sectorSubspace (sector : FivePhysicalSector) : Submodule Real E :=
  (coordinates.sectorProjector sector).range

/-- A vector in one sector range is fixed by that sector projector. -/
theorem sectorProjector_eq_self_of_mem
    (sector : FivePhysicalSector) {x : E}
    (hx : x ∈ coordinates.sectorSubspace sector) :
    coordinates.sectorProjector sector x = x := by
  rcases hx with ⟨source, rfl⟩
  exact coordinates.sectorProjector_idempotent sector source

/-- Distinct coordinate ranges intersect only at zero. -/
theorem sectorSubspaces_intersection_zero
    {first second : FivePhysicalSector} (h : first ≠ second)
    {x : E}
    (hFirst : x ∈ coordinates.sectorSubspace first)
    (hSecond : x ∈ coordinates.sectorSubspace second) : x = 0 := by
  have hFixed := coordinates.sectorProjector_eq_self_of_mem first hFirst
  rcases hSecond with ⟨source, rfl⟩
  rw [← hFixed]
  exact coordinates.sectorProjector_comp_zero h source

/-- Every vector has a canonical five-sector decomposition with each summand
in its corresponding projector range. -/
theorem exists_canonical_sector_decomposition (x : E) :
    ∃ metric abelian matter longitudinal boundary : E,
      metric ∈ coordinates.sectorSubspace .metricDiffeomorphism ∧
      abelian ∈ coordinates.sectorSubspace .abelianGauge ∧
      matter ∈ coordinates.sectorSubspace .primitiveSpinCMatter ∧
      longitudinal ∈ coordinates.sectorSubspace .longitudinalLL ∧
      boundary ∈ coordinates.sectorSubspace .boundaryFiniteBV ∧
      metric + abelian + matter + longitudinal + boundary = x := by
  refine ⟨coordinates.metricProjector x, coordinates.abelianProjector x,
    coordinates.matterProjector x, coordinates.longitudinalProjector x,
    coordinates.boundaryProjector x, ?_, ?_, ?_, ?_, ?_,
    coordinates.projectors_decompose x⟩
  · exact ⟨x, rfl⟩
  · exact ⟨x, rfl⟩
  · exact ⟨x, rfl⟩
  · exact ⟨x, rfl⟩
  · exact ⟨x, rfl⟩

/-- Public algebraic checkpoint for the five-sector coordinate resolution. -/
theorem five_sector_hilbert_coordinates_gate :
    (∀ sector x, coordinates.sectorProjector sector
        (coordinates.sectorProjector sector x) =
      coordinates.sectorProjector sector x) ∧
    (∀ first second, first ≠ second → ∀ x,
      coordinates.sectorProjector first
        (coordinates.sectorProjector second x) = 0) ∧
    (∀ x, coordinates.metricProjector x + coordinates.abelianProjector x +
      coordinates.matterProjector x + coordinates.longitudinalProjector x +
      coordinates.boundaryProjector x = x) :=
  ⟨coordinates.sectorProjector_idempotent,
    fun _ _ h => coordinates.sectorProjector_comp_zero h,
    coordinates.projectors_decompose⟩

end FiveSectorHilbertCoordinates
end HilbertCoordinates

end
end P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
end JanusFormal
