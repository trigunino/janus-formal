import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Hilbert-renormed canonical physical Dirichlet space

The unconditional physical trace is transported through the canonical
Hilbert renorming.  Its kernel is a closed Hilbert subspace and is continuously
linearly equivalent to the previously constructed graph-norm Dirichlet space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertDirichlet4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1DirichletSpace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Canonical physical trace transported to the Hilbert-renormed graph. -/
def canonicalPhysicalHilbertH1Trace :
    CanonicalPhysicalScalarHilbertH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  (canonicalPhysicalH1TraceRadialPolar period hPeriod).comp
    (canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod).toContinuousLinearMap

/-- Homogeneous Dirichlet subspace in the canonical Hilbert renorming. -/
abbrev CanonicalPhysicalDirichletHilbertH1 :=
  (canonicalPhysicalHilbertH1Trace period hPeriod).ker

theorem mem_canonicalPhysicalDirichletHilbertH1_iff
    (field : CanonicalPhysicalScalarHilbertH1 period hPeriod) :
    field ∈ CanonicalPhysicalDirichletHilbertH1 period hPeriod ↔
      canonicalPhysicalHilbertH1Trace period hPeriod field = 0 :=
  Iff.rfl

theorem canonicalPhysicalDirichletHilbertH1_isClosed :
    IsClosed
      (CanonicalPhysicalDirichletHilbertH1 period hPeriod :
        Set (CanonicalPhysicalScalarHilbertH1 period hPeriod)) :=
  (canonicalPhysicalHilbertH1Trace period hPeriod).isClosed_ker

@[implicit_reducible]
def canonicalPhysicalDirichletHilbertH1CompleteSpace :
    CompleteSpace (CanonicalPhysicalDirichletHilbertH1 period hPeriod) := by
  letI : CompleteSpace (CanonicalPhysicalScalarHilbertH1 period hPeriod) :=
    canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod
  exact (canonicalPhysicalDirichletHilbertH1_isClosed
    period hPeriod).completeSpace_coe

@[implicit_reducible]
def canonicalPhysicalDirichletHilbertH1HilbertSpace :
    let _ : CompleteSpace
        (CanonicalPhysicalDirichletHilbertH1 period hPeriod) :=
      canonicalPhysicalDirichletHilbertH1CompleteSpace period hPeriod
    HilbertSpace Real
      (CanonicalPhysicalDirichletHilbertH1 period hPeriod) := by
  letI : CompleteSpace (CanonicalPhysicalScalarHilbertH1 period hPeriod) :=
    canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod
  letI : HilbertSpace Real
      (CanonicalPhysicalScalarHilbertH1 period hPeriod) :=
    canonicalPhysicalScalarHilbertH1HilbertSpace period hPeriod
  exact @HilbertSpace.mk Real
    (CanonicalPhysicalDirichletHilbertH1 period hPeriod)
    inferInstance inferInstance inferInstance
    (canonicalPhysicalDirichletHilbertH1CompleteSpace period hPeriod)

theorem canonicalPhysicalDirichletHilbertH1_nonempty :
    Nonempty (CanonicalPhysicalDirichletHilbertH1 period hPeriod) :=
  ⟨0⟩

local instance physicalScalarHilbertH1Complete :
    CompleteSpace (CanonicalPhysicalScalarHilbertH1 period hPeriod) :=
  canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod

local instance physicalDirichletHilbertH1Complete :
    CompleteSpace (CanonicalPhysicalDirichletHilbertH1 period hPeriod) :=
  canonicalPhysicalDirichletHilbertH1CompleteSpace period hPeriod

/-- Contractive orthogonal projection onto homogeneous physical Dirichlet
data in the canonical Hilbert graph. -/
def canonicalPhysicalDirichletHilbertProjection :
    CanonicalPhysicalScalarHilbertH1 period hPeriod →L[Real]
      CanonicalPhysicalDirichletHilbertH1 period hPeriod :=
  (CanonicalPhysicalDirichletHilbertH1 period hPeriod).orthogonalProjectionOnto

@[simp]
theorem canonicalPhysicalDirichletHilbertProjection_mem
    (field : CanonicalPhysicalDirichletHilbertH1 period hPeriod) :
    canonicalPhysicalDirichletHilbertProjection period hPeriod field = field :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self field

theorem canonicalPhysicalDirichletHilbertProjection_norm_le_one :
    ‖canonicalPhysicalDirichletHilbertProjection period hPeriod‖ ≤ 1 :=
  by
    change
      ‖(CanonicalPhysicalDirichletHilbertH1 period hPeriod).orthogonalProjectionOnto‖ ≤ 1
    exact
      (CanonicalPhysicalDirichletHilbertH1 period hPeriod).orthogonalProjectionOnto_norm_le

/-- Every Hilbert-renormed physical field splits into homogeneous Dirichlet
data and an orthogonal boundary component. -/
theorem canonicalPhysicalHilbertH1_dirichlet_orthogonal_decomposition
    (field : CanonicalPhysicalScalarHilbertH1 period hPeriod) :
    ∃ dirichlet : CanonicalPhysicalScalarHilbertH1 period hPeriod,
        dirichlet ∈ CanonicalPhysicalDirichletHilbertH1 period hPeriod ∧
      ∃ boundary : CanonicalPhysicalScalarHilbertH1 period hPeriod,
          boundary ∈
            (CanonicalPhysicalDirichletHilbertH1 period hPeriod)ᗮ ∧
        field = dirichlet + boundary := by
  simpa only using
    (CanonicalPhysicalDirichletHilbertH1 period hPeriod).exists_add_mem_mem_orthogonal
      field

/-- The ambient Hilbert equivalence maps the new kernel exactly to the old
graph-norm kernel. -/
theorem canonicalPhysicalDirichletHilbertH1_map_eq_graphDirichlet :
    (CanonicalPhysicalDirichletHilbertH1 period hPeriod).map
        (canonicalPhysicalScalarHilbertH1EquivGraph
          period hPeriod).toLinearMap =
      CanonicalPhysicalDirichletH1 period hPeriod := by
  ext field
  constructor
  · rintro ⟨hilbertField, hHilbertField, rfl⟩
    exact hHilbertField
  · intro hField
    refine ⟨(canonicalPhysicalScalarHilbertH1EquivGraph
      period hPeriod).symm field, ?_, by simp⟩
    simpa [CanonicalPhysicalDirichletHilbertH1,
      canonicalPhysicalHilbertH1Trace,
      CanonicalPhysicalDirichletH1] using hField

/-- Exact continuous linear equivalence of the two homogeneous Dirichlet
completions. -/
def canonicalPhysicalDirichletHilbertH1EquivGraph :
    CanonicalPhysicalDirichletHilbertH1 period hPeriod ≃L[Real]
      CanonicalPhysicalDirichletH1 period hPeriod :=
  (canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod).ofSubmodules
    (CanonicalPhysicalDirichletHilbertH1 period hPeriod)
    (CanonicalPhysicalDirichletH1 period hPeriod)
    (canonicalPhysicalDirichletHilbertH1_map_eq_graphDirichlet
      period hPeriod)

/-- Canonical smooth first jet viewed in the Hilbert-renormed completion. -/
def smoothToCanonicalPhysicalScalarHilbertH1
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalPhysicalScalarHilbertH1 period hPeriod :=
  ⟨canonicalPhysicalHilbertFirstJet period hPeriod field,
    (LinearMap.range
      (canonicalPhysicalHilbertFirstJet period hPeriod)).le_topologicalClosure
        (LinearMap.mem_range_self
          (canonicalPhysicalHilbertFirstJet period hPeriod) field)⟩

theorem canonicalPhysicalHilbertH1Trace_agrees_on_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalHilbertH1Trace period hPeriod
        (smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field := by
  rw [canonicalPhysicalHilbertH1Trace]
  change canonicalPhysicalH1TraceRadialPolar period hPeriod
      (canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod
        (smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field)) = _
  rw [show canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod
      (smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field) =
        smoothToCanonicalPhysicalScalarH1 period hPeriod field from
    canonicalPhysicalScalarHilbertH1EquivGraph_agrees_on_smooth
      period hPeriod field]
  exact canonicalPhysicalH1TraceRadialPolar_agrees_on_smooth
    period hPeriod field

theorem smooth_mem_canonicalPhysicalDirichletHilbertH1_iff
    (field : SmoothQuotientField period hPeriod Real) :
    smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field ∈
        CanonicalPhysicalDirichletHilbertH1 period hPeriod ↔
      smoothCanonicalPhysicalTraceL2 period hPeriod field = 0 := by
  rw [mem_canonicalPhysicalDirichletHilbertH1_iff,
    canonicalPhysicalHilbertH1Trace_agrees_on_smooth]

end

end P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertDirichlet4D
end JanusFormal
