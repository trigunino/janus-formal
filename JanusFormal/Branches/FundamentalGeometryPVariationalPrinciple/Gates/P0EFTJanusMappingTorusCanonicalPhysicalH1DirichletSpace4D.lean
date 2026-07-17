import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D

/-!
# Canonical physical Dirichlet graph-H1 space

The unconditional radial-polar trace defines the homogeneous Dirichlet space
as its kernel.  It is a closed, complete, nonempty linear subspace, and its
smooth elements are exactly the smooth fields with zero canonical `L²` trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalH1DirichletSpace4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Homogeneous physical Dirichlet fields: the kernel of the canonical trace. -/
abbrev CanonicalPhysicalDirichletH1 :
    Submodule Real (CanonicalPhysicalScalarH1 period hPeriod) :=
  (canonicalPhysicalH1TraceRadialPolar period hPeriod).ker

/-- Exact membership characterization by vanishing physical trace. -/
theorem mem_canonicalPhysicalDirichletH1_iff
    (field : CanonicalPhysicalScalarH1 period hPeriod) :
    field ∈ CanonicalPhysicalDirichletH1 period hPeriod ↔
      canonicalPhysicalH1TraceRadialPolar period hPeriod field = 0 := by
  rfl

/-- The homogeneous Dirichlet subspace is closed in physical graph-H1. -/
theorem canonicalPhysicalDirichletH1_isClosed :
    IsClosed
      (CanonicalPhysicalDirichletH1 period hPeriod :
        Set (CanonicalPhysicalScalarH1 period hPeriod)) :=
  (canonicalPhysicalH1TraceRadialPolar period hPeriod).isClosed_ker

/-- Completeness inherited from the complete physical graph-H1 domain. -/
@[implicit_reducible]
def canonicalPhysicalDirichletH1CompleteSpace :
    CompleteSpace (CanonicalPhysicalDirichletH1 period hPeriod) := by
  letI : CompleteSpace (CanonicalPhysicalScalarH1 period hPeriod) :=
    canonicalPhysicalScalarH1CompleteSpace period hPeriod
  infer_instance

/-- The zero field makes the canonical homogeneous Dirichlet space nonempty. -/
theorem canonicalPhysicalDirichletH1_nonempty :
    Nonempty (CanonicalPhysicalDirichletH1 period hPeriod) :=
  ⟨0⟩

/-- A smooth field lies in the completed Dirichlet space exactly when its
canonical smooth `L²` trace vanishes. -/
theorem smooth_mem_canonicalPhysicalDirichletH1_iff
    (field : SmoothQuotientField period hPeriod Real) :
    smoothToCanonicalPhysicalScalarH1 period hPeriod field ∈
        CanonicalPhysicalDirichletH1 period hPeriod ↔
      smoothCanonicalPhysicalTraceL2 period hPeriod field = 0 := by
  rw [mem_canonicalPhysicalDirichletH1_iff,
    canonicalPhysicalH1TraceRadialPolar_agrees_on_smooth]

/-- Pointwise-zero smooth Dirichlet data map into the completed kernel. -/
theorem smooth_zeroDirichlet_mem_canonicalPhysicalDirichletH1
    (field : SmoothQuotientField period hPeriod Real)
    (hField : SatisfiesDirichlet period hPeriod Real 0 field) :
    smoothToCanonicalPhysicalScalarH1 period hPeriod field ∈
      CanonicalPhysicalDirichletH1 period hPeriod := by
  rw [smooth_mem_canonicalPhysicalDirichletH1_iff]
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  change smoothTraceToL2 period hPeriod Real
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) field = 0
  apply Lp.ext
  have hTrace :
      (smoothTraceToL2 period hPeriod Real
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) field :
        _ → Real) =ᵐ[intrinsicCanonicalThroatVolumeMeasure period hPeriod]
          (throatTrace period hPeriod Real field).toFun := by
    simpa only [smoothTraceToL2] using
      (smoothThroatField_memLp period hPeriod Real
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (throatTrace period hPeriod Real field)).coeFn_toLp
  have hZero := Lp.coeFn_zero Real (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  filter_upwards [hTrace, hZero] with point hPoint hZeroPoint
  rw [hPoint, hZeroPoint]
  have hPointwise := congrArg
    (fun trace : SmoothThroatField period hPeriod Real => trace point) hField
  change (throatTrace period hPeriod Real field) point = 0 at hPointwise
  exact hPointwise

/-- Closure package for the canonical physical homogeneous Dirichlet space. -/
theorem canonicalPhysicalDirichletH1_closure :
    IsClosed
        (CanonicalPhysicalDirichletH1 period hPeriod :
          Set (CanonicalPhysicalScalarH1 period hPeriod)) ∧
      Nonempty (CanonicalPhysicalDirichletH1 period hPeriod) ∧
      (∀ field : CanonicalPhysicalScalarH1 period hPeriod,
        field ∈ CanonicalPhysicalDirichletH1 period hPeriod ↔
          canonicalPhysicalH1TraceRadialPolar period hPeriod field = 0) :=
  ⟨canonicalPhysicalDirichletH1_isClosed period hPeriod,
    canonicalPhysicalDirichletH1_nonempty period hPeriod,
    mem_canonicalPhysicalDirichletH1_iff period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalH1DirichletSpace4D
end JanusFormal
