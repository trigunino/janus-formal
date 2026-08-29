import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D

/-!
# Physical Janus scalar Hilbert Green-system interface

This file connects the abstract closed-graph/boundary-triple architecture to the
actual physical bulk and throat L2 spaces already constructed on the effective
D8 quotient.

The only supplied smooth data are:

* the smooth scalar Euler operator as a linear map into physical bulk L2;
* the smooth normal trace into physical throat L2;
* the exact Green identity;
* surjectivity of the paired smooth Cauchy trace.

No analytic property is smuggled into these fields.  In particular, the graph
trace estimate is a separate quantitative package and closability is handled by
the later closed-graph realization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev SmoothScalarDomain :=
  SmoothQuotientField period hPeriod Real

private abbrev BulkL2 :=
  CanonicalPhysicalBulkL2 period hPeriod

private abbrev ThroatL2 :=
  CanonicalPhysicalThroatL2 period hPeriod

/-- Concrete smooth scalar differential data needed by the Hilbert Green
system.  The value trace is already canonical; only the smooth normal trace and
bulk Euler operator remain supplied. -/
structure CanonicalPhysicalSmoothScalarGreenData where
  operator : SmoothScalarDomain period hPeriod →ₗ[Real] BulkL2 period hPeriod
  normalTrace : SmoothScalarDomain period hPeriod →ₗ[Real] ThroatL2 period hPeriod
  boundary_surjective : Function.Surjective
    (fun field : SmoothScalarDomain period hPeriod =>
      (smoothCanonicalPhysicalTraceL2 period hPeriod field,
        normalTrace field))
  green_identity : ∀ first second : SmoothScalarDomain period hPeriod,
    inner Real (operator first)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
          (operator second) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (smoothCanonicalPhysicalTraceL2 period hPeriod first,
          normalTrace first)
        (smoothCanonicalPhysicalTraceL2 period hPeriod second,
          normalTrace second)

/-- Paired smooth physical Cauchy trace `(valueTrace, normalTrace)`. -/
def canonicalPhysicalSmoothPairedBoundaryTrace
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod) :
    SmoothScalarDomain period hPeriod →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := ThroatL2 period hPeriod) where
  toFun field :=
    (smoothCanonicalPhysicalTraceL2 period hPeriod field,
      data.normalTrace field)
  map_add' first second := by
    ext <;> simp
  map_smul' scalar field := by
    ext <;> simp

@[simp] theorem canonicalPhysicalSmoothPairedBoundaryTrace_fst
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod)
    (field : SmoothScalarDomain period hPeriod) :
    (canonicalPhysicalSmoothPairedBoundaryTrace period hPeriod data field).1 =
      smoothCanonicalPhysicalTraceL2 period hPeriod field :=
  rfl

@[simp] theorem canonicalPhysicalSmoothPairedBoundaryTrace_snd
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod)
    (field : SmoothScalarDomain period hPeriod) :
    (canonicalPhysicalSmoothPairedBoundaryTrace period hPeriod data field).2 =
      data.normalTrace field :=
  rfl

/-- The actual physical smooth spaces instantiate the abstract scalar Hilbert
Green system. -/
def canonicalPhysicalScalarHilbertGreenSystem
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod) :
    CanonicalScalarHilbertGreenSystem
      (Domain := SmoothScalarDomain period hPeriod)
      (Ambient := BulkL2 period hPeriod)
      (Trace := ThroatL2 period hPeriod) where
  inclusion := smoothToCanonicalPhysicalBulkL2 period hPeriod
  operator := data.operator
  boundaryTrace := canonicalPhysicalSmoothPairedBoundaryTrace
    period hPeriod data
  boundary_surjective := by
    intro boundary
    obtain ⟨field, hField⟩ := data.boundary_surjective boundary
    exact ⟨field, hField⟩
  green_identity := data.green_identity

/-- Quantitative graph-norm estimate for the paired physical Cauchy trace. -/
structure CanonicalPhysicalPairedBoundaryGraphBound
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : SmoothScalarDomain period hPeriod,
    ‖canonicalPhysicalSmoothPairedBoundaryTrace period hPeriod data field‖ ≤
      constant *
        ‖canonicalScalarSmoothToOperatorGraphLinearMap
          (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data) field‖

/-- Conversion of the concrete graph bound into the generic completion input. -/
def CanonicalPhysicalPairedBoundaryGraphBound.toAbstract
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod)
    (bound : CanonicalPhysicalPairedBoundaryGraphBound period hPeriod data) :
    HasCanonicalScalarHilbertBoundaryGraphBound
      (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data) where
  constant := bound.constant
  nonnegative := bound.nonnegative
  bound := bound.bound

/-- Completed physical graph domain. -/
abbrev CanonicalPhysicalScalarOperatorGraphSpace
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod) :=
  CanonicalScalarOperatorGraphSpace
    (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data)

/-- Completed paired physical Cauchy trace. -/
def canonicalPhysicalCompletedBoundaryTrace
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod)
    (bound : CanonicalPhysicalPairedBoundaryGraphBound period hPeriod data) :
    CanonicalPhysicalScalarOperatorGraphSpace period hPeriod data →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := ThroatL2 period hPeriod) :=
  canonicalScalarCompletedBoundaryTrace
    (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data)
    (bound.toAbstract period hPeriod data)

/-- Agreement of the completed physical Cauchy trace with its smooth origin. -/
theorem canonicalPhysicalCompletedBoundaryTrace_agrees_on_smooth
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod)
    (bound : CanonicalPhysicalPairedBoundaryGraphBound period hPeriod data)
    (field : SmoothScalarDomain period hPeriod) :
    canonicalPhysicalCompletedBoundaryTrace period hPeriod data bound
        (canonicalScalarSmoothToOperatorGraphLinearMap
          (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data) field) =
      canonicalPhysicalSmoothPairedBoundaryTrace period hPeriod data field :=
  canonicalScalarCompletedBoundaryTrace_agrees_on_smooth
    (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data)
    (bound.toAbstract period hPeriod data) field

/-- The abstract completion theorem specialized to the physical Janus scalar
spaces. -/
theorem canonicalPhysicalScalarHilbertGreenSystem_certificate
    (data : CanonicalPhysicalSmoothScalarGreenData period hPeriod)
    (bound : CanonicalPhysicalPairedBoundaryGraphBound period hPeriod data) :
    DenseRange
        (canonicalScalarSmoothToOperatorGraphLinearMap
          (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data)) ∧
      Function.Surjective
        (canonicalPhysicalCompletedBoundaryTrace period hPeriod data bound) ∧
      (∀ first second : CanonicalPhysicalScalarOperatorGraphSpace
          period hPeriod data,
        inner Real
            (canonicalScalarOperatorGraphOperator
              (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data) first)
            (canonicalScalarOperatorGraphInclusion
              (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data) second) -
          inner Real
            (canonicalScalarOperatorGraphInclusion
              (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data) first)
            (canonicalScalarOperatorGraphOperator
              (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data) second) =
        canonicalScalarCompletedBoundaryGreenPairing
          (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data)
          (bound.toAbstract period hPeriod data) first second) :=
  canonicalScalarOperatorGraphCompletion_certificate
    (canonicalPhysicalScalarHilbertGreenSystem period hPeriod data)
    (bound.toAbstract period hPeriod data)

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
end JanusFormal
