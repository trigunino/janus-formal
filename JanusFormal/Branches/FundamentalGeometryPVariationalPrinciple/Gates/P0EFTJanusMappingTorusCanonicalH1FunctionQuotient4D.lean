import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D

/-!
# The canonical H1 function quotient on the effective mapping torus

The existing first-jet completion is a closed subspace of an `L2` jet space.
This file removes exactly the possible vertical states in that closure: it
quotients by the kernel of the continuous value projection to spacetime `L2`.
The resulting normed quotient has an injective continuous realization in the
canonical physical `L2`, and smooth fields remain dense.

This is a genuine first-order construction on the effective mapping torus. It
does not identify the periodic `Z^4` coefficient model with global sections,
does not construct higher Sobolev orders, and does not assert that the trace
descends through the value-kernel.  The last issue is exposed as the exact
kernel inclusion needed for such a descent.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalH1FunctionQuotient4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Scalar `L2` on the canonical physical volume of the effective quotient. -/
abbrev CanonicalPhysicalScalarL2 :=
  let _ : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  Lp Real (2 : ENNReal)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Smooth scalar field viewed in the canonical physical spacetime `L2`. -/
def smoothCanonicalPhysicalScalarL2
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalPhysicalScalarL2 period hPeriod := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact smoothFieldToL2 period hPeriod Real
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field

/-- Forget the derivative coordinates of the canonical graph-H1 completion. -/
def canonicalPhysicalH1ToL2 :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalScalarL2 period hPeriod := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact h1GraphToL2 period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- The function-valued first-order quotient: possible vertical limit jets
are identified precisely when they have the same spacetime `L2` value. -/
abbrev CanonicalPhysicalScalarH1FunctionQuotient :=
  CanonicalPhysicalScalarH1 period hPeriod ⧸
    (canonicalPhysicalH1ToL2 period hPeriod).ker

/-- Completeness of the function quotient follows from completeness of the
canonical graph space and closedness of the continuous value kernel. -/
@[implicit_reducible]
def canonicalPhysicalScalarH1FunctionQuotientCompleteSpace :
    CompleteSpace
      (CanonicalPhysicalScalarH1FunctionQuotient period hPeriod) := by
  letI : CompleteSpace (CanonicalPhysicalScalarH1 period hPeriod) :=
    canonicalPhysicalScalarH1CompleteSpace period hPeriod
  infer_instance

/-- The quotient map from the graph completion to its function quotient. -/
def canonicalH1FunctionQuotientMap :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalScalarH1FunctionQuotient period hPeriod :=
  (canonicalPhysicalH1ToL2 period hPeriod).ker.mkQL

/-- The value projection descends continuously through its own kernel. -/
def canonicalH1FunctionQuotientToL2 :
    CanonicalPhysicalScalarH1FunctionQuotient period hPeriod →L[Real]
      CanonicalPhysicalScalarL2 period hPeriod :=
  (canonicalPhysicalH1ToL2 period hPeriod).ker.liftQL
    (canonicalPhysicalH1ToL2 period hPeriod) le_rfl

@[simp]
theorem canonicalH1FunctionQuotientToL2_mk
    (field : CanonicalPhysicalScalarH1 period hPeriod) :
    canonicalH1FunctionQuotientToL2 period hPeriod
        (canonicalH1FunctionQuotientMap period hPeriod field) =
      canonicalPhysicalH1ToL2 period hPeriod field := by
  rfl

/-- No nonzero class is lost by the canonical `L2` realization. -/
theorem canonicalH1FunctionQuotientToL2_injective :
    Function.Injective
      (canonicalH1FunctionQuotientToL2 period hPeriod) := by
  let f := canonicalPhysicalH1ToL2 period hPeriod
  let S := f.ker
  change Function.Injective (S.liftQL f le_rfl)
  have hKer : (S.liftQ f.toLinearMap le_rfl).ker = ⊥ :=
    Submodule.ker_liftQ_eq_bot S f.toLinearMap le_rfl le_rfl
  exact LinearMap.ker_eq_bot.mp hKer

/-- Smooth quotient fields map to the genuine function quotient. -/
def smoothToCanonicalH1FunctionQuotient :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalScalarH1FunctionQuotient period hPeriod :=
  (canonicalPhysicalH1ToL2 period hPeriod).ker.mkQ.comp
    (smoothToCanonicalPhysicalScalarH1 period hPeriod)

/-- Smooth fields are still dense after passing from graph jets to functions. -/
theorem smoothToCanonicalH1FunctionQuotient_denseRange :
    DenseRange (smoothToCanonicalH1FunctionQuotient period hPeriod) := by
  have hQuotient : DenseRange
      ((canonicalPhysicalH1ToL2 period hPeriod).ker.mkQL) :=
    ((canonicalPhysicalH1ToL2 period hPeriod).ker.mkQ_surjective).denseRange
  exact hQuotient.comp
    (smoothToCanonicalPhysicalScalarH1_denseRange period hPeriod)
    (canonicalPhysicalH1ToL2 period hPeriod).ker.continuous_mkQ

theorem canonicalH1FunctionQuotientToL2_agrees_on_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalH1FunctionQuotientToL2 period hPeriod
        (smoothToCanonicalH1FunctionQuotient period hPeriod field) =
      smoothCanonicalPhysicalScalarL2 period hPeriod field := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  rw [smoothToCanonicalH1FunctionQuotient]
  change canonicalPhysicalH1ToL2 period hPeriod
      (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
    smoothFieldToL2 period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field
  exact h1GraphToL2_agrees_on_smooth period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field

/-- Exact remaining condition for the already proved unconditional graph-H1
trace to be a trace on the function quotient. -/
def CanonicalH1TraceDescendsToFunctionQuotient : Prop :=
  (canonicalPhysicalH1ToL2 period hPeriod).ker ≤
    (canonicalPhysicalH1TraceRadialPolar period hPeriod).ker

/-- Existence of a quotient trace that factors the already constructed
canonical graph-H1 trace. -/
def CanonicalH1FunctionQuotientTraceExists : Prop :=
  ∃ trace : CanonicalPhysicalScalarH1FunctionQuotient period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod,
    trace.comp (canonicalH1FunctionQuotientMap period hPeriod) =
      canonicalPhysicalH1TraceRadialPolar period hPeriod

/-- Under the exact kernel condition, the canonical physical trace descends. -/
def canonicalH1FunctionQuotientTrace
    (hDescends : CanonicalH1TraceDescendsToFunctionQuotient period hPeriod) :
    CanonicalPhysicalScalarH1FunctionQuotient period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  (canonicalPhysicalH1ToL2 period hPeriod).ker.liftQL
    (canonicalPhysicalH1TraceRadialPolar period hPeriod) hDescends

theorem canonicalH1FunctionQuotientTrace_agrees_on_smooth
    (hDescends : CanonicalH1TraceDescendsToFunctionQuotient period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalH1FunctionQuotientTrace period hPeriod hDescends
        (smoothToCanonicalH1FunctionQuotient period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field := by
  rw [smoothToCanonicalH1FunctionQuotient]
  change canonicalPhysicalH1TraceRadialPolar period hPeriod
      (smoothToCanonicalPhysicalScalarH1 period hPeriod field) = _
  exact canonicalPhysicalH1TraceRadialPolar_agrees_on_smooth
    period hPeriod field

/-- Exact quotient universal property: the physical trace factors through
the function quotient if and only if it vanishes on every vertical limit jet. -/
theorem canonicalH1FunctionQuotientTraceExists_iff :
    CanonicalH1FunctionQuotientTraceExists period hPeriod ↔
      CanonicalH1TraceDescendsToFunctionQuotient period hPeriod := by
  constructor
  · rintro ⟨trace, hTrace⟩ field hField
    change canonicalPhysicalH1TraceRadialPolar period hPeriod field = 0
    have hQuotient : canonicalH1FunctionQuotientMap period hPeriod field = 0 := by
      change Submodule.Quotient.mk field = 0
      exact (Submodule.Quotient.mk_eq_zero
        (canonicalPhysicalH1ToL2 period hPeriod).ker).2 hField
    have hApply := DFunLike.congr_fun hTrace field
    change trace (canonicalH1FunctionQuotientMap period hPeriod field) =
      canonicalPhysicalH1TraceRadialPolar period hPeriod field at hApply
    rw [← hApply, hQuotient, map_zero]
  · intro hDescends
    refine ⟨canonicalH1FunctionQuotientTrace period hPeriod hDescends, ?_⟩
    apply ContinuousLinearMap.ext
    intro field
    rfl

theorem canonical_h1_function_quotient_gate :
    Function.Injective
        (canonicalH1FunctionQuotientToL2 period hPeriod) ∧
      DenseRange (smoothToCanonicalH1FunctionQuotient period hPeriod) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        canonicalH1FunctionQuotientToL2 period hPeriod
            (smoothToCanonicalH1FunctionQuotient period hPeriod field) =
          smoothCanonicalPhysicalScalarL2 period hPeriod field) :=
  ⟨canonicalH1FunctionQuotientToL2_injective period hPeriod,
    smoothToCanonicalH1FunctionQuotient_denseRange period hPeriod,
    canonicalH1FunctionQuotientToL2_agrees_on_smooth period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalH1FunctionQuotient4D
end JanusFormal
