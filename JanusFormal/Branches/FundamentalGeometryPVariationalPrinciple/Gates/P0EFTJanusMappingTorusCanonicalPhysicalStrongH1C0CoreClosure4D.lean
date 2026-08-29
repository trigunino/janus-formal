import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D

/-!
# Smooth-core closure in canonical physical `C⁰ ∩ H¹`

The closed equalizer `C⁰ ∩ H¹` need not by itself expose simultaneous smooth
approximation in its combined norm. The canonical analytic domain is therefore
the closure of the exact smooth lift inside that equalizer. It is complete,
embeds injectively into the ambient strong space, and has dense smooth core by
construction. No new analytic or physical assumption is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance ambientStrongH1C0CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarStrongH1C0 period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CompleteSpace period hPeriod

/-- Closure of the exact smooth lift in the ambient strong equalizer. -/
def canonicalPhysicalScalarStrongH1C0CoreSubmodule :
    Submodule Real (CanonicalPhysicalScalarStrongH1C0 period hPeriod) :=
  (LinearMap.range
    (smoothToCanonicalPhysicalScalarStrongH1C0
      period hPeriod)).topologicalClosure

/-- Canonical strong scalar domain with simultaneous smooth approximation. -/
abbrev CanonicalPhysicalScalarStrongH1C0Core :=
  canonicalPhysicalScalarStrongH1C0CoreSubmodule period hPeriod

theorem canonicalPhysicalScalarStrongH1C0Core_isClosed :
    IsClosed
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod :
        Set (CanonicalPhysicalScalarStrongH1C0 period hPeriod)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def canonicalPhysicalScalarStrongH1C0CoreCompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (smoothToCanonicalPhysicalScalarStrongH1C0 period hPeriod))

/-- Smooth fields lifted into their strong core closure. -/
def smoothToCanonicalPhysicalScalarStrongH1C0Core :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalScalarStrongH1C0Core period hPeriod where
  toFun field :=
    ⟨smoothToCanonicalPhysicalScalarStrongH1C0 period hPeriod field,
      (LinearMap.range
        (smoothToCanonicalPhysicalScalarStrongH1C0
          period hPeriod)).le_topologicalClosure
        (LinearMap.mem_range_self
          (smoothToCanonicalPhysicalScalarStrongH1C0
            period hPeriod) field)⟩
  map_add' first second := Subtype.ext
    ((smoothToCanonicalPhysicalScalarStrongH1C0
      period hPeriod).map_add first second)
  map_smul' scalar field := Subtype.ext
    ((smoothToCanonicalPhysicalScalarStrongH1C0
      period hPeriod).map_smul scalar field)

/-- The smooth lift is dense in the canonical strong core by construction. -/
theorem smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange :
    DenseRange
      (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion :=
    smoothToCanonicalPhysicalScalarStrongH1C0 period hPeriod
  have hRange :
      Subtype.val '' Set.range
          (smoothToCanonicalPhysicalScalarStrongH1C0Core
            period hPeriod) =
        (LinearMap.range inclusion :
          Set (CanonicalPhysicalScalarStrongH1C0 period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨field, rfl⟩, rfl⟩
      exact ⟨field, rfl⟩
    · rintro ⟨field, rfl⟩
      exact
        ⟨smoothToCanonicalPhysicalScalarStrongH1C0Core
            period hPeriod field,
          ⟨field, rfl⟩, rfl⟩
  change closure (LinearMap.range inclusion :
      Set (CanonicalPhysicalScalarStrongH1C0 period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod))
  rw [hRange]

/-- Continuous inclusion into the ambient strong equalizer. -/
def canonicalPhysicalScalarStrongH1C0CoreToStrong :
    CanonicalPhysicalScalarStrongH1C0Core period hPeriod →L[Real]
      CanonicalPhysicalScalarStrongH1C0 period hPeriod :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).subtypeL

theorem canonicalPhysicalScalarStrongH1C0CoreToStrong_injective :
    Function.Injective
      (canonicalPhysicalScalarStrongH1C0CoreToStrong period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).subtype_injective

/-- Continuous representative of a canonical strong-core field. -/
def canonicalPhysicalScalarStrongH1C0CoreToContinuous :=
  (canonicalPhysicalScalarStrongH1C0ToContinuous period hPeriod).comp
    (canonicalPhysicalScalarStrongH1C0CoreToStrong period hPeriod)

/-- Intrinsic `H¹` representative of a canonical strong-core field. -/
def canonicalPhysicalScalarStrongH1C0CoreToHilbertH1 :=
  (canonicalPhysicalScalarStrongH1C0ToHilbertH1 period hPeriod).comp
    (canonicalPhysicalScalarStrongH1C0CoreToStrong period hPeriod)

@[simp]
theorem strongH1C0CoreToContinuous_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod field) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod field :=
  rfl

@[simp]
theorem strongH1C0CoreToHilbertH1_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarStrongH1C0CoreToHilbertH1 period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod field) =
      smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field :=
  rfl

/-- Summary gate for the canonical dense strong core. -/
theorem canonical_physical_scalar_strong_h1_c0_core_closure_gate :
    IsClosed
        (CanonicalPhysicalScalarStrongH1C0Core period hPeriod :
          Set (CanonicalPhysicalScalarStrongH1C0 period hPeriod)) ∧
      DenseRange
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod) ∧
      Function.Injective
        (canonicalPhysicalScalarStrongH1C0CoreToStrong period hPeriod) := by
  exact ⟨canonicalPhysicalScalarStrongH1C0Core_isClosed period hPeriod,
    smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
      period hPeriod,
    canonicalPhysicalScalarStrongH1C0CoreToStrong_injective
      period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
end JanusFormal
