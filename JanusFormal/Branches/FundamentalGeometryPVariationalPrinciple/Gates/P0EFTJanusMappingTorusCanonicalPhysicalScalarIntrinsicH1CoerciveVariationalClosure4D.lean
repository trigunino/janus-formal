import Mathlib.Analysis.InnerProductSpace.Adjoint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-!
# Intrinsic coercive variational closure on canonical physical H1

The canonical first-jet graph norm defines a positive coercive form on the
full physical `H¹` completion.  For every physical bulk `L²` source, its
adjoint inclusion is the unique minimizer of the sourced graph-energy action.
The induced bulk response is positive and self-adjoint.

This is an intrinsic elliptic graph-energy regulator, not the Hessian of the
unchanged Lorentzian action.  Physical Rellich compactness makes its bulk
response compact; no compactness or boundary axiom is hidden in the
construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D

set_option autoImplicit false
noncomputable section

open scoped InnerProduct
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev PhysicalHilbertH1 :=
  CanonicalPhysicalScalarHilbertH1 period hPeriod

private abbrev BulkL2 :=
  CanonicalPhysicalBulkL2 period hPeriod

local instance intrinsicPhysicalH1CompleteSpace :
    CompleteSpace (PhysicalHilbertH1 period hPeriod) :=
  canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod

/-- Canonical physical bulk inclusion after Hilbert renorming of the same
first-jet closure. -/
def canonicalPhysicalScalarHilbertH1ToBulkL2 :
    PhysicalHilbertH1 period hPeriod →L[Real] BulkL2 period hPeriod :=
  (canonicalPhysicalScalarH1ToBulkL2 period hPeriod).comp
    (canonicalPhysicalScalarHilbertH1EquivGraph
      period hPeriod).toContinuousLinearMap

/-- Smooth physical fields included in the Hilbert renorming of the same
first-jet closure. -/
def smoothToCanonicalPhysicalScalarHilbertH1 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      PhysicalHilbertH1 period hPeriod where
  toFun field :=
    ⟨canonicalPhysicalHilbertFirstJet period hPeriod field,
      (LinearMap.range
        (canonicalPhysicalHilbertFirstJet
          period hPeriod)).le_topologicalClosure
        (LinearMap.mem_range_self
          (canonicalPhysicalHilbertFirstJet period hPeriod) field)⟩
  map_add' first second := Subtype.ext
    ((canonicalPhysicalHilbertFirstJet period hPeriod).map_add first second)
  map_smul' scalar field := Subtype.ext
    ((canonicalPhysicalHilbertFirstJet period hPeriod).map_smul scalar field)

/-- The Hilbert-renormed bulk inclusion is the original physical smooth
inclusion on the dense smooth core. -/
theorem canonicalPhysicalScalarHilbertH1ToBulkL2_agrees_on_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
        (smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod field := by
  change canonicalPhysicalScalarH1ToBulkL2 period hPeriod
      (canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod
        (smoothToCanonicalPhysicalScalarHilbertH1
          period hPeriod field)) = _
  rw [show canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod
      (smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field) =
        smoothToCanonicalPhysicalScalarH1 period hPeriod field from
    canonicalPhysicalScalarHilbertH1EquivGraph_agrees_on_smooth
      period hPeriod field]
  exact canonicalPhysicalScalarH1ToBulkL2_agrees_on_smooth
    period hPeriod field

/-- The Hilbert-renormed physical H1 inclusion has dense range in bulk L2. -/
theorem canonicalPhysicalScalarHilbertH1ToBulkL2_denseRange :
    DenseRange
      (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod) := by
  apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).mono
  rintro bulk ⟨field, rfl⟩
  exact ⟨smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field,
    canonicalPhysicalScalarHilbertH1ToBulkL2_agrees_on_smooth
      period hPeriod field⟩

/-- Riesz operator of the canonical positive physical graph-H1 form. -/
def canonicalPhysicalScalarIntrinsicH1RieszOperator :
    PhysicalHilbertH1 period hPeriod →L[Real]
      PhysicalHilbertH1 period hPeriod :=
  ContinuousLinearMap.id Real (PhysicalHilbertH1 period hPeriod)

/-- The intrinsic graph-H1 form has coercivity constant one. -/
theorem canonicalPhysicalScalarIntrinsicH1RieszOperator_coercive
    (field : PhysicalHilbertH1 period hPeriod) :
    ‖field‖ ^ 2 ≤
      inner Real
        (canonicalPhysicalScalarIntrinsicH1RieszOperator period hPeriod field)
        field := by
  change ‖field‖ ^ 2 ≤ inner Real field field
  rw [real_inner_self_eq_norm_sq]

/-- Riesz representative of a physical bulk-L2 source. -/
def canonicalPhysicalScalarIntrinsicH1SourceRepresenter :
    BulkL2 period hPeriod →L[Real] PhysicalHilbertH1 period hPeriod :=
  (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).adjoint

/-- Exact duality between the bulk source and its graph-H1 representer. -/
theorem canonicalPhysicalScalarIntrinsicH1SourceRepresenter_duality
    (source : BulkL2 period hPeriod)
    (field : PhysicalHilbertH1 period hPeriod) :
    inner Real
        (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source)
        field =
      inner Real source
        (canonicalPhysicalScalarHilbertH1ToBulkL2
          period hPeriod field) := by
  exact ContinuousLinearMap.adjoint_inner_left
    (canonicalPhysicalScalarHilbertH1ToBulkL2
      period hPeriod) field source

/-- No nonzero bulk source is annihilated by the H1 source representer. -/
theorem canonicalPhysicalScalarIntrinsicH1SourceRepresenter_injective :
    Function.Injective
      (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
        period hPeriod) := by
  intro first second hEqual
  refine
    (canonicalPhysicalScalarHilbertH1ToBulkL2_denseRange
      period hPeriod).eq_of_inner_left Real ?_
  intro field
  rw [← canonicalPhysicalScalarIntrinsicH1SourceRepresenter_duality
      period hPeriod first field,
    ← canonicalPhysicalScalarIntrinsicH1SourceRepresenter_duality
      period hPeriod second field,
    hEqual]

/-- Canonical sourced graph-energy action on the full physical H1 space. -/
def canonicalPhysicalScalarIntrinsicH1SourceAction
    (source : BulkL2 period hPeriod)
    (field : PhysicalHilbertH1 period hPeriod) : Real :=
  (1 / 2 : Real) * ‖field‖ ^ 2 -
    inner Real source
      (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod field)

/-- Strong Riesz equation for the bulk-source representer. -/
theorem canonicalPhysicalScalarIntrinsicH1SourceRepresenter_equation
    (source : BulkL2 period hPeriod) :
    canonicalPhysicalScalarIntrinsicH1RieszOperator period hPeriod
        (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source) =
      canonicalPhysicalScalarIntrinsicH1SourceRepresenter
        period hPeriod source := by
  rfl

/-- Exact completion of the square for the intrinsic sourced action. -/
theorem canonicalPhysicalScalarIntrinsicH1SourceAction_completion
    (source : BulkL2 period hPeriod)
    (field : PhysicalHilbertH1 period hPeriod) :
    canonicalPhysicalScalarIntrinsicH1SourceAction
        period hPeriod source field =
      canonicalPhysicalScalarIntrinsicH1SourceAction period hPeriod source
          (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
            period hPeriod source) +
        (1 / 2 : Real) *
          ‖field -
            canonicalPhysicalScalarIntrinsicH1SourceRepresenter
              period hPeriod source‖ ^ 2 := by
  simp only [canonicalPhysicalScalarIntrinsicH1SourceAction]
  rw [← canonicalPhysicalScalarIntrinsicH1SourceRepresenter_duality
      period hPeriod source field,
    ← canonicalPhysicalScalarIntrinsicH1SourceRepresenter_duality
      period hPeriod source
        (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source),
    real_inner_self_eq_norm_sq, norm_sub_sq_real,
    real_inner_comm field
      (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
        period hPeriod source)]
  ring

/-- The adjoint source representer is the unique global minimizer. -/
theorem canonicalPhysicalScalarIntrinsicH1SourceRepresenter_unique_minimizer
    (source : BulkL2 period hPeriod) :
    (∀ field : PhysicalHilbertH1 period hPeriod,
      canonicalPhysicalScalarIntrinsicH1SourceAction period hPeriod source
          (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
            period hPeriod source) ≤
        canonicalPhysicalScalarIntrinsicH1SourceAction
          period hPeriod source field) ∧
      (∀ field : PhysicalHilbertH1 period hPeriod,
        canonicalPhysicalScalarIntrinsicH1SourceAction
              period hPeriod source field =
            canonicalPhysicalScalarIntrinsicH1SourceAction period hPeriod source
              (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
                period hPeriod source) →
          field =
            canonicalPhysicalScalarIntrinsicH1SourceRepresenter
              period hPeriod source) := by
  constructor
  · intro field
    rw [canonicalPhysicalScalarIntrinsicH1SourceAction_completion
      period hPeriod source field]
    nlinarith [sq_nonneg
      ‖field -
        canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source‖]
  · intro field hAction
    rw [canonicalPhysicalScalarIntrinsicH1SourceAction_completion
      period hPeriod source field] at hAction
    have hNorm :
        ‖field -
          canonicalPhysicalScalarIntrinsicH1SourceRepresenter
            period hPeriod source‖ = 0 := by
      nlinarith [norm_nonneg
        (field -
          canonicalPhysicalScalarIntrinsicH1SourceRepresenter
            period hPeriod source)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Positive bulk response induced by the canonical graph-H1 form. -/
def canonicalPhysicalScalarIntrinsicH1BulkResponse :
    BulkL2 period hPeriod →L[Real] BulkL2 period hPeriod :=
  (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).comp
    (canonicalPhysicalScalarIntrinsicH1SourceRepresenter period hPeriod)

/-- Exact positive quadratic identity for the bulk response. -/
theorem canonicalPhysicalScalarIntrinsicH1BulkResponse_pairing
    (source : BulkL2 period hPeriod) :
    inner Real source
        (canonicalPhysicalScalarIntrinsicH1BulkResponse
          period hPeriod source) =
      ‖canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source‖ ^ 2 := by
  change inner Real source
      (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
        ((canonicalPhysicalScalarHilbertH1ToBulkL2
          period hPeriod).adjoint source)) =
    ‖(canonicalPhysicalScalarHilbertH1ToBulkL2
      period hPeriod).adjoint source‖ ^ 2
  rw [← ContinuousLinearMap.adjoint_inner_left
      (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod)
      ((canonicalPhysicalScalarHilbertH1ToBulkL2
        period hPeriod).adjoint source)
      source,
    real_inner_self_eq_norm_sq]

/-- The bulk response has no zero mode, without a Rellich assumption. -/
theorem canonicalPhysicalScalarIntrinsicH1BulkResponse_injective :
    Function.Injective
      (canonicalPhysicalScalarIntrinsicH1BulkResponse period hPeriod) := by
  let inclusion :=
    canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
  change Function.Injective (inclusion ∘ inclusion.adjoint)
  exact inclusion.self_comp_adjoint_injective_iff.mpr
    (canonicalPhysicalScalarIntrinsicH1SourceRepresenter_injective
      period hPeriod)

/-- Every nonzero bulk source has strictly positive graph-energy response. -/
theorem canonicalPhysicalScalarIntrinsicH1BulkResponse_pairing_pos
    (source : BulkL2 period hPeriod)
    (hSource : source ≠ 0) :
    0 < inner Real source
      (canonicalPhysicalScalarIntrinsicH1BulkResponse
        period hPeriod source) := by
  rw [canonicalPhysicalScalarIntrinsicH1BulkResponse_pairing]
  have hRepresenter :
      canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source ≠ 0 := by
    intro hZero
    apply hSource
    apply
      (canonicalPhysicalScalarIntrinsicH1SourceRepresenter_injective
        period hPeriod)
    simpa using hZero
  exact sq_pos_of_pos (norm_pos_iff.mpr hRepresenter)

/-- The induced bulk response is self-adjoint before any compactness input. -/
theorem canonicalPhysicalScalarIntrinsicH1BulkResponse_isSelfAdjoint :
    IsSelfAdjoint
      (canonicalPhysicalScalarIntrinsicH1BulkResponse period hPeriod) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro first second
  change inner Real
      (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
        ((canonicalPhysicalScalarHilbertH1ToBulkL2
          period hPeriod).adjoint first))
      second =
    inner Real first
      (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
        ((canonicalPhysicalScalarHilbertH1ToBulkL2
          period hPeriod).adjoint second))
  calc
    _ = inner Real
        ((canonicalPhysicalScalarHilbertH1ToBulkL2
          period hPeriod).adjoint first)
        ((canonicalPhysicalScalarHilbertH1ToBulkL2
          period hPeriod).adjoint second) := by
      exact (ContinuousLinearMap.adjoint_inner_right
        (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod)
        ((canonicalPhysicalScalarHilbertH1ToBulkL2
          period hPeriod).adjoint first)
        second).symm
    _ = _ := ContinuousLinearMap.adjoint_inner_left
      (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod)
      ((canonicalPhysicalScalarHilbertH1ToBulkL2
        period hPeriod).adjoint second)
      first

/-- Gaussian response of the intrinsic coercive bulk-source problem. -/
def canonicalPhysicalScalarIntrinsicH1GaussianResponse
    (source : BulkL2 period hPeriod) : Real :=
  (1 / 2 : Real) *
    inner Real source
      (canonicalPhysicalScalarIntrinsicH1BulkResponse
        period hPeriod source)

theorem canonicalPhysicalScalarIntrinsicH1GaussianResponse_nonneg
    (source : BulkL2 period hPeriod) :
    0 ≤ canonicalPhysicalScalarIntrinsicH1GaussianResponse
      period hPeriod source := by
  rw [canonicalPhysicalScalarIntrinsicH1GaussianResponse,
    canonicalPhysicalScalarIntrinsicH1BulkResponse_pairing]
  positivity

/-- The Gaussian response is minus the graph-energy action at its minimizer. -/
theorem canonicalPhysicalScalarIntrinsicH1GaussianResponse_eq_neg_onShell
    (source : BulkL2 period hPeriod) :
    canonicalPhysicalScalarIntrinsicH1GaussianResponse
        period hPeriod source =
      -canonicalPhysicalScalarIntrinsicH1SourceAction period hPeriod source
        (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source) := by
  rw [canonicalPhysicalScalarIntrinsicH1GaussianResponse,
    canonicalPhysicalScalarIntrinsicH1BulkResponse_pairing,
    canonicalPhysicalScalarIntrinsicH1SourceAction,
    ← canonicalPhysicalScalarIntrinsicH1SourceRepresenter_duality
      period hPeriod source
        (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source),
    real_inner_self_eq_norm_sq]
  ring

/-- Complete unconditional coercive certificate for the intrinsic graph
energy.  It does not assert continuum compactness. -/
theorem canonicalPhysicalScalarIntrinsicH1CoerciveVariational_certificate
    (source : BulkL2 period hPeriod) :
    IsSelfAdjoint
        (canonicalPhysicalScalarIntrinsicH1BulkResponse period hPeriod) ∧
      Function.Injective
        (canonicalPhysicalScalarIntrinsicH1BulkResponse period hPeriod) ∧
      (∀ field : PhysicalHilbertH1 period hPeriod,
        ‖field‖ ^ 2 ≤
          inner Real
            (canonicalPhysicalScalarIntrinsicH1RieszOperator
              period hPeriod field)
            field) ∧
      canonicalPhysicalScalarIntrinsicH1RieszOperator period hPeriod
          (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
            period hPeriod source) =
        canonicalPhysicalScalarIntrinsicH1SourceRepresenter
          period hPeriod source ∧
      (∀ field : PhysicalHilbertH1 period hPeriod,
        canonicalPhysicalScalarIntrinsicH1SourceAction period hPeriod source
            (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
              period hPeriod source) ≤
          canonicalPhysicalScalarIntrinsicH1SourceAction
            period hPeriod source field) ∧
      (∀ field : PhysicalHilbertH1 period hPeriod,
        canonicalPhysicalScalarIntrinsicH1SourceAction
              period hPeriod source field =
            canonicalPhysicalScalarIntrinsicH1SourceAction period hPeriod source
              (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
                period hPeriod source) →
          field =
            canonicalPhysicalScalarIntrinsicH1SourceRepresenter
              period hPeriod source) ∧
      0 ≤ canonicalPhysicalScalarIntrinsicH1GaussianResponse
        period hPeriod source := by
  exact
    ⟨canonicalPhysicalScalarIntrinsicH1BulkResponse_isSelfAdjoint
        period hPeriod,
      canonicalPhysicalScalarIntrinsicH1BulkResponse_injective
        period hPeriod,
      canonicalPhysicalScalarIntrinsicH1RieszOperator_coercive
        period hPeriod,
      canonicalPhysicalScalarIntrinsicH1SourceRepresenter_equation
        period hPeriod source,
      (canonicalPhysicalScalarIntrinsicH1SourceRepresenter_unique_minimizer
        period hPeriod source).1,
      (canonicalPhysicalScalarIntrinsicH1SourceRepresenter_unique_minimizer
        period hPeriod source).2,
      canonicalPhysicalScalarIntrinsicH1GaussianResponse_nonneg
        period hPeriod source⟩

/-- Hilbert renorming neither adds nor removes the Rellich obligation: its
bulk inclusion is compact exactly when the original graph-H1 inclusion is. -/
theorem canonicalPhysicalScalarHilbertH1ToBulkL2_isCompact_iff :
    IsCompactOperator
        (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod) ↔
      PhysicalH1RellichCompactness period hPeriod := by
  constructor
  · intro hCompact
    have hComposed := hCompact.comp_clm
      (canonicalPhysicalScalarHilbertH1EquivGraph
        period hPeriod).symm.toContinuousLinearMap
    change IsCompactOperator
      ((canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).comp
        (canonicalPhysicalScalarHilbertH1EquivGraph
          period hPeriod).symm.toContinuousLinearMap) at hComposed
    have hFactor :
        (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).comp
            (canonicalPhysicalScalarHilbertH1EquivGraph
              period hPeriod).symm.toContinuousLinearMap =
          canonicalPhysicalScalarH1ToBulkL2 period hPeriod := by
      ext field
      simp [canonicalPhysicalScalarHilbertH1ToBulkL2]
    rwa [hFactor] at hComposed
  · intro rellich
    change IsCompactOperator
      ((canonicalPhysicalScalarH1ToBulkL2 period hPeriod).comp
        (canonicalPhysicalScalarHilbertH1EquivGraph
          period hPeriod).toContinuousLinearMap)
    exact rellich.comp_clm
      (canonicalPhysicalScalarHilbertH1EquivGraph
        period hPeriod).toContinuousLinearMap

/-- Physical Rellich compactness makes the induced full-bulk response
compact. -/
theorem canonicalPhysicalScalarIntrinsicH1BulkResponse_isCompact
    (rellich : PhysicalH1RellichCompactness period hPeriod) :
    IsCompactOperator
      (canonicalPhysicalScalarIntrinsicH1BulkResponse period hPeriod) := by
  have hHilbertInclusion :
      IsCompactOperator
        (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod) := by
    change IsCompactOperator
      ((canonicalPhysicalScalarH1ToBulkL2 period hPeriod).comp
        (canonicalPhysicalScalarHilbertH1EquivGraph
          period hPeriod).toContinuousLinearMap)
    exact rellich.comp_clm
      (canonicalPhysicalScalarHilbertH1EquivGraph
        period hPeriod).toContinuousLinearMap
  change IsCompactOperator
    ((canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).comp
      (canonicalPhysicalScalarIntrinsicH1SourceRepresenter
        period hPeriod))
  exact hHilbertInclusion.comp_clm
    (canonicalPhysicalScalarIntrinsicH1SourceRepresenter period hPeriod)

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
end JanusFormal
