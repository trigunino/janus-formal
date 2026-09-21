import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusUnboundedResolventDomainReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLocalResolventResponseReconstruction
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# T08: the completed boundary triple supplies the reconstruction resolvent

The actual Lagrangian domain, inclusion, operator, and two inverse identities
produce an injective self-adjoint ambient resolvent.  Its range recovers the
actual operator domain.  The sign is reversed here because reconstruction uses
`(lambda I - A)⁻¹`, while the completed boundary triple uses `(A - lambda I)⁻¹`.
-/

namespace JanusFormal
namespace P0EFTJanusBoundaryTripleResolventSelectionBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusUnboundedResolventDomainReconstruction
open P0EFTJanusCyclicMomentReconstruction
open P0EFTJanusLocalResolventResponseReconstruction
open Filter Topology

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}
  (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
  (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
  (spectralParameter : Real)
  (bounded : triple.LagrangianBoundedResolventAt condition spectralParameter)

/-- The ambient inverse is injective because both the domain inclusion and the
domain-valued inverse are injective. -/
theorem ambientResolvent_injective :
    Function.Injective (bounded.ambientResolvent triple condition spectralParameter) := by
  intro first second hEqual
  have hDomain : bounded.resolvent first = bounded.resolvent second :=
    triple.lagrangianInclusion_injective condition hEqual
  have hShifted := congrArg
    (triple.lagrangianShiftedOperator condition spectralParameter) hDomain
  simpa only [bounded.left_inverse] using hShifted

/-- Symmetry already proved from Green's identity gives bounded self-adjointness. -/
theorem ambientResolvent_isSelfAdjoint :
    IsSelfAdjoint (bounded.ambientResolvent triple condition spectralParameter) :=
  (bounded.ambient_isSymmetric triple condition spectralParameter).isSelfAdjoint

/-- The resolvent convention used by spectral parent reconstruction. -/
def selectionResolvent : Ambient →L[Real] Ambient :=
  -(bounded.ambientResolvent triple condition spectralParameter)

theorem selectionResolvent_injective :
    Function.Injective (selectionResolvent triple condition spectralParameter bounded) := by
  intro first second hEqual
  apply ambientResolvent_injective triple condition spectralParameter bounded
  exact neg_injective hEqual

theorem selectionResolvent_isSelfAdjoint :
    IsSelfAdjoint (selectionResolvent triple condition spectralParameter bounded) :=
  (ambientResolvent_isSelfAdjoint triple condition spectralParameter bounded).neg

omit [CompleteSpace Ambient] in
/-- The bounded resolvent range is exactly the concrete unbounded domain. -/
theorem selectionResolvent_range :
    Set.range (selectionResolvent triple condition spectralParameter bounded) =
      triple.realizationDomain condition := by
  ext field
  constructor
  · rintro ⟨source, rfl⟩
    refine ⟨-bounded.resolvent source, ?_⟩
    simp [selectionResolvent,
      CanonicalScalarCompletedBoundaryTripleData.LagrangianBoundedResolventAt.ambientResolvent]
  · rintro ⟨field, rfl⟩
    refine ⟨-(triple.lagrangianShiftedOperator condition spectralParameter field), ?_⟩
    change -(triple.lagrangianInclusion condition
      (bounded.resolvent (-(triple.lagrangianShiftedOperator condition spectralParameter field)))) = _
    rw [map_neg, map_neg, neg_neg, bounded.right_inverse]

/-- On the reconstructed range, the operator value is the original concrete
Lagrangian operator value. -/
theorem selectionResolvent_operator (source : Ambient) :
    triple.lagrangianOperator condition (-bounded.resolvent source) =
      spectralParameter • selectionResolvent triple condition spectralParameter bounded source -
        source := by
  have hInverse := bounded.left_inverse source
  rw [triple.lagrangianShiftedOperator_apply] at hInverse
  simp only [selectionResolvent,
    CanonicalScalarCompletedBoundaryTripleData.LagrangianBoundedResolventAt.ambientResolvent,
    neg_apply, ContinuousLinearMap.comp_apply, map_neg]
  rw [eq_add_of_sub_eq hInverse]
  module

/-- The concrete graph domain identified with its image in the ambient space. -/
def realizationDomainEquiv : triple.lagrangianDomainSubmodule condition ≃ₗ[Real]
    LinearMap.range (triple.lagrangianInclusion condition).toLinearMap :=
  LinearEquiv.ofInjective (triple.lagrangianInclusion condition).toLinearMap
    (triple.lagrangianInclusion_injective condition)

/-- The actual Lagrangian realization as a partially defined ambient operator. -/
def realizationPartialOperator : Ambient →ₗ.[Real] Ambient where
  domain := LinearMap.range (triple.lagrangianInclusion condition).toLinearMap
  toFun := (triple.lagrangianOperator condition).toLinearMap.comp
    (realizationDomainEquiv triple condition).symm.toLinearMap

theorem realizationPartialOperator_domain :
    ((realizationPartialOperator triple condition).domain : Set Ambient) =
      triple.realizationDomain condition := rfl

/-- Passing to an ambient domain does not alter the concrete operator. -/
theorem realizationPartialOperator_apply
    (field : triple.lagrangianDomainSubmodule condition) :
    realizationPartialOperator triple condition
      (realizationDomainEquiv triple condition field) =
      triple.lagrangianOperator condition field := by
  change triple.lagrangianOperator condition
    ((realizationDomainEquiv triple condition).symm
      (realizationDomainEquiv triple condition field)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem realizationPartialOperator_apply_of_eq
    (field : (realizationPartialOperator triple condition).domain)
    (representative : triple.lagrangianDomainSubmodule condition)
    (hRepresentative : triple.lagrangianInclusion condition representative =
      (field : Ambient)) :
    realizationPartialOperator triple condition field =
      triple.lagrangianOperator condition representative := by
  have hField : field = realizationDomainEquiv triple condition representative :=
    Subtype.ext hRepresentative.symm
  rw [hField, realizationPartialOperator_apply]

/-- The ambient partial operator inherits Green symmetry from the concrete
Lagrangian boundary condition. -/
theorem realizationPartialOperator_isFormalAdjoint :
    (realizationPartialOperator triple condition).IsFormalAdjoint
      (realizationPartialOperator triple condition) := by
  intro first second
  obtain ⟨first, rfl⟩ := (realizationDomainEquiv triple condition).surjective first
  obtain ⟨second, rfl⟩ := (realizationDomainEquiv triple condition).surjective second
  rw [realizationPartialOperator_apply, realizationPartialOperator_apply]
  exact triple.lagrangianOperator_symmetric condition first second

theorem selectionResolvent_mem_domain (source : Ambient) :
    selectionResolvent triple condition spectralParameter bounded source ∈
      (realizationPartialOperator triple condition).domain := by
  rw [← SetLike.mem_coe, realizationPartialOperator_domain,
    ← selectionResolvent_range triple condition spectralParameter bounded]
  exact ⟨source, rfl⟩

theorem selectionResolvent_left_inverse
    (field : (realizationPartialOperator triple condition).domain) :
    selectionResolvent triple condition spectralParameter bounded
      (spectralParameter • (field : Ambient) -
        realizationPartialOperator triple condition field) = (field : Ambient) := by
  obtain ⟨representative, rfl⟩ := (realizationDomainEquiv triple condition).surjective field
  rw [realizationPartialOperator_apply]
  have hShift : spectralParameter •
      ((realizationDomainEquiv triple condition representative :
        (realizationPartialOperator triple condition).domain) : Ambient) -
      triple.lagrangianOperator condition representative =
      -(triple.lagrangianShiftedOperator condition spectralParameter representative) := by
    change spectralParameter • triple.lagrangianInclusion condition representative - _ = _
    rw [triple.lagrangianShiftedOperator_apply, neg_sub]
  rw [hShift]
  change -(triple.lagrangianInclusion condition
    (bounded.resolvent (-(triple.lagrangianShiftedOperator condition spectralParameter
      representative)))) = triple.lagrangianInclusion condition representative
  rw [map_neg, map_neg, neg_neg, bounded.right_inverse]

theorem selectionResolvent_right_inverse (source : Ambient) :
    spectralParameter • selectionResolvent triple condition spectralParameter bounded source -
      realizationPartialOperator triple condition
        ⟨selectionResolvent triple condition spectralParameter bounded source,
          selectionResolvent_mem_domain triple condition spectralParameter bounded source⟩ =
        source := by
  rw [realizationPartialOperator_apply_of_eq triple condition _ (-bounded.resolvent source)
    (by simp [selectionResolvent,
      CanonicalScalarCompletedBoundaryTripleData.LagrangianBoundedResolventAt.ambientResolvent])]
  rw [selectionResolvent_operator]
  abel

/-- The existing boundary-triple package supplies every inverse axiom required
by T08 reconstruction; no operator or domain matching assumption is added. -/
def selectionResolventAt :
    ResolventAt (realizationPartialOperator triple condition) spectralParameter where
  R := selectionResolvent triple condition spectralParameter bounded
  range_mem := selectionResolvent_mem_domain triple condition spectralParameter bounded
  left_inv := selectionResolvent_left_inverse triple condition spectralParameter bounded
  right_inv := selectionResolvent_right_inverse triple condition spectralParameter bounded

variable {Other : Type*} [NormedAddCommGroup Other] [InnerProductSpace Real Other]
  (otherOperator : Other →ₗ.[Real] Other)
  (otherResolvent : ResolventAt otherOperator spectralParameter)
  (U : Ambient ≃ₗᵢ[Real] Other)
  (hU : ∀ source, U (selectionResolvent triple condition spectralParameter bounded source) =
    otherResolvent.R (U source))

/-- A reconstructed resolvent isometry transports the original completed
Lagrangian domain, including its concrete boundary condition. -/
def selectionLagrangianDomainEquiv :
    triple.lagrangianDomainSubmodule condition ≃ₗ[Real] otherOperator.domain :=
  (realizationDomainEquiv triple condition).trans
    (ResolventAt.domainEquiv
      (selectionResolventAt triple condition spectralParameter bounded)
      otherResolvent U hU)

theorem selectionLagrangianDomainEquiv_coe
    (field : triple.lagrangianDomainSubmodule condition) :
    (selectionLagrangianDomainEquiv triple condition spectralParameter bounded
      otherOperator otherResolvent U hU field : Other) =
      U (triple.lagrangianInclusion condition field) := rfl

/-- The transported action is the actual completed-triple operator, not a new
operator stipulated to match the spectral data. -/
theorem selectionLagrangian_action_intertwining
    (field : triple.lagrangianDomainSubmodule condition) :
    U (triple.lagrangianOperator condition field) =
      otherOperator (selectionLagrangianDomainEquiv triple condition spectralParameter bounded
        otherOperator otherResolvent U hU field) := by
  rw [← realizationPartialOperator_apply triple condition field]
  exact ResolventAt.action_intertwining
    (selectionResolventAt triple condition spectralParameter bounded)
    otherResolvent U hU (realizationDomainEquiv triple condition field)

/-- Equality of the measured local response constructs the unique bulk
isometry and transports the concrete boundary-conditioned operator domain. -/
theorem measured_local_response_selects_lagrangian_realization
    [CompleteSpace Other] {Boundary : Type*}
    (hOther : otherOperator.IsFormalAdjoint otherOperator)
    (B₁ : Boundary → Ambient) (B₂ : Boundary → Other)
    (C₁ C₂ : Boundary → Boundary → Real)
    (hcyclic₁ : IsCyclic (selectionResolvent triple condition spectralParameter bounded) B₁)
    (hcyclic₂ : IsCyclic otherResolvent.R B₂)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝[≠] (0 : Real),
      localSchurResponse (selectionResolvent triple condition spectralParameter bounded)
        B₁ C₁ t q r = localSchurResponse otherResolvent.R B₂ C₂ t q r) :
    (∀ q r, C₁ q r = C₂ q r) ∧
    ∃! U : Ambient ≃ₗᵢ[Real] Other,
      ((∀ q, U (B₁ q) = B₂ q) ∧
        (∀ source, U (selectionResolvent triple condition spectralParameter bounded source) =
          otherResolvent.R (U source))) ∧
      ∃ E : triple.lagrangianDomainSubmodule condition ≃ₗ[Real] otherOperator.domain,
        (∀ field, (E field : Other) = U (triple.lagrangianInclusion condition field)) ∧
        (∀ field, U (triple.lagrangianOperator condition field) = otherOperator (E field)) := by
  obtain ⟨hC, W, hW, hUnique⟩ := local_response_reconstructs_resolvent
    (selectionResolvent triple condition spectralParameter bounded) otherResolvent.R
    (selectionResolvent_isSelfAdjoint triple condition spectralParameter bounded)
    (otherResolvent.isSymmetric hOther).isSelfAdjoint
    (selectionResolvent_injective triple condition spectralParameter bounded)
    otherResolvent.injective B₁ B₂ C₁ C₂ hcyclic₁ hcyclic₂ hresponse
  refine ⟨hC, W, ⟨hW, ?_⟩, ?_⟩
  · refine ⟨selectionLagrangianDomainEquiv triple condition spectralParameter bounded
      otherOperator otherResolvent W hW.2, ?_, ?_⟩
    · intro field
      rfl
    · exact selectionLagrangian_action_intertwining triple condition spectralParameter bounded
        otherOperator otherResolvent W hW.2
  · intro V hV
    exact hUnique V hV.1

end
end P0EFTJanusBoundaryTripleResolventSelectionBridge4D
end JanusFormal
