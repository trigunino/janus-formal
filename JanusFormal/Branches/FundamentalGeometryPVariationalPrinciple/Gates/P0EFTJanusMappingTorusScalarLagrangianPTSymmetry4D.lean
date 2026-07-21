import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

/-!
# PT symmetry of closed scalar Lagrangian realizations

A real PT symmetry acts involutively on the bulk Hilbert space, boundary trace
space and actual Lagrangian operator domain.  Compatibility with inclusion,
operator and boundary trace implies:

* invariance of the shifted operator;
* invariance of every operator eigenspace;
* commutation of every bounded resolvent with PT;
* canonical PT-even/PT-odd projections and decomposition of the operator domain.

All intertwining data remain explicit and can later be instantiated by the
actual quotient PT pullback.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianPTSymmetry4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

private abbrev LagrangianDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    data hClosable traceBound condition

/-- Involutive PT action compatible with one closed Lagrangian scalar
realization. -/
structure CanonicalScalarClosedLagrangianPTSymmetry
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) where
  bulkPT : Ambient ≃ₗᵢ[Real] Ambient
  tracePT : Trace ≃ₗᵢ[Real] Trace
  domainPT : LagrangianDomain data hClosable traceBound condition ≃ₗ[Real]
    LagrangianDomain data hClosable traceBound condition
  bulk_involutive : ∀ field : Ambient, bulkPT (bulkPT field) = field
  trace_involutive : ∀ boundary : Trace, tracePT (tracePT boundary) = boundary
  domain_involutive : ∀ field, domainPT (domainPT field) = field
  inclusion_intertwines : ∀ field,
    canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (domainPT field) =
      bulkPT (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field)
  operator_intertwines : ∀ field,
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition (domainPT field) =
      bulkPT (canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field)
  boundary_intertwines : ∀ field,
    canonicalScalarClosedBoundaryTrace data hClosable traceBound (domainPT field.1) =
      (tracePT
          (canonicalScalarClosedBoundaryTrace data hClosable traceBound field.1).1,
        tracePT
          (canonicalScalarClosedBoundaryTrace data hClosable traceBound field.1).2)

/-- PT intertwines every shifted realization. -/
theorem CanonicalScalarClosedLagrangianPTSymmetry.shifted_intertwines
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (spectralParameter : Real)
    (field : LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter
        (symmetry.domainPT field) =
      symmetry.bulkPT
        (canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition spectralParameter field) := by
  rw [canonicalScalarClosedLagrangianShiftedOperator_apply,
    canonicalScalarClosedLagrangianShiftedOperator_apply,
    symmetry.operator_intertwines, symmetry.inclusion_intertwines,
    map_sub, map_smul]

/-- PT sends an eigenfield to an eigenfield with the same eigenvalue. -/
theorem CanonicalScalarClosedLagrangianPTSymmetry.eigenfield
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (eigenvalue : Real)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hField : canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field =
      eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition (symmetry.domainPT field) =
      eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (symmetry.domainPT field) := by
  rw [symmetry.operator_intertwines, symmetry.inclusion_intertwines,
    hField, map_smul]

/-- PT acts linearly on every operator eigenspace. -/
def CanonicalScalarClosedLagrangianPTSymmetry.eigenspaceMap
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (eigenvalue : Real) :
    canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition eigenvalue →ₗ[Real]
      canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition eigenvalue where
  toFun field :=
    ⟨symmetry.domainPT field.1,
      (mem_canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition eigenvalue _).2
        (symmetry.eigenfield eigenvalue field.1
          ((mem_canonicalScalarClosedLagrangianOperatorEigenspace
            data hClosable traceBound condition eigenvalue field.1).1 field.2))⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- PT action on an eigenspace is involutive. -/
theorem CanonicalScalarClosedLagrangianPTSymmetry.eigenspaceMap_involutive
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (eigenvalue : Real)
    (field : canonicalScalarClosedLagrangianOperatorEigenspace
      data hClosable traceBound condition eigenvalue) :
    symmetry.eigenspaceMap eigenvalue
        (symmetry.eigenspaceMap eigenvalue field) = field := by
  apply Subtype.ext
  exact symmetry.domain_involutive field.1

/-- PT-even operator-domain submodule. -/
def CanonicalScalarClosedLagrangianPTSymmetry.evenSubmodule
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition) :
    Submodule Real (LagrangianDomain data hClosable traceBound condition) :=
  LinearMap.ker
    (symmetry.domainPT.toLinearMap - LinearMap.id)

/-- PT-odd operator-domain submodule. -/
def CanonicalScalarClosedLagrangianPTSymmetry.oddSubmodule
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition) :
    Submodule Real (LagrangianDomain data hClosable traceBound condition) :=
  LinearMap.ker
    (symmetry.domainPT.toLinearMap + LinearMap.id)

@[simp] theorem CanonicalScalarClosedLagrangianPTSymmetry.mem_evenSubmodule
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (field : LagrangianDomain data hClosable traceBound condition) :
    field ∈ symmetry.evenSubmodule ↔ symmetry.domainPT field = field := by
  rw [CanonicalScalarClosedLagrangianPTSymmetry.evenSubmodule,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

@[simp] theorem CanonicalScalarClosedLagrangianPTSymmetry.mem_oddSubmodule
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (field : LagrangianDomain data hClosable traceBound condition) :
    field ∈ symmetry.oddSubmodule ↔ symmetry.domainPT field = -field := by
  rw [CanonicalScalarClosedLagrangianPTSymmetry.oddSubmodule,
    LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]

/-- PT-even projection. -/
def CanonicalScalarClosedLagrangianPTSymmetry.evenProjection
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition) :
    LagrangianDomain data hClosable traceBound condition →ₗ[Real]
      LagrangianDomain data hClosable traceBound condition :=
  (1 / 2 : Real) • (symmetry.domainPT.toLinearMap + LinearMap.id)

/-- PT-odd projection. -/
def CanonicalScalarClosedLagrangianPTSymmetry.oddProjection
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition) :
    LagrangianDomain data hClosable traceBound condition →ₗ[Real]
      LagrangianDomain data hClosable traceBound condition :=
  (1 / 2 : Real) • (LinearMap.id - symmetry.domainPT.toLinearMap)

/-- Even plus odd projections reconstruct every field. -/
theorem CanonicalScalarClosedLagrangianPTSymmetry.even_add_odd
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (field : LagrangianDomain data hClosable traceBound condition) :
    symmetry.evenProjection field + symmetry.oddProjection field = field := by
  unfold CanonicalScalarClosedLagrangianPTSymmetry.evenProjection
    CanonicalScalarClosedLagrangianPTSymmetry.oddProjection
  module

/-- The even projection is PT-even. -/
theorem CanonicalScalarClosedLagrangianPTSymmetry.evenProjection_mem
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (field : LagrangianDomain data hClosable traceBound condition) :
    symmetry.evenProjection field ∈ symmetry.evenSubmodule := by
  rw [symmetry.mem_evenSubmodule]
  unfold CanonicalScalarClosedLagrangianPTSymmetry.evenProjection
  rw [map_smul, map_add, symmetry.domain_involutive]
  module

/-- The odd projection is PT-odd. -/
theorem CanonicalScalarClosedLagrangianPTSymmetry.oddProjection_mem
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (field : LagrangianDomain data hClosable traceBound condition) :
    symmetry.oddProjection field ∈ symmetry.oddSubmodule := by
  rw [symmetry.mem_oddSubmodule]
  unfold CanonicalScalarClosedLagrangianPTSymmetry.oddProjection
  rw [map_smul, map_sub, symmetry.domain_involutive]
  module

/-- PT commutes with every bounded domain-valued resolvent. -/
theorem CanonicalScalarClosedLagrangianPTSymmetry.resolvent_commutes
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (spectralParameter : Real)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (source : Ambient) :
    bounded.resolvent (symmetry.bulkPT source) =
      symmetry.domainPT (bounded.resolvent source) := by
  apply (bounded.resolventPoint
    data hClosable traceBound condition spectralParameter).1
  rw [bounded.left_inverse,
    symmetry.shifted_intertwines,
    bounded.left_inverse]

/-- PT commutes with the ambient bounded resolvent. -/
theorem CanonicalScalarClosedLagrangianPTSymmetry.ambientResolvent_commutes
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (spectralParameter : Real)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (source : Ambient) :
    bounded.ambientResolvent
        data hClosable traceBound condition spectralParameter
        (symmetry.bulkPT source) =
      symmetry.bulkPT
        (bounded.ambientResolvent
          data hClosable traceBound condition spectralParameter source) := by
  change canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (bounded.resolvent (symmetry.bulkPT source)) = _
  rw [symmetry.resolvent_commutes,
    symmetry.inclusion_intertwines]

/-- PT symmetry certificate. -/
theorem canonicalScalarLagrangianPTSymmetry_certificate
    (symmetry : CanonicalScalarClosedLagrangianPTSymmetry
      data hClosable traceBound condition)
    (spectralParameter : Real)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    (∀ field : LagrangianDomain data hClosable traceBound condition,
      symmetry.evenProjection field + symmetry.oddProjection field = field) ∧
      (∀ source : Ambient,
        bounded.ambientResolvent
            data hClosable traceBound condition spectralParameter
            (symmetry.bulkPT source) =
          symmetry.bulkPT
            (bounded.ambientResolvent
              data hClosable traceBound condition spectralParameter source)) :=
  ⟨symmetry.even_add_odd,
    symmetry.ambientResolvent_commutes spectralParameter bounded⟩

end
end P0EFTJanusMappingTorusScalarLagrangianPTSymmetry4D
end JanusFormal
