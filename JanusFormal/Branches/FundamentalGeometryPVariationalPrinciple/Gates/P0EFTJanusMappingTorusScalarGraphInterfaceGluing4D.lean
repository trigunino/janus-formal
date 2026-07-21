import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianGaussianGeneratingFunctional4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D

/-!
# Two-bulk scalar interface gluing

Two scalar bulks sharing one Hilbert trace space are glued by a common boundary
value `g`.  The Poisson fields on the two sides have normal traces
`M_left g` and `M_right g`.  A symmetric junction operator `J` imposes

`M_left g + M_right g = J g`.

The corresponding interface Schur operator is

`M_left + M_right - J`.

This file constructs the common-boundary Poisson lift, the reduced junction
action and an exact equivalence between the interface Schur kernel and glued
homogeneous bulk pairs.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphInterfaceGluing4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D

universe u₁ u₂ v₁ v₂ w

variable {DomainLeft : Type u₁} {DomainRight : Type u₂}
  {AmbientLeft : Type v₁} {AmbientRight : Type v₂}
  {Trace : Type w}
  [AddCommGroup DomainLeft] [Module Real DomainLeft]
  [AddCommGroup DomainRight] [Module Real DomainRight]
  [NormedAddCommGroup AmbientLeft] [InnerProductSpace Real AmbientLeft]
  [CompleteSpace AmbientLeft]
  [NormedAddCommGroup AmbientRight] [InnerProductSpace Real AmbientRight]
  [CompleteSpace AmbientRight]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Poisson data on both sides of one interface. -/
structure CanonicalScalarGraphInterfacePoissonData
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := Trace))
    (leftTraceBound : HasCanonicalScalarHilbertBoundaryGraphBound left)
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := Trace))
    (rightTraceBound : HasCanonicalScalarHilbertBoundaryGraphBound right)
    (spectralParameter : Real) where
  leftPoisson : CanonicalScalarGraphDirichletPoissonData
    left leftTraceBound spectralParameter
  rightPoisson : CanonicalScalarGraphDirichletPoissonData
    right rightTraceBound spectralParameter

namespace CanonicalScalarGraphInterfacePoissonData

/-- Common-boundary Poisson field pair. -/
def poissonPair
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter) :
    Trace →L[Real]
      CanonicalScalarOperatorGraphSpace left ×
        CanonicalScalarOperatorGraphSpace right where
  toFun boundary :=
    (interfaceData.leftPoisson.poisson boundary,
      interfaceData.rightPoisson.poisson boundary)
  map_add' first second := by ext <;> simp
  map_smul' scalar boundary := by ext <;> simp
  cont := by fun_prop

/-- Left Dirichlet-to-Neumann map. -/
def leftDtN
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter) :
    Trace →L[Real] Trace :=
  canonicalScalarGraphDirichletToNeumann
    left leftTraceBound spectralParameter interfaceData.leftPoisson

/-- Right Dirichlet-to-Neumann map. -/
def rightDtN
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter) :
    Trace →L[Real] Trace :=
  canonicalScalarGraphDirichletToNeumann
    right rightTraceBound spectralParameter interfaceData.rightPoisson

/-- Both Poisson fields have the prescribed common value trace. -/
theorem poissonPair_value_trace
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (boundary : Trace) :
    canonicalScalarCompletedValueTrace left leftTraceBound
        (interfaceData.poissonPair boundary).1 = boundary ∧
      canonicalScalarCompletedValueTrace right rightTraceBound
        (interfaceData.poissonPair boundary).2 = boundary :=
  ⟨interfaceData.leftPoisson.value_trace boundary,
    interfaceData.rightPoisson.value_trace boundary⟩

/-- Both Poisson fields solve their homogeneous shifted equations. -/
theorem poissonPair_homogeneous
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (boundary : Trace) :
    canonicalScalarGraphShiftedOperator left spectralParameter
        (interfaceData.poissonPair boundary).1 = 0 ∧
      canonicalScalarGraphShiftedOperator right spectralParameter
        (interfaceData.poissonPair boundary).2 = 0 :=
  ⟨interfaceData.leftPoisson.homogeneous boundary,
    interfaceData.rightPoisson.homogeneous boundary⟩

/-- Interface Schur operator `M_left + M_right - J`. -/
def schurOperator
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    Trace →L[Real] Trace :=
  interfaceData.leftDtN + interfaceData.rightDtN - junction

@[simp] theorem schurOperator_apply
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (boundary : Trace) :
    interfaceData.schurOperator junction boundary =
      interfaceData.leftDtN boundary + interfaceData.rightDtN boundary -
        junction boundary :=
  rfl

/-- Symmetry of the interface Schur operator. -/
theorem schurOperator_isSymmetric
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (hJunction : junction.toLinearMap.IsSymmetric) :
    (interfaceData.schurOperator junction).toLinearMap.IsSymmetric := by
  intro first second
  unfold schurOperator
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [canonicalScalarGraphDirichletToNeumann_isSymmetric
      left leftTraceBound spectralParameter interfaceData.leftPoisson first second,
    canonicalScalarGraphDirichletToNeumann_isSymmetric
      right rightTraceBound spectralParameter interfaceData.rightPoisson first second,
    hJunction first second]

/-- Glued homogeneous bulk pairs satisfying common value and junction flux law. -/
def gluedHomogeneousSolutionSubmodule
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    Submodule Real
      (CanonicalScalarOperatorGraphSpace left ×
        CanonicalScalarOperatorGraphSpace right) where
  carrier := {field |
    canonicalScalarGraphShiftedOperator left spectralParameter field.1 = 0 ∧
    canonicalScalarGraphShiftedOperator right spectralParameter field.2 = 0 ∧
    canonicalScalarCompletedValueTrace left leftTraceBound field.1 =
      canonicalScalarCompletedValueTrace right rightTraceBound field.2 ∧
    canonicalScalarCompletedNormalTrace left leftTraceBound field.1 +
        canonicalScalarCompletedNormalTrace right rightTraceBound field.2 =
      junction (canonicalScalarCompletedValueTrace left leftTraceBound field.1)}
  zero_mem' := by simp
  add_mem' := by
    intro first second hFirst hSecond
    exact ⟨by rw [map_add, hFirst.1, hSecond.1, add_zero],
      by rw [map_add, hFirst.2.1, hSecond.2.1, add_zero],
      by rw [map_add, map_add, hFirst.2.2.1, hSecond.2.2.1],
      by rw [map_add, map_add, map_add, hFirst.2.2.2, hSecond.2.2.2]⟩
  smul_mem' := by
    intro scalar field hField
    exact ⟨by rw [map_smul, hField.1, smul_zero],
      by rw [map_smul, hField.2.1, smul_zero],
      by rw [map_smul, map_smul, hField.2.2.1],
      by rw [map_smul, map_smul, map_smul, hField.2.2.2]⟩

/-- A Schur-kernel value produces a glued homogeneous pair. -/
def schurKernelToGluedSolution
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    LinearMap.ker (interfaceData.schurOperator junction).toLinearMap →ₗ[Real]
      interfaceData.gluedHomogeneousSolutionSubmodule junction where
  toFun boundary :=
    ⟨interfaceData.poissonPair boundary.1,
      ⟨interfaceData.leftPoisson.homogeneous boundary.1,
        interfaceData.rightPoisson.homogeneous boundary.1,
        by rw [interfaceData.leftPoisson.value_trace,
          interfaceData.rightPoisson.value_trace],
        by
          have hKernel := LinearMap.mem_ker.mp boundary.2
          change interfaceData.leftDtN boundary.1 +
              interfaceData.rightDtN boundary.1 - junction boundary.1 = 0
            at hKernel
          rw [interfaceData.leftPoisson.value_trace]
          exact sub_eq_zero.mp hKernel⟩⟩
  map_add' first second := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_smul' scalar boundary := by
    apply Subtype.ext
    apply Prod.ext <;> simp

/-- A glued homogeneous pair is reconstructed from its common value. -/
def gluedSolutionToSchurKernel
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    interfaceData.gluedHomogeneousSolutionSubmodule junction →ₗ[Real]
      LinearMap.ker (interfaceData.schurOperator junction).toLinearMap where
  toFun field :=
    ⟨canonicalScalarCompletedValueTrace left leftTraceBound field.1.1, by
      rw [LinearMap.mem_ker]
      have hLeftReconstruct := interfaceData.leftPoisson.reconstruct
        left leftTraceBound spectralParameter field.1.1 field.2.1
      have hRightReconstruct := interfaceData.rightPoisson.reconstruct
        right rightTraceBound spectralParameter field.1.2 field.2.1
      have hCommon := field.2.2.1
      have hJunction := field.2.2.2
      rw [hLeftReconstruct] at hJunction
      rw [hRightReconstruct, ← hCommon] at hJunction
      change interfaceData.leftDtN
            (canonicalScalarCompletedValueTrace left leftTraceBound field.1.1) +
          interfaceData.rightDtN
            (canonicalScalarCompletedValueTrace left leftTraceBound field.1.1) -
          junction
            (canonicalScalarCompletedValueTrace left leftTraceBound field.1.1) = 0
      exact sub_eq_zero.mpr hJunction⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- Exact interface Schur-kernel/glued-bulk equivalence. -/
noncomputable def schurKernelGluedSolutionEquiv
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    LinearMap.ker (interfaceData.schurOperator junction).toLinearMap ≃ₗ[Real]
      interfaceData.gluedHomogeneousSolutionSubmodule junction where
  toFun := interfaceData.schurKernelToGluedSolution junction
  invFun := interfaceData.gluedSolutionToSchurKernel junction
  left_inv := by
    intro boundary
    apply Subtype.ext
    exact interfaceData.leftPoisson.value_trace boundary.1
  right_inv := by
    intro field
    apply Subtype.ext
    apply Prod.ext
    · exact (interfaceData.leftPoisson.reconstruct
        left leftTraceBound spectralParameter field.1.1 field.2.1).symm
    · have hRight := interfaceData.rightPoisson.reconstruct
        right rightTraceBound spectralParameter field.1.2 field.2.1
      have hCommon := field.2.2.1
      rw [← hCommon]
      exact hRight.symm
  map_add' := by
    intro first second
    exact (interfaceData.schurKernelToGluedSolution junction).map_add first second
  map_smul' := by
    intro scalar boundary
    exact (interfaceData.schurKernelToGluedSolution junction).map_smul scalar boundary

/-- Reduced interface action. -/
def reducedInterfaceAction
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (boundary : Trace) : Real :=
  (1 / 2 : Real) * inner Real boundary
    (interfaceData.schurOperator junction boundary)

/-- First variation of the reduced interface action. -/
theorem reducedInterfaceAction_hasDerivAt
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (hJunction : junction.toLinearMap.IsSymmetric)
    (boundary variation : Trace) :
    HasDerivAt
      (fun parameter : Real =>
        interfaceData.reducedInterfaceAction junction
          (boundary + parameter • variation))
      (inner Real variation (interfaceData.schurOperator junction boundary)) 0 := by
  have hSymmetric := interfaceData.schurOperator_isSymmetric junction hJunction
  unfold reducedInterfaceAction
  have hAffine : ∀ parameter : Real,
      (1 / 2 : Real) * inner Real (boundary + parameter • variation)
          (interfaceData.schurOperator junction
            (boundary + parameter • variation)) =
        (1 / 2 : Real) * inner Real boundary
            (interfaceData.schurOperator junction boundary) +
          parameter * inner Real variation
            (interfaceData.schurOperator junction boundary) +
          parameter ^ 2 *
            ((1 / 2 : Real) * inner Real variation
              (interfaceData.schurOperator junction variation)) := by
    intro parameter
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hSymmetric boundary variation]
    ring
  rw [show (fun parameter : Real =>
      (1 / 2 : Real) * inner Real (boundary + parameter • variation)
        (interfaceData.schurOperator junction
          (boundary + parameter • variation))) =
    (fun parameter : Real =>
      (1 / 2 : Real) * inner Real boundary
          (interfaceData.schurOperator junction boundary) +
        parameter * inner Real variation
          (interfaceData.schurOperator junction boundary) +
        parameter ^ 2 *
          ((1 / 2 : Real) * inner Real variation
            (interfaceData.schurOperator junction variation))) from by
      funext parameter
      exact hAffine parameter]
  convert (((hasDerivAt_const (x := (0 : Real))
      ((1 / 2 : Real) * inner Real boundary
        (interfaceData.schurOperator junction boundary))).add
      ((hasDerivAt_id (0 : Real)).mul_const
        (inner Real variation
          (interfaceData.schurOperator junction boundary)))).add
      (((hasDerivAt_id (0 : Real)).pow 2).mul_const
        ((1 / 2 : Real) * inner Real variation
          (interfaceData.schurOperator junction variation)))) using 1 <;> norm_num

/-- Interface gluing certificate. -/
theorem certificate
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (hJunction : junction.toLinearMap.IsSymmetric) :
    (interfaceData.schurOperator junction).toLinearMap.IsSymmetric ∧
      Nonempty
        (LinearMap.ker (interfaceData.schurOperator junction).toLinearMap ≃ₗ[Real]
          interfaceData.gluedHomogeneousSolutionSubmodule junction) ∧
      (∀ boundary variation : Trace,
        HasDerivAt
          (fun parameter : Real =>
            interfaceData.reducedInterfaceAction junction
              (boundary + parameter • variation))
          (inner Real variation
            (interfaceData.schurOperator junction boundary)) 0) :=
  ⟨interfaceData.schurOperator_isSymmetric junction hJunction,
    ⟨interfaceData.schurKernelGluedSolutionEquiv junction⟩,
    interfaceData.reducedInterfaceAction_hasDerivAt junction hJunction⟩

end CanonicalScalarGraphInterfacePoissonData

end
end P0EFTJanusMappingTorusScalarGraphInterfaceGluing4D
end JanusFormal
