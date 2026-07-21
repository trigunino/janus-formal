import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphWeylFunctionIdentity4D

/-!
# Boundary reduction of the scalar Robin spectrum

At a spectral parameter where the Dirichlet Poisson operator exists, every
homogeneous bulk solution is determined by its value trace.  Imposing a Robin
law `normal = B value` therefore reduces exactly to the boundary equation

`(DtN - B) value = 0`.

This file constructs a linear equivalence between the Robin homogeneous-solution
space in the completed graph and the kernel of the boundary Schur operator.  It
then transfers triviality, nontriviality and finite-dimensionality between the
bulk and boundary descriptions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Homogeneous completed-graph solutions obeying one Robin boundary law. -/
def canonicalScalarGraphRobinHomogeneousSolutionSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (robin : Trace →L[Real] Trace) :
    Submodule Real (CanonicalScalarOperatorGraphSpace data) where
  carrier := {field |
    canonicalScalarGraphShiftedOperator data spectralParameter field = 0 ∧
      canonicalScalarCompletedNormalTrace data traceBound field =
        robin (canonicalScalarCompletedValueTrace data traceBound field)}
  zero_mem' := by simp
  add_mem' := by
    intro first second hFirst hSecond
    exact ⟨by rw [map_add, hFirst.1, hSecond.1, add_zero],
      by rw [map_add, map_add, hFirst.2, hSecond.2]⟩
  smul_mem' := by
    intro scalar field hField
    exact ⟨by rw [map_smul, hField.1, smul_zero],
      by rw [map_smul, map_smul, hField.2]⟩

@[simp] theorem mem_canonicalScalarGraphRobinHomogeneousSolutionSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (robin : Trace →L[Real] Trace)
    (field : CanonicalScalarOperatorGraphSpace data) :
    field ∈ canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin ↔
      canonicalScalarGraphShiftedOperator data spectralParameter field = 0 ∧
        canonicalScalarCompletedNormalTrace data traceBound field =
          robin (canonicalScalarCompletedValueTrace data traceBound field) :=
  Iff.rfl

/-- Boundary value of a Robin homogeneous solution belongs to the Schur kernel. -/
def canonicalScalarGraphRobinSolutionToSchurKernel
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin →ₗ[Real]
      LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap where
  toFun field :=
    ⟨canonicalScalarCompletedValueTrace data traceBound field.1, by
      rw [LinearMap.mem_ker]
      have hReconstruct := poissonData.reconstruct
        data traceBound spectralParameter field.1 field.2.1
      have hBoundary := field.2.2
      rw [hReconstruct] at hBoundary
      change canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData
            (canonicalScalarCompletedValueTrace data traceBound field.1) -
        robin (canonicalScalarCompletedValueTrace data traceBound field.1) = 0
      exact sub_eq_zero.mpr hBoundary⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- A boundary Schur-kernel vector produces the corresponding Robin homogeneous
Poisson solution. -/
def canonicalScalarGraphSchurKernelToRobinSolution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap →ₗ[Real]
      canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin where
  toFun boundary :=
    ⟨poissonData.poisson boundary.1,
      ⟨poissonData.homogeneous boundary.1, by
        have hKernel := LinearMap.mem_ker.mp boundary.2
        change canonicalScalarGraphDirichletToNeumann
              data traceBound spectralParameter poissonData boundary.1 -
            robin boundary.1 = 0 at hKernel
        rw [poissonData.value_trace]
        exact sub_eq_zero.mp hKernel⟩⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar boundary := by
    apply Subtype.ext
    simp

/-- Exact bulk/boundary equivalence at the chosen spectral parameter. -/
noncomputable def canonicalScalarGraphRobinSolutionSchurKernelEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin ≃ₗ[Real]
      LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap where
  toFun := canonicalScalarGraphRobinSolutionToSchurKernel
    data traceBound spectralParameter poissonData robin
  invFun := canonicalScalarGraphSchurKernelToRobinSolution
    data traceBound spectralParameter poissonData robin
  left_inv := by
    intro field
    apply Subtype.ext
    exact (poissonData.reconstruct
      data traceBound spectralParameter field.1 field.2.1).symm
  right_inv := by
    intro boundary
    apply Subtype.ext
    exact poissonData.value_trace boundary.1
  map_add' := by
    intro first second
    exact (canonicalScalarGraphRobinSolutionToSchurKernel
      data traceBound spectralParameter poissonData robin).map_add first second
  map_smul' := by
    intro scalar field
    exact (canonicalScalarGraphRobinSolutionToSchurKernel
      data traceBound spectralParameter poissonData robin).map_smul scalar field

/-- The bulk Robin homogeneous space is trivial exactly when the Schur kernel is
trivial. -/
theorem canonicalScalarGraphRobinHomogeneousSolutionSubmodule_eq_bot_iff
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin = ⊥ ↔
      LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap = ⊥ := by
  constructor
  · intro hBulk
    apply LinearMap.ker_eq_bot.mpr
    intro first second hEqual
    have hLift :
        canonicalScalarGraphSchurKernelToRobinSolution
            data traceBound spectralParameter poissonData robin first =
          canonicalScalarGraphSchurKernelToRobinSolution
            data traceBound spectralParameter poissonData robin second := by
      have hFirstZero : canonicalScalarGraphSchurKernelToRobinSolution
          data traceBound spectralParameter poissonData robin first = 0 := by
        rw [show canonicalScalarGraphSchurKernelToRobinSolution
          data traceBound spectralParameter poissonData robin first ∈
            canonicalScalarGraphRobinHomogeneousSolutionSubmodule
              data traceBound spectralParameter robin from Subtype.property _]
        simpa [hBulk]
      have hSecondZero : canonicalScalarGraphSchurKernelToRobinSolution
          data traceBound spectralParameter poissonData robin second = 0 := by
        rw [show canonicalScalarGraphSchurKernelToRobinSolution
          data traceBound spectralParameter poissonData robin second ∈
            canonicalScalarGraphRobinHomogeneousSolutionSubmodule
              data traceBound spectralParameter robin from Subtype.property _]
        simpa [hBulk]
      rw [hFirstZero, hSecondZero]
    exact (canonicalScalarGraphRobinSolutionSchurKernelEquiv
      data traceBound spectralParameter poissonData robin).symm.injective hLift
  · intro hBoundary
    apply Submodule.eq_bot_iff.mpr
    intro field hField
    have hValue : canonicalScalarGraphRobinSolutionToSchurKernel
        data traceBound spectralParameter poissonData robin ⟨field, hField⟩ = 0 := by
      apply Subtype.ext
      have hMem := (canonicalScalarGraphRobinSolutionToSchurKernel
        data traceBound spectralParameter poissonData robin ⟨field, hField⟩).2
      simpa [hBoundary] using hMem
    have hFieldZero := (canonicalScalarGraphRobinSolutionSchurKernelEquiv
      data traceBound spectralParameter poissonData robin).injective hValue
    exact congrArg Subtype.val hFieldZero

/-- Finite-dimensionality of the boundary Schur kernel transfers to the bulk
Robin homogeneous-solution space. -/
theorem canonicalScalarGraphRobinHomogeneousSolution_finiteDimensional
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    [FiniteDimensional Real
      (LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap)] :
    FiniteDimensional Real
      (canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin) := by
  exact FiniteDimensional.of_injective
    (canonicalScalarGraphRobinSolutionToSchurKernel
      data traceBound spectralParameter poissonData robin)
    (canonicalScalarGraphRobinSolutionSchurKernelEquiv
      data traceBound spectralParameter poissonData robin).injective

/-- Nontrivial bulk Robin modes are equivalent to nontrivial Schur-kernel
boundary data. -/
theorem canonicalScalarGraphRobin_hasNonzeroSolution_iff_schurKernel
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    (∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0) ↔
      ∃ boundary : LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap,
        boundary ≠ 0 := by
  constructor
  · rintro ⟨field, hField⟩
    refine ⟨canonicalScalarGraphRobinSolutionSchurKernelEquiv
      data traceBound spectralParameter poissonData robin field, ?_⟩
    exact fun hZero => hField
      ((canonicalScalarGraphRobinSolutionSchurKernelEquiv
        data traceBound spectralParameter poissonData robin).injective (by simpa using hZero))
  · rintro ⟨boundary, hBoundary⟩
    refine ⟨(canonicalScalarGraphRobinSolutionSchurKernelEquiv
      data traceBound spectralParameter poissonData robin).symm boundary, ?_⟩
    exact fun hZero => hBoundary
      ((canonicalScalarGraphRobinSolutionSchurKernelEquiv
        data traceBound spectralParameter poissonData robin).symm.injective
        (by simpa using hZero))

/-- Bulk/boundary spectral-reduction certificate. -/
theorem canonicalScalarGraphBoundarySpectrumReduction_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    Nonempty
      (canonicalScalarGraphRobinHomogeneousSolutionSubmodule
          data traceBound spectralParameter robin ≃ₗ[Real]
        LinearMap.ker
          (canonicalScalarGraphBoundarySchurOperator
            data traceBound spectralParameter poissonData robin).toLinearMap) ∧
      ((∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
          data traceBound spectralParameter robin, field ≠ 0) ↔
        ∃ boundary : LinearMap.ker
          (canonicalScalarGraphBoundarySchurOperator
            data traceBound spectralParameter poissonData robin).toLinearMap,
          boundary ≠ 0) :=
  ⟨⟨canonicalScalarGraphRobinSolutionSchurKernelEquiv
      data traceBound spectralParameter poissonData robin⟩,
    canonicalScalarGraphRobin_hasNonzeroSolution_iff_schurKernel
      data traceBound spectralParameter poissonData robin⟩

end
end P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D
end JanusFormal
