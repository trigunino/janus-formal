import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianBoundedPerturbation4D

/-!
# Birman--Schwinger principle for scalar Lagrangian perturbations

At a bounded resolvent point of the unperturbed realization, the perturbed
homogeneous equation

`(A + V - lambda) u = 0`

is equivalent to the ambient Birman--Schwinger equation

`(I + V R_lambda) f = 0`.

This file constructs an exact linear equivalence of the two kernels.  It
therefore transfers nontriviality, triviality and finite-dimensional
multiplicity between the perturbed bulk problem and the bounded ambient factor.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianBirmanSchwinger4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianBoundedPerturbation4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Perturbed homogeneous-solution space. -/
def canonicalScalarClosedLagrangianPerturbedKernel
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real) :
    Submodule Real
      (canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition) :=
  LinearMap.ker
    (canonicalScalarClosedLagrangianPerturbedShiftedOperator
      data hClosable traceBound condition perturbation spectralParameter)

/-- Ambient Birman--Schwinger kernel. -/
def canonicalScalarClosedLagrangianBirmanSchwingerKernel
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    Submodule Real Ambient :=
  LinearMap.ker
    (canonicalScalarClosedLagrangianPerturbationFactor
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent).toLinearMap

/-- A perturbed bulk kernel vector produces a Birman--Schwinger kernel source by
applying the unperturbed shift. -/
def canonicalScalarPerturbedKernelToBirmanSchwingerKernel
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    canonicalScalarClosedLagrangianPerturbedKernel
        data hClosable traceBound condition perturbation spectralParameter →ₗ[Real]
      canonicalScalarClosedLagrangianBirmanSchwingerKernel
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent where
  toFun field :=
    ⟨canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter field.1, by
      rw [LinearMap.mem_ker]
      have hPerturbed := LinearMap.mem_ker.mp field.2
      have hFactorization := canonicalScalarClosedLagrangianPerturbedShift_factorization
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent field.1
      rw [hPerturbed] at hFactorization
      exact hFactorization.symm⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- A Birman--Schwinger kernel source produces a perturbed bulk kernel vector by
applying the base resolvent. -/
def canonicalScalarBirmanSchwingerKernelToPerturbedKernel
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    canonicalScalarClosedLagrangianBirmanSchwingerKernel
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent →ₗ[Real]
      canonicalScalarClosedLagrangianPerturbedKernel
        data hClosable traceBound condition perturbation spectralParameter where
  toFun source :=
    ⟨baseResolvent.resolvent source.1, by
      rw [LinearMap.mem_ker]
      rw [← canonicalScalarClosedLagrangianPerturbedShift_factorization
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent,
        baseResolvent.left_inverse]
      exact LinearMap.mem_ker.mp source.2⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar source := by
    apply Subtype.ext
    simp

/-- Exact Birman--Schwinger kernel equivalence. -/
noncomputable def canonicalScalarPerturbedBirmanSchwingerKernelEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    canonicalScalarClosedLagrangianPerturbedKernel
        data hClosable traceBound condition perturbation spectralParameter ≃ₗ[Real]
      canonicalScalarClosedLagrangianBirmanSchwingerKernel
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent where
  toFun := canonicalScalarPerturbedKernelToBirmanSchwingerKernel
    data hClosable traceBound condition perturbation spectralParameter
      baseResolvent
  invFun := canonicalScalarBirmanSchwingerKernelToPerturbedKernel
    data hClosable traceBound condition perturbation spectralParameter
      baseResolvent
  left_inv := by
    intro field
    apply Subtype.ext
    exact baseResolvent.right_inverse field.1
  right_inv := by
    intro source
    apply Subtype.ext
    exact baseResolvent.left_inverse source.1
  map_add' := by
    intro first second
    exact (canonicalScalarPerturbedKernelToBirmanSchwingerKernel
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent).map_add first second
  map_smul' := by
    intro scalar field
    exact (canonicalScalarPerturbedKernelToBirmanSchwingerKernel
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent).map_smul scalar field

/-- Nontrivial perturbed bulk modes are exactly nontrivial Birman--Schwinger
kernel vectors. -/
theorem canonicalScalarPerturbedKernel_ne_bot_iff_birmanSchwinger
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    canonicalScalarClosedLagrangianPerturbedKernel
        data hClosable traceBound condition perturbation spectralParameter ≠ ⊥ ↔
      canonicalScalarClosedLagrangianBirmanSchwingerKernel
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent ≠ ⊥ := by
  rw [Submodule.ne_bot_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨field, hField⟩
    refine ⟨canonicalScalarPerturbedBirmanSchwingerKernelEquiv
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent field, ?_⟩
    exact fun hZero => hField
      ((canonicalScalarPerturbedBirmanSchwingerKernelEquiv
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent).injective (by simpa using hZero))
  · rintro ⟨source, hSource⟩
    refine ⟨(canonicalScalarPerturbedBirmanSchwingerKernelEquiv
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent).symm source, ?_⟩
    exact fun hZero => hSource
      ((canonicalScalarPerturbedBirmanSchwingerKernelEquiv
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent).symm.injective (by simpa using hZero))

/-- Finite-dimensional Birman--Schwinger kernel gives finite-dimensional
perturbed eigenspace. -/
theorem canonicalScalarPerturbedKernel_finiteDimensional
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    [FiniteDimensional Real
      (canonicalScalarClosedLagrangianBirmanSchwingerKernel
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent)] :
    FiniteDimensional Real
      (canonicalScalarClosedLagrangianPerturbedKernel
        data hClosable traceBound condition perturbation spectralParameter) := by
  exact FiniteDimensional.of_injective
    (canonicalScalarPerturbedBirmanSchwingerKernelEquiv
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent).toLinearMap
    (canonicalScalarPerturbedBirmanSchwingerKernelEquiv
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent).injective

/-- Birman--Schwinger certificate. -/
theorem canonicalScalarLagrangianBirmanSchwinger_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    Nonempty
      (canonicalScalarClosedLagrangianPerturbedKernel
          data hClosable traceBound condition perturbation spectralParameter ≃ₗ[Real]
        canonicalScalarClosedLagrangianBirmanSchwingerKernel
          data hClosable traceBound condition perturbation spectralParameter
            baseResolvent) ∧
      (canonicalScalarClosedLagrangianPerturbedKernel
          data hClosable traceBound condition perturbation spectralParameter ≠ ⊥ ↔
        canonicalScalarClosedLagrangianBirmanSchwingerKernel
          data hClosable traceBound condition perturbation spectralParameter
            baseResolvent ≠ ⊥) :=
  ⟨⟨canonicalScalarPerturbedBirmanSchwingerKernelEquiv
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent⟩,
    canonicalScalarPerturbedKernel_ne_bot_iff_birmanSchwinger
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent⟩

end
end P0EFTJanusMappingTorusScalarLagrangianBirmanSchwinger4D
end JanusFormal
