import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

/-!
# Bounded symmetric perturbations of scalar Lagrangian realizations

Let `A_L` be a closed scalar operator with Lagrangian boundary condition and let
`V` be a bounded symmetric ambient operator.  This file develops the perturbed
realization `A_L + V` on the same boundary domain.

At a bounded resolvent point of `A_L`, the perturbed shift factorizes through
the Birman--Schwinger factor

`I + V R_lambda`.

An explicit inverse of this factor constructs the perturbed bounded resolvent.
The two ambient resolvents satisfy

`R^V_lambda - R_lambda = - R_lambda V R^V_lambda`,

and compactness of the reference resolvent is preserved.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianBoundedPerturbation4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Closed Lagrangian operator perturbed by a bounded ambient operator. -/
noncomputable def canonicalScalarClosedLagrangianPerturbedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient) :
    canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition →ₗ[Real] Ambient :=
  canonicalScalarClosedLagrangianDomainOperator
      data hClosable traceBound condition +
    perturbation.toLinearMap.comp
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)

@[simp] theorem canonicalScalarClosedLagrangianPerturbedOperator_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianPerturbedOperator
        data hClosable traceBound condition perturbation field =
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field +
        perturbation
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition field) :=
  rfl

/-- A bounded symmetric perturbation preserves symmetry of the realization. -/
theorem canonicalScalarClosedLagrangianPerturbedOperator_symmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (hPerturbation : perturbation.toLinearMap.IsSymmetric)
    (first second : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    inner Real
        (canonicalScalarClosedLagrangianPerturbedOperator
          data hClosable traceBound condition perturbation first)
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition second) =
      inner Real
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition first)
        (canonicalScalarClosedLagrangianPerturbedOperator
          data hClosable traceBound condition perturbation second) := by
  simp only [canonicalScalarClosedLagrangianPerturbedOperator_apply,
    canonicalScalarClosedLagrangianPerturbedOperator_apply,
    inner_add_left, inner_add_right]
  rw [canonicalScalarClosedLagrangianDomainOperator_symmetric
    data hClosable traceBound condition first second]
  exact congrArg (fun value : Real =>
    inner Real
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition first)
        (canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition second) + value)
    (hPerturbation
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition first)
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition second))

/-- Shifted perturbed operator. -/
noncomputable def canonicalScalarClosedLagrangianPerturbedShiftedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real) :
    canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition →ₗ[Real] Ambient :=
  canonicalScalarClosedLagrangianPerturbedOperator
      data hClosable traceBound condition perturbation -
    spectralParameter • canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition

@[simp] theorem canonicalScalarClosedLagrangianPerturbedShiftedOperator_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianPerturbedShiftedOperator
        data hClosable traceBound condition perturbation spectralParameter field =
      canonicalScalarClosedLagrangianPerturbedOperator
          data hClosable traceBound condition perturbation field -
        spectralParameter • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field :=
  rfl

/-- Birman--Schwinger factor `I + V R_lambda`. -/
def canonicalScalarClosedLagrangianPerturbationFactor
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) :
    Ambient →L[Real] Ambient :=
  ContinuousLinearMap.id Real Ambient +
    perturbation.comp
      (baseResolvent.ambientResolvent
        data hClosable traceBound condition spectralParameter)

@[simp] theorem canonicalScalarClosedLagrangianPerturbationFactor_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (source : Ambient) :
    canonicalScalarClosedLagrangianPerturbationFactor
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent source =
      source + perturbation
        (baseResolvent.ambientResolvent
          data hClosable traceBound condition spectralParameter source) :=
  rfl

/-- Exact factorization of the perturbed shift. -/
theorem canonicalScalarClosedLagrangianPerturbedShift_factorization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianPerturbationFactor
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent
        (canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition spectralParameter field) =
      canonicalScalarClosedLagrangianPerturbedShiftedOperator
        data hClosable traceBound condition perturbation spectralParameter field := by
  rw [canonicalScalarClosedLagrangianPerturbationFactor_apply]
  change canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter field +
      perturbation
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition
          (baseResolvent.resolvent
            (canonicalScalarClosedLagrangianShiftedOperator
              data hClosable traceBound condition spectralParameter field))) = _
  rw [baseResolvent.right_inverse]
  rw [canonicalScalarClosedLagrangianShiftedOperator_apply,
    canonicalScalarClosedLagrangianPerturbedShiftedOperator_apply,
    canonicalScalarClosedLagrangianPerturbedOperator_apply]
  module

/-- Explicit two-sided inverse for the Birman--Schwinger factor. -/
structure CanonicalScalarClosedLagrangianPerturbationFactorInverseAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter) where
  inverse : Ambient →L[Real] Ambient
  left_inverse : ∀ source,
    canonicalScalarClosedLagrangianPerturbationFactor
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent (inverse source) = source
  right_inverse : ∀ source,
    inverse (canonicalScalarClosedLagrangianPerturbationFactor
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent source) = source

/-- Bounded perturbed resolvent on the same Lagrangian domain. -/
structure CanonicalScalarClosedLagrangianPerturbedBoundedResolventAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real) where
  resolvent : Ambient →L[Real]
    canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition
  left_inverse : ∀ source,
    canonicalScalarClosedLagrangianPerturbedShiftedOperator
        data hClosable traceBound condition perturbation spectralParameter
        (resolvent source) = source
  right_inverse : ∀ field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition,
    resolvent (canonicalScalarClosedLagrangianPerturbedShiftedOperator
      data hClosable traceBound condition perturbation spectralParameter field) = field

/-- Construction of the perturbed resolvent from a base resolvent and inverse
Birman--Schwinger factor. -/
noncomputable def canonicalScalarClosedLagrangianPerturbedBoundedResolventOfFactor
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (factorInverse : CanonicalScalarClosedLagrangianPerturbationFactorInverseAt
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent) :
    CanonicalScalarClosedLagrangianPerturbedBoundedResolventAt
      data hClosable traceBound condition perturbation spectralParameter where
  resolvent := baseResolvent.resolvent.comp factorInverse.inverse
  left_inverse := by
    intro source
    rw [← canonicalScalarClosedLagrangianPerturbedShift_factorization
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent]
    change canonicalScalarClosedLagrangianPerturbationFactor
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent
        (canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition spectralParameter
          (baseResolvent.resolvent (factorInverse.inverse source))) = source
    rw [baseResolvent.left_inverse, factorInverse.left_inverse]
  right_inverse := by
    intro field
    change baseResolvent.resolvent
        (factorInverse.inverse
          (canonicalScalarClosedLagrangianPerturbedShiftedOperator
            data hClosable traceBound condition perturbation spectralParameter field)) = field
    rw [← canonicalScalarClosedLagrangianPerturbedShift_factorization
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent,
      factorInverse.right_inverse,
      baseResolvent.right_inverse]

/-- Ambient perturbed resolvent. -/
def CanonicalScalarClosedLagrangianPerturbedBoundedResolventAt.ambientResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (perturbed : CanonicalScalarClosedLagrangianPerturbedBoundedResolventAt
      data hClosable traceBound condition perturbation spectralParameter) :
    Ambient →L[Real] Ambient :=
  (canonicalScalarClosedLagrangianDomainInclusionCLM
    data hClosable traceBound condition).comp perturbed.resolvent

/-- Domain-valued perturbative resolvent identity. -/
theorem canonicalScalarClosedLagrangianPerturbed_resolvent_identity_domain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (perturbed : CanonicalScalarClosedLagrangianPerturbedBoundedResolventAt
      data hClosable traceBound condition perturbation spectralParameter)
    (source : Ambient) :
    perturbed.resolvent source - baseResolvent.resolvent source =
      -baseResolvent.resolvent
        (perturbation
          (perturbed.ambientResolvent
            data hClosable traceBound condition perturbation spectralParameter
              source)) := by
  apply (baseResolvent.resolventPoint
    data hClosable traceBound condition spectralParameter).1
  rw [map_sub, map_neg,
    baseResolvent.left_inverse,
    baseResolvent.left_inverse]
  have hPerturbed := perturbed.left_inverse source
  rw [canonicalScalarClosedLagrangianPerturbedShiftedOperator_apply,
    canonicalScalarClosedLagrangianPerturbedOperator_apply] at hPerturbed
  have hPerturbed' :
      canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter
        (perturbed.resolvent source) +
        perturbation
          (perturbed.ambientResolvent data hClosable traceBound condition
            perturbation spectralParameter source) = source := by
    rw [canonicalScalarClosedLagrangianShiftedOperator_apply]
    change
      (canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition (perturbed.resolvent source) -
        spectralParameter • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition (perturbed.resolvent source)) +
        perturbation (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition (perturbed.resolvent source)) = source
    calc
      _ = canonicalScalarClosedLagrangianDomainOperator
            data hClosable traceBound condition (perturbed.resolvent source) +
          perturbation (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition (perturbed.resolvent source)) -
          spectralParameter • canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition (perturbed.resolvent source) := by
        module
      _ = source := hPerturbed
  calc
    _ = canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition spectralParameter
            (perturbed.resolvent source) -
        (canonicalScalarClosedLagrangianShiftedOperator
            data hClosable traceBound condition spectralParameter
              (perturbed.resolvent source) +
          perturbation
            (perturbed.ambientResolvent data hClosable traceBound condition
              perturbation spectralParameter source)) :=
      congrArg (fun value : Ambient =>
        canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition spectralParameter
            (perturbed.resolvent source) - value) hPerturbed'.symm
    _ = _ := by module

/-- Ambient perturbative resolvent identity
`R^V - R = - R V R^V`. -/
theorem canonicalScalarClosedLagrangianPerturbed_resolvent_identity
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (perturbed : CanonicalScalarClosedLagrangianPerturbedBoundedResolventAt
      data hClosable traceBound condition perturbation spectralParameter)
    (source : Ambient) :
    perturbed.ambientResolvent
          data hClosable traceBound condition perturbation spectralParameter source -
        baseResolvent.ambientResolvent
          data hClosable traceBound condition spectralParameter source =
      -baseResolvent.ambientResolvent
        data hClosable traceBound condition spectralParameter
        (perturbation
          (perturbed.ambientResolvent
            data hClosable traceBound condition perturbation spectralParameter source)) := by
  change canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (perturbed.resolvent source) -
      canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (baseResolvent.resolvent source) = _
  rw [← map_sub,
    canonicalScalarClosedLagrangianPerturbed_resolvent_identity_domain
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent perturbed source,
    map_neg]
  rfl

/-- The factor construction identifies the perturbed ambient resolvent with the
base compact resolvent composed with the inverse factor. -/
theorem canonicalScalarClosedLagrangianPerturbedAmbientResolvent_ofFactor_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (factorInverse : CanonicalScalarClosedLagrangianPerturbationFactorInverseAt
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent) :
    (canonicalScalarClosedLagrangianPerturbedBoundedResolventOfFactor
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent factorInverse).ambientResolvent
          data hClosable traceBound condition perturbation spectralParameter =
      (baseResolvent.ambientResolvent
        data hClosable traceBound condition spectralParameter).comp
        factorInverse.inverse := by
  rfl

/-- Compactness of the base ambient resolvent is stable under a bounded
symmetric perturbation whenever the Birman--Schwinger factor is invertible. -/
theorem canonicalScalarClosedLagrangianPerturbedAmbientResolvent_compact
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (factorInverse : CanonicalScalarClosedLagrangianPerturbationFactorInverseAt
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent)
    (hCompact : IsCompactOperator
      (baseResolvent.ambientResolvent
        data hClosable traceBound condition spectralParameter)) :
    IsCompactOperator
      ((canonicalScalarClosedLagrangianPerturbedBoundedResolventOfFactor
          data hClosable traceBound condition perturbation spectralParameter
            baseResolvent factorInverse).ambientResolvent
        data hClosable traceBound condition perturbation spectralParameter) := by
  rw [canonicalScalarClosedLagrangianPerturbedAmbientResolvent_ofFactor_eq]
  change IsCompactOperator (fun source =>
    baseResolvent.ambientResolvent
      data hClosable traceBound condition spectralParameter
      (factorInverse.inverse source))
  exact hCompact.comp_clm factorInverse.inverse

/-- Symmetry of a perturbed ambient resolvent. -/
theorem canonicalScalarClosedLagrangianPerturbedAmbientResolvent_isSymmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (hPerturbation : perturbation.toLinearMap.IsSymmetric)
    (spectralParameter : Real)
    (perturbed : CanonicalScalarClosedLagrangianPerturbedBoundedResolventAt
      data hClosable traceBound condition perturbation spectralParameter) :
    (perturbed.ambientResolvent
      data hClosable traceBound condition perturbation spectralParameter).toLinearMap.IsSymmetric := by
  intro source test
  let first := perturbed.resolvent source
  let second := perturbed.resolvent test
  have hOperatorSymmetric :=
    canonicalScalarClosedLagrangianPerturbedOperator_symmetric
      data hClosable traceBound condition perturbation hPerturbation first second
  have hShiftedSymmetric :
      inner Real
          (canonicalScalarClosedLagrangianPerturbedShiftedOperator
            data hClosable traceBound condition perturbation spectralParameter first)
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition second) =
        inner Real
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition first)
          (canonicalScalarClosedLagrangianPerturbedShiftedOperator
            data hClosable traceBound condition perturbation spectralParameter second) := by
    rw [canonicalScalarClosedLagrangianPerturbedShiftedOperator_apply,
      canonicalScalarClosedLagrangianPerturbedShiftedOperator_apply,
      inner_sub_left, inner_sub_right, hOperatorSymmetric]
    simp only [real_inner_smul_left, real_inner_smul_right]
  rw [perturbed.left_inverse source, perturbed.left_inverse test] at hShiftedSymmetric
  exact hShiftedSymmetric.symm

/-- Bounded-perturbation closure certificate. -/
theorem canonicalScalarLagrangianBoundedPerturbation_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (hPerturbation : perturbation.toLinearMap.IsSymmetric)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (factorInverse : CanonicalScalarClosedLagrangianPerturbationFactorInverseAt
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent)
    (hCompact : IsCompactOperator
      (baseResolvent.ambientResolvent
        data hClosable traceBound condition spectralParameter)) :
    let perturbed :=
      canonicalScalarClosedLagrangianPerturbedBoundedResolventOfFactor
        data hClosable traceBound condition perturbation spectralParameter
          baseResolvent factorInverse
    (perturbed.ambientResolvent
        data hClosable traceBound condition perturbation spectralParameter).toLinearMap.IsSymmetric ∧
      IsCompactOperator
        (perturbed.ambientResolvent
          data hClosable traceBound condition perturbation spectralParameter) ∧
      (∀ source : Ambient,
        perturbed.ambientResolvent
              data hClosable traceBound condition perturbation spectralParameter source -
            baseResolvent.ambientResolvent
              data hClosable traceBound condition spectralParameter source =
          -baseResolvent.ambientResolvent
            data hClosable traceBound condition spectralParameter
            (perturbation
              (perturbed.ambientResolvent
                data hClosable traceBound condition perturbation spectralParameter source))) := by
  dsimp
  exact ⟨canonicalScalarClosedLagrangianPerturbedAmbientResolvent_isSymmetric
      data hClosable traceBound condition perturbation hPerturbation
        spectralParameter _,
    canonicalScalarClosedLagrangianPerturbedAmbientResolvent_compact
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent factorInverse hCompact,
    canonicalScalarClosedLagrangianPerturbed_resolvent_identity
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent _⟩

end
end P0EFTJanusMappingTorusScalarLagrangianBoundedPerturbation4D
end JanusFormal
