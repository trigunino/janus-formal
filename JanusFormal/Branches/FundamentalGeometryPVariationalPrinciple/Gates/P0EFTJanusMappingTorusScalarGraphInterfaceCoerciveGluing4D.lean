import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphInterfaceGluing4D

/-!
# Coercive source problem for two-bulk scalar gluing

For the interface Schur operator `S = M_left + M_right - J`, a positive lower
norm bound and surjectivity construct a bounded inverse.  A boundary junction
source `q` then has the unique common boundary value `g=S⁻¹q`; its two Poisson
lifts form the unique glued homogeneous bulk pair with sourced junction law.

A positive quadratic lower bound makes the sourced reduced interface action
strictly convex and the inverse image its unique global minimizer.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphInterfaceCoerciveGluing4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphInterfaceGluing4D

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

/-- Norm-coercive and surjective interface Schur problem. -/
structure CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) where
  junction_symmetric : junction.toLinearMap.IsSymmetric
  constant : Real
  constant_pos : 0 < constant
  lower_bound : ∀ boundary : Trace,
    constant * ‖boundary‖ ≤
      ‖interfaceData.schurOperator junction boundary‖
  surjective : Function.Surjective (interfaceData.schurOperator junction)

namespace CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData

/-- Coercivity gives injectivity. -/
theorem injective
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction) :
    Function.Injective (interfaceData.schurOperator junction) := by
  intro first second hEqual
  have hZero : interfaceData.schurOperator junction (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hBound := coercive.lower_bound (first - second)
  rw [hZero, norm_zero] at hBound
  have hNorm : ‖first - second‖ = 0 := by
    nlinarith [norm_nonneg (first - second), coercive.constant_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Interface Schur bijectivity. -/
theorem bijective
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction) :
    Function.Bijective (interfaceData.schurOperator junction) :=
  ⟨coercive.injective, coercive.surjective⟩

/-- Interface Schur equivalence. -/
noncomputable def equiv
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction) : Trace ≃ₗ[Real] Trace :=
  LinearEquiv.ofBijective
    (interfaceData.schurOperator junction).toLinearMap coercive.bijective

/-- Algebraic inverse. -/
noncomputable def algebraicInverse
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction) : Trace →ₗ[Real] Trace :=
  coercive.equiv.symm.toLinearMap

@[simp] theorem schur_inverse
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction)
    (source : Trace) :
    interfaceData.schurOperator junction (coercive.algebraicInverse source) = source :=
  coercive.equiv.apply_symm_apply source

@[simp] theorem inverse_schur
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction)
    (boundary : Trace) :
    coercive.algebraicInverse
        (interfaceData.schurOperator junction boundary) = boundary :=
  coercive.equiv.symm_apply_apply boundary

/-- Reciprocal inverse estimate. -/
theorem inverse_norm_le
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction)
    (source : Trace) :
    ‖coercive.algebraicInverse source‖ ≤
      coercive.constant⁻¹ * ‖source‖ := by
  have hBound := coercive.lower_bound (coercive.algebraicInverse source)
  rw [coercive.schur_inverse] at hBound
  calc
    ‖coercive.algebraicInverse source‖ ≤ ‖source‖ / coercive.constant :=
      (le_div_iff₀ coercive.constant_pos).2 (by
        simpa [mul_comm] using hBound)
    _ = coercive.constant⁻¹ * ‖source‖ := by
      rw [div_eq_mul_inv, mul_comm]

/-- Bounded interface inverse. -/
noncomputable def inverse
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction) : Trace →L[Real] Trace :=
  coercive.algebraicInverse.mkContinuous
    coercive.constant⁻¹ coercive.inverse_norm_le

/-- Glued bulk pair generated by an interface source. -/
def gluedSolution
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction) :
    Trace →L[Real]
      CanonicalScalarOperatorGraphSpace left ×
        CanonicalScalarOperatorGraphSpace right :=
  interfaceData.poissonPair.comp coercive.inverse

/-- Common value trace of the sourced glued solution. -/
theorem gluedSolution_value_trace
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction)
    (source : Trace) :
    canonicalScalarCompletedValueTrace left leftTraceBound
        (coercive.gluedSolution source).1 = coercive.inverse source ∧
      canonicalScalarCompletedValueTrace right rightTraceBound
        (coercive.gluedSolution source).2 = coercive.inverse source :=
  interfaceData.poissonPair_value_trace (coercive.inverse source)

/-- The sourced glued fields solve the homogeneous bulk equations. -/
theorem gluedSolution_homogeneous
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction)
    (source : Trace) :
    canonicalScalarGraphShiftedOperator left spectralParameter
        (coercive.gluedSolution source).1 = 0 ∧
      canonicalScalarGraphShiftedOperator right spectralParameter
        (coercive.gluedSolution source).2 = 0 :=
  interfaceData.poissonPair_homogeneous (coercive.inverse source)

/-- The sourced junction flux law. -/
theorem gluedSolution_junction_equation
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction)
    (source : Trace) :
    canonicalScalarCompletedNormalTrace left leftTraceBound
          (coercive.gluedSolution source).1 +
        canonicalScalarCompletedNormalTrace right rightTraceBound
          (coercive.gluedSolution source).2 -
        junction (canonicalScalarCompletedValueTrace left leftTraceBound
          (coercive.gluedSolution source).1) =
      source := by
  change interfaceData.schurOperator junction (coercive.inverse source) = source
  exact coercive.schur_inverse source

/-- Unique common boundary value satisfying the sourced interface equation. -/
theorem boundary_unique
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction)
    (source boundary : Trace)
    (hEquation : interfaceData.schurOperator junction boundary = source) :
    boundary = coercive.inverse source := by
  rw [← hEquation, coercive.inverse_schur]

end CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData

/-- Positive quadratic lower bound for the interface Schur action. -/
structure CanonicalScalarGraphInterfaceSchurPositiveData
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) where
  junction_symmetric : junction.toLinearMap.IsSymmetric
  constant : Real
  constant_pos : 0 < constant
  lower_bound : ∀ boundary : Trace,
    constant * ‖boundary‖ ^ 2 ≤
      inner Real boundary (interfaceData.schurOperator junction boundary)

/-- Sourced reduced interface action. -/
def canonicalScalarGraphInterfaceSourceAction
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (source boundary : Trace) : Real :=
  interfaceData.reducedInterfaceAction junction boundary -
    inner Real source boundary

/-- Energy difference from a sourced interface solution. -/
theorem canonicalScalarGraphInterfaceSourceAction_sub_solution
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (hJunction : junction.toLinearMap.IsSymmetric)
    (source solution boundary : Trace)
    (hSolution : interfaceData.schurOperator junction solution = source) :
    canonicalScalarGraphInterfaceSourceAction
          interfaceData junction source boundary -
        canonicalScalarGraphInterfaceSourceAction
          interfaceData junction source solution =
      interfaceData.reducedInterfaceAction junction (boundary - solution) := by
  let displacement := boundary - solution
  have hBoundary : boundary = solution + displacement := by
    dsimp [displacement]
    module
  rw [hBoundary]
  unfold canonicalScalarGraphInterfaceSourceAction
    CanonicalScalarGraphInterfacePoissonData.reducedInterfaceAction
  simp only [map_add, inner_add_left, inner_add_right,
    inner_sub_right]
  rw [interfaceData.schurOperator_isSymmetric junction hJunction
      solution displacement,
    hSolution]
  ring

/-- Positive interface Schur data give a unique global source minimizer. -/
theorem canonicalScalarGraphInterfaceSourceAction_unique_minimizer
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (positive : CanonicalScalarGraphInterfaceSchurPositiveData
      interfaceData junction)
    (source solution : Trace)
    (hSolution : interfaceData.schurOperator junction solution = source) :
    (∀ boundary : Trace,
      canonicalScalarGraphInterfaceSourceAction
          interfaceData junction source solution ≤
        canonicalScalarGraphInterfaceSourceAction
          interfaceData junction source boundary) ∧
      (∀ boundary : Trace,
        canonicalScalarGraphInterfaceSourceAction
            interfaceData junction source boundary =
          canonicalScalarGraphInterfaceSourceAction
            interfaceData junction source solution →
        boundary = solution) := by
  constructor
  · intro boundary
    have hDifference := canonicalScalarGraphInterfaceSourceAction_sub_solution
      interfaceData junction positive.junction_symmetric
        source solution boundary hSolution
    have hBound := positive.lower_bound (boundary - solution)
    unfold CanonicalScalarGraphInterfacePoissonData.reducedInterfaceAction
      at hDifference
    linarith [sq_nonneg ‖boundary - solution‖]
  · intro boundary hEqual
    have hDifference := canonicalScalarGraphInterfaceSourceAction_sub_solution
      interfaceData junction positive.junction_symmetric
        source solution boundary hSolution
    rw [hEqual, sub_self] at hDifference
    have hBound := positive.lower_bound (boundary - solution)
    unfold CanonicalScalarGraphInterfacePoissonData.reducedInterfaceAction
      at hDifference
    have hNorm : ‖boundary - solution‖ = 0 := by
      nlinarith [sq_nonneg ‖boundary - solution‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Coercive interface-gluing certificate. -/
theorem canonicalScalarGraphInterfaceCoerciveGluing_certificate
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
      interfaceData junction)
    (positive : CanonicalScalarGraphInterfaceSchurPositiveData
      interfaceData junction)
    (source : Trace) :
    let boundary := coercive.inverse source
    interfaceData.schurOperator junction boundary = source ∧
      (∀ testBoundary : Trace,
        canonicalScalarGraphInterfaceSourceAction
            interfaceData junction source boundary ≤
          canonicalScalarGraphInterfaceSourceAction
            interfaceData junction source testBoundary) ∧
      canonicalScalarGraphShiftedOperator left spectralParameter
          (coercive.gluedSolution source).1 = 0 ∧
      canonicalScalarGraphShiftedOperator right spectralParameter
          (coercive.gluedSolution source).2 = 0 := by
  dsimp
  have hSolution := coercive.schur_inverse source
  exact ⟨hSolution,
    (canonicalScalarGraphInterfaceSourceAction_unique_minimizer
      interfaceData junction positive source (coercive.inverse source)
        hSolution).1,
    (coercive.gluedSolution_homogeneous source).1,
    (coercive.gluedSolution_homogeneous source).2⟩

end
end P0EFTJanusMappingTorusScalarGraphInterfaceCoerciveGluing4D
end JanusFormal
