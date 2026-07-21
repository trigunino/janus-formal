import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphFiniteBoundaryValueLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryCoerciveAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

/-!
# Coercive construction of the boundary Schur inverse

A boundary Schur operator with positive lower norm bound and full range is
bijective.  Its algebraic inverse obeys the reciprocal coercivity bound and
therefore upgrades to a continuous linear inverse.

This file constructs both inverse interfaces used earlier:

* the sourced reduced-action inverse;
* the Krein boundary Schur inverse.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundarySchurCoerciveInverse4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D
open P0EFTJanusMappingTorusScalarGraphBoundaryCoerciveAction4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Norm-coercive and surjective boundary Schur operator. -/
structure CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) where
  constant : Real
  constant_pos : 0 < constant
  lower_bound : ∀ boundary : Trace,
    constant * ‖boundary‖ ≤
      ‖canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin boundary‖
  surjective : Function.Surjective
    (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin)

/-- Norm coercivity gives injectivity. -/
theorem CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.injective
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin) :
    Function.Injective
      (canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin) := by
  intro first second hEqual
  have hZero : canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hBound := coercive.lower_bound (first - second)
  rw [hZero, norm_zero] at hBound
  have hNorm : ‖first - second‖ = 0 := by
    nlinarith [norm_nonneg (first - second), coercive.constant_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Bijectivity of the Schur operator. -/
theorem CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.bijective
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin) :
    Function.Bijective
      (canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin) :=
  ⟨coercive.injective, coercive.surjective⟩

/-- Schur operator as a linear equivalence. -/
noncomputable def CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.equiv
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin) :
    Trace ≃ₗ[Real] Trace :=
  LinearEquiv.ofBijective
    (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin).toLinearMap
    coercive.bijective

/-- Algebraic inverse of the Schur operator. -/
noncomputable def CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.algebraicInverse
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin) :
    Trace →ₗ[Real] Trace :=
  coercive.equiv.symm.toLinearMap

@[simp] theorem CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.schur_inverse
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin)
    (source : Trace) :
    canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin
        (coercive.algebraicInverse source) = source :=
  coercive.equiv.apply_symm_apply source

@[simp] theorem CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.inverse_schur
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin)
    (boundary : Trace) :
    coercive.algebraicInverse
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin boundary) = boundary :=
  coercive.equiv.symm_apply_apply boundary

/-- Reciprocal norm estimate for the inverse. -/
theorem CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.inverse_norm_le
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin)
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

/-- Continuous Schur inverse. -/
noncomputable def CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.inverse
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin) :
    Trace →L[Real] Trace :=
  coercive.algebraicInverse.mkContinuous
    coercive.constant⁻¹ coercive.inverse_norm_le

@[simp] theorem CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.inverse_apply
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin)
    (source : Trace) :
    coercive.inverse source = coercive.algebraicInverse source :=
  rfl

/-- Reduced-action inverse package. -/
noncomputable def CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.toBoundedInverseData
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin) :
    CanonicalScalarGraphBoundarySchurBoundedInverseData
      data traceBound spectralParameter poissonData robin where
  inverse := coercive.inverse
  left_inverse := coercive.schur_inverse
  right_inverse := coercive.inverse_schur

/-- Krein Schur-inverse package. -/
noncomputable def CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData.toKreinInverseData
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin) :
    CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin where
  inverse := coercive.inverse
  left_inverse := coercive.schur_inverse
  right_inverse := coercive.inverse_schur

/-- Coercive Schur inverse certificate. -/
theorem canonicalScalarGraphBoundarySchurCoerciveInverse_certificate
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
      data traceBound spectralParameter poissonData robin) :
    Function.Bijective
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin) ∧
      (∀ source : Trace,
        canonicalScalarGraphBoundarySchurOperator
            data traceBound spectralParameter poissonData robin
            (coercive.inverse source) = source) ∧
      (∀ source : Trace,
        ‖coercive.inverse source‖ ≤
          coercive.constant⁻¹ * ‖source‖) :=
  ⟨coercive.bijective,
    coercive.schur_inverse,
    coercive.inverse_norm_le⟩

end
end P0EFTJanusMappingTorusScalarGraphBoundarySchurCoerciveInverse4D
end JanusFormal
