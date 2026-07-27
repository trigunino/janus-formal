import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.Normed.Lp.lpHolder
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketHilbertFredholm4D

/-!
# Uniform Hilbert--Fredholm realization of the D9 gauge--ghost block

Finite D9 packets are promoted to the complete Hilbert sum `ℓ²(ι × Fin 8)`
for an arbitrary mode type.  The exact symbol multiplier is bounded when its
norm has a uniform upper bound.  A uniform bound on its reciprocal is the
explicit elliptic-gap hypothesis needed for a bounded inverse.

Under this honest contract, the resulting operator is self-adjoint,
bijective, has closed range, finite kernel and cokernel, and index zero.  For
finite mode types it is exactly the previous Euclidean packet operator under
the canonical `lp`--`PiLp` isometry.  This closes the complete D9 `ℓ²` block
under uniform ellipticity; it does not identify the full action Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9L2UniformFredholm4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace lp ENNReal
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeGhostBlockD9FinitePacketHilbertFredholm4D

/-- Complete square-summable Hilbert space of all eight D9 gauge--ghost
coordinates over an arbitrary mode type. -/
abbrev D9GaugeGhostPacketL2 (ι : Type*) :=
  lp (fun _ : ι × Fin 8 => Real) 2

/-- Exact analytic hypotheses for bounded invertibility of the diagonal D9
symbol on `ℓ²`: bounded symbol, no zero mode, and uniformly bounded inverse.
The last condition is the explicit uniform elliptic gap. -/
structure D9GaugeGhostL2UniformEllipticity
    {ι : Type*} (covector : ι → TangentVector3) where
  operatorBound : Real
  inverseBound : Real
  operatorBound_nonnegative : 0 ≤ operatorBound
  inverseBound_nonnegative : 0 ≤ inverseBound
  covector_nonzero : ∀ mode, covector mode ≠ zeroTangent
  multiplier_norm_le :
    ∀ mode, ‖normSquared (covector mode)‖ ≤ operatorBound
  inverse_multiplier_norm_le :
    ∀ mode, ‖(normSquared (covector mode))⁻¹‖ ≤ inverseBound

/-- Scalar multiplication as a continuous real-linear endomorphism. -/
def d9GaugeGhostL2ScalarOperator
    (scalar : Real) : Real →L[Real] Real :=
  (ContinuousLinearMap.lsmul Real Real) scalar

@[simp]
theorem d9GaugeGhostL2ScalarOperator_apply
    (scalar value : Real) :
    d9GaugeGhostL2ScalarOperator scalar value = scalar * value := by
  simp [d9GaugeGhostL2ScalarOperator]

/-- The genuine bounded D9 symbol on the complete Hilbert packet. -/
def d9GaugeGhostL2Operator
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    D9GaugeGhostPacketL2 ι →L[Real] D9GaugeGhostPacketL2 ι :=
  lp.mapCLM 2
    (fun index =>
      d9GaugeGhostL2ScalarOperator
        (normSquared (covector index.1)))
    ellipticity.operatorBound_nonnegative
    (fun index => by
      rw [d9GaugeGhostL2ScalarOperator,
        ContinuousLinearMap.opNorm_lsmul_apply]
      exact ellipticity.multiplier_norm_le index.1)

@[simp]
theorem d9GaugeGhostL2Operator_apply
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector)
    (state : D9GaugeGhostPacketL2 ι) (index : ι × Fin 8) :
    d9GaugeGhostL2Operator ellipticity state index =
      normSquared (covector index.1) * state index := by
  rfl

/-- Bounded reciprocal multiplier supplied by the uniform elliptic gap. -/
def d9GaugeGhostL2Inverse
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    D9GaugeGhostPacketL2 ι →L[Real] D9GaugeGhostPacketL2 ι :=
  lp.mapCLM 2
    (fun index =>
      d9GaugeGhostL2ScalarOperator
        (normSquared (covector index.1))⁻¹)
    ellipticity.inverseBound_nonnegative
    (fun index => by
      rw [d9GaugeGhostL2ScalarOperator,
        ContinuousLinearMap.opNorm_lsmul_apply]
      exact ellipticity.inverse_multiplier_norm_le index.1)

@[simp]
theorem d9GaugeGhostL2Inverse_apply
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector)
    (state : D9GaugeGhostPacketL2 ι) (index : ι × Fin 8) :
    d9GaugeGhostL2Inverse ellipticity state index =
      (normSquared (covector index.1))⁻¹ * state index := by
  rfl

theorem d9GaugeGhostL2_multiplier_ne_zero
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector)
    (mode : ι) :
    normSquared (covector mode) ≠ 0 :=
  ne_of_gt
    (norm_squared_positive_of_nonzero
      (covector mode) (ellipticity.covector_nonzero mode))

theorem d9GaugeGhostL2Inverse_operator
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector)
    (state : D9GaugeGhostPacketL2 ι) :
    d9GaugeGhostL2Inverse ellipticity
        (d9GaugeGhostL2Operator ellipticity state) =
      state := by
  ext index
  simp only [d9GaugeGhostL2Inverse_apply,
    d9GaugeGhostL2Operator_apply]
  rw [← mul_assoc,
    inv_mul_cancel₀
      (d9GaugeGhostL2_multiplier_ne_zero ellipticity index.1),
    one_mul]

theorem d9GaugeGhostL2Operator_inverse
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector)
    (state : D9GaugeGhostPacketL2 ι) :
    d9GaugeGhostL2Operator ellipticity
        (d9GaugeGhostL2Inverse ellipticity state) =
      state := by
  ext index
  simp only [d9GaugeGhostL2Operator_apply,
    d9GaugeGhostL2Inverse_apply]
  rw [← mul_assoc,
    mul_inv_cancel₀
      (d9GaugeGhostL2_multiplier_ne_zero ellipticity index.1),
    one_mul]

theorem d9GaugeGhostL2Operator_bijective
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    Function.Bijective (d9GaugeGhostL2Operator ellipticity) := by
  constructor
  · exact
      Function.LeftInverse.injective
        (fun state =>
          d9GaugeGhostL2Inverse_operator ellipticity state)
  · intro state
    exact
      ⟨d9GaugeGhostL2Inverse ellipticity state,
        d9GaugeGhostL2Operator_inverse ellipticity state⟩

/-- Real diagonal multiplication is self-adjoint on the complete Hilbert
sum, not only on each finite packet. -/
theorem d9GaugeGhostL2Operator_isSelfAdjoint
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    IsSelfAdjoint (d9GaugeGhostL2Operator ellipticity) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro first second
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro index
  change
    ⟪normSquared (covector index.1) • first index, second index⟫_Real =
      ⟪first index,
        normSquared (covector index.1) • second index⟫_Real
  rw [real_inner_smul_left, real_inner_smul_right]

theorem d9GaugeGhostL2Operator_range_eq_top
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    LinearMap.range (d9GaugeGhostL2Operator ellipticity).toLinearMap =
      (⊤ : Submodule Real (D9GaugeGhostPacketL2 ι)) :=
  LinearMap.range_eq_top.mpr
    (d9GaugeGhostL2Operator_bijective ellipticity).2

theorem d9GaugeGhostL2Operator_ker_eq_bot
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    LinearMap.ker (d9GaugeGhostL2Operator ellipticity).toLinearMap =
      (⊥ : Submodule Real (D9GaugeGhostPacketL2 ι)) :=
  LinearMap.ker_eq_bot.mpr
    (d9GaugeGhostL2Operator_bijective ellipticity).1

theorem d9GaugeGhostL2Operator_range_isClosed
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    IsClosed
      (LinearMap.range
        (d9GaugeGhostL2Operator ellipticity).toLinearMap :
        Set (D9GaugeGhostPacketL2 ι)) := by
  rw [d9GaugeGhostL2Operator_range_eq_top ellipticity]
  exact isClosed_univ

theorem d9GaugeGhostL2Operator_kernel_finite
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    FiniteDimensional Real
      (LinearMap.ker
        (d9GaugeGhostL2Operator ellipticity).toLinearMap) := by
  rw [d9GaugeGhostL2Operator_ker_eq_bot ellipticity]
  infer_instance

theorem d9GaugeGhostL2Operator_cokernel_finite
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    FiniteDimensional Real
      (D9GaugeGhostPacketL2 ι ⧸
        LinearMap.range
          (d9GaugeGhostL2Operator ellipticity).toLinearMap) := by
  rw [d9GaugeGhostL2Operator_range_eq_top ellipticity]
  infer_instance

theorem d9GaugeGhostL2Operator_index_zero
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    (d9GaugeGhostL2Operator ellipticity).toLinearMap.index = 0 := by
  rw [LinearMap.index_of_surjective
    (d9GaugeGhostL2Operator_bijective ellipticity).2]
  rw [d9GaugeGhostL2Operator_ker_eq_bot ellipticity]
  simp

/-- For a finite mode type, `ℓ²` is canonically the Euclidean packet used by
the preceding finite-dimensional gate. -/
noncomputable def d9GaugeGhostFinitePacketL2EquivHilbert
    (ι : Type*) [Fintype ι] :
    D9GaugeGhostPacketL2 ι ≃ₗᵢ[Real]
      D9GaugeGhostFinitePacketHilbert ι :=
  lpPiLpₗᵢ (fun _ : ι × Fin 8 => Real) Real

/-- The complete `ℓ²` operator restricts exactly to the existing finite
Euclidean packet operator. -/
theorem d9GaugeGhostL2Operator_finiteCompatibility
    {ι : Type*} [Fintype ι]
    {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector)
    (state : D9GaugeGhostPacketL2 ι) :
    d9GaugeGhostFinitePacketL2EquivHilbert ι
        (d9GaugeGhostL2Operator ellipticity state) =
      d9GaugeGhostFinitePacketHilbertOperator covector
        (d9GaugeGhostFinitePacketL2EquivHilbert ι state) := by
  apply PiLp.ext
  intro index
  change
    normSquared (covector index.1) * state index =
      normSquared (covector index.1) * state index
  rfl

/-- Terminal certificate for the uniformly elliptic complete D9 Hilbert
block. -/
structure D9GaugeGhostL2UniformFredholmCertificate
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) : Prop where
  inverseLeft :
    Function.LeftInverse
      (d9GaugeGhostL2Inverse ellipticity)
      (d9GaugeGhostL2Operator ellipticity)
  inverseRight :
    Function.RightInverse
      (d9GaugeGhostL2Inverse ellipticity)
      (d9GaugeGhostL2Operator ellipticity)
  selfAdjoint :
    IsSelfAdjoint (d9GaugeGhostL2Operator ellipticity)
  rangeClosed :
    IsClosed
      (LinearMap.range
        (d9GaugeGhostL2Operator ellipticity).toLinearMap :
        Set (D9GaugeGhostPacketL2 ι))
  kernelFinite :
    FiniteDimensional Real
      (LinearMap.ker
        (d9GaugeGhostL2Operator ellipticity).toLinearMap)
  cokernelFinite :
    FiniteDimensional Real
      (D9GaugeGhostPacketL2 ι ⧸
        LinearMap.range
          (d9GaugeGhostL2Operator ellipticity).toLinearMap)
  indexZero :
    (d9GaugeGhostL2Operator ellipticity).toLinearMap.index = 0

def d9GaugeGhostL2UniformFredholmCertificate
    {ι : Type*} {covector : ι → TangentVector3}
    (ellipticity : D9GaugeGhostL2UniformEllipticity covector) :
    D9GaugeGhostL2UniformFredholmCertificate ellipticity where
  inverseLeft := d9GaugeGhostL2Inverse_operator ellipticity
  inverseRight := d9GaugeGhostL2Operator_inverse ellipticity
  selfAdjoint := d9GaugeGhostL2Operator_isSelfAdjoint ellipticity
  rangeClosed := d9GaugeGhostL2Operator_range_isClosed ellipticity
  kernelFinite := d9GaugeGhostL2Operator_kernel_finite ellipticity
  cokernelFinite := d9GaugeGhostL2Operator_cokernel_finite ellipticity
  indexZero := d9GaugeGhostL2Operator_index_zero ellipticity

end
end P0EFTJanusGaugeGhostBlockD9L2UniformFredholm4D
end JanusFormal
