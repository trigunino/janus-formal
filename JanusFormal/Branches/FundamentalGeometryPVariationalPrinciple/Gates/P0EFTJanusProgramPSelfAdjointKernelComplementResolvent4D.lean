import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointSmallPerturbation4D

/-!
# Resolvent on the orthogonal complement of the actual kernel

The actual-kernel gap gives more than a Green operator at zero.  For every real
spectral parameter `lambda` with `|lambda| < gap`, the reduced shift

`H_red - lambda I`

is a small self-adjoint perturbation of `H_red`.  It is a bounded bijection on
`(ker H)ᗮ`, and its inverse satisfies

`‖R(lambda)‖ ≤ (gap - |lambda|)⁻¹`.

This is the canonical local resolvent of the physical Hessian after removing
its genuine zero modes.  No finite projection enters the construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementResolvent4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointSmallPerturbation4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance actualKernelResolventCompleteSpace
    (operator : E →L[Real] E) :
    CompleteSpace (SelfAdjointKernelComplement operator) :=
  inferInstance

/-- Scalar shift `-lambda I` on the actual kernel complement. -/
def selfAdjointKernelComplementScalarShift
    (operator : E →L[Real] E)
    (spectralParameter : Real) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  (-spectralParameter) •
    ContinuousLinearMap.id Real (SelfAdjointKernelComplement operator)

@[simp]
theorem selfAdjointKernelComplementScalarShift_apply
    (operator : E →L[Real] E)
    (spectralParameter : Real)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementScalarShift operator spectralParameter vector =
      (-spectralParameter) • vector :=
  rfl

/-- A real scalar shift is self-adjoint. -/
theorem selfAdjointKernelComplementScalarShift_isSelfAdjoint
    (operator : E →L[Real] E)
    (spectralParameter : Real) :
    IsSelfAdjoint
      (selfAdjointKernelComplementScalarShift operator spectralParameter) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  change inner Real ((-spectralParameter) • first) second =
    inner Real first ((-spectralParameter) • second)
  simp

/-- Reduced spectral shift `H_red - lambda I`. -/
def selfAdjointKernelComplementShiftedOperator
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (spectralParameter : Real) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  selfAdjointKernelComplementOperator operator hSelfAdjoint +
    selfAdjointKernelComplementScalarShift operator spectralParameter

@[simp]
theorem selfAdjointKernelComplementShiftedOperator_apply
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (spectralParameter : Real)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementShiftedOperator operator hSelfAdjoint
        spectralParameter vector =
      selfAdjointKernelComplementOperator operator hSelfAdjoint vector -
        spectralParameter • vector := by
  simp [selfAdjointKernelComplementShiftedOperator,
    selfAdjointKernelComplementScalarShift, sub_eq_add_neg]

/-- Small-perturbation packet for one parameter in the actual gap. -/
def selfAdjointKernelComplementRealShiftData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :
    SelfAdjointSmallPerturbationData
      (selfAdjointKernelComplementOperator operator hSelfAdjoint)
      (selfAdjointKernelComplementScalarShift operator spectralParameter) where
  operator_selfAdjoint :=
    selfAdjointKernelComplementOperator_isSelfAdjoint operator hSelfAdjoint
  perturbation_selfAdjoint :=
    selfAdjointKernelComplementScalarShift_isSelfAdjoint operator
      spectralParameter
  gap := data.gap
  gap_pos := data.gap_pos
  operator_lowerBound := data.lowerBound
  perturbationBound := |spectralParameter|
  perturbationBound_nonneg := abs_nonneg spectralParameter
  perturbation_norm_le := by
    intro vector
    change ‖(-spectralParameter) • vector‖ ≤
      |spectralParameter| * ‖vector‖
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
  perturbation_small := hSpectral

/-- Bijectivity and lower-bound certificate for `H_red - lambda I`. -/
def selfAdjointKernelComplementRealShiftCertificate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :=
  selfAdjointSmallPerturbationCertificate
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
    (selfAdjointKernelComplementScalarShift operator spectralParameter)
    (selfAdjointKernelComplementRealShiftData operator hSelfAdjoint data
      spectralParameter hSpectral)

/-- Continuous equivalence induced by the reduced spectral shift. -/
noncomputable def selfAdjointKernelComplementResolventEquiv
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :
    SelfAdjointKernelComplement operator ≃L[Real]
      SelfAdjointKernelComplement operator :=
  ContinuousLinearEquiv.ofBijective
    (selfAdjointKernelComplementShiftedOperator operator hSelfAdjoint
      spectralParameter)
    ⟨(selfAdjointKernelComplementRealShiftCertificate operator hSelfAdjoint data
        spectralParameter hSpectral).injective,
      (selfAdjointKernelComplementRealShiftCertificate operator hSelfAdjoint data
        spectralParameter hSpectral).surjective⟩

/-- Real reduced resolvent on the actual zero-mode complement. -/
noncomputable def selfAdjointKernelComplementResolvent
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  (selfAdjointKernelComplementResolventEquiv operator hSelfAdjoint data
    spectralParameter hSpectral).symm

@[simp]
theorem selfAdjointKernelComplementShiftedOperator_resolvent
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementShiftedOperator operator hSelfAdjoint
        spectralParameter
        (selfAdjointKernelComplementResolvent operator hSelfAdjoint data
          spectralParameter hSpectral vector) =
      vector :=
  (selfAdjointKernelComplementResolventEquiv operator hSelfAdjoint data
    spectralParameter hSpectral).apply_symm_apply vector

@[simp]
theorem selfAdjointKernelComplementResolvent_shiftedOperator
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementResolvent operator hSelfAdjoint data
        spectralParameter hSpectral
        (selfAdjointKernelComplementShiftedOperator operator hSelfAdjoint
          spectralParameter vector) =
      vector :=
  (selfAdjointKernelComplementResolventEquiv operator hSelfAdjoint data
    spectralParameter hSpectral).symm_apply_apply vector

/-- Pointwise resolvent estimate inside the true spectral gap. -/
theorem selfAdjointKernelComplementResolvent_norm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap)
    (vector : SelfAdjointKernelComplement operator) :
    ‖selfAdjointKernelComplementResolvent operator hSelfAdjoint data
        spectralParameter hSpectral vector‖ ≤
      (data.gap - |spectralParameter|)⁻¹ * ‖vector‖ := by
  let shiftData := selfAdjointKernelComplementRealShiftData operator
    hSelfAdjoint data spectralParameter hSpectral
  let preimage := selfAdjointKernelComplementResolvent operator hSelfAdjoint
    data spectralParameter hSpectral vector
  have hLower := selfAdjointSmallPerturbation_lowerBound
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
    (selfAdjointKernelComplementScalarShift operator spectralParameter)
    shiftData preimage
  rw [selfAdjointKernelComplementShiftedOperator_resolvent operator hSelfAdjoint
      data spectralParameter hSpectral vector] at hLower
  have hGapPos : 0 < data.gap - |spectralParameter| := by
    linarith
  have hGapNe : data.gap - |spectralParameter| ≠ 0 := ne_of_gt hGapPos
  change (data.gap - |spectralParameter|) * ‖preimage‖ ≤ ‖vector‖ at hLower
  calc
    ‖preimage‖ = (data.gap - |spectralParameter|)⁻¹ *
        ((data.gap - |spectralParameter|) * ‖preimage‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ (data.gap - |spectralParameter|)⁻¹ * ‖vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt hGapPos))

/-- Operator norm estimate for the actual-kernel resolvent. -/
theorem selfAdjointKernelComplementResolvent_opNorm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :
    ‖selfAdjointKernelComplementResolvent operator hSelfAdjoint data
        spectralParameter hSpectral‖ ≤
      (data.gap - |spectralParameter|)⁻¹ := by
  have hGapPos : 0 < data.gap - |spectralParameter| := by
    linarith
  apply ContinuousLinearMap.opNorm_le_bound
    (inv_nonneg.mpr (le_of_lt hGapPos))
  intro vector
  exact selfAdjointKernelComplementResolvent_norm_le operator hSelfAdjoint data
    spectralParameter hSpectral vector

/-- At zero, the local resolvent is the canonical reduced Green operator. -/
theorem selfAdjointKernelComplementResolvent_zero
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (hZero : |(0 : Real)| < data.gap) :
    selfAdjointKernelComplementResolvent operator hSelfAdjoint data 0 hZero =
      selfAdjointKernelComplementGreen operator hSelfAdjoint data := by
  apply ContinuousLinearMap.ext
  intro vector
  apply selfAdjointKernelComplementOperator_injective operator hSelfAdjoint data
  rw [selfAdjointKernelComplementOperator_green operator hSelfAdjoint data]
  simpa using selfAdjointKernelComplementShiftedOperator_resolvent operator
    hSelfAdjoint data 0 hZero vector

/-- Exact first resolvent identity on the real gap. -/
theorem selfAdjointKernelComplement_resolvent_identity
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (first second : Real)
    (hFirst : |first| < data.gap)
    (hSecond : |second| < data.gap) :
    selfAdjointKernelComplementResolvent operator hSelfAdjoint data first hFirst -
        selfAdjointKernelComplementResolvent operator hSelfAdjoint data second
          hSecond =
      (first - second) •
        ((selfAdjointKernelComplementResolvent operator hSelfAdjoint data first
            hFirst).comp
          (selfAdjointKernelComplementResolvent operator hSelfAdjoint data second
            hSecond)) := by
  apply ContinuousLinearMap.ext
  intro vector
  let firstR := selfAdjointKernelComplementResolvent operator hSelfAdjoint data
    first hFirst
  let secondR := selfAdjointKernelComplementResolvent operator hSelfAdjoint data
    second hSecond
  let firstH := selfAdjointKernelComplementShiftedOperator operator hSelfAdjoint
    first
  apply (selfAdjointKernelComplementRealShiftCertificate operator hSelfAdjoint
    data first hFirst).injective
  change firstH ((firstR - secondR) vector) =
    firstH (((first - second) • firstR.comp secondR) vector)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [selfAdjointKernelComplementShiftedOperator_resolvent operator hSelfAdjoint
    data first hFirst]
  have hFirstOnSecond :
      firstH (secondR vector) = vector + (second - first) • secondR vector := by
    rw [show firstH =
        selfAdjointKernelComplementShiftedOperator operator hSelfAdjoint second +
          (second - first) • ContinuousLinearMap.id Real
            (SelfAdjointKernelComplement operator) by
      ext test
      simp [firstH, selfAdjointKernelComplementShiftedOperator,
        selfAdjointKernelComplementScalarShift]
      module]
    simp [selfAdjointKernelComplementShiftedOperator_resolvent operator
      hSelfAdjoint data second hSecond]
  rw [hFirstOnSecond]
  have hFirstOnFirstSecond :
      firstH (firstR (secondR vector)) = secondR vector :=
    selfAdjointKernelComplementShiftedOperator_resolvent operator hSelfAdjoint
      data first hFirst (secondR vector)
  rw [map_smul, hFirstOnFirstSecond]
  module

/-- Public actual-kernel resolvent checkpoint. -/
theorem self_adjoint_actual_kernel_resolvent_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :
    Function.LeftInverse
        (selfAdjointKernelComplementResolvent operator hSelfAdjoint data
          spectralParameter hSpectral)
        (selfAdjointKernelComplementShiftedOperator operator hSelfAdjoint
          spectralParameter) ∧
      Function.RightInverse
        (selfAdjointKernelComplementResolvent operator hSelfAdjoint data
          spectralParameter hSpectral)
        (selfAdjointKernelComplementShiftedOperator operator hSelfAdjoint
          spectralParameter) ∧
      ‖selfAdjointKernelComplementResolvent operator hSelfAdjoint data
          spectralParameter hSpectral‖ ≤
        (data.gap - |spectralParameter|)⁻¹ :=
  ⟨selfAdjointKernelComplementResolvent_shiftedOperator operator hSelfAdjoint
      data spectralParameter hSpectral,
    selfAdjointKernelComplementShiftedOperator_resolvent operator hSelfAdjoint
      data spectralParameter hSpectral,
    selfAdjointKernelComplementResolvent_opNorm_le operator hSelfAdjoint data
      spectralParameter hSpectral⟩

end
end P0EFTJanusProgramPSelfAdjointKernelComplementResolvent4D
end JanusFormal
