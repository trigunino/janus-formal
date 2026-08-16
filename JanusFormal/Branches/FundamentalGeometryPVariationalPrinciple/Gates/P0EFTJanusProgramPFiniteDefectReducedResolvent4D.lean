import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointSmallPerturbation4D

/-!
# Real resolvent of the reduced finite-defect operator

Let `H` be a bounded self-adjoint operator with a finite defect projection `P`.
The finite-defect coercivity packet restricts `H` to a bijective operator on
`ker P` with lower bound `c > 0`.

For every real spectral parameter `lambda` satisfying `|lambda| < c`, the
shifted reduced operator

`H_red - lambda I`

is a small self-adjoint perturbation of `H_red`.  It is therefore bijective,
and its inverse is a bounded real resolvent with

`‖R(lambda)‖ ≤ (c - |lambda|)⁻¹`.

The construction stays on the exact zero-mode complement.  It introduces no
new quotient, completion or operator formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectReducedResolvent4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectReducedOperator4D
open P0EFTJanusProgramPFiniteDefectReducedInverse4D
open P0EFTJanusProgramPSelfAdjointSmallPerturbation4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance finiteDefectReducedResolventCompleteSpace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    CompleteSpace data.projection.ker :=
  inferInstance

/-- Self-adjointness descends to the invariant finite-defect complement. -/
theorem finiteDefectReducedOperator_isSelfAdjoint
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator) :
    IsSelfAdjoint (finiteDefectReducedOperator operator data) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  change inner Real (operator first.1) second.1 =
    inner Real first.1 (operator second.1)
  exact hSelfAdjoint.isSymmetric first.1 second.1

/-- Scalar perturbation `-lambda I` on the reduced space. -/
def finiteDefectReducedScalarPerturbation
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real) :
    data.projection.ker →L[Real] data.projection.ker :=
  (-spectralParameter) •
    ContinuousLinearMap.id Real data.projection.ker

@[simp]
theorem finiteDefectReducedScalarPerturbation_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (vector : data.projection.ker) :
    finiteDefectReducedScalarPerturbation operator data spectralParameter vector =
      (-spectralParameter) • vector := by
  rfl

/-- The real scalar shift is self-adjoint. -/
theorem finiteDefectReducedScalarPerturbation_isSelfAdjoint
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real) :
    IsSelfAdjoint
      (finiteDefectReducedScalarPerturbation operator data spectralParameter) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  change inner Real ((-spectralParameter) • first) second =
    inner Real first ((-spectralParameter) • second)
  simp

/-- The reduced spectral shift `H_red - lambda I`. -/
def finiteDefectReducedShiftedOperator
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real) :
    data.projection.ker →L[Real] data.projection.ker :=
  finiteDefectReducedOperator operator data +
    finiteDefectReducedScalarPerturbation operator data spectralParameter

@[simp]
theorem finiteDefectReducedShiftedOperator_apply
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (vector : data.projection.ker) :
    finiteDefectReducedShiftedOperator operator data spectralParameter vector =
      finiteDefectReducedOperator operator data vector -
        spectralParameter • vector := by
  simp [finiteDefectReducedShiftedOperator,
    finiteDefectReducedScalarPerturbation, sub_eq_add_neg]

/-- Small-perturbation data for a spectral parameter inside the coercive gap. -/
def finiteDefectReducedRealShiftData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant) :
    SelfAdjointSmallPerturbationData
      (finiteDefectReducedOperator operator data)
      (finiteDefectReducedScalarPerturbation operator data spectralParameter) where
  operator_selfAdjoint :=
    finiteDefectReducedOperator_isSelfAdjoint operator hSelfAdjoint data
  perturbation_selfAdjoint :=
    finiteDefectReducedScalarPerturbation_isSelfAdjoint operator data
      spectralParameter
  gap := data.coercivityConstant
  gap_pos := data.coercivityConstant_pos
  operator_lowerBound :=
    finiteDefectReducedOperator_lowerBound operator data
  perturbationBound := |spectralParameter|
  perturbationBound_nonneg := abs_nonneg spectralParameter
  perturbation_norm_le := by
    intro vector
    change ‖(-spectralParameter) • vector‖ ≤
      |spectralParameter| * ‖vector‖
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
  perturbation_small := hSpectral

/-- Quantitative bijectivity certificate for the real shifted operator. -/
def finiteDefectReducedRealShiftCertificate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant) :
    SelfAdjointSmallPerturbationCertificate
      (finiteDefectReducedOperator operator data)
      (finiteDefectReducedScalarPerturbation operator data spectralParameter)
      (finiteDefectReducedRealShiftData operator hSelfAdjoint data
        spectralParameter hSpectral) :=
  selfAdjointSmallPerturbationCertificate
    (finiteDefectReducedOperator operator data)
    (finiteDefectReducedScalarPerturbation operator data spectralParameter)
    (finiteDefectReducedRealShiftData operator hSelfAdjoint data
      spectralParameter hSpectral)

/-- Continuous linear equivalence associated with `H_red - lambda I`. -/
noncomputable def finiteDefectReducedRealResolventEquiv
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant) :
    data.projection.ker ≃L[Real] data.projection.ker :=
  ContinuousLinearEquiv.ofBijective
    (finiteDefectReducedShiftedOperator operator data spectralParameter)
    ⟨(finiteDefectReducedRealShiftCertificate operator hSelfAdjoint data
        spectralParameter hSpectral).injective,
      (finiteDefectReducedRealShiftCertificate operator hSelfAdjoint data
        spectralParameter hSpectral).surjective⟩

/-- Real reduced resolvent `(H_red - lambda I)⁻¹`. -/
noncomputable def finiteDefectReducedRealResolvent
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant) :
    data.projection.ker →L[Real] data.projection.ker :=
  (finiteDefectReducedRealResolventEquiv operator hSelfAdjoint data
    spectralParameter hSpectral).symm

@[simp]
theorem finiteDefectReducedShiftedOperator_resolvent
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant)
    (vector : data.projection.ker) :
    finiteDefectReducedShiftedOperator operator data spectralParameter
        (finiteDefectReducedRealResolvent operator hSelfAdjoint data
          spectralParameter hSpectral vector) =
      vector :=
  (finiteDefectReducedRealResolventEquiv operator hSelfAdjoint data
    spectralParameter hSpectral).apply_symm_apply vector

@[simp]
theorem finiteDefectReducedResolvent_shiftedOperator
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant)
    (vector : data.projection.ker) :
    finiteDefectReducedRealResolvent operator hSelfAdjoint data
        spectralParameter hSpectral
        (finiteDefectReducedShiftedOperator operator data spectralParameter
          vector) =
      vector :=
  (finiteDefectReducedRealResolventEquiv operator hSelfAdjoint data
    spectralParameter hSpectral).symm_apply_apply vector

/-- Pointwise resolvent estimate inside the real gap. -/
theorem finiteDefectReducedRealResolvent_norm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant)
    (vector : data.projection.ker) :
    ‖finiteDefectReducedRealResolvent operator hSelfAdjoint data
        spectralParameter hSpectral vector‖ ≤
      (data.coercivityConstant - |spectralParameter|)⁻¹ * ‖vector‖ := by
  let shiftData := finiteDefectReducedRealShiftData operator hSelfAdjoint data
    spectralParameter hSpectral
  let preimage := finiteDefectReducedRealResolvent operator hSelfAdjoint data
    spectralParameter hSpectral vector
  have hLower := selfAdjointSmallPerturbation_lowerBound
    (finiteDefectReducedOperator operator data)
    (finiteDefectReducedScalarPerturbation operator data spectralParameter)
    shiftData preimage
  rw [finiteDefectReducedShiftedOperator_resolvent operator hSelfAdjoint data
      spectralParameter hSpectral vector] at hLower
  have hGapPos : 0 < data.coercivityConstant - |spectralParameter| := by
    linarith
  have hGapNe : data.coercivityConstant - |spectralParameter| ≠ 0 :=
    ne_of_gt hGapPos
  change (data.coercivityConstant - |spectralParameter|) * ‖preimage‖ ≤
    ‖vector‖ at hLower
  calc
    ‖preimage‖ = (data.coercivityConstant - |spectralParameter|)⁻¹ *
        ((data.coercivityConstant - |spectralParameter|) * ‖preimage‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ (data.coercivityConstant - |spectralParameter|)⁻¹ * ‖vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt hGapPos))

/-- Operator norm estimate for the real reduced resolvent. -/
theorem finiteDefectReducedRealResolvent_opNorm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant) :
    ‖finiteDefectReducedRealResolvent operator hSelfAdjoint data
        spectralParameter hSpectral‖ ≤
      (data.coercivityConstant - |spectralParameter|)⁻¹ := by
  have hGapPos : 0 < data.coercivityConstant - |spectralParameter| := by
    linarith
  apply ContinuousLinearMap.opNorm_le_bound
    (inv_nonneg.mpr (le_of_lt hGapPos))
  intro vector
  simpa using finiteDefectReducedRealResolvent_norm_le operator hSelfAdjoint
    data spectralParameter hSpectral vector

/-- At spectral parameter zero the real resolvent is the reduced Green
operator built from the same full shifted-surjectivity proof. -/
theorem finiteDefectReducedRealResolvent_zero
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (hShiftSurjective : Function.Surjective
      (finiteDefectShiftedOperator operator data))
    (hZero : |(0 : Real)| < data.coercivityConstant) :
    finiteDefectReducedRealResolvent operator hSelfAdjoint data 0 hZero =
      finiteDefectReducedInverse operator data hShiftSurjective := by
  apply ContinuousLinearMap.ext
  intro vector
  apply finiteDefectReducedOperator_injective operator data
  rw [finiteDefectReducedOperator_inverse operator data hShiftSurjective]
  simpa using finiteDefectReducedShiftedOperator_resolvent operator hSelfAdjoint
    data 0 hZero vector

/-- Public real reduced-resolvent checkpoint. -/
theorem finite_defect_reduced_real_resolvent_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.coercivityConstant) :
    Function.LeftInverse
        (finiteDefectReducedRealResolvent operator hSelfAdjoint data
          spectralParameter hSpectral)
        (finiteDefectReducedShiftedOperator operator data spectralParameter) ∧
      Function.RightInverse
        (finiteDefectReducedRealResolvent operator hSelfAdjoint data
          spectralParameter hSpectral)
        (finiteDefectReducedShiftedOperator operator data spectralParameter) ∧
      ‖finiteDefectReducedRealResolvent operator hSelfAdjoint data
          spectralParameter hSpectral‖ ≤
        (data.coercivityConstant - |spectralParameter|)⁻¹ := by
  exact
    ⟨finiteDefectReducedResolvent_shiftedOperator operator hSelfAdjoint data
        spectralParameter hSpectral,
      finiteDefectReducedShiftedOperator_resolvent operator hSelfAdjoint data
        spectralParameter hSpectral,
      finiteDefectReducedRealResolvent_opNorm_le operator hSelfAdjoint data
        spectralParameter hSpectral⟩

end
end P0EFTJanusProgramPFiniteDefectReducedResolvent4D
end JanusFormal
