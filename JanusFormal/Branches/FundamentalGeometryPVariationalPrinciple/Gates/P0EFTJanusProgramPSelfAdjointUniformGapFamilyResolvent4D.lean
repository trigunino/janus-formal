import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointUniformGapFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointSmallPerturbation4D

/-!
# Uniform real resolvent for a self-adjoint gap family

A uniform gap `c` controls not only every Green operator at zero but the full
two-parameter real resolvent

`(H_a - lambda I)⁻¹`,  `|lambda| < c`.

The same open spectral interval works for every family parameter, and the norm
bound `(c - |lambda|)⁻¹` is uniform in that parameter.  In particular, zero is
never crossed by the reduced family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointUniformGapFamilyResolvent4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open P0EFTJanusProgramPSelfAdjointSmallPerturbation4D
open P0EFTJanusProgramPSelfAdjointUniformGapFamily4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Real scalar perturbation `-lambda I`. -/
def uniformGapFamilyScalarShift
    (spectralParameter : Real) : E →L[Real] E :=
  (-spectralParameter) • ContinuousLinearMap.id Real E

@[simp]
theorem uniformGapFamilyScalarShift_apply
    (spectralParameter : Real) (vector : E) :
    uniformGapFamilyScalarShift (E := E) spectralParameter vector =
      (-spectralParameter) • vector :=
  rfl

/-- Scalar shifts are self-adjoint. -/
theorem uniformGapFamilyScalarShift_isSelfAdjoint
    (spectralParameter : Real) :
    IsSelfAdjoint (uniformGapFamilyScalarShift (E := E) spectralParameter) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  change inner Real ((-spectralParameter) • first) second =
    inner Real first ((-spectralParameter) • second)
  simp only [real_inner_smul_left, real_inner_smul_right]

/-- Shifted member `H_a - lambda I`. -/
def uniformGapFamilyShiftedOperator
    (operator : Real → E →L[Real] E)
    (parameter spectralParameter : Real) : E →L[Real] E :=
  operator parameter + uniformGapFamilyScalarShift spectralParameter

@[simp]
theorem uniformGapFamilyShiftedOperator_apply
    (operator : Real → E →L[Real] E)
    (parameter spectralParameter : Real) (vector : E) :
    uniformGapFamilyShiftedOperator operator parameter spectralParameter vector =
      operator parameter vector - spectralParameter • vector := by
  simp [uniformGapFamilyShiftedOperator, uniformGapFamilyScalarShift,
    sub_eq_add_neg]

/-- Small-perturbation packet uniform in the family parameter. -/
def uniformGapFamilyRealShiftData
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :
    SelfAdjointSmallPerturbationData
      (operator parameter)
      (uniformGapFamilyScalarShift spectralParameter) where
  operator_selfAdjoint := data.selfAdjoint parameter
  perturbation_selfAdjoint :=
    uniformGapFamilyScalarShift_isSelfAdjoint spectralParameter
  gap := data.gap
  gap_pos := data.gap_pos
  operator_lowerBound := data.lowerBound parameter
  perturbationBound := |spectralParameter|
  perturbationBound_nonneg := abs_nonneg spectralParameter
  perturbation_norm_le := by
    intro vector
    change ‖(-spectralParameter) • vector‖ ≤
      |spectralParameter| * ‖vector‖
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
  perturbation_small := hSpectral

/-- Bijectivity certificate for one point of the two-parameter resolvent. -/
def uniformGapFamilyRealShiftCertificate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :=
  selfAdjointSmallPerturbationCertificate
    (operator parameter)
    (uniformGapFamilyScalarShift spectralParameter)
    (uniformGapFamilyRealShiftData data parameter spectralParameter hSpectral)

/-- Continuous equivalence induced by `H_a - lambda I`. -/
noncomputable def uniformGapFamilyResolventEquiv
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) : E ≃L[Real] E :=
  ContinuousLinearEquiv.ofBijective
    (uniformGapFamilyShiftedOperator operator parameter spectralParameter)
    (LinearMap.ker_eq_bot.mpr
      (uniformGapFamilyRealShiftCertificate data parameter spectralParameter
        hSpectral).injective)
    (LinearMap.range_eq_top.mpr
      (uniformGapFamilyRealShiftCertificate data parameter spectralParameter
        hSpectral).surjective)

/-- Uniform family resolvent. -/
noncomputable def uniformGapFamilyResolvent
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) : E →L[Real] E :=
  (uniformGapFamilyResolventEquiv data parameter spectralParameter hSpectral).symm

@[simp]
theorem shiftedOperator_resolvent
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap)
    (vector : E) :
    uniformGapFamilyShiftedOperator operator parameter spectralParameter
        (uniformGapFamilyResolvent data parameter spectralParameter hSpectral
          vector) = vector :=
  by
    simpa [uniformGapFamilyResolvent, uniformGapFamilyResolventEquiv] using
      (uniformGapFamilyResolventEquiv data parameter spectralParameter hSpectral
        ).apply_symm_apply vector

@[simp]
theorem resolvent_shiftedOperator
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap)
    (vector : E) :
    uniformGapFamilyResolvent data parameter spectralParameter hSpectral
        (uniformGapFamilyShiftedOperator operator parameter spectralParameter
          vector) = vector :=
  by
    simpa [uniformGapFamilyResolvent, uniformGapFamilyResolventEquiv] using
      (uniformGapFamilyResolventEquiv data parameter spectralParameter hSpectral
        ).symm_apply_apply vector

/-- Pointwise resolvent estimate, uniform in the family parameter. -/
theorem uniformGapFamilyResolvent_norm_le
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap)
    (vector : E) :
    ‖uniformGapFamilyResolvent data parameter spectralParameter hSpectral
        vector‖ ≤
      (data.gap - |spectralParameter|)⁻¹ * ‖vector‖ := by
  let shiftData :=
    uniformGapFamilyRealShiftData data parameter spectralParameter hSpectral
  let preimage :=
    uniformGapFamilyResolvent data parameter spectralParameter hSpectral vector
  have hLower := selfAdjointSmallPerturbation_lowerBound
    (operator parameter)
    (uniformGapFamilyScalarShift spectralParameter) shiftData preimage
  change shiftData.remainingGap * ‖preimage‖ ≤
    ‖uniformGapFamilyShiftedOperator operator parameter spectralParameter preimage‖
    at hLower
  rw [shiftedOperator_resolvent data parameter spectralParameter hSpectral
      vector] at hLower
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

/-- Operator-norm estimate uniform in `a`. -/
theorem uniformGapFamilyResolvent_opNorm_le
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter spectralParameter : Real)
    (hSpectral : |spectralParameter| < data.gap) :
    ‖uniformGapFamilyResolvent data parameter spectralParameter hSpectral‖ ≤
      (data.gap - |spectralParameter|)⁻¹ := by
  have hGapPos : 0 < data.gap - |spectralParameter| := by
    linarith
  apply (uniformGapFamilyResolvent data parameter spectralParameter hSpectral).opNorm_le_bound
    (inv_nonneg.mpr (le_of_lt hGapPos))
  intro vector
  exact uniformGapFamilyResolvent_norm_le data parameter spectralParameter
    hSpectral vector

/-- At zero spectral parameter, the family resolvent is the Green family. -/
theorem uniformGapFamilyResolvent_zero
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real)
    (hZero : |(0 : Real)| < data.gap) :
    uniformGapFamilyResolvent data parameter 0 hZero =
      data.green parameter := by
  apply ContinuousLinearMap.ext
  intro vector
  apply (data.bijective parameter).1
  rw [data.operator_green parameter vector]
  simpa using shiftedOperator_resolvent data parameter 0 hZero vector

/-- Uniform absence of zero crossings. -/
def UniformGapFamilyNoCrossingCertificate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator) : Prop :=
  ∀ parameter vector, operator parameter vector = 0 → vector = 0

/-- A positive uniform gap gives the no-crossing certificate. -/
theorem uniformGapFamily_noCrossing
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator) :
    UniformGapFamilyNoCrossingCertificate data := by
  intro parameter vector hZero
  apply (data.bijective parameter).1
  simpa using hZero

/-- Public uniform resolvent and no-crossing checkpoint. -/
theorem self_adjoint_uniform_gap_family_resolvent_gate
    (operator : Real → E →L[Real] E)
    (data : SelfAdjointUniformGapFamilyData operator) :
    (∀ parameter spectralParameter,
      ∀ hSpectral : |spectralParameter| < data.gap,
        Function.Bijective
          (uniformGapFamilyShiftedOperator operator parameter
            spectralParameter)) ∧
      (∀ parameter spectralParameter,
        ∀ hSpectral : |spectralParameter| < data.gap,
          ‖uniformGapFamilyResolvent data parameter spectralParameter
              hSpectral‖ ≤
            (data.gap - |spectralParameter|)⁻¹) ∧
      UniformGapFamilyNoCrossingCertificate data :=
  ⟨fun parameter spectralParameter hSpectral =>
      ⟨(uniformGapFamilyRealShiftCertificate data parameter spectralParameter
          hSpectral).injective,
        (uniformGapFamilyRealShiftCertificate data parameter spectralParameter
          hSpectral).surjective⟩,
    uniformGapFamilyResolvent_opNorm_le data,
    uniformGapFamily_noCrossing data⟩

end
end P0EFTJanusProgramPSelfAdjointUniformGapFamilyResolvent4D
end JanusFormal
