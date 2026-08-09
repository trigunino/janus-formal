import Mathlib.Analysis.InnerProductSpace.Projection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# Actual-kernel gap from the complement of finitely many named modes

The H12 actual-kernel packet should not ask independently that the kernel is
finite.  Suppose finitely many ambient vectors are killed by a self-adjoint
operator and the operator has a positive lower bound on the orthogonal
complement of their ambient span.  Orthogonal projection onto the finite span
then shows that every zero mode belongs to this span.

Consequently:

* the named span is exactly the genuine kernel;
* the genuine kernel is finite dimensional;
* the supplied lower bound is already the lower bound on `(ker H)ᗮ`.

This is the direct bridge between physical named symmetries and the canonical
actual-kernel Green construction.  It introduces no defect projector,
parametrix or separately supplied finite-kernel certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteNamedModeComplementGap4D

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 1300000

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Ambient span of finitely many named modes. -/
def finiteNamedModeAmbientSpan
    {ZeroMode : Type*} (vector : ZeroMode → E) : Submodule Real E :=
  Submodule.span Real (Set.range vector)

local instance finiteNamedModeAmbientSpanFiniteDimensional
    {ZeroMode : Type*} [Fintype ZeroMode]
    (vector : ZeroMode → E) :
    FiniteDimensional Real (finiteNamedModeAmbientSpan vector) := by
  unfold finiteNamedModeAmbientSpan
  exact FiniteDimensional.span_of_finite (Set.finite_range vector)

/-- The span of named vectors lies in the genuine kernel. -/
theorem finiteNamedModeAmbientSpan_le_kernel
    (operator : E →L[Real] E)
    {ZeroMode : Type*}
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0) :
    finiteNamedModeAmbientSpan vector ≤ operator.ker := by
  rw [finiteNamedModeAmbientSpan, Submodule.span_le]
  rintro current ⟨mode, rfl⟩
  exact LinearMap.mem_ker.mpr (annihilated mode)

/-- The operator vanishes on the complete named span. -/
theorem operator_zero_on_finiteNamedModeAmbientSpan
    (operator : E →L[Real] E)
    {ZeroMode : Type*}
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0)
    (current : finiteNamedModeAmbientSpan vector) :
    operator current.1 = 0 :=
  LinearMap.mem_ker.mp
    (finiteNamedModeAmbientSpan_le_kernel operator vector annihilated
      current.property)

/-- Self-adjointness and annihilation of the named span make its orthogonal
complement invariant. -/
theorem selfAdjoint_operator_mem_finiteNamedModeComplement
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {ZeroMode : Type*}
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0)
    (current : (finiteNamedModeAmbientSpan vector)ᗮ) :
    operator current.1 ∈ (finiteNamedModeAmbientSpan vector)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro named hNamed
  calc
    inner Real (operator current.1) named =
        inner Real current.1 (operator named) :=
      hSelfAdjoint.isSymmetric current.1 named
    _ = 0 := by
      have hNamedZero : operator named = 0 :=
        operator_zero_on_finiteNamedModeAmbientSpan operator vector annihilated
          ⟨named, hNamed⟩
      rw [hNamedZero, inner_zero_right]

/-- Restriction of the same operator to the orthogonal complement of the named
span. -/
def finiteNamedModeComplementOperator
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {ZeroMode : Type*}
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0) :
    (finiteNamedModeAmbientSpan vector)ᗮ →L[Real]
      (finiteNamedModeAmbientSpan vector)ᗮ := by
  let linear : (finiteNamedModeAmbientSpan vector)ᗮ →ₗ[Real]
      (finiteNamedModeAmbientSpan vector)ᗮ :=
    { toFun := fun current =>
        ⟨operator current.1,
          selfAdjoint_operator_mem_finiteNamedModeComplement operator
            hSelfAdjoint vector annihilated current⟩
      map_add' := by
        intro first second
        apply Subtype.ext
        exact map_add operator first.1 second.1
      map_smul' := by
        intro scalar current
        apply Subtype.ext
        exact map_smul operator scalar current.1 }
  exact linear.mkContinuous ‖operator‖ (by
    intro current
    change ‖operator current.1‖ ≤ ‖operator‖ * ‖current.1‖
    exact operator.le_opNorm current.1)

@[simp]
theorem finiteNamedModeComplementOperator_apply
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {ZeroMode : Type*}
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0)
    (current : (finiteNamedModeAmbientSpan vector)ᗮ) :
    (finiteNamedModeComplementOperator operator hSelfAdjoint vector annihilated
      current).1 = operator current.1 :=
  rfl

/-- Finitely many named zero modes and one positive bound on the complement of
their ambient span.  No finite-dimensionality of `ker operator` is stored. -/
structure FiniteNamedModeComplementGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  vector : ZeroMode → E
  annihilated : ∀ mode, operator (vector mode) = 0
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ current : (finiteNamedModeAmbientSpan vector)ᗮ,
    gap * ‖current‖ ≤
      ‖finiteNamedModeComplementOperator operator hSelfAdjoint vector
        annihilated current‖

namespace FiniteNamedModeComplementGapData

/-- Coercivity on the named-span complement excludes every hidden zero mode. -/
theorem kernel_eq_namedSpan
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteNamedModeComplementGapData operator hSelfAdjoint ZeroMode) :
    operator.ker = finiteNamedModeAmbientSpan data.vector := by
  apply le_antisymm
  · intro zeroMode hZeroMode
    let span := finiteNamedModeAmbientSpan data.vector
    letI : FiniteDimensional Real span :=
      finiteNamedModeAmbientSpanFiniteDimensional data.vector
    letI : CompleteSpace span := FiniteDimensional.complete Real span
    let projected : span := span.orthogonalProjection zeroMode
    let remainder : spanᗮ :=
      ⟨zeroMode - projected.1,
        span.sub_orthogonalProjection_mem_orthogonal zeroMode⟩
    have hProjectedZero : operator projected.1 = 0 :=
      operator_zero_on_finiteNamedModeAmbientSpan operator data.vector
        data.annihilated projected
    have hRemainderZero :
        finiteNamedModeComplementOperator operator hSelfAdjoint data.vector
          data.annihilated remainder = 0 := by
      apply Subtype.ext
      change operator (zeroMode - projected.1) = 0
      rw [map_sub, LinearMap.mem_ker.mp hZeroMode, hProjectedZero, sub_self]
    have hLower := data.lowerBound remainder
    rw [hRemainderZero, norm_zero] at hLower
    have hRemainderNorm : ‖remainder‖ = 0 := by
      by_contra hNonzero
      have hNormPos : 0 < ‖remainder‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hNonzero)
      have hProductPos : 0 < data.gap * ‖remainder‖ :=
        mul_pos data.gap_pos hNormPos
      exact (not_lt_of_ge hLower) hProductPos
    have hRemainder : remainder = 0 := norm_eq_zero.mp hRemainderNorm
    have hAmbient : zeroMode = projected.1 := by
      have hValue := congrArg Subtype.val hRemainder
      change zeroMode - projected.1 = 0 at hValue
      exact sub_eq_zero.mp hValue
    rw [hAmbient]
    exact projected.property
  · exact finiteNamedModeAmbientSpan_le_kernel operator data.vector
      data.annihilated

/-- The genuine kernel is finite dimensional because it is the finite named
span. -/
def kernelFinite
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteNamedModeComplementGapData operator hSelfAdjoint ZeroMode) :
    FiniteDimensional Real operator.ker := by
  rw [data.kernel_eq_namedSpan]
  infer_instance

/-- Convert the named-complement estimate to the canonical actual-kernel gap. -/
def toActualKernelGap
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteNamedModeComplementGapData operator hSelfAdjoint ZeroMode) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint where
  kernel_finite := data.kernelFinite
  gap := data.gap
  gap_pos := data.gap_pos
  lowerBound := by
    intro current
    let namedCurrent : (finiteNamedModeAmbientSpan data.vector)ᗮ :=
      ⟨current.1, by
        rw [← data.kernel_eq_namedSpan]
        exact current.property⟩
    simpa [namedCurrent] using data.lowerBound namedCurrent

/-- Public named-span-to-actual-kernel checkpoint. -/
theorem finite_named_mode_complement_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteNamedModeComplementGapData operator hSelfAdjoint ZeroMode) :
    operator.ker = finiteNamedModeAmbientSpan data.vector ∧
      SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  ⟨data.kernel_eq_namedSpan, data.toActualKernelGap⟩

end FiniteNamedModeComplementGapData

end
end P0EFTJanusProgramPFiniteNamedModeComplementGap4D
end JanusFormal
