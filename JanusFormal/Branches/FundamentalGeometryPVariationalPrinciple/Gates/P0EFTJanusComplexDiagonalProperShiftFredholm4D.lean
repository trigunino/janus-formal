import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalRealFredholm4D

/-!
# Fredholm diagonal multipliers after a constant shift

A proper real diagonal weight has only finitely many modes in every bounded
spectral window.  Therefore an arbitrary constant shift can create only
finitely many zero modes and leaves a positive gap away from them.
-/

namespace JanusFormal
namespace P0EFTJanusComplexDiagonalProperShiftFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalRealFredholm4D

variable (Mode : Type*) [DecidableEq Mode]

/-- Diagonal weight on a disjoint union of mode families. -/
def complexDiagonalSumWeight
    {First Second : Type*}
    (firstWeight : First → Real)
    (secondWeight : Second → Real) :
    First ⊕ Second → Real
  | .inl mode => firstWeight mode
  | .inr mode => secondWeight mode

/-- A finite direct sum of finite-zero-gap diagonal blocks is again
finite-zero-gap. -/
def complexDiagonalFiniteZeroGap_sum
    {First Second : Type*}
    (firstWeight : First → Real)
    (secondWeight : Second → Real)
    (firstData : ComplexDiagonalFiniteZeroGap First firstWeight)
    (secondData : ComplexDiagonalFiniteZeroGap Second secondWeight) :
    ComplexDiagonalFiniteZeroGap (First ⊕ Second)
      (complexDiagonalSumWeight firstWeight secondWeight) where
  gap := min firstData.gap secondData.gap
  gap_pos := lt_min firstData.gap_pos secondData.gap_pos
  gap_le := by
    intro mode hNonzero
    cases mode with
    | inl mode =>
        exact (min_le_left _ _).trans
          (firstData.gap_le mode hNonzero)
    | inr mode =>
        exact (min_le_right _ _).trans
          (secondData.gap_le mode hNonzero)
  zeroModeFinite := by
    letI : Finite (ComplexDiagonalZeroMode First firstWeight) :=
      firstData.zeroModeFinite
    letI : Finite (ComplexDiagonalZeroMode Second secondWeight) :=
      secondData.zeroModeFinite
    let zeroEquiv :
        ComplexDiagonalZeroMode (First ⊕ Second)
            (complexDiagonalSumWeight firstWeight secondWeight) ≃
          ComplexDiagonalZeroMode First firstWeight ⊕
            ComplexDiagonalZeroMode Second secondWeight :=
      {
      toFun mode := by
        rcases mode with ⟨mode, hZero⟩
        cases mode with
        | inl mode => exact Sum.inl ⟨mode, hZero⟩
        | inr mode => exact Sum.inr ⟨mode, hZero⟩
      invFun mode := by
        cases mode with
        | inl mode => exact ⟨Sum.inl mode.1, mode.2⟩
        | inr mode => exact ⟨Sum.inr mode.1, mode.2⟩
      left_inv mode := by
        rcases mode with ⟨mode, hZero⟩
        cases mode <;> rfl
      right_inv mode := by
        cases mode <;> rfl
      }
    exact Finite.of_equiv
      (ComplexDiagonalZeroMode First firstWeight ⊕
        ComplexDiagonalZeroMode Second secondWeight)
      zeroEquiv.symm

/-- Replicate one diagonal block over a finite family of sectors. -/
def complexDiagonalFiniteZeroGap_finiteProduct
    {Index : Type*} [Finite Index]
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    ComplexDiagonalFiniteZeroGap (Index × Mode)
      (fun mode => weight mode.2) where
  gap := data.gap
  gap_pos := data.gap_pos
  gap_le := fun mode hNonzero => data.gap_le mode.2 hNonzero
  zeroModeFinite := by
    letI : Finite (ComplexDiagonalZeroMode Mode weight) :=
      data.zeroModeFinite
    let zeroEquiv :
        ComplexDiagonalZeroMode (Index × Mode)
            (fun mode => weight mode.2) ≃
          Index × ComplexDiagonalZeroMode Mode weight :=
      {
      toFun mode := (mode.1.1, ⟨mode.1.2, mode.2⟩)
      invFun mode := ⟨(mode.1, mode.2.1), mode.2.2⟩
      left_inv mode := by
        rcases mode with ⟨⟨index, mode⟩, hZero⟩
        rfl
      right_inv mode := by
        rcases mode with ⟨index, ⟨mode, hZero⟩⟩
        rfl
      }
    exact Finite.of_equiv
      (Index × ComplexDiagonalZeroMode Mode weight)
      zeroEquiv.symm

/-- A uniform positive gap is the zero-kernel special case. -/
def complexDiagonalFiniteZeroGap_of_gap
    (weight : Mode → Real)
    (gap : Real)
    (gap_pos : 0 < gap)
    (gap_le : ∀ mode, gap ≤ |weight mode|) :
    ComplexDiagonalFiniteZeroGap Mode weight where
  gap := gap
  gap_pos := gap_pos
  gap_le := fun mode _ => gap_le mode
  zeroModeFinite := by
    letI : IsEmpty (ComplexDiagonalZeroMode Mode weight) :=
      ⟨fun mode => by
        have hBound := gap_le mode.1
        rw [mode.2, abs_zero] at hBound
        exact (not_lt_of_ge hBound) gap_pos⟩
    infer_instance

/-- Compact-resolvent discreteness at the coefficient level. -/
structure ComplexDiagonalProperWeight (weight : Mode → Real) : Prop where
  finite_sublevel :
    ∀ bound : Real, {mode | |weight mode| ≤ bound}.Finite

/-- Multiplication by a nonzero constant preserves properness. -/
def ComplexDiagonalProperWeight.scale
    {weight : Mode → Real}
    (proper : ComplexDiagonalProperWeight Mode weight)
    (scale : Real)
    (hScale : scale ≠ 0) :
    ComplexDiagonalProperWeight Mode
      (fun mode => scale * weight mode) where
  finite_sublevel := by
    intro bound
    apply (proper.finite_sublevel (bound / |scale|)).subset
    intro mode hMode
    change |scale * weight mode| ≤ bound at hMode
    change |weight mode| ≤ bound / |scale|
    rw [abs_mul] at hMode
    apply (le_div_iff₀ (abs_pos.mpr hScale)).2
    simpa [mul_comm] using hMode

/-- Modes which can contain a zero, or a small nonzero value, after shifting. -/
def complexDiagonalShiftRelevantModes
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real) : Finset Mode :=
  (proper.finite_sublevel (|shift| + 1)).toFinset

/-- Nonzero shifted absolute values in the finite relevant window. -/
def complexDiagonalShiftNonzeroValues
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real) : Finset Real :=
  ((complexDiagonalShiftRelevantModes Mode weight proper shift).image
      (fun mode => |weight mode + shift|)).erase 0

/-- Positive lower bound for a properly diverging weight after shifting. -/
def complexDiagonalShiftGap
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real) : Real :=
  if h :
      (complexDiagonalShiftNonzeroValues Mode weight proper shift).Nonempty
    then
      min 1
        ((complexDiagonalShiftNonzeroValues Mode weight proper shift).min' h)
    else 1

private theorem complexDiagonalShiftNonzeroValues_pos
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real)
    {value : Real}
    (hValue :
      value ∈
        complexDiagonalShiftNonzeroValues Mode weight proper shift) :
    0 < value := by
  rw [complexDiagonalShiftNonzeroValues, Finset.mem_erase] at hValue
  rcases Finset.mem_image.mp hValue.2 with ⟨mode, _, rfl⟩
  exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hValue.1)

theorem complexDiagonalShiftGap_pos
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real) :
    0 < complexDiagonalShiftGap Mode weight proper shift := by
  rw [complexDiagonalShiftGap]
  split_ifs with hNonempty
  · exact lt_min one_pos
      (complexDiagonalShiftNonzeroValues_pos Mode weight proper shift
        (Finset.min'_mem _ hNonempty))
  · exact one_pos

private theorem one_le_abs_add_of_not_relevant
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real)
    (mode : Mode)
    (hMode :
      mode ∉ complexDiagonalShiftRelevantModes Mode weight proper shift) :
    1 ≤ |weight mode + shift| := by
  have hLarge : |shift| + 1 < |weight mode| := by
    rw [complexDiagonalShiftRelevantModes,
      Set.Finite.mem_toFinset] at hMode
    exact lt_of_not_ge hMode
  have hReverse : |weight mode| - |shift| ≤ |weight mode + shift| := by
    simpa [sub_neg_eq_add, abs_neg] using
      (abs_sub_abs_le_abs_sub (weight mode) (-shift))
  linarith

theorem complexDiagonalShiftGap_le
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real)
    (mode : Mode)
    (hNonzero : weight mode + shift ≠ 0) :
    complexDiagonalShiftGap Mode weight proper shift ≤
      |weight mode + shift| := by
  by_cases hMode :
      mode ∈ complexDiagonalShiftRelevantModes Mode weight proper shift
  · have hValue :
        |weight mode + shift| ∈
          complexDiagonalShiftNonzeroValues Mode weight proper shift := by
      rw [complexDiagonalShiftNonzeroValues, Finset.mem_erase]
      exact ⟨abs_ne_zero.mpr hNonzero,
        Finset.mem_image.mpr ⟨mode, hMode, rfl⟩⟩
    have hNonempty :
        (complexDiagonalShiftNonzeroValues Mode weight proper shift).Nonempty :=
      ⟨_, hValue⟩
    rw [complexDiagonalShiftGap, dif_pos hNonempty]
    exact (min_le_right _ _).trans
      (Finset.min'_le _ _ hValue)
  · have hOutside :=
      one_le_abs_add_of_not_relevant Mode weight proper shift mode hMode
    rw [complexDiagonalShiftGap]
    split_ifs
    · exact (min_le_left _ _).trans hOutside
    · exact hOutside

/-- A proper weight remains elliptic modulo a finite kernel after any real
constant shift. -/
def complexDiagonalFiniteZeroGap_of_proper_shift
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real) :
    ComplexDiagonalFiniteZeroGap Mode (fun mode => weight mode + shift) where
  gap := complexDiagonalShiftGap Mode weight proper shift
  gap_pos := complexDiagonalShiftGap_pos Mode weight proper shift
  gap_le :=
    complexDiagonalShiftGap_le Mode weight proper shift
  zeroModeFinite := by
    have hFinite :
        {mode | weight mode + shift = 0}.Finite := by
      apply (proper.finite_sublevel (|shift| + 1)).subset
      intro mode hZero
      change weight mode + shift = 0 at hZero
      change |weight mode| ≤ |shift| + 1
      have hWeight : weight mode = -shift := by linarith
      rw [hWeight, abs_neg]
      linarith [abs_nonneg shift]
    letI :
        Fintype {mode // weight mode + shift = 0} :=
      hFinite.fintype
    exact Finite.of_fintype _

/-- Complex maximal-domain Fredholm realization of a shifted proper
multiplier. -/
theorem complexDiagonalOperator_fredholm_of_proper_shift
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real) :
    IsClosed
        (LinearMap.range
          (complexDiagonalOperator Mode (fun mode => weight mode + shift)).toFun :
          Set (ComplexDiagonalHilbert Mode)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (complexDiagonalOperator Mode
            (fun mode => weight mode + shift)).toFun) ∧
      FiniteDimensional Complex
        (ComplexDiagonalOperatorCokernel Mode
          (fun mode => weight mode + shift)) :=
  complexDiagonalOperator_fredholm_of_finiteZeroGap Mode
    (fun mode => weight mode + shift)
    (complexDiagonalFiniteZeroGap_of_proper_shift
      Mode weight proper shift)

/-- Real maximal-domain Fredholm realization of a shifted proper
multiplier. -/
theorem complexDiagonalRealOperator_fredholm_of_proper_shift
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (shift : Real) :
    IsClosed
        (LinearMap.range
          (complexDiagonalRealOperator Mode
            (fun mode => weight mode + shift)).toFun :
          Set (ComplexDiagonalHilbert Mode)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (complexDiagonalRealOperator Mode
            (fun mode => weight mode + shift)).toFun) ∧
      FiniteDimensional Real
        (ComplexDiagonalRealOperatorCokernel Mode
          (fun mode => weight mode + shift)) := by
  letI : InnerProductSpace Real (ComplexDiagonalHilbert Mode) :=
    InnerProductSpace.complexToReal
  letI :
      Star (ComplexDiagonalHilbert Mode →ₗ.[Real]
        ComplexDiagonalHilbert Mode) :=
    LinearPMap.instStar
  exact complexDiagonalRealOperator_fredholm_of_finiteZeroGap Mode
    (fun mode => weight mode + shift)
    (complexDiagonalFiniteZeroGap_of_proper_shift
      Mode weight proper shift)

end
end P0EFTJanusComplexDiagonalProperShiftFredholm4D
end JanusFormal
