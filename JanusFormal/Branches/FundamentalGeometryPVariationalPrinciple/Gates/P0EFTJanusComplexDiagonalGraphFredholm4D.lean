import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalMaximalOperator4D

/-!
# Graph-norm Fredholm theorem for complex diagonal operators

A real diagonal multiplier may be unbounded and may have finitely many zero
modes.  On its closed graph it is a bounded operator into the ambient
Hilbert space.  A positive spectral gap away from the finite zero set gives
closed range and finite-dimensional kernel and cokernel.
-/

namespace JanusFormal
namespace P0EFTJanusComplexDiagonalGraphFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D

variable (Mode : Type*) [DecidableEq Mode]

/-- Exact zero-mode type of one diagonal multiplier. -/
abbrev ComplexDiagonalZeroMode (weight : Mode → Real) :=
  {mode : Mode // weight mode = 0}

/-- Ellipticity modulo a finite-dimensional kernel. -/
structure ComplexDiagonalFiniteZeroGap (weight : Mode → Real) where
  gap : Real
  gap_pos : 0 < gap
  gap_le : ∀ mode, weight mode ≠ 0 → gap ≤ |weight mode|
  zeroModeFinite : Finite (ComplexDiagonalZeroMode Mode weight)

/-- Closed graph carrying the inherited graph norm. -/
abbrev ComplexDiagonalGraphDomain (weight : Mode → Real) :=
  (complexDiagonalOperator Mode weight).graph

noncomputable instance complexDiagonalGraphDomainCompleteSpace
    (weight : Mode → Real) :
    CompleteSpace (ComplexDiagonalGraphDomain Mode weight) := by
  letI : IsClosed
      ((complexDiagonalOperator Mode weight).graph :
        Set (ComplexDiagonalHilbert Mode ×
          ComplexDiagonalHilbert Mode)) :=
    complexDiagonalOperator_isClosed Mode weight
  infer_instance

/-- Graph-domain inclusion into the ambient Hilbert space. -/
def complexDiagonalGraphFstCLM
    (weight : Mode → Real) :
    ComplexDiagonalGraphDomain Mode weight →L[Complex]
      ComplexDiagonalHilbert Mode :=
  (ContinuousLinearMap.fst Complex
      (ComplexDiagonalHilbert Mode)
      (ComplexDiagonalHilbert Mode)).comp
    ((complexDiagonalOperator Mode weight).graph.subtypeL)

/-- The maximal operator, bounded from its graph norm to the ambient space. -/
def complexDiagonalGraphOperatorCLM
    (weight : Mode → Real) :
    ComplexDiagonalGraphDomain Mode weight →L[Complex]
      ComplexDiagonalHilbert Mode :=
  (ContinuousLinearMap.snd Complex
      (ComplexDiagonalHilbert Mode)
      (ComplexDiagonalHilbert Mode)).comp
    ((complexDiagonalOperator Mode weight).graph.subtypeL)

@[simp]
theorem complexDiagonalGraphFstCLM_apply
    (weight : Mode → Real)
    (state : ComplexDiagonalGraphDomain Mode weight) :
    complexDiagonalGraphFstCLM Mode weight state = state.1.1 :=
  rfl

@[simp]
theorem complexDiagonalGraphOperatorCLM_apply
    (weight : Mode → Real)
    (state : ComplexDiagonalGraphDomain Mode weight) :
    complexDiagonalGraphOperatorCLM Mode weight state = state.1.2 :=
  rfl

theorem complexDiagonalGraphDomain_relation
    (weight : Mode → Real)
    (state : ComplexDiagonalGraphDomain Mode weight)
    (mode : Mode) :
    state.1.2 mode = (weight mode : Complex) * state.1.1 mode := by
  rcases
      ((LinearPMap.mem_graph_iff
        (complexDiagonalOperator Mode weight)).mp state.property) with
    ⟨domainState, hFirst, hSecond⟩
  rw [← hSecond, ← hFirst]
  exact complexDiagonalOperator_apply Mode weight domainState mode

/-- Restriction to the exact finite zero-mode set. -/
def complexDiagonalZeroRestriction
    (weight : Mode → Real) :
    ComplexDiagonalHilbert Mode →ₗ[Complex]
      (ComplexDiagonalZeroMode Mode weight → Complex) where
  toFun state mode := state mode.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zero-mode restriction is bounded by the ambient `ℓ²` norm. -/
def complexDiagonalZeroRestrictionCLM
    (weight : Mode → Real)
    [Finite (ComplexDiagonalZeroMode Mode weight)] :
    ComplexDiagonalHilbert Mode →L[Complex]
      (ComplexDiagonalZeroMode Mode weight → Complex) := by
  letI := Fintype.ofFinite
    (ComplexDiagonalZeroMode Mode weight)
  exact LinearMap.mkContinuous
    (complexDiagonalZeroRestriction Mode weight) 1 (by
      intro state
      rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg state)]
      intro mode
      exact lp.norm_apply_le_norm (by norm_num) state mode.1)

/-- Replace zero weights by the positive gap. -/
def complexDiagonalRegularizedWeight
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight)
    (mode : Mode) : Real :=
  if weight mode = 0 then data.gap else weight mode

omit [DecidableEq Mode] in
theorem complexDiagonalRegularizedWeight_gap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight)
    (mode : Mode) :
    data.gap ≤
      |complexDiagonalRegularizedWeight Mode weight data mode| := by
  by_cases hZero : weight mode = 0
  · rw [complexDiagonalRegularizedWeight, if_pos hZero,
      abs_of_pos data.gap_pos]
  · rw [complexDiagonalRegularizedWeight, if_neg hZero]
    exact data.gap_le mode hZero

/-- Bounded pseudoinverse multiplier, zero on the finite kernel. -/
def complexDiagonalGraphPseudoinverse
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    ComplexDiagonalHilbert Mode →L[Complex]
      ComplexDiagonalHilbert Mode :=
  complexDiagonalInverseCLM Mode
    (complexDiagonalRegularizedWeight Mode weight data)
    data.gap data.gap_pos
    (complexDiagonalRegularizedWeight_gap Mode weight data)

theorem complexDiagonal_mul_pseudoinverse_of_zeroRestriction
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight)
    (state : ComplexDiagonalHilbert Mode)
    (hRestriction :
      complexDiagonalZeroRestriction Mode weight state = 0)
    (mode : Mode) :
    (weight mode : Complex) *
        complexDiagonalGraphPseudoinverse Mode weight data state mode =
      state mode := by
  by_cases hZero : weight mode = 0
  · have hAt := congrFun hRestriction
      (⟨mode, hZero⟩ : ComplexDiagonalZeroMode Mode weight)
    have hState : state mode = 0 := by
      change state mode = 0 at hAt
      exact hAt
    simp [hZero, hState]
  · rw [complexDiagonalGraphPseudoinverse,
      complexDiagonalInverseCLM_apply,
      complexDiagonalInverseImage_apply,
      complexDiagonalInverseCoefficient,
      complexDiagonalRegularizedWeight, if_neg hZero]
    have hWeight : (weight mode : Complex) ≠ 0 := by
      exact_mod_cast hZero
    field_simp

/-- The graph range is exactly the subspace vanishing on zero modes. -/
theorem complexDiagonalGraphOperator_range_eq_zeroRestriction_ker
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    LinearMap.range
        (complexDiagonalGraphOperatorCLM Mode weight).toLinearMap =
      LinearMap.ker (complexDiagonalZeroRestriction Mode weight) := by
  apply le_antisymm
  · intro output hOutput
    rcases hOutput with ⟨graphState, rfl⟩
    rw [LinearMap.mem_ker]
    ext zeroMode
    change graphState.1.2 zeroMode.1 = 0
    simp [complexDiagonalGraphDomain_relation Mode weight graphState
      zeroMode.1, zeroMode.property]
  · intro output hOutput
    rw [LinearMap.mem_ker] at hOutput
    let preimage : ComplexDiagonalHilbert Mode :=
      complexDiagonalGraphPseudoinverse Mode weight data output
    have hRelation :
        ∀ mode,
          output mode = (weight mode : Complex) * preimage mode := by
      intro mode
      exact
        (complexDiagonal_mul_pseudoinverse_of_zeroRestriction
          Mode weight data output hOutput mode).symm
    let domainState :
        (complexDiagonalOperator Mode weight).domain :=
      ⟨preimage, ⟨output, hRelation⟩⟩
    have hImage :
        complexDiagonalOperator Mode weight domainState = output := by
      ext mode
      rw [complexDiagonalOperator_apply]
      exact (hRelation mode).symm
    let graphState : ComplexDiagonalGraphDomain Mode weight :=
      ⟨(preimage, output),
        (LinearPMap.mem_graph_iff
          (complexDiagonalOperator Mode weight)).mpr
            ⟨domainState, rfl, hImage⟩⟩
    exact ⟨graphState, rfl⟩

theorem complexDiagonalGraphOperator_range_isClosed
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    IsClosed
      (LinearMap.range
        (complexDiagonalGraphOperatorCLM Mode weight).toLinearMap :
        Set (ComplexDiagonalHilbert Mode)) := by
  letI : Finite (ComplexDiagonalZeroMode Mode weight) :=
    data.zeroModeFinite
  rw [complexDiagonalGraphOperator_range_eq_zeroRestriction_ker
    Mode weight data]
  change IsClosed
    ((complexDiagonalZeroRestrictionCLM Mode weight).ker :
      Set (ComplexDiagonalHilbert Mode))
  exact (complexDiagonalZeroRestrictionCLM Mode weight).isClosed_ker

/-- Zero-mode coordinates of an element of the graph kernel. -/
def complexDiagonalGraphKernelZeroRestriction
    (weight : Mode → Real)
    (_data : ComplexDiagonalFiniteZeroGap Mode weight) :
    LinearMap.ker
        (complexDiagonalGraphOperatorCLM Mode weight).toLinearMap →ₗ[Complex]
      (ComplexDiagonalZeroMode Mode weight → Complex) where
  toFun state mode := state.1.1.1 mode.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem complexDiagonalGraphKernelZeroRestriction_injective
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    Function.Injective
      (complexDiagonalGraphKernelZeroRestriction Mode weight data) := by
  intro first second hCoordinates
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · ext mode
    by_cases hZero : weight mode = 0
    · exact congrFun hCoordinates
        (⟨mode, hZero⟩ : ComplexDiagonalZeroMode Mode weight)
    · have hFirstImage : first.1.1.2 = 0 := first.property
      have hSecondImage : second.1.1.2 = 0 := second.property
      have hFirstAt : first.1.1.2 mode = 0 := by
        have hAt := congrArg
          (fun state : ComplexDiagonalHilbert Mode => state mode)
          hFirstImage
        simpa using hAt
      have hSecondAt : second.1.1.2 mode = 0 := by
        have hAt := congrArg
          (fun state : ComplexDiagonalHilbert Mode => state mode)
          hSecondImage
        simpa using hAt
      have hFirstRelation :=
        complexDiagonalGraphDomain_relation Mode weight first.1 mode
      have hSecondRelation :=
        complexDiagonalGraphDomain_relation Mode weight second.1 mode
      rw [hFirstAt] at hFirstRelation
      rw [hSecondAt] at hSecondRelation
      have hWeight : (weight mode : Complex) ≠ 0 := by
        exact_mod_cast hZero
      have hFirstZero : first.1.1.1 mode = 0 :=
        (mul_eq_zero.mp hFirstRelation.symm).resolve_left hWeight
      have hSecondZero : second.1.1.1 mode = 0 :=
        (mul_eq_zero.mp hSecondRelation.symm).resolve_left hWeight
      rw [hFirstZero, hSecondZero]
  · exact first.property.trans second.property.symm

theorem complexDiagonalGraphOperator_kernel_finite
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    FiniteDimensional Complex
      (LinearMap.ker
        (complexDiagonalGraphOperatorCLM Mode weight).toLinearMap) := by
  letI : Finite (ComplexDiagonalZeroMode Mode weight) :=
    data.zeroModeFinite
  exact FiniteDimensional.of_injective
    (complexDiagonalGraphKernelZeroRestriction Mode weight data)
    (complexDiagonalGraphKernelZeroRestriction_injective
      Mode weight data)

/-- Algebraic cokernel of the bounded graph-norm realization. -/
abbrev ComplexDiagonalGraphCokernel
    (weight : Mode → Real) :=
  ComplexDiagonalHilbert Mode ⧸
    LinearMap.range
      (complexDiagonalGraphOperatorCLM Mode weight).toLinearMap

theorem complexDiagonalGraphOperator_cokernel_finite
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    FiniteDimensional Complex
      (ComplexDiagonalGraphCokernel Mode weight) := by
  letI : Finite (ComplexDiagonalZeroMode Mode weight) :=
    data.zeroModeFinite
  let quotientEquivalence :
      ComplexDiagonalGraphCokernel Mode weight ≃ₗ[Complex]
        (ComplexDiagonalHilbert Mode ⧸
          LinearMap.ker
            (complexDiagonalZeroRestriction Mode weight)) :=
    Submodule.quotEquivOfEq _ _
      (complexDiagonalGraphOperator_range_eq_zeroRestriction_ker
        Mode weight data)
  let rangeEquivalence :=
    (complexDiagonalZeroRestriction Mode weight).quotKerEquivRange
  exact FiniteDimensional.of_injective
    (quotientEquivalence.trans rangeEquivalence).toLinearMap
    (quotientEquivalence.trans rangeEquivalence).injective

/-- Complete graph-norm Fredholm criterion. -/
theorem complexDiagonalGraphOperator_fredholm
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    IsClosed
        (LinearMap.range
          (complexDiagonalGraphOperatorCLM Mode weight).toLinearMap :
          Set (ComplexDiagonalHilbert Mode)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (complexDiagonalGraphOperatorCLM Mode weight).toLinearMap) ∧
      FiniteDimensional Complex
        (ComplexDiagonalGraphCokernel Mode weight) :=
  ⟨complexDiagonalGraphOperator_range_isClosed Mode weight data,
    complexDiagonalGraphOperator_kernel_finite Mode weight data,
    complexDiagonalGraphOperator_cokernel_finite Mode weight data⟩

/-- The maximal-domain operator and its bounded graph-norm realization have
exactly the same ambient range. -/
theorem complexDiagonalOperator_range_eq_graphOperator_range
    (weight : Mode → Real) :
    LinearMap.range (complexDiagonalOperator Mode weight).toFun =
      LinearMap.range
        (complexDiagonalGraphOperatorCLM Mode weight).toLinearMap := by
  apply le_antisymm
  · rintro output ⟨state, rfl⟩
    let graphState : ComplexDiagonalGraphDomain Mode weight :=
      ⟨((state : ComplexDiagonalHilbert Mode),
          complexDiagonalOperator Mode weight state),
        LinearPMap.mem_graph (complexDiagonalOperator Mode weight) state⟩
    exact ⟨graphState, rfl⟩
  · rintro output ⟨state, rfl⟩
    rcases
        ((LinearPMap.mem_graph_iff
          (complexDiagonalOperator Mode weight)).mp state.property) with
      ⟨domainState, _, hImage⟩
    exact ⟨domainState, hImage⟩

theorem complexDiagonalOperator_range_isClosed_of_finiteZeroGap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    IsClosed
      (LinearMap.range (complexDiagonalOperator Mode weight).toFun :
        Set (ComplexDiagonalHilbert Mode)) := by
  rw [complexDiagonalOperator_range_eq_graphOperator_range Mode weight]
  exact complexDiagonalGraphOperator_range_isClosed Mode weight data

/-- Zero-mode coordinates of the kernel on the genuine maximal domain. -/
def complexDiagonalOperatorKernelZeroRestriction
    (weight : Mode → Real) :
    LinearMap.ker (complexDiagonalOperator Mode weight).toFun →ₗ[Complex]
      (ComplexDiagonalZeroMode Mode weight → Complex) where
  toFun state mode := state.1.1 mode.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem complexDiagonalOperatorKernelZeroRestriction_injective
    (weight : Mode → Real) :
    Function.Injective
      (complexDiagonalOperatorKernelZeroRestriction Mode weight) := by
  intro first second hCoordinates
  apply Subtype.ext
  apply Subtype.ext
  ext mode
  by_cases hZero : weight mode = 0
  · exact congrFun hCoordinates
      (⟨mode, hZero⟩ : ComplexDiagonalZeroMode Mode weight)
  · have hFirstImage :
        complexDiagonalOperator Mode weight first.1 = 0 :=
      first.property
    have hSecondImage :
        complexDiagonalOperator Mode weight second.1 = 0 :=
      second.property
    have hFirstAt :
        (complexDiagonalOperator Mode weight first.1) mode = 0 := by
      rw [hFirstImage]
      rfl
    have hSecondAt :
        (complexDiagonalOperator Mode weight second.1) mode = 0 := by
      rw [hSecondImage]
      rfl
    rw [complexDiagonalOperator_apply] at hFirstAt hSecondAt
    have hWeight : (weight mode : Complex) ≠ 0 := by
      exact_mod_cast hZero
    exact
      ((mul_eq_zero.mp hFirstAt).resolve_left hWeight).trans
        ((mul_eq_zero.mp hSecondAt).resolve_left hWeight).symm

theorem complexDiagonalOperator_kernel_finite_of_finiteZeroGap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    FiniteDimensional Complex
      (LinearMap.ker (complexDiagonalOperator Mode weight).toFun) := by
  letI : Finite (ComplexDiagonalZeroMode Mode weight) :=
    data.zeroModeFinite
  exact FiniteDimensional.of_injective
    (complexDiagonalOperatorKernelZeroRestriction Mode weight)
    (complexDiagonalOperatorKernelZeroRestriction_injective Mode weight)

/-- Algebraic cokernel of the genuine maximal-domain operator. -/
abbrev ComplexDiagonalOperatorCokernel
    (weight : Mode → Real) :=
  ComplexDiagonalHilbert Mode ⧸
    LinearMap.range (complexDiagonalOperator Mode weight).toFun

theorem complexDiagonalOperator_cokernel_finite_of_finiteZeroGap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    FiniteDimensional Complex
      (ComplexDiagonalOperatorCokernel Mode weight) := by
  letI : Finite (ComplexDiagonalZeroMode Mode weight) :=
    data.zeroModeFinite
  let quotientEquivalence :
      ComplexDiagonalOperatorCokernel Mode weight ≃ₗ[Complex]
        (ComplexDiagonalHilbert Mode ⧸
          LinearMap.ker
            (complexDiagonalZeroRestriction Mode weight)) :=
    Submodule.quotEquivOfEq _ _
      ((complexDiagonalOperator_range_eq_graphOperator_range
          Mode weight).trans
        (complexDiagonalGraphOperator_range_eq_zeroRestriction_ker
          Mode weight data))
  let rangeEquivalence :=
    (complexDiagonalZeroRestriction Mode weight).quotKerEquivRange
  exact FiniteDimensional.of_injective
    (quotientEquivalence.trans rangeEquivalence).toLinearMap
    (quotientEquivalence.trans rangeEquivalence).injective

/-- Fredholm criterion directly for the maximal unbounded multiplier. -/
theorem complexDiagonalOperator_fredholm_of_finiteZeroGap
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    IsClosed
        (LinearMap.range (complexDiagonalOperator Mode weight).toFun :
          Set (ComplexDiagonalHilbert Mode)) ∧
      FiniteDimensional Complex
        (LinearMap.ker (complexDiagonalOperator Mode weight).toFun) ∧
      FiniteDimensional Complex
        (ComplexDiagonalOperatorCokernel Mode weight) :=
  ⟨complexDiagonalOperator_range_isClosed_of_finiteZeroGap
      Mode weight data,
    complexDiagonalOperator_kernel_finite_of_finiteZeroGap
      Mode weight data,
    complexDiagonalOperator_cokernel_finite_of_finiteZeroGap
      Mode weight data⟩

end
end P0EFTJanusComplexDiagonalGraphFredholm4D
end JanusFormal
