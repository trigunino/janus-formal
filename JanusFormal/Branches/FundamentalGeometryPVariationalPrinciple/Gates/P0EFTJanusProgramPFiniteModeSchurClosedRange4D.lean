import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurKernel4D

/-!
# Closed range from finite-mode Schur coordinates

A finite Schur factorization already contains the algebraic reason that the
full operator has closed range: in reduced coordinates its range is

`range(S) × G`,

where `S` acts on a finite-dimensional space.  The only topological datum
needed to transfer this statement back is continuity of the reduced range
coordinate map.

This file proves the exact range characterization and derives closed range.
It removes `range H is closed` as an independent hypothesis from the Schur
zero-mode route.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeSchurClosedRange4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPFiniteModeSchurKernel4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- A Schur factorization whose left reduced coordinates depend continuously
on the original Hilbert-space vector. -/
structure FiniteModeSchurClosedRangeData
    (operator : E →L[Real] E)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement] where
  schurData : FiniteModeSchurKernelData operator Mode Complement
  rangeCoordinates : E →L[Real] ((Mode → Real) × Complement)
  rangeCoordinates_eq : ∀ state : E,
    rangeCoordinates state =
      schurData.leftReduction (schurData.decomposition state)

/-- In reduced coordinates the full operator range is exactly
`range(S) × G`. -/
theorem finiteModeSchur_operatorRange_eq_preimage
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurClosedRangeData operator Mode Complement) :
    (operator.range : Set E) =
      data.rangeCoordinates ⁻¹'
        ((data.schurData.schur.range : Set (Mode → Real)) ×ˢ
          (Set.univ : Set Complement)) := by
  ext target
  constructor
  · rintro ⟨source, rfl⟩
    let reduced := data.schurData.rightReduction.symm
      (data.schurData.decomposition source)
    have hFactor :
        data.schurData.leftReduction
            (data.schurData.decomposition (operator source)) =
          (data.schurData.schur reduced.1,
            data.schurData.complementOperator reduced.2) := by
      simpa [reduced] using data.schurData.factorization reduced
    rw [Set.mem_preimage, data.rangeCoordinates_eq, hFactor]
    exact ⟨⟨reduced.1, rfl⟩, Set.mem_univ _⟩
  · intro hTarget
    rw [Set.mem_preimage, data.rangeCoordinates_eq] at hTarget
    obtain ⟨finiteSource, hFinite⟩ := hTarget.1
    obtain ⟨complementSource, hComplement⟩ :=
      data.schurData.complement_bijective.2
        (data.schurData.leftReduction
          (data.schurData.decomposition target)).2
    let reduced : (Mode → Real) × Complement :=
      (finiteSource, complementSource)
    let source : E :=
      data.schurData.decomposition.symm
        (data.schurData.rightReduction reduced)
    refine ⟨source, ?_⟩
    apply data.schurData.decomposition.injective
    apply data.schurData.leftReduction.injective
    rw [data.schurData.factorization reduced]
    apply Prod.ext
    · exact hFinite
    · exact hComplement

/-- The finite Schur range is closed. -/
theorem finiteModeSchur_finiteRange_closed
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurClosedRangeData operator Mode Complement) :
    IsClosed (data.schurData.schur.range : Set (Mode → Real)) := by
  letI : FiniteDimensional Real data.schurData.schur.range := inferInstance
  exact Submodule.closed_of_finiteDimensional data.schurData.schur.range

/-- Closed range of the full operator follows from the finite Schur
factorization and continuity of the reduced coordinates. -/
theorem finiteModeSchur_operatorRange_closed
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurClosedRangeData operator Mode Complement) :
    IsClosed (operator.range : Set E) := by
  rw [finiteModeSchur_operatorRange_eq_preimage data]
  exact
    ((finiteModeSchur_finiteRange_closed data).prod isClosed_univ).preimage
      data.rangeCoordinates.continuous

/-- Public closed-range checkpoint. -/
theorem finite_mode_schur_closed_range_gate
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurClosedRangeData operator Mode Complement) :
    IsClosed (operator.range : Set E) ∧
      Module.finrank Real operator.ker ≤ Fintype.card Mode :=
  ⟨finiteModeSchur_operatorRange_closed data,
    finiteModeSchur_operatorKernel_finrank_le_card data.schurData⟩

end
end P0EFTJanusProgramPFiniteModeSchurClosedRange4D
end JanusFormal
