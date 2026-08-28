import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSchurDeterminantFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurNondegenerate4D

/-!
# Continuous families of full operators with finite Schur reduction

A parameterized family of operators on one fixed Hilbert space is supplied with
bounded four-block Schur data at every parameter.  Continuity of the finite
Schur matrices makes the nondegenerate parameter locus open.  At every point of
that locus the full operator is bijective and has a bounded inverse.

This is the local stability statement needed before differentiating Green
operators or determinant lines along a physical family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeContinuousSchurFamily4D

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open P0EFTJanusProgramPFiniteModeSchurBlockElimination4D
open P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D
open P0EFTJanusProgramPFiniteModeSchurDeterminant4D
open P0EFTJanusProgramPFiniteModeSchurNondegenerate4D
open P0EFTJanusProgramPFiniteSchurDeterminantFamily4D

variable {Parameter E Mode Complement : Type*}
  [TopologicalSpace Parameter]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [Fintype Mode] [DecidableEq Mode]
  [NormedAddCommGroup Complement] [NormedSpace Real Complement]

/-- One continuous family of full operators with bounded Schur blocks. -/
structure FiniteModeContinuousSchurFamilyData where
  operator : Parameter → (E →L[Real] E)
  blocks : ∀ parameter,
    FiniteModeContinuousSchurBlockData
      (operator parameter) Mode Complement
  continuous_schur_matrix : Continuous fun parameter =>
    finiteModeSchurMatrix (blocks parameter).toLinearBlockData

/-- The finite Schur operator family. -/
def FiniteModeContinuousSchurFamilyData.schur
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement))
    (parameter : Parameter) :
    (Mode → Real) →ₗ[Real] (Mode → Real) :=
  finiteModeSchurBlockOperator (family.blocks parameter).toLinearBlockData

/-- Determinant family controlling full invertibility. -/
def FiniteModeContinuousSchurFamilyData.determinantFamily
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement)) :
    FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode) where
  schur := family.schur
  continuous_matrix := family.continuous_schur_matrix

/-- Nondegenerate parameters of the full operator family. -/
def FiniteModeContinuousSchurFamilyData.nondegenerateSet
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement)) : Set Parameter :=
  family.determinantFamily.nondegenerateSet

/-- The full nondegenerate locus is open. -/
theorem FiniteModeContinuousSchurFamilyData.isOpen_nondegenerateSet
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement)) :
    IsOpen family.nondegenerateSet :=
  family.determinantFamily.isOpen_nondegenerateSet

/-- Pointwise determinant certificate. -/
def FiniteModeContinuousSchurFamilyData.determinantDataAt
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement))
    (parameter : Parameter)
    (hNondegenerate : parameter ∈ family.nondegenerateSet) :
    FiniteModeSchurDeterminantData
      (family.operator parameter) Mode Complement where
  blockData := (family.blocks parameter).toLinearBlockData
  determinant_ne_zero := hNondegenerate

/-- Pointwise nondegenerate Schur packet. -/
def FiniteModeContinuousSchurFamilyData.nondegenerateDataAt
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement))
    (parameter : Parameter)
    (hNondegenerate : parameter ∈ family.nondegenerateSet) :
    FiniteModeSchurNondegenerateData
      (family.operator parameter) Mode Complement :=
  (family.determinantDataAt parameter hNondegenerate).toNondegenerateData

/-- Every operator on the nondegenerate locus is bijective. -/
theorem FiniteModeContinuousSchurFamilyData.operator_bijective
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement))
    (parameter : Parameter)
    (hNondegenerate : parameter ∈ family.nondegenerateSet) :
    Function.Bijective (family.operator parameter) :=
  finiteModeSchur_operator_bijective
    (family.nondegenerateDataAt parameter hNondegenerate)

/-- Pointwise full Green operator on the nondegenerate locus. -/
noncomputable def FiniteModeContinuousSchurFamilyData.fullGreenAt
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement))
    (parameter : Parameter)
    (hNondegenerate : parameter ∈ family.nondegenerateSet) :
    E →L[Real] E :=
  finiteModeSchurFullGreen
    (family.nondegenerateDataAt parameter hNondegenerate)

@[simp]
theorem FiniteModeContinuousSchurFamilyData.fullGreen_operator
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement))
    (parameter : Parameter)
    (hNondegenerate : parameter ∈ family.nondegenerateSet)
    (state : E) :
    family.fullGreenAt parameter hNondegenerate
        (family.operator parameter state) = state :=
  finiteModeSchurFullGreen_operator
    (family.nondegenerateDataAt parameter hNondegenerate) state

@[simp]
theorem FiniteModeContinuousSchurFamilyData.operator_fullGreen
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement))
    (parameter : Parameter)
    (hNondegenerate : parameter ∈ family.nondegenerateSet)
    (state : E) :
    family.operator parameter
        (family.fullGreenAt parameter hNondegenerate state) = state :=
  finiteModeSchur_operator_fullGreen
    (family.nondegenerateDataAt parameter hNondegenerate) state

/-- Near every nondegenerate parameter all full operators remain bijective. -/
theorem FiniteModeContinuousSchurFamilyData.eventually_operator_bijective
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement))
    {parameter : Parameter}
    (hNondegenerate : parameter ∈ family.nondegenerateSet) :
    ∀ᶠ nearby in 𝓝 parameter,
      Function.Bijective (family.operator nearby) := by
  filter_upwards
    [family.determinantFamily.eventually_nondegenerate hNondegenerate]
      with nearby hNearby
  exact family.operator_bijective nearby hNearby

/-- Public family-stability checkpoint. -/
theorem finite_mode_continuous_schur_family_gate
    (family : FiniteModeContinuousSchurFamilyData
      (Parameter := Parameter) (E := E) (Mode := Mode)
      (Complement := Complement)) :
    IsOpen family.nondegenerateSet ∧
      (∀ parameter, parameter ∈ family.nondegenerateSet →
        Function.Bijective (family.operator parameter)) ∧
      (∀ parameter, parameter ∈ family.nondegenerateSet →
        ∀ᶠ nearby in 𝓝 parameter,
          Function.Bijective (family.operator nearby)) :=
  ⟨family.isOpen_nondegenerateSet,
    family.operator_bijective,
    fun parameter hNondegenerate =>
      family.eventually_operator_bijective
        (parameter := parameter) hNondegenerate⟩

end
end P0EFTJanusProgramPFiniteModeContinuousSchurFamily4D
end JanusFormal
