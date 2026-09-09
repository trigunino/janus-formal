import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteOrderUniformization

/-!
# Four-dimensional multi-index jet tower for Program P

This gate supplies the finite multi-index carrier shared by the local
Helmholtz and variational-bicomplex constructions.  It records arbitrary jet
extractions, honest truncation maps, and commuting formal total derivatives.
It does not choose a physical extraction or assert a terminal conclusion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPhysicalMultiindexJetTower4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusFiniteOrderUniformization

universe u v

/-- A spacetime multi-index in four dimensions. -/
abbrev SpacetimeMultiIndex4D := Fin 4 →₀ Nat

/-- Total differential order of a spacetime multi-index. -/
def multiIndexOrder (index : SpacetimeMultiIndex4D) : Nat :=
  index.sum fun _ exponent => exponent

@[simp] theorem multiIndexOrder_zero :
    multiIndexOrder (0 : SpacetimeMultiIndex4D) = 0 := by
  simp [multiIndexOrder]

@[simp] theorem multiIndexOrder_single
    (direction : Fin 4) (exponent : Nat) :
    multiIndexOrder (Finsupp.single direction exponent) = exponent := by
  classical
  simp [multiIndexOrder]

theorem multiIndexOrder_add
    (first second : SpacetimeMultiIndex4D) :
    multiIndexOrder (first + second) =
      multiIndexOrder first + multiIndexOrder second := by
  classical
  simp [multiIndexOrder, Finsupp.sum_add_index']

/-- The unit multi-index in one spacetime direction. -/
def coordinateMultiIndex (direction : Fin 4) : SpacetimeMultiIndex4D :=
  Finsupp.single direction 1

@[simp] theorem multiIndexOrder_coordinateMultiIndex
    (direction : Fin 4) :
    multiIndexOrder (coordinateMultiIndex direction) = 1 := by
  simp [coordinateMultiIndex]

theorem multiIndexOrder_add_coordinateMultiIndex
    (index : SpacetimeMultiIndex4D) (direction : Fin 4) :
    multiIndexOrder (index + coordinateMultiIndex direction) =
      multiIndexOrder index + 1 := by
  rw [multiIndexOrder_add, multiIndexOrder_coordinateMultiIndex]

/-- Coefficients of all multi-indices whose total order is at most `order`. -/
abbrev TruncatedMultiindexJet4D (Fiber : Type v) (order : Nat) : Type v :=
  {index : SpacetimeMultiIndex4D // multiIndexOrder index ≤ order} → Fiber

/-- Restrict a higher-order jet to a lower order. -/
def truncateMultiindexJet
    {Fiber : Type v} {lower higher : Nat}
    (hOrder : lower ≤ higher) :
    TruncatedMultiindexJet4D Fiber higher →
      TruncatedMultiindexJet4D Fiber lower :=
  fun jet index => jet ⟨index.1, index.2.trans hOrder⟩

/-- A supplied coefficient extraction from sections. -/
structure MultiindexJetExtraction4D
    (SectionSpace : Type u) (Fiber : Type v) where
  coefficient : SectionSpace → SpacetimeMultiIndex4D → Fiber

/-- Finite truncation of a supplied coefficient extraction. -/
def MultiindexJetExtraction4D.truncatedJet
    {SectionSpace : Type u} {Fiber : Type v}
    (extraction : MultiindexJetExtraction4D SectionSpace Fiber)
    (order : Nat) (sectionValue : SectionSpace) :
    TruncatedMultiindexJet4D Fiber order :=
  fun index => extraction.coefficient sectionValue index.1

@[simp] theorem truncateMultiindexJet_truncatedJet
    {SectionSpace : Type u} {Fiber : Type v}
    (extraction : MultiindexJetExtraction4D SectionSpace Fiber)
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (sectionValue : SectionSpace) :
    truncateMultiindexJet hOrder
        (extraction.truncatedJet higher sectionValue) =
      extraction.truncatedJet lower sectionValue := by
  rfl

/-- Every supplied multi-index extraction forms an actual finite jet tower. -/
def MultiindexJetExtraction4D.jetTower
    {SectionSpace : Type u} {Fiber : Type v}
    (extraction : MultiindexJetExtraction4D SectionSpace Fiber) :
    JetTower SectionSpace where
  Jet := TruncatedMultiindexJet4D Fiber
  jet := extraction.truncatedJet
  truncate := truncateMultiindexJet
  truncateJet := by
    intro lower higher hOrder sectionValue
    exact truncateMultiindexJet_truncatedJet extraction hOrder sectionValue

/-- Formal total derivative in one coordinate direction. -/
def totalDerivative
    {Fiber : Type v} {order : Nat} (direction : Fin 4) :
    TruncatedMultiindexJet4D Fiber (order + 1) →
      TruncatedMultiindexJet4D Fiber order :=
  fun jet index =>
    jet ⟨index.1 + coordinateMultiIndex direction, by
      rw [multiIndexOrder_add_coordinateMultiIndex]
      omega⟩

/-- Formal total derivatives commute on finite multi-index jets. -/
theorem totalDerivative_comm
    {Fiber : Type v} {order : Nat}
    (first second : Fin 4)
    (jet : TruncatedMultiindexJet4D Fiber ((order + 1) + 1)) :
    totalDerivative first (totalDerivative second jet) =
      totalDerivative second (totalDerivative first jet) := by
  funext index
  apply congrArg jet
  apply Subtype.ext
  change
    (index.1 + coordinateMultiIndex first) + coordinateMultiIndex second =
      (index.1 + coordinateMultiIndex second) + coordinateMultiIndex first
  ac_rfl

end
end P0EFTJanusProgramPPhysicalMultiindexJetTower4D
end JanusFormal
