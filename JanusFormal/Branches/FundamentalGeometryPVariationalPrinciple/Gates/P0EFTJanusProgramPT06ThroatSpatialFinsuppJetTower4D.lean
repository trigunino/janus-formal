import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteOrderUniformization
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D

/-!
# Genuine spatial multi-index jet tower on the throat

This gate replaces the finite order-two index presentation by genuine
three-direction multi-indices `Fin 3 →₀ Nat`.  It supplies finite truncated
index types, truncation maps and commuting formal total derivatives at every
order, in particular through the orders zero to four needed by the local T06
Euler calculation.

No polynomial local-functional carrier, Euler operator, horizontal complex or
terminal T06 classification is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusFiniteOrderUniformization

universe u v

/-- A genuine spatial multi-index in the three throat directions. -/
abbrev ThroatSpatialMultiIndex := Fin 3 →₀ Nat

/-- Total order of a spatial throat multi-index. -/
def throatSpatialMultiIndexOrder (index : ThroatSpatialMultiIndex) : Nat :=
  index.degree

@[simp] theorem throatSpatialMultiIndexOrder_zero :
    throatSpatialMultiIndexOrder (0 : ThroatSpatialMultiIndex) = 0 := by
  simp [throatSpatialMultiIndexOrder]

@[simp] theorem throatSpatialMultiIndexOrder_single
    (direction : Fin 3) (exponent : Nat) :
    throatSpatialMultiIndexOrder (Finsupp.single direction exponent) =
      exponent := by
  simp [throatSpatialMultiIndexOrder]

theorem throatSpatialMultiIndexOrder_add
    (first second : ThroatSpatialMultiIndex) :
    throatSpatialMultiIndexOrder (first + second) =
      throatSpatialMultiIndexOrder first +
        throatSpatialMultiIndexOrder second := by
  simp [throatSpatialMultiIndexOrder]

/-- The unit multi-index in one throat direction. -/
def throatSpatialCoordinateMultiIndex
    (direction : Fin 3) : ThroatSpatialMultiIndex :=
  Finsupp.single direction 1

@[simp] theorem throatSpatialMultiIndexOrder_coordinateMultiIndex
    (direction : Fin 3) :
    throatSpatialMultiIndexOrder
        (throatSpatialCoordinateMultiIndex direction) = 1 := by
  simp [throatSpatialCoordinateMultiIndex]

theorem throatSpatialMultiIndexOrder_add_coordinateMultiIndex
    (index : ThroatSpatialMultiIndex) (direction : Fin 3) :
    throatSpatialMultiIndexOrder
        (index + throatSpatialCoordinateMultiIndex direction) =
      throatSpatialMultiIndexOrder index + 1 := by
  rw [throatSpatialMultiIndexOrder_add,
    throatSpatialMultiIndexOrder_coordinateMultiIndex]

/-- Spatial throat multi-indices of total order at most `order`. -/
abbrev ThroatSpatialTruncatedIndex (order : Nat) :=
  {index : ThroatSpatialMultiIndex //
    throatSpatialMultiIndexOrder index ≤ order}

instance throatSpatialTruncatedIndexDecidableEq (order : Nat) :
    DecidableEq (ThroatSpatialTruncatedIndex order) :=
  inferInstance

noncomputable instance throatSpatialTruncatedIndexFintype (order : Nat) :
    Fintype (ThroatSpatialTruncatedIndex order) :=
  (Finsupp.finite_of_degree_le (σ := Fin 3) order).fintype

/-- Coefficients of all genuine spatial multi-indices through `order`. -/
abbrev TruncatedThroatSpatialMultiindexJet
    (Fiber : Type v) (order : Nat) : Type v :=
  ThroatSpatialTruncatedIndex order → Fiber

abbrev ThroatSpatialMultiindexJet0 (Fiber : Type v) :=
  TruncatedThroatSpatialMultiindexJet Fiber 0

abbrev ThroatSpatialMultiindexJet1 (Fiber : Type v) :=
  TruncatedThroatSpatialMultiindexJet Fiber 1

abbrev ThroatSpatialMultiindexJet2 (Fiber : Type v) :=
  TruncatedThroatSpatialMultiindexJet Fiber 2

abbrev ThroatSpatialMultiindexJet3 (Fiber : Type v) :=
  TruncatedThroatSpatialMultiindexJet Fiber 3

abbrev ThroatSpatialMultiindexJet4 (Fiber : Type v) :=
  TruncatedThroatSpatialMultiindexJet Fiber 4

/-- Restrict a higher-order spatial jet to a lower order. -/
def truncateThroatSpatialMultiindexJet
    {Fiber : Type v} {lower higher : Nat}
    (hOrder : lower ≤ higher) :
    TruncatedThroatSpatialMultiindexJet Fiber higher →
      TruncatedThroatSpatialMultiindexJet Fiber lower :=
  fun jet index => jet ⟨index.1, index.2.trans hOrder⟩

/-- Linear form of spatial jet truncation. -/
def truncateThroatSpatialMultiindexJetLinear
    {Fiber : Type v} [AddCommMonoid Fiber] [Module Real Fiber]
    {lower higher : Nat} (hOrder : lower ≤ higher) :
    TruncatedThroatSpatialMultiindexJet Fiber higher →ₗ[Real]
      TruncatedThroatSpatialMultiindexJet Fiber lower where
  toFun := truncateThroatSpatialMultiindexJet hOrder
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A supplied genuine spatial multi-index extraction from sections. -/
structure ThroatSpatialMultiindexJetExtraction
    (SectionSpace : Type u) (Fiber : Type v) where
  coefficient : SectionSpace → ThroatSpatialMultiIndex → Fiber

/-- Finite truncation of a supplied spatial multi-index extraction. -/
def ThroatSpatialMultiindexJetExtraction.truncatedJet
    {SectionSpace : Type u} {Fiber : Type v}
    (extraction : ThroatSpatialMultiindexJetExtraction SectionSpace Fiber)
    (order : Nat) (sectionValue : SectionSpace) :
    TruncatedThroatSpatialMultiindexJet Fiber order :=
  fun index => extraction.coefficient sectionValue index.1

@[simp] theorem truncateThroatSpatialMultiindexJet_truncatedJet
    {SectionSpace : Type u} {Fiber : Type v}
    (extraction : ThroatSpatialMultiindexJetExtraction SectionSpace Fiber)
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (sectionValue : SectionSpace) :
    truncateThroatSpatialMultiindexJet hOrder
        (extraction.truncatedJet higher sectionValue) =
      extraction.truncatedJet lower sectionValue := by
  rfl

/-- Every supplied spatial multi-index extraction forms a genuine jet tower. -/
def ThroatSpatialMultiindexJetExtraction.jetTower
    {SectionSpace : Type u} {Fiber : Type v}
    (extraction : ThroatSpatialMultiindexJetExtraction SectionSpace Fiber) :
    JetTower SectionSpace where
  Jet := TruncatedThroatSpatialMultiindexJet Fiber
  jet := extraction.truncatedJet
  truncate := truncateThroatSpatialMultiindexJet
  truncateJet := by
    intro lower higher hOrder sectionValue
    exact truncateThroatSpatialMultiindexJet_truncatedJet
      extraction hOrder sectionValue

/-- Formal total derivative in one throat direction. -/
def throatSpatialTotalDerivative
    {Fiber : Type v} {order : Nat} (direction : Fin 3) :
    TruncatedThroatSpatialMultiindexJet Fiber (order + 1) →
      TruncatedThroatSpatialMultiindexJet Fiber order :=
  fun jet index =>
    jet ⟨index.1 + throatSpatialCoordinateMultiIndex direction, by
      rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
      omega⟩

/-- Linear form of the formal spatial total derivative. -/
def throatSpatialTotalDerivativeLinear
    {Fiber : Type v} [AddCommMonoid Fiber] [Module Real Fiber]
    {order : Nat} (direction : Fin 3) :
    TruncatedThroatSpatialMultiindexJet Fiber (order + 1) →ₗ[Real]
      TruncatedThroatSpatialMultiindexJet Fiber order where
  toFun := throatSpatialTotalDerivative direction
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Formal total derivatives commute at every finite order. -/
theorem throatSpatialTotalDerivative_comm
    {Fiber : Type v} {order : Nat}
    (first second : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber ((order + 1) + 1)) :
    throatSpatialTotalDerivative first
        (throatSpatialTotalDerivative second jet) =
      throatSpatialTotalDerivative second
        (throatSpatialTotalDerivative first jet) := by
  funext index
  apply congrArg jet
  apply Subtype.ext
  change
    (index.1 + throatSpatialCoordinateMultiIndex first) +
        throatSpatialCoordinateMultiIndex second =
      (index.1 + throatSpatialCoordinateMultiIndex second) +
        throatSpatialCoordinateMultiIndex first
  ac_rfl

end
end P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
end JanusFormal
