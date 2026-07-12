import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteOrderUniformization

set_option autoImplicit false

universe u v

/-- A tower of finite jets with truncation maps. -/
structure JetTower (SectionSpace : Type u) where
  Jet : ℕ → Type v
  jet : ∀ order, SectionSpace → Jet order
  truncate :
    ∀ {lower higher},
      lower ≤ higher → Jet higher → Jet lower
  truncateJet :
    ∀ {lower higher}
      (hOrder : lower ≤ higher)
      (sectionValue : SectionSpace),
      truncate hOrder (jet higher sectionValue) =
        jet lower sectionValue

/-- One finite-order factorization of an operator. -/
structure FiniteOrderFactorization
    {SectionSpace : Type u}
    (tower : JetTower SectionSpace)
    (Target : Type v) where
  order : ℕ
  operator : SectionSpace → Target
  evaluator : tower.Jet order → Target
  factorization :
    ∀ sectionValue,
      operator sectionValue =
        evaluator (tower.jet order sectionValue)

/-- Lift an evaluator to any higher jet order by truncation. -/
def liftEvaluator
    {SectionSpace : Type u}
    {Target : Type v}
    (tower : JetTower SectionSpace)
    (factorization : FiniteOrderFactorization tower Target)
    (higher : ℕ)
    (hOrder : factorization.order ≤ higher) :
    tower.Jet higher → Target :=
  fun higherJet =>
    factorization.evaluator
      (tower.truncate hOrder higherJet)

/-- Raising the jet order does not change the represented operator. -/
theorem lifted_evaluator_factorization
    {SectionSpace : Type u}
    {Target : Type v}
    (tower : JetTower SectionSpace)
    (factorization : FiniteOrderFactorization tower Target)
    (higher : ℕ)
    (hOrder : factorization.order ≤ higher)
    (sectionValue : SectionSpace) :
    factorization.operator sectionValue =
      liftEvaluator tower factorization higher hOrder
        (tower.jet higher sectionValue) := by
  unfold liftEvaluator
  rw [tower.truncateJet]
  exact factorization.factorization sectionValue

/-- Sum of finitely many local orders, used as a simple uniform bound. -/
def finiteCoverOrderBound (orders : List ℕ) : ℕ :=
  orders.sum

/-- Every member of a finite list is bounded by the sum of the list. -/
theorem member_le_finite_cover_order_bound
    (orders : List ℕ)
    (order : ℕ)
    (hMember : order ∈ orders) :
    order ≤ finiteCoverOrderBound orders := by
  unfold finiteCoverOrderBound
  induction orders with
  | nil => simp at hMember
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hMember
      simp only [List.sum_cons]
      rcases hMember with rfl | hTail
      · omega
      · have hBound := inductionHypothesis hTail
        omega

/-- A finite local-order atlas admits a common finite upper order. -/
theorem finite_local_orders_have_common_bound
    (orders : List ℕ) :
    ∃ globalOrder : ℕ,
      ∀ localOrder,
        localOrder ∈ orders → localOrder ≤ globalOrder := by
  exact ⟨finiteCoverOrderBound orders,
    member_le_finite_cover_order_bound orders⟩

/-- Local order assigned to a disconnected component. -/
def componentLocalOrder (component : ℕ) : ℕ :=
  component

/-- Locally finite order on every component does not imply one global bound. -/
theorem componentwise_finite_order_has_no_uniform_bound :
    Not (∃ globalOrder : ℕ,
      ∀ component : ℕ,
        componentLocalOrder component ≤ globalOrder) := by
  rintro ⟨globalOrder, hBound⟩
  have hContradiction := hBound (globalOrder + 1)
  unfold componentLocalOrder at hContradiction
  omega

/-- Data needed to pass from the local Peetre--Slovak statement to one uniform
finite order on a chosen family. -/
structure UniformOrderHypotheses where
  relevantJetRegionCovered : Prop
  finiteSubcoverChosen : Prop
  localOrdersRecorded : Prop
  truncationMapsConstructed : Prop
  overlapCompatibilityProved : Prop
  commonOrderChosen : Prop

/-- Uniformization closure. -/
def uniformOrderHypothesesClosed
    (s : UniformOrderHypotheses) : Prop :=
  s.relevantJetRegionCovered /\
  s.finiteSubcoverChosen /\
  s.localOrdersRecorded /\
  s.truncationMapsConstructed /\
  s.overlapCompatibilityProved /\
  s.commonOrderChosen

/-- Without a finite/bounded family hypothesis, local finite order is not a
global finite-order theorem. -/
theorem missing_finite_subcover_blocks_uniform_order
    (s : UniformOrderHypotheses)
    (hMissing : Not s.finiteSubcoverChosen) :
    Not (uniformOrderHypothesesClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.1

/--
Peetre--Slovak yields local factorization through finite jets. A single global
order follows on a region admitting finitely many such neighborhoods, after
raising every local evaluator to the common order and proving compatibility on
overlaps. Compactness of the base alone is insufficient when the local order
also varies over an unbounded configuration/jet space.
-/
structure JanusUniformOrderPhysicalStatus where
  backgroundNeighborhoodSpecified : Prop
  compactOrBoundedParameterRegionSpecified : Prop
  localPeetreSlovakOrdersDerived : Prop
  finiteSubcoverDerived : Prop
  commonOrderDerived : Prop
  overlapGluingProved : Prop
  globalFiniteJetEvaluatorConstructed : Prop


def janusUniformOrderPhysicalClosure
    (s : JanusUniformOrderPhysicalStatus) : Prop :=
  s.backgroundNeighborhoodSpecified /\
  s.compactOrBoundedParameterRegionSpecified /\
  s.localPeetreSlovakOrdersDerived /\
  s.finiteSubcoverDerived /\
  s.commonOrderDerived /\
  s.overlapGluingProved /\
  s.globalFiniteJetEvaluatorConstructed

end P0EFTJanusFiniteOrderUniformization
end JanusFormal
