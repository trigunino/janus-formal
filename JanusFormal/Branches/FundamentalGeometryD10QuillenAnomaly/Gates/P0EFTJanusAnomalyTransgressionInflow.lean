import Mathlib

namespace JanusFormal
namespace P0EFTJanusAnomalyTransgressionInflow

set_option autoImplicit false

/-- Boundary anomaly together with a bulk invertible-theory inflow class. -/
structure RelativeAnomalyClass (A : Type*) [AddCommGroup A] where
  boundary : A
  bulkInflow : A

def totalRelativeAnomaly {A : Type*} [AddCommGroup A]
    (a : RelativeAnomalyClass A) : A :=
  a.boundary + a.bulkInflow

def anomalyCancelled {A : Type*} [AddCommGroup A]
    (a : RelativeAnomalyClass A) : Prop :=
  totalRelativeAnomaly a = 0

/-- Canonical opposite bulk class at the level of additive anomaly classes. -/
def oppositeInflow {A : Type*} [AddCommGroup A]
    (boundary : A) : RelativeAnomalyClass A :=
  { boundary := boundary, bulkInflow := -boundary }

@[simp] theorem opposite_inflow_cancels
    {A : Type*} [AddCommGroup A] (boundary : A) :
    anomalyCancelled (oppositeInflow boundary) := by
  simp [anomalyCancelled, totalRelativeAnomaly, oppositeInflow]

/-- Transgression transports additive bulk classes to additive boundary classes. -/
def transgressedBoundaryClass
    {Bulk Boundary : Type*} [AddCommGroup Bulk] [AddCommGroup Boundary]
    (transgression : Bulk →+ Boundary) (bulk : Bulk) : Boundary :=
  transgression bulk

theorem transgression_preserves_stacking
    {Bulk Boundary : Type*} [AddCommGroup Bulk] [AddCommGroup Boundary]
    (transgression : Bulk →+ Boundary) (first second : Bulk) :
    transgressedBoundaryClass transgression (first + second) =
      transgressedBoundaryClass transgression first +
        transgressedBoundaryClass transgression second := by
  exact transgression.map_add first second

theorem transgression_of_opposite_is_opposite
    {Bulk Boundary : Type*} [AddCommGroup Bulk] [AddCommGroup Boundary]
    (transgression : Bulk →+ Boundary) (bulk : Bulk) :
    transgressedBoundaryClass transgression (-bulk) =
      -transgressedBoundaryClass transgression bulk := by
  exact transgression.map_neg bulk

/-- Topological interface required before analytic eta/Quillen representatives are compared. -/
structure TransgressionInflowStatus where
  bulkInvertibleTheoryClassConstructed : Prop
  boundaryAnomalyClassConstructed : Prop
  transgressionMapConstructed : Prop
  transgressionNaturalityProved : Prop
  boundaryClassMatchedToTransgression : Prop
  oppositeInflowCancellationProved : Prop
  differentialRepresentativeMatched : Prop
  globalHolonomyMatched : Prop
  localityCompatibleTrivializationConstructed : Prop

def transgressionInflowClosed (s : TransgressionInflowStatus) : Prop :=
  s.bulkInvertibleTheoryClassConstructed ∧
  s.boundaryAnomalyClassConstructed ∧ s.transgressionMapConstructed ∧
  s.transgressionNaturalityProved ∧
  s.boundaryClassMatchedToTransgression ∧
  s.oppositeInflowCancellationProved ∧
  s.differentialRepresentativeMatched ∧ s.globalHolonomyMatched ∧
  s.localityCompatibleTrivializationConstructed

theorem class_cancellation_without_holonomy_match_is_incomplete
    (s : TransgressionInflowStatus) (h : Not s.globalHolonomyMatched) :
    Not (transgressionInflowClosed s) := by
  intro hs
  exact h hs.2.2.2.2.2.2.2.1

end P0EFTJanusAnomalyTransgressionInflow
end JanusFormal
