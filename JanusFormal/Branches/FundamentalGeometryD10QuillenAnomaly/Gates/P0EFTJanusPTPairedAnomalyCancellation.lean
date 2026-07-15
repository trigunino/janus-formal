import Mathlib

namespace JanusFormal
namespace P0EFTJanusPTPairedAnomalyCancellation

set_option autoImplicit false

/-- Additive anomaly carried by the two PT-related sectors. -/
structure PTPairedAnomaly (A : Type*) [AddCommGroup A] where
  positiveSector : A
  negativeSector : A

/-- Total anomaly of the paired theory. -/
def totalAnomaly {A : Type*} [AddCommGroup A]
    (a : PTPairedAnomaly A) : A :=
  a.positiveSector + a.negativeSector

/-- PT conjugation reverses the additive anomaly class. -/
def ptConjugatePair {A : Type*} [AddCommGroup A]
    (anomaly : A) : PTPairedAnomaly A :=
  { positiveSector := anomaly
    negativeSector := -anomaly }

@[simp] theorem pt_conjugate_pair_cancels
    {A : Type*} [AddCommGroup A] (anomaly : A) :
    totalAnomaly (ptConjugatePair anomaly) = 0 := by
  simp [totalAnomaly, ptConjugatePair]

/-- A bulk inflow class cancels the boundary anomaly exactly when their sum vanishes. -/
def inflowCancels {A : Type*} [AddCommGroup A]
    (boundaryAnomaly bulkInflow : A) : Prop :=
  boundaryAnomaly + bulkInflow = 0

theorem canonical_opposite_inflow_cancels
    {A : Type*} [AddCommGroup A] (boundaryAnomaly : A) :
    inflowCancels boundaryAnomaly (-boundaryAnomaly) := by
  simp [inflowCancels]

theorem cancelling_inflow_is_unique
    {A : Type*} [AddCommGroup A]
    {boundaryAnomaly bulkInflow : A}
    (h : inflowCancels boundaryAnomaly bulkInflow) :
    bulkInflow = -boundaryAnomaly := by
  apply eq_neg_of_add_eq_zero_left
  simpa [inflowCancels, add_comm] using h

/-- Closure ledger separating class cancellation from the construction of a scalar partition function. -/
structure PTPairedPartitionStatus where
  sectorAnomalyClassesConstructed : Prop
  ptActionOnAnomalyProved : Prop
  totalAnomalyClassVanishingProved : Prop
  determinantGerbeTrivializationConstructed : Prop
  partitionSectionGaugeInvariant : Prop
  finiteLocalTermsFixed : Prop

def scalarPartitionFunctionClosed (s : PTPairedPartitionStatus) : Prop :=
  s.sectorAnomalyClassesConstructed /\
  s.ptActionOnAnomalyProved /\
  s.totalAnomalyClassVanishingProved /\
  s.determinantGerbeTrivializationConstructed /\
  s.partitionSectionGaugeInvariant /\
  s.finiteLocalTermsFixed

/-- Vanishing of the total class alone does not construct a trivialization. -/
theorem missing_trivialization_blocks_scalar_partition
    (s : PTPairedPartitionStatus)
    (hMissing : Not s.determinantGerbeTrivializationConstructed) :
    Not (scalarPartitionFunctionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.1

/-- An anomaly-free section still needs finite local data to define the final scalar theory. -/
theorem missing_finite_terms_blocks_scalar_partition
    (s : PTPairedPartitionStatus)
    (hMissing : Not s.finiteLocalTermsFixed) :
    Not (scalarPartitionFunctionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2

end P0EFTJanusPTPairedAnomalyCancellation
end JanusFormal
