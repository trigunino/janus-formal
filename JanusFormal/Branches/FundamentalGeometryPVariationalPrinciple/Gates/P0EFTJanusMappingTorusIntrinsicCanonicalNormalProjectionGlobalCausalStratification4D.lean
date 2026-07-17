import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftLocalRegularity4D

/-!
# Direct causal stratification from the canonical global normal lift

This gate deliberately avoids packaging the dependent quadratic-form record:
the canonical metric square itself is enough to define and stratify the normal
total space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalCausalStratification4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuity4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftLocalRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)

def canonicalGlobalNormalSpacelikeStratum :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | 0 < canonicalGlobalNormalMetricSquare period hPeriod normal}

def canonicalGlobalNormalTimelikeStratum :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | canonicalGlobalNormalMetricSquare period hPeriod normal < 0}

def canonicalGlobalNormalNullStratum :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | canonicalGlobalNormalMetricSquare period hPeriod normal = 0}

def canonicalGlobalNormalNonNullStratum :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | canonicalGlobalNormalMetricSquare period hPeriod normal ≠ 0}

def canonicalGlobalNormalJointStratum :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  frontier (canonicalGlobalNormalNullStratum period hPeriod)

theorem canonicalGlobalNormalSpacelikeStratum_isOpen
    (hLocal : CanonicalGlobalNormalMetricSquareLocalRegularity
      period hPeriod) :
    IsOpen (canonicalGlobalNormalSpacelikeStratum period hPeriod) := by
  have hContinuous : Continuous
      (canonicalGlobalNormalMetricSquare period hPeriod) := by
    exact (canonicalGlobalOrthogonalNormalLift_continuous_metric_square
      period hPeriod hLocal).congr fun normal => by
        rfl
  simpa [canonicalGlobalNormalSpacelikeStratum] using
    (isOpen_lt continuous_const hContinuous)

theorem canonicalGlobalNormalTimelikeStratum_isOpen
    (hLocal : CanonicalGlobalNormalMetricSquareLocalRegularity
      period hPeriod) :
    IsOpen (canonicalGlobalNormalTimelikeStratum period hPeriod) := by
  have hContinuous : Continuous
      (canonicalGlobalNormalMetricSquare period hPeriod) := by
    exact (canonicalGlobalOrthogonalNormalLift_continuous_metric_square
      period hPeriod hLocal).congr fun normal => by
        rfl
  simpa [canonicalGlobalNormalTimelikeStratum] using
    (isOpen_lt hContinuous continuous_const)

theorem canonicalGlobalNormalNullStratum_isClosed
    (hLocal : CanonicalGlobalNormalMetricSquareLocalRegularity
      period hPeriod) :
    IsClosed (canonicalGlobalNormalNullStratum period hPeriod) := by
  have hContinuous : Continuous
      (canonicalGlobalNormalMetricSquare period hPeriod) := by
    exact (canonicalGlobalOrthogonalNormalLift_continuous_metric_square
      period hPeriod hLocal).congr fun normal => by
        rfl
  simpa [canonicalGlobalNormalNullStratum] using
    (isClosed_eq hContinuous continuous_const)

theorem canonicalGlobalNormalNonNullStratum_isOpen
    (hLocal : CanonicalGlobalNormalMetricSquareLocalRegularity
      period hPeriod) :
    IsOpen (canonicalGlobalNormalNonNullStratum period hPeriod) := by
  rw [show canonicalGlobalNormalNonNullStratum period hPeriod =
      (canonicalGlobalNormalNullStratum period hPeriod)ᶜ by
    ext normal
    simp [canonicalGlobalNormalNonNullStratum,
      canonicalGlobalNormalNullStratum]]
  exact (canonicalGlobalNormalNullStratum_isClosed
    period hPeriod hLocal).isOpen_compl

theorem canonicalGlobalNormalJointStratum_isClosed :
    IsClosed (canonicalGlobalNormalJointStratum period hPeriod) :=
  isClosed_frontier

theorem canonicalGlobalNormalJointStratum_subset_null
    (hLocal : CanonicalGlobalNormalMetricSquareLocalRegularity
      period hPeriod) :
    canonicalGlobalNormalJointStratum period hPeriod ⊆
      canonicalGlobalNormalNullStratum period hPeriod :=
  (canonicalGlobalNormalNullStratum_isClosed
    period hPeriod hLocal).frontier_subset

theorem canonicalGlobalNormalCausalStrata_cover :
    canonicalGlobalNormalSpacelikeStratum period hPeriod ∪
        canonicalGlobalNormalTimelikeStratum period hPeriod ∪
        canonicalGlobalNormalNullStratum period hPeriod = univ := by
  ext normal
  simp only [canonicalGlobalNormalSpacelikeStratum,
    canonicalGlobalNormalTimelikeStratum, canonicalGlobalNormalNullStratum,
    mem_union, mem_setOf_eq, mem_univ, iff_true]
  rcases lt_trichotomy
      (canonicalGlobalNormalMetricSquare period hPeriod normal) 0 with
    hNeg | hZero | hPos
  · exact Or.inl (Or.inr hNeg)
  · exact Or.inr hZero
  · exact Or.inl (Or.inl hPos)

theorem canonicalGlobalDifferentialNormalCausalStratification
    (hLocal : CanonicalGlobalNormalMetricSquareLocalRegularity
      period hPeriod) :
    IsOpen (canonicalGlobalNormalSpacelikeStratum period hPeriod) ∧
      IsOpen (canonicalGlobalNormalTimelikeStratum period hPeriod) ∧
      IsClosed (canonicalGlobalNormalNullStratum period hPeriod) ∧
      IsOpen (canonicalGlobalNormalNonNullStratum period hPeriod) ∧
      IsClosed (canonicalGlobalNormalJointStratum period hPeriod) ∧
      canonicalGlobalNormalJointStratum period hPeriod ⊆
        canonicalGlobalNormalNullStratum period hPeriod ∧
      canonicalGlobalNormalSpacelikeStratum period hPeriod ∪
          canonicalGlobalNormalTimelikeStratum period hPeriod ∪
          canonicalGlobalNormalNullStratum period hPeriod = univ := by
  exact ⟨canonicalGlobalNormalSpacelikeStratum_isOpen period hPeriod hLocal,
    canonicalGlobalNormalTimelikeStratum_isOpen period hPeriod hLocal,
    canonicalGlobalNormalNullStratum_isClosed period hPeriod hLocal,
    canonicalGlobalNormalNonNullStratum_isOpen period hPeriod hLocal,
    canonicalGlobalNormalJointStratum_isClosed period hPeriod,
    canonicalGlobalNormalJointStratum_subset_null period hPeriod hLocal,
    canonicalGlobalNormalCausalStrata_cover period hPeriod⟩

/-- The explicit latitude-normal equivalence discharges the sole local
regularity hypothesis of the global causal stratification. -/
def canonicalGlobalDifferentialNormalCausalStratification_unconditional :=
  canonicalGlobalDifferentialNormalCausalStratification period hPeriod
    (canonicalGlobalNormalMetricSquareLocalRegularity period hPeriod)

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalCausalStratification4D
end JanusFormal
