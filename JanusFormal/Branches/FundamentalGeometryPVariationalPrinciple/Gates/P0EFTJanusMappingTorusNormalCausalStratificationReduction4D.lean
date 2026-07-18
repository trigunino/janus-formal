import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusDifferentialNormalZeroNonzeroStratification

/-!
# Causal stratification of the differential normal bundle

This gate isolates the exact remaining geometric input: a continuous
fiberwise quadratic form on the already constructed differential normal
bundle.  Such a form canonically produces the spacelike, timelike, null and
joint strata, with the expected topology and scaling laws.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusNormalCausalStratificationReduction4D

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

/-- A continuous intrinsic quadratic form on the differential normal line.
The scaling law is stated directly on each dependent fiber. -/
structure ContinuousDifferentialNormalQuadraticForm where
  value : DifferentialNormalTotalSpace period hPeriod → Real
  continuous_value : Continuous value
  zero_section : ∀ point, value ⟨point, 0⟩ = 0
  map_smul : ∀ (point) (scalar : Real)
      (normal : DifferentialNormalFiber period hPeriod point),
    value ⟨point, scalar • normal⟩ = scalar ^ 2 * value ⟨point, normal⟩

def normalSpacelikeStratum
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | 0 < form.value normal}

def normalTimelikeStratum
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | form.value normal < 0}

def normalNullStratum
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | form.value normal = 0}

def normalNonNullStratum
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  {normal | form.value normal ≠ 0}

/-- Joint locus of the causal stratification: the frontier of the null locus. -/
def normalJointStratum
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    Set (DifferentialNormalTotalSpace period hPeriod) :=
  frontier (normalNullStratum period hPeriod form)

theorem normalSpacelikeStratum_isOpen
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    IsOpen (normalSpacelikeStratum period hPeriod form) := by
  simpa [normalSpacelikeStratum] using
    (isOpen_lt continuous_const form.continuous_value)

theorem normalTimelikeStratum_isOpen
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    IsOpen (normalTimelikeStratum period hPeriod form) := by
  simpa [normalTimelikeStratum] using
    (isOpen_lt form.continuous_value continuous_const)

theorem normalNullStratum_isClosed
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    IsClosed (normalNullStratum period hPeriod form) := by
  simpa [normalNullStratum] using
    (isClosed_eq form.continuous_value continuous_const)

theorem normalNonNullStratum_isOpen
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    IsOpen (normalNonNullStratum period hPeriod form) := by
  rw [show normalNonNullStratum period hPeriod form =
      (normalNullStratum period hPeriod form)ᶜ by
    ext normal
    simp [normalNonNullStratum, normalNullStratum]]
  exact (normalNullStratum_isClosed period hPeriod form).isOpen_compl

theorem normalCausalStrata_pairwise_disjoint
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    Disjoint (normalSpacelikeStratum period hPeriod form)
        (normalTimelikeStratum period hPeriod form) ∧
      Disjoint (normalSpacelikeStratum period hPeriod form)
        (normalNullStratum period hPeriod form) ∧
      Disjoint (normalTimelikeStratum period hPeriod form)
        (normalNullStratum period hPeriod form) := by
  constructor
  · rw [Set.disjoint_left]
    intro normal hSpace hTime
    change 0 < form.value normal at hSpace
    change form.value normal < 0 at hTime
    exact (not_lt_of_ge (le_of_lt hSpace)) hTime
  · constructor
    · rw [Set.disjoint_left]
      intro normal hSpace hNull
      change 0 < form.value normal at hSpace
      change form.value normal = 0 at hNull
      exact (ne_of_gt hSpace) hNull
    · rw [Set.disjoint_left]
      intro normal hTime hNull
      change form.value normal < 0 at hTime
      change form.value normal = 0 at hNull
      exact (ne_of_lt hTime) hNull

theorem normalCausalStrata_cover
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    normalSpacelikeStratum period hPeriod form ∪
        normalTimelikeStratum period hPeriod form ∪
        normalNullStratum period hPeriod form = univ := by
  ext normal
  simp only [normalSpacelikeStratum, normalTimelikeStratum,
    normalNullStratum, mem_union, mem_setOf_eq, mem_univ, iff_true]
  rcases lt_trichotomy (form.value normal) 0 with hNeg | hZero | hPos
  · exact Or.inl (Or.inr hNeg)
  · exact Or.inr hZero
  · exact Or.inl (Or.inl hPos)

theorem normalZeroSection_subset_null
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    Set.range
        (Bundle.zeroSection Real
          (DifferentialNormalFiber period hPeriod)) ⊆
      normalNullStratum period hPeriod form := by
  rintro _ ⟨point, rfl⟩
  exact form.zero_section point

theorem normalNullStratum_smul
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod)
    (point : ThroatBase period hPeriod) (scalar : Real)
    (normal : DifferentialNormalFiber period hPeriod point)
    (hNull : ⟨point, normal⟩ ∈ normalNullStratum period hPeriod form) :
    ⟨point, scalar • normal⟩ ∈ normalNullStratum period hPeriod form := by
  rw [normalNullStratum, mem_setOf_eq, form.map_smul, hNull, mul_zero]

theorem normalSpacelikeStratum_smul_iff
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod)
    (point : ThroatBase period hPeriod) {scalar : Real} (hScalar : scalar ≠ 0)
    (normal : DifferentialNormalFiber period hPeriod point) :
    ⟨point, scalar • normal⟩ ∈ normalSpacelikeStratum period hPeriod form ↔
      ⟨point, normal⟩ ∈ normalSpacelikeStratum period hPeriod form := by
  change 0 < form.value ⟨point, scalar • normal⟩ ↔
    0 < form.value ⟨point, normal⟩
  rw [form.map_smul]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hScalar))

theorem normalTimelikeStratum_smul_iff
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod)
    (point : ThroatBase period hPeriod) {scalar : Real} (hScalar : scalar ≠ 0)
    (normal : DifferentialNormalFiber period hPeriod point) :
    ⟨point, scalar • normal⟩ ∈ normalTimelikeStratum period hPeriod form ↔
      ⟨point, normal⟩ ∈ normalTimelikeStratum period hPeriod form := by
  change form.value ⟨point, scalar • normal⟩ < 0 ↔
    form.value ⟨point, normal⟩ < 0
  rw [form.map_smul]
  constructor <;> intro h <;>
    nlinarith [sq_pos_of_ne_zero hScalar]

theorem normalJointStratum_isClosed
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    IsClosed (normalJointStratum period hPeriod form) :=
  isClosed_frontier

theorem normalJointStratum_subset_null
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    normalJointStratum period hPeriod form ⊆
      normalNullStratum period hPeriod form :=
  (normalNullStratum_isClosed period hPeriod form).frontier_subset

/-- Complete causal-stratification reduction.  Instantiating the continuous
quadratic form from a chosen spacetime metric closes the geometric frontier. -/
theorem normalCausalStratification_of_continuousQuadraticForm
    (form : ContinuousDifferentialNormalQuadraticForm period hPeriod) :
    IsOpen (normalSpacelikeStratum period hPeriod form) ∧
      IsOpen (normalTimelikeStratum period hPeriod form) ∧
      IsClosed (normalNullStratum period hPeriod form) ∧
      IsOpen (normalNonNullStratum period hPeriod form) ∧
      IsClosed (normalJointStratum period hPeriod form) ∧
      normalJointStratum period hPeriod form ⊆
        normalNullStratum period hPeriod form ∧
      normalSpacelikeStratum period hPeriod form ∪
          normalTimelikeStratum period hPeriod form ∪
          normalNullStratum period hPeriod form = univ :=
  ⟨normalSpacelikeStratum_isOpen period hPeriod form,
    normalTimelikeStratum_isOpen period hPeriod form,
    normalNullStratum_isClosed period hPeriod form,
    normalNonNullStratum_isOpen period hPeriod form,
    normalJointStratum_isClosed period hPeriod form,
    normalJointStratum_subset_null period hPeriod form,
    normalCausalStrata_cover period hPeriod form⟩

end

end P0EFTJanusMappingTorusNormalCausalStratificationReduction4D
end JanusFormal
