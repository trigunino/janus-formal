import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableRootGluing4D

/-!
# Regularity frontier for the global positive diagonalizable root

The global selector is already independent of its diagonalization.  The
remaining analytic question is whether roots of nearby positive
diagonalizable matrices stay in the local inverse-function branch.

This gate isolates that statement exactly and proves it is equivalent to
continuity of the global selector.  Once it holds, differentiability within
the locus and the inverse-Sylvester derivative follow automatically.  Thus no
extra differentiability or derivative hypothesis is left after continuity.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableGlobalRootRegularity4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableSylvesterInverse4D
open P0EFTJanusPositiveDiagonalizableLocalRootBranch4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module Real Matrix4 :=
  matrix4NormedSpace.toModule

/-- Ambient partial representative of the global selector.  Values outside
the positive diagonalizable locus are irrelevant and are set to zero. -/
def positiveDiagonalizableGlobalRootOn (target : Matrix4) : Matrix4 := by
  classical
  exact if hTarget : target ∈ positiveDiagonalizableLocus then
    positiveDiagonalizableGlobalRoot ⟨target, hTarget⟩
  else
    0

@[simp] theorem positiveDiagonalizableGlobalRootOn_of_mem
    (target : Matrix4) (hTarget : target ∈ positiveDiagonalizableLocus) :
    positiveDiagonalizableGlobalRootOn target =
      positiveDiagonalizableGlobalRoot ⟨target, hTarget⟩ := by
  simp [positiveDiagonalizableGlobalRootOn, hTarget]

theorem positiveDiagonalizable_target_mem
    (data : PositiveDiagonalizableRelativeMatrix) :
    data.target ∈ positiveDiagonalizableLocus :=
  ⟨data, rfl⟩

/-- The ambient representative agrees with every presentation at its base. -/
theorem positiveDiagonalizableGlobalRootOn_at_presentation
    (data : PositiveDiagonalizableRelativeMatrix) :
    positiveDiagonalizableGlobalRootOn data.target =
      positiveSimilarityRoot data := by
  rw [positiveDiagonalizableGlobalRootOn_of_mem data.target
    (positiveDiagonalizable_target_mem data)]
  exact positiveDiagonalizableGlobalRoot_eq_of_presentation
    ⟨data.target, positiveDiagonalizable_target_mem data⟩ data rfl

/-- On its genuine domain, the ambient representative squares to its input. -/
theorem positiveDiagonalizableGlobalRootOn_square
    (target : Matrix4) (hTarget : target ∈ positiveDiagonalizableLocus) :
    matrixSquare (positiveDiagonalizableGlobalRootOn target) = target := by
  rw [positiveDiagonalizableGlobalRootOn_of_mem target hTarget]
  simpa [matrixSquare] using
    positiveDiagonalizableGlobalRoot_square ⟨target, hTarget⟩

/-- Weakest local spectral-stability datum consumed by the IFT: on the
positive diagonalizable locus, the global selector eventually agrees with
the local branch based at the supplied presentation. -/
def PositiveDiagonalizableLocalIFTStable
    (data : PositiveDiagonalizableRelativeMatrix) : Prop :=
  ∀ᶠ target in 𝓝[positiveDiagonalizableLocus] data.target,
    positiveDiagonalizableGlobalRootOn target =
      positiveDiagonalizableLocalRootBranch data target

/-- Local stability is independent of the chosen diagonalization of a fixed
target. -/
theorem positiveDiagonalizableLocalIFTStable_iff_of_same_target
    (first second : PositiveDiagonalizableRelativeMatrix)
    (hTarget : first.target = second.target) :
    PositiveDiagonalizableLocalIFTStable first ↔
      PositiveDiagonalizableLocalIFTStable second := by
  have hGerm :
      ∀ᶠ target in 𝓝[positiveDiagonalizableLocus] first.target,
        positiveDiagonalizableLocalRootBranch first target =
          positiveDiagonalizableLocalRootBranch second target :=
    (eventually_positiveDiagonalizableLocalRootBranch_eq_of_same_target
      first second hTarget).filter_mono inf_le_left
  constructor
  · intro hFirst
    change ∀ᶠ target in 𝓝[positiveDiagonalizableLocus] second.target,
      positiveDiagonalizableGlobalRootOn target =
        positiveDiagonalizableLocalRootBranch second target
    rw [← hTarget]
    filter_upwards [hFirst, hGerm] with target hRoot hBranches
    exact hRoot.trans hBranches
  · intro hSecond
    change ∀ᶠ target in 𝓝[positiveDiagonalizableLocus] second.target,
      positiveDiagonalizableGlobalRootOn target =
        positiveDiagonalizableLocalRootBranch second target at hSecond
    rw [← hTarget] at hSecond
    filter_upwards [hSecond, hGerm] with target hRoot hBranches
    exact hRoot.trans hBranches.symm

/-- Exact local frontier: continuity within the locus is equivalent to
eventual membership in the unique IFT branch. -/
theorem positiveDiagonalizableLocalIFTStable_iff_continuousWithinAt
    (data : PositiveDiagonalizableRelativeMatrix) :
    PositiveDiagonalizableLocalIFTStable data ↔
      ContinuousWithinAt positiveDiagonalizableGlobalRootOn
        positiveDiagonalizableLocus data.target := by
  constructor
  · intro hStable
    have hBranch :
        ContinuousWithinAt (positiveDiagonalizableLocalRootBranch data)
          positiveDiagonalizableLocus data.target :=
      (positiveDiagonalizableLocalRootBranch_hasStrictFDerivAt data).continuousAt.continuousWithinAt
    have hBase :
        positiveDiagonalizableGlobalRootOn data.target =
          positiveDiagonalizableLocalRootBranch data data.target := by
      rw [positiveDiagonalizableGlobalRootOn_at_presentation,
        positiveDiagonalizableLocalRootBranch_at_target]
    exact hBranch.congr_of_eventuallyEq hStable hBase
  · intro hContinuous
    have hLeft :
        ∀ᶠ root in 𝓝 (positiveSimilarityRoot data),
          positiveDiagonalizableLocalRootBranch data (matrixSquare root) = root := by
      simpa [positiveDiagonalizableLocalRootBranch] using
        eventually_localRootBranch_matrixSquare
          (positiveSimilarityRoot data)
          (positiveDiagonalizableSylvesterEquivWitness data)
    have hTendsto :
        Tendsto positiveDiagonalizableGlobalRootOn
          (𝓝[positiveDiagonalizableLocus] data.target)
          (𝓝 (positiveSimilarityRoot data)) := by
      rw [← positiveDiagonalizableGlobalRootOn_at_presentation data]
      exact hContinuous
    have hPulled := hTendsto.eventually hLeft
    filter_upwards [hPulled, self_mem_nhdsWithin] with target hLocal hTarget
    calc
      positiveDiagonalizableGlobalRootOn target =
          positiveDiagonalizableLocalRootBranch data
            (matrixSquare (positiveDiagonalizableGlobalRootOn target)) :=
        hLocal.symm
      _ = positiveDiagonalizableLocalRootBranch data target := by
        rw [positiveDiagonalizableGlobalRootOn_square target hTarget]

/-- Local continuity already forces the full inverse-Sylvester derivative
within the positive diagonalizable locus. -/
theorem positiveDiagonalizableGlobalRootOn_hasFDerivWithinAt
    (data : PositiveDiagonalizableRelativeMatrix)
    (hContinuous :
      ContinuousWithinAt positiveDiagonalizableGlobalRootOn
        positiveDiagonalizableLocus data.target) :
    HasFDerivWithinAt positiveDiagonalizableGlobalRootOn
      (positiveDiagonalizableSylvesterInverseCLM data)
      positiveDiagonalizableLocus data.target := by
  have hStable :=
    (positiveDiagonalizableLocalIFTStable_iff_continuousWithinAt data).2 hContinuous
  have hBranch :
      HasFDerivWithinAt (positiveDiagonalizableLocalRootBranch data)
        (positiveDiagonalizableSylvesterInverseCLM data)
        positiveDiagonalizableLocus data.target :=
    (positiveDiagonalizableLocalRootBranch_hasStrictFDerivAt data).hasFDerivAt.hasFDerivWithinAt
  have hBase :
      positiveDiagonalizableGlobalRootOn data.target =
        positiveDiagonalizableLocalRootBranch data data.target := by
    rw [positiveDiagonalizableGlobalRootOn_at_presentation,
      positiveDiagonalizableLocalRootBranch_at_target]
  exact hBranch.congr_of_eventuallyEq hStable hBase

/-- The inverse-Sylvester derivative is itself presentation-independent. -/
theorem positiveDiagonalizableSylvesterInverseCLM_eq_of_same_target
    (first second : PositiveDiagonalizableRelativeMatrix)
    (hTarget : first.target = second.target) :
    positiveDiagonalizableSylvesterInverseCLM first =
      positiveDiagonalizableSylvesterInverseCLM second := by
  have hRoot : positiveSimilarityRoot first = positiveSimilarityRoot second :=
    positiveSimilarityRoot_eq_of_same_target first second hTarget
  apply ContinuousLinearMap.ext
  intro variation
  apply (positiveDiagonalizable_sylvester_bijective first).1
  rw [positiveDiagonalizableSylvesterInverseCLM_apply,
    positiveDiagonalizableSylvesterInverse_right]
  rw [positiveDiagonalizableSylvesterInverseCLM_apply, hRoot]
  exact (positiveDiagonalizableSylvesterInverse_right second variation).symm

/-- Global form of the one missing regularity datum. -/
def PositiveDiagonalizableGlobalRootLocallyStable : Prop :=
  ∀ data : PositiveDiagonalizableRelativeMatrix,
    PositiveDiagonalizableLocalIFTStable data

/-- Atlas-free global criterion: local IFT stability at every presentation is
equivalent to continuity of the ambient selector on its genuine locus. -/
theorem positiveDiagonalizableGlobalRootLocallyStable_iff_continuousOn :
    PositiveDiagonalizableGlobalRootLocallyStable ↔
      ContinuousOn positiveDiagonalizableGlobalRootOn
        positiveDiagonalizableLocus := by
  constructor
  · intro hStable target hTarget
    obtain ⟨data, hData⟩ := hTarget
    rw [← hData]
    exact (positiveDiagonalizableLocalIFTStable_iff_continuousWithinAt data).1
      (hStable data)
  · intro hContinuous data
    exact (positiveDiagonalizableLocalIFTStable_iff_continuousWithinAt data).2
      (hContinuous data.target (positiveDiagonalizable_target_mem data))

/-- Restricting the ambient representative recovers the original subtype
selector exactly. -/
theorem positiveDiagonalizableGlobalRootOn_restrict :
    positiveDiagonalizableLocus.restrict positiveDiagonalizableGlobalRootOn =
      positiveDiagonalizableGlobalRoot := by
  funext target
  exact positiveDiagonalizableGlobalRootOn_of_mem target.1 target.2

/-- Continuity of the original subtype selector is exactly continuity of its
ambient representative on the locus. -/
theorem positiveDiagonalizableGlobalRoot_continuous_iff_continuousOn :
    Continuous positiveDiagonalizableGlobalRoot ↔
      ContinuousOn positiveDiagonalizableGlobalRootOn
        positiveDiagonalizableLocus := by
  rw [continuousOn_iff_continuous_restrict,
    positiveDiagonalizableGlobalRootOn_restrict]

/-- Complete regularity frontier for the actual global selector. -/
theorem positiveDiagonalizableGlobalRoot_continuous_iff_localIFTStable :
    Continuous positiveDiagonalizableGlobalRoot ↔
      PositiveDiagonalizableGlobalRootLocallyStable :=
  positiveDiagonalizableGlobalRoot_continuous_iff_continuousOn.trans
    positiveDiagonalizableGlobalRootLocallyStable_iff_continuousOn.symm

/-- Therefore a proof of global continuity automatically supplies the
inverse-Sylvester derivative at every presentation, within the locus. -/
theorem positiveDiagonalizableGlobalRootOn_hasFDerivWithinAt_of_continuous
    (hContinuous : Continuous positiveDiagonalizableGlobalRoot)
    (data : PositiveDiagonalizableRelativeMatrix) :
    HasFDerivWithinAt positiveDiagonalizableGlobalRootOn
      (positiveDiagonalizableSylvesterInverseCLM data)
      positiveDiagonalizableLocus data.target :=
  positiveDiagonalizableGlobalRootOn_hasFDerivWithinAt data
    ((positiveDiagonalizableGlobalRoot_continuous_iff_continuousOn.1 hContinuous)
      data.target (positiveDiagonalizable_target_mem data))

end

end P0EFTJanusPositiveDiagonalizableGlobalRootRegularity4D
end JanusFormal
