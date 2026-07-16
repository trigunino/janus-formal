import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMinkowskiRelativeRootBranch4D

/-!
# Explicit open domain for the Minkowski relative-root chart

The inverse-function root is promoted from an eventual statement to an
explicit open domain: the plus metric is invertible and its relative metric
lies in the target of the genuine square-map local homeomorphism at the
identity.  On this domain the selected root is continuous, squares exactly to
`gPlus⁻¹ * gMinus`, and is unique among roots in the matching chart source.

This remains the identity component chart, not a global principal or causal
Lorentzian square-root domain.
-/

namespace JanusFormal
namespace P0EFTJanusMinkowskiRelativeRootOpenDomain4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusMetricInverseRelativeRootFrechet
open P0EFTJanusMinkowskiRelativeRootBranch4D

abbrev Matrix4 := P0EFTJanusMinkowskiRelativeRootBranch4D.Matrix4
abbrev MetricPair := P0EFTJanusMinkowskiRelativeRootBranch4D.MetricPair

attribute [local instance]
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4AddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4TopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4Module
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairTopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairModule

/-- Target of the actual local square-map homeomorphism at the identity. -/
def identityRootTarget : Set Matrix4 :=
  (localSquareChart (1 : Matrix4) identitySylvesterWitness).target

/-- Corresponding root chart source. -/
def identityRootSource : Set Matrix4 :=
  (localSquareChart (1 : Matrix4) identitySylvesterWitness).source

theorem identityRootTarget_isOpen : IsOpen identityRootTarget :=
  (localSquareChart (1 : Matrix4) identitySylvesterWitness).open_target

theorem identityRootSource_isOpen : IsOpen identityRootSource :=
  (localSquareChart (1 : Matrix4) identitySylvesterWitness).open_source

theorem one_mem_identityRootTarget : (1 : Matrix4) ∈ identityRootTarget := by
  simpa [identityRootTarget, identity_matrixSquare] using
    square_mem_localSquareChart_target (1 : Matrix4) identitySylvesterWitness

/-- Open matrix-pair domain obtained by pulling the explicit root target back
through the genuine relative-metric map. -/
def minkowskiRelativeRootOpenDomain : Set MetricPair :=
  {input | IsUnit input.1} ∩ relativeMetricTarget ⁻¹' identityRootTarget

theorem invertiblePlusDomain_isOpen :
    IsOpen {input : MetricPair | IsUnit input.1} := by
  exact Units.isOpen.preimage continuous_fst

theorem relativeMetricTarget_continuousOn_invertiblePlus :
    ContinuousOn relativeMetricTarget {input : MetricPair | IsUnit input.1} := by
  intro input hInput
  exact (relativeMetricTarget_hasFDerivAt_frobenius input hInput).continuousAt.continuousWithinAt

theorem minkowskiRelativeRootOpenDomain_isOpen :
    IsOpen minkowskiRelativeRootOpenDomain := by
  exact relativeMetricTarget_continuousOn_invertiblePlus.isOpen_inter_preimage
    invertiblePlusDomain_isOpen identityRootTarget_isOpen

theorem minkowskiMetricPair_mem_openDomain :
    minkowskiMetricPair ∈ minkowskiRelativeRootOpenDomain := by
  refine ⟨minkowskiMetric_isUnit, ?_⟩
  simpa [minkowski_relativeMetricTarget] using one_mem_identityRootTarget

/-- Exact square identity at every point of the explicit open domain. -/
theorem minkowskiRelativeRootBranch_square_on_openDomain
    {input : MetricPair} (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    matrixSquare (minkowskiRelativeRootBranch input) =
      relativeMetricTarget input := by
  change (localSquareChart (1 : Matrix4) identitySylvesterWitness)
      ((localSquareChart (1 : Matrix4) identitySylvesterWitness).symm
        (relativeMetricTarget input)) = relativeMetricTarget input
  exact (localSquareChart (1 : Matrix4) identitySylvesterWitness).right_inv
    hInput.2

/-- The selected root varies continuously on the entire explicit chart
domain, not merely at the base point. -/
theorem minkowskiRelativeRootBranch_continuousOn_openDomain :
    ContinuousOn minkowskiRelativeRootBranch
      minkowskiRelativeRootOpenDomain := by
  have hRelative : ContinuousOn relativeMetricTarget
      minkowskiRelativeRootOpenDomain :=
    relativeMetricTarget_continuousOn_invertiblePlus.mono
      (fun _ hInput => hInput.1)
  exact (localSquareChart (1 : Matrix4) identitySylvesterWitness).continuousOn_symm.comp
    hRelative (fun input hInput => hInput.2)

/-- The chosen root lies in the corresponding source chart. -/
theorem minkowskiRelativeRootBranch_mem_source
    {input : MetricPair} (hInput : input ∈ minkowskiRelativeRootOpenDomain) :
    minkowskiRelativeRootBranch input ∈ identityRootSource := by
  exact (localSquareChart (1 : Matrix4) identitySylvesterWitness).map_target hInput.2

/-- Uniqueness of the selected square root inside the same IFT source chart. -/
theorem root_unique_in_identityChart
    {input : MetricPair} (hInput : input ∈ minkowskiRelativeRootOpenDomain)
    {candidate : Matrix4} (hCandidate : candidate ∈ identityRootSource)
    (hSquare : matrixSquare candidate = relativeMetricTarget input) :
    candidate = minkowskiRelativeRootBranch input := by
  apply (localSquareChart (1 : Matrix4) identitySylvesterWitness).injOn
    hCandidate (minkowskiRelativeRootBranch_mem_source hInput)
  change matrixSquare candidate =
    matrixSquare (minkowskiRelativeRootBranch input)
  rw [hSquare, minkowskiRelativeRootBranch_square_on_openDomain hInput]

/-- Complete explicit-chart closure delivered by this gate. -/
theorem minkowski_relative_root_open_domain_closure :
    IsOpen minkowskiRelativeRootOpenDomain ∧
    minkowskiMetricPair ∈ minkowskiRelativeRootOpenDomain ∧
    ContinuousOn minkowskiRelativeRootBranch minkowskiRelativeRootOpenDomain ∧
    ∀ input ∈ minkowskiRelativeRootOpenDomain,
      matrixSquare (minkowskiRelativeRootBranch input) =
        relativeMetricTarget input :=
  ⟨minkowskiRelativeRootOpenDomain_isOpen,
    minkowskiMetricPair_mem_openDomain,
    minkowskiRelativeRootBranch_continuousOn_openDomain,
    fun _ hInput => minkowskiRelativeRootBranch_square_on_openDomain hInput⟩

end

end P0EFTJanusMinkowskiRelativeRootOpenDomain4D
end JanusFormal
