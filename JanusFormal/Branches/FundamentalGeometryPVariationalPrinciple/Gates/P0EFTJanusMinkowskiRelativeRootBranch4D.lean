import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFlatFieldBranch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzLocalRootBranch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInverseRelativeRootFrechet

/-!
# Unconditional local relative root at the Minkowski diagonal

The concrete inverse-function root branch around the identity is composed with
the genuine map `(gPlus,gMinus) ↦ gPlus⁻¹ gMinus`.  This yields an actual local
four-dimensional root branch on independent metric pairs near the Minkowski
diagonal, together with its Frechet derivative and eventual square identity.
-/

namespace JanusFormal
namespace P0EFTJanusMinkowskiRelativeRootBranch4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusFlatFieldBranch4D
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusMetricInverseRelativeRootFrechet

abbrev Matrix4 := P0EFTJanusMetricInverseRelativeRootFrechet.Matrix4
abbrev MetricPair := P0EFTJanusMetricInverseRelativeRootFrechet.MetricPair

local instance localMatrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  P0EFTJanusLorentzLocalRootBranch4D.matrix4NormedAddCommGroup

local instance localMatrix4AddCommGroup : AddCommGroup Matrix4 :=
  P0EFTJanusLorentzLocalRootBranch4D.matrix4AddCommGroup

local instance localMatrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  P0EFTJanusLorentzLocalRootBranch4D.matrix4TopologicalSpace

local instance localMatrix4NormedSpace : NormedSpace Real Matrix4 :=
  P0EFTJanusLorentzLocalRootBranch4D.matrix4NormedSpace

local instance localMatrix4Module : Module Real Matrix4 :=
  P0EFTJanusLorentzLocalRootBranch4D.matrix4Module

local instance localMetricPairNormedAddCommGroup : NormedAddCommGroup MetricPair :=
  Prod.normedAddCommGroup

local instance localMetricPairAddCommGroup : AddCommGroup MetricPair :=
  localMetricPairNormedAddCommGroup.toAddCommGroup

local instance localMetricPairTopologicalSpace : TopologicalSpace MetricPair :=
  localMetricPairNormedAddCommGroup.toUniformSpace.toTopologicalSpace

local instance localMetricPairNormedSpace : NormedSpace Real MetricPair :=
  Prod.normedSpace

local instance localMetricPairModule : Module Real MetricPair :=
  localMetricPairNormedSpace.toModule

abbrev PairMatrixHasFDerivAt
    (function : MetricPair → Matrix4)
    (derivative : MetricPair →L[Real] Matrix4)
    (point : MetricPair) : Prop :=
  @HasFDerivAt Real _ MetricPair
    localMetricPairNormedAddCommGroup.toAddCommGroup
    localMetricPairNormedSpace.toModule
    localMetricPairNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Matrix4 localMatrix4NormedAddCommGroup.toAddCommGroup
    localMatrix4NormedSpace.toModule
    localMatrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    function derivative point

/-- Matrix-inverse derivative rebuilt in the exact Frobenius topology used by
the local inverse-function root chart. -/
def frobeniusMatrixInverseDerivative (metric : Matrix4) : Matrix4 →L[Real] Matrix4 :=
  -ContinuousLinearMap.mulLeftRight Real Matrix4 metric⁻¹ metric⁻¹

theorem frobeniusMatrixInverse_hasFDerivAt
    (metric : Matrix4) (hMetric : IsUnit metric) :
    HasFDerivAt (fun point : Matrix4 ↦ point⁻¹)
      (frobeniusMatrixInverseDerivative metric) metric := by
  obtain ⟨unit, rfl⟩ := hMetric
  convert (hasFDerivAt_ringInverse (𝕜 := Real) unit) using 1
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point
    exact Matrix.nonsing_inv_eq_ringInverse point
  · rename_i hAdd hModule hTopology
    cases hAdd
    cases hModule
    cases hTopology
    simp only [frobeniusMatrixInverseDerivative,
      Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]

/-- Relative-metric derivative in the same Frobenius topology. -/
def frobeniusRelativeMetricDerivative
    (input : MetricPair) : MetricPair →L[Real] Matrix4 :=
  ((ContinuousLinearMap.mul Real Matrix4).flip input.2).comp
      ((frobeniusMatrixInverseDerivative input.1).comp
        (ContinuousLinearMap.fst Real Matrix4 Matrix4)) +
    ((ContinuousLinearMap.mul Real Matrix4) input.1⁻¹).comp
      (ContinuousLinearMap.snd Real Matrix4 Matrix4)

@[simp] theorem frobeniusRelativeMetricDerivative_apply
    (input variation : MetricPair) :
    frobeniusRelativeMetricDerivative input variation =
      -(input.1⁻¹ * variation.1 * input.1⁻¹) * input.2 +
        input.1⁻¹ * variation.2 := by
  rfl

theorem relativeMetricTarget_hasFDerivAt_frobenius
    (input : MetricPair) (hPlus : IsUnit input.1) :
    HasFDerivAt relativeMetricTarget
      (frobeniusRelativeMetricDerivative input) input := by
  have hFirst : HasFDerivAt (fun point : MetricPair ↦ point.1)
      (ContinuousLinearMap.fst Real Matrix4 Matrix4) input :=
    (ContinuousLinearMap.fst Real Matrix4 Matrix4).hasFDerivAt
  have hInverse : HasFDerivAt (fun point : MetricPair ↦ point.1⁻¹)
      ((frobeniusMatrixInverseDerivative input.1).comp
        (ContinuousLinearMap.fst Real Matrix4 Matrix4)) input :=
    (frobeniusMatrixInverse_hasFDerivAt input.1 hPlus).comp input hFirst
  have hSecond : HasFDerivAt (fun point : MetricPair ↦ point.2)
      (ContinuousLinearMap.snd Real Matrix4 Matrix4) input :=
    (ContinuousLinearMap.snd Real Matrix4 Matrix4).hasFDerivAt
  exact (hInverse.mul' hSecond).congr_fderiv (add_comm _ _)

/-- The independent Minkowski metric pair. -/
def minkowskiMetricPair : MetricPair :=
  (minkowskiMetric4, minkowskiMetric4)

theorem minkowskiMetric_isUnit : IsUnit minkowskiMetric4 :=
  minkowskiLorentzMetricPoint4.metric_isUnit

@[simp] theorem minkowski_relativeMetricTarget :
    relativeMetricTarget minkowskiMetricPair = (1 : Matrix4) := by
  change minkowskiMetric4⁻¹ * minkowskiMetric4 = 1
  rw [Matrix.nonsing_inv_mul]
  exact isUnit_iff_ne_zero.mpr minkowskiLorentzMetricPoint4.det_ne_zero

/-- Actual local root selection on metric pairs. -/
def minkowskiRelativeRootBranch : MetricPair → Matrix4 :=
  identityLocalRootBranch ∘ relativeMetricTarget

@[simp] theorem minkowskiRelativeRootBranch_at_base :
    minkowskiRelativeRootBranch minkowskiMetricPair = (1 : Matrix4) := by
  simp [minkowskiRelativeRootBranch]

/-- Chain-rule derivative of the genuine local relative-root selection. -/
theorem minkowskiRelativeRootBranch_hasFDerivAt :
    PairMatrixHasFDerivAt minkowskiRelativeRootBranch
      ((twiceEquiv.symm : Matrix4 →L[Real] Matrix4).comp
        (frobeniusRelativeMetricDerivative minkowskiMetricPair))
      minkowskiMetricPair := by
  have hBase : relativeMetricTarget minkowskiMetricPair = (1 : Matrix4) :=
    minkowski_relativeMetricTarget
  have hOuter : HasFDerivAt identityLocalRootBranch
      (twiceEquiv.symm : Matrix4 →L[Real] Matrix4)
      (relativeMetricTarget minkowskiMetricPair) := by
    rw [hBase]
    exact identityLocalRootBranch_hasFDerivAt
  have hInner := relativeMetricTarget_hasFDerivAt_frobenius
    minkowskiMetricPair minkowskiMetric_isUnit
  simpa only [PairMatrixHasFDerivAt, minkowskiRelativeRootBranch,
    Function.comp_def] using
    hOuter.comp minkowskiMetricPair hInner

theorem minkowskiRelativeRootBranch_fderiv :
    fderiv Real minkowskiRelativeRootBranch minkowskiMetricPair =
      (twiceEquiv.symm : Matrix4 →L[Real] Matrix4).comp
        (frobeniusRelativeMetricDerivative minkowskiMetricPair) :=
  minkowskiRelativeRootBranch_hasFDerivAt.fderiv

/-- The local selection really squares to `gPlus⁻¹ gMinus` throughout a
neighbourhood of the independent Minkowski pair. -/
theorem eventually_minkowskiRelativeRootBranch_square :
    ∀ᶠ input in 𝓝 minkowskiMetricPair,
      matrixSquare (minkowskiRelativeRootBranch input) =
        relativeMetricTarget input := by
  have hTarget : Tendsto relativeMetricTarget
      (𝓝 minkowskiMetricPair) (𝓝 (1 : Matrix4)) := by
    have hContinuous := (relativeMetricTarget_hasFDerivAt_frobenius
      minkowskiMetricPair minkowskiMetric_isUnit).continuousAt
    change Tendsto relativeMetricTarget (𝓝 minkowskiMetricPair)
      (𝓝 (relativeMetricTarget minkowskiMetricPair)) at hContinuous
    rwa [minkowski_relativeMetricTarget] at hContinuous
  have hSquare := eventually_identityLocalRootBranch_square
  exact hTarget.eventually hSquare

/-- The Sylvester inverse at the identity is multiplication by one half. -/
theorem twiceEquiv_symm_apply (target : Matrix4) :
    twiceEquiv.symm target = (1 / 2 : Real) • target := by
  apply twiceEquiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, twiceEquiv_apply]
  ext first second
  simp [Matrix.smul_apply]

/-- Explicit independent-metric directional derivative at the diagonal. -/
theorem minkowskiRelativeRootBranch_fderiv_apply
    (variation : MetricPair) :
    fderiv Real minkowskiRelativeRootBranch minkowskiMetricPair variation =
      (1 / 2 : Real) •
        frobeniusRelativeMetricDerivative minkowskiMetricPair variation := by
  rw [minkowskiRelativeRootBranch_fderiv]
  change twiceEquiv.symm
      (frobeniusRelativeMetricDerivative minkowskiMetricPair variation) =
    (1 / 2 : Real) •
      frobeniusRelativeMetricDerivative minkowskiMetricPair variation
  exact twiceEquiv_symm_apply _

/-- Complete local-diagonal closure delivered by this gate. -/
theorem minkowski_relative_root_local_closure :
    minkowskiRelativeRootBranch minkowskiMetricPair = (1 : Matrix4) ∧
      PairMatrixHasFDerivAt minkowskiRelativeRootBranch
        ((twiceEquiv.symm : Matrix4 →L[Real] Matrix4).comp
          (frobeniusRelativeMetricDerivative minkowskiMetricPair))
        minkowskiMetricPair ∧
      (∀ᶠ input in 𝓝 minkowskiMetricPair,
        matrixSquare (minkowskiRelativeRootBranch input) =
          relativeMetricTarget input) :=
  ⟨minkowskiRelativeRootBranch_at_base,
    minkowskiRelativeRootBranch_hasFDerivAt,
    eventually_minkowskiRelativeRootBranch_square⟩

end

end P0EFTJanusMinkowskiRelativeRootBranch4D
end JanusFormal
