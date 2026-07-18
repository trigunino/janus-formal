import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzLocalRootBranch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInverseRelativeRootFrechet

/-!
# Sylvester-regular continuation of a local real `4 x 4` root

The inverse-function-theorem branch can be pulled back along any target path
through its base point.  This gives a genuine local square-root lift and its
Frechet derivative.

Conversely, a continuous square-root lift that remains Sylvester-regular is,
near every parameter value, equal to the IFT branch based at its current
root.  Thus the local branches glue along the supplied lift and the lift is
automatically differentiable whenever the target is.  In particular, the
metric-relative-root derivative no longer needs an independently assumed
differentiability of the selected root.

The continuous lift and pointwise Sylvester equivalences are explicit
hypotheses.  They are the no-branch-jump and no-linearization-boundary data
available in the current formalization; no global principal, causal, or
spectral square-root domain is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzRootRegularTube4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusLorentzLocalRootBranch4D

abbrev Matrix4 := P0EFTJanusLorentzLocalRootBranch4D.Matrix4

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace ℝ Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module ℝ Matrix4 :=
  matrix4NormedSpace.toModule

/-- Pull the IFT root branch at `root` back along a target family. -/
def localTargetLift {E : Type*} (target : E → Matrix4)
    (root : Matrix4) (witness : SylvesterEquivWitness root) : E → Matrix4 :=
  fun point => localRootBranch root witness (target point)

/-- A target family through `root²` has a genuine square-root lift on a
neighbourhood of the base parameter. -/
theorem eventually_localTargetLift_square
    {E : Type*} [TopologicalSpace E]
    (target : E → Matrix4) (point : E)
    (root : Matrix4) (witness : SylvesterEquivWitness root)
    (hTarget : ContinuousAt target point)
    (hBase : target point = matrixSquare root) :
    ∀ᶠ nearby in 𝓝 point,
      matrixSquare (localTargetLift target root witness nearby) =
        target nearby := by
  have hInverse := eventually_matrixSquare_localRootBranch root witness
  have hInverseAtTarget :
      ∀ᶠ value in 𝓝 (target point),
        matrixSquare (localRootBranch root witness value) = value := by
    simpa only [hBase] using hInverse
  exact hTarget.eventually hInverseAtTarget

/-- The locally lifted target path has the inverse-Sylvester derivative. -/
theorem localTargetLift_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E → Matrix4) (targetDerivative : E →L[ℝ] Matrix4)
    (point : E) (root : Matrix4)
    (witness : SylvesterEquivWitness root)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hBase : target point = matrixSquare root) :
    HasFDerivAt (localTargetLift target root witness)
      ((witness.equiv.symm : Matrix4 →L[ℝ] Matrix4).comp targetDerivative)
      point := by
  have hBranch := localRootBranch_hasFDerivAt root witness
  have hBranchAtTarget :
      HasFDerivAt (localRootBranch root witness)
        (witness.equiv.symm : Matrix4 →L[ℝ] Matrix4)
        (target point) := by
    simpa only [hBase] using hBranch
  exact hBranchAtTarget.comp point hTarget

/-- A continuous square-root lift agrees locally with the IFT branch based at
its current value.  This is the overlap compatibility needed to glue the
local branches along the lift. -/
theorem continuousRootLift_eventuallyEq_localTargetLift
    {E : Type*} [TopologicalSpace E]
    (target rootLift : E → Matrix4) (point : E)
    (witness : SylvesterEquivWitness (rootLift point))
    (hRoot : ContinuousAt rootLift point)
    (hSquare : ∀ nearby,
      matrixSquare (rootLift nearby) = target nearby) :
    rootLift =ᶠ[𝓝 point]
      localTargetLift target (rootLift point) witness := by
  have hLeft :=
    eventually_localRootBranch_matrixSquare (rootLift point) witness
  have hAlong :
      ∀ᶠ nearby in 𝓝 point,
        localRootBranch (rootLift point) witness
            (matrixSquare (rootLift nearby)) = rootLift nearby :=
    hRoot.eventually hLeft
  filter_upwards [hAlong] with nearby hNearby
  change rootLift nearby =
    localRootBranch (rootLift point) witness (target nearby)
  rw [← hSquare nearby]
  exact hNearby.symm

/-- Continuity of a regular square-root lift is enough to deduce its
derivative; differentiability of the lift is not assumed. -/
theorem continuousRootLift_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target rootLift : E → Matrix4)
    (targetDerivative : E →L[ℝ] Matrix4) (point : E)
    (witness : SylvesterEquivWitness (rootLift point))
    (hRoot : ContinuousAt rootLift point)
    (hSquare : ∀ nearby,
      matrixSquare (rootLift nearby) = target nearby)
    (hTarget : HasFDerivAt target targetDerivative point) :
    HasFDerivAt rootLift
      ((witness.equiv.symm : Matrix4 →L[ℝ] Matrix4).comp targetDerivative)
      point := by
  have hBase : target point = matrixSquare (rootLift point) :=
    (hSquare point).symm
  have hLocal := localTargetLift_hasFDerivAt target targetDerivative point
    (rootLift point) witness hTarget hBase
  exact hLocal.congr_of_eventuallyEq
    (continuousRootLift_eventuallyEq_localTargetLift target rootLift point
      witness hRoot hSquare)

/-- The derivative obtained by continuation solves the exact Sylvester
equation at the lifted root. -/
theorem continuousRootLift_derivative_sylvester
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (targetDerivative : E →L[ℝ] Matrix4)
    (root : Matrix4) (witness : SylvesterEquivWitness root)
    (variation : E) :
    sylvesterMap root
        (((witness.equiv.symm : Matrix4 →L[ℝ] Matrix4).comp
          targetDerivative) variation) =
      targetDerivative variation := by
  exact inverseSylvester_right root witness (targetDerivative variation)

/-- Metric bridge: an invertible plus metric, a continuous selected root,
the square identity, and Sylvester regularity imply the full relative-metric
root derivative.  The older bridge required differentiability of `root`. -/
theorem relativeMetricRoot_hasFDerivAt_of_continuous
    (root :
      P0EFTJanusMetricInverseRelativeRootFrechet.MetricPair → Matrix4)
    (input : P0EFTJanusMetricInverseRelativeRootFrechet.MetricPair)
    (hPlus : IsUnit input.1)
    (witness : SylvesterEquivWitness (root input))
    (hRoot : ContinuousAt root input)
    (hSquare : ∀ point,
      matrixSquare (root point) =
        P0EFTJanusMetricInverseRelativeRootFrechet.relativeMetricTarget point) :
    HasFDerivAt root
      ((witness.equiv.symm : Matrix4 →L[ℝ] Matrix4).comp
        (P0EFTJanusMetricInverseRelativeRootFrechet.relativeMetricDerivative
          input))
      input := by
  exact continuousRootLift_hasFDerivAt
    P0EFTJanusMetricInverseRelativeRootFrechet.relativeMetricTarget root
    (P0EFTJanusMetricInverseRelativeRootFrechet.relativeMetricDerivative input)
    input witness hRoot hSquare
    (P0EFTJanusMetricInverseRelativeRootFrechet.relativeMetricTarget_hasFDerivAt
      input hPlus)

/-- Pathwise gate: a continuous square lift that is Sylvester-regular at
every time is locally the canonical IFT lift at every time, is automatically
differentiable with the inverse-Sylvester derivative, and that derivative
solves the differentiated square identity. -/
theorem lorentzRootRegularTube4D_gate
    (target rootLift : ℝ → Matrix4)
    (targetDerivative : ℝ → (ℝ →L[ℝ] Matrix4))
    (witness : ∀ time, SylvesterEquivWitness (rootLift time))
    (hRoot : Continuous rootLift)
    (hSquare : ∀ time,
      matrixSquare (rootLift time) = target time)
    (hTarget : ∀ time,
      HasFDerivAt target (targetDerivative time) time) :
    (∀ time, rootLift =ᶠ[𝓝 time]
      localTargetLift target (rootLift time) (witness time)) ∧
    (∀ time, HasFDerivAt rootLift
      (((witness time).equiv.symm : Matrix4 →L[ℝ] Matrix4).comp
        (targetDerivative time)) time) ∧
    (∀ time variation,
      sylvesterMap (rootLift time)
          ((((witness time).equiv.symm : Matrix4 →L[ℝ] Matrix4).comp
            (targetDerivative time)) variation) =
        targetDerivative time variation) := by
  refine ⟨?_, ?_, ?_⟩
  · intro time
    exact continuousRootLift_eventuallyEq_localTargetLift target rootLift time
      (witness time) hRoot.continuousAt hSquare
  · intro time
    exact continuousRootLift_hasFDerivAt target rootLift
      (targetDerivative time) time (witness time) hRoot.continuousAt hSquare
      (hTarget time)
  · intro time variation
    exact continuousRootLift_derivative_sylvester
      (targetDerivative time) (rootLift time) (witness time) variation

end

end P0EFTJanusLorentzRootRegularTube4D
end JanusFormal
