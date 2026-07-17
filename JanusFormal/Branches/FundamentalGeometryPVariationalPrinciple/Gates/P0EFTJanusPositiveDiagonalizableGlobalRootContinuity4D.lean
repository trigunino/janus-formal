import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRootTraceContinuity4D

/-!
# Continuity of the global positive diagonalizable root

The four scalar coefficients of the selected root are continuous.  The
Cayley--Hamilton reconstruction denominator is nonsingular everywhere on the
positive diagonalizable locus, so the rational reconstruction is continuous.
This closes continuity of the global selector and, through the existing local
inverse-function gate, gives local stability and the inverse-Sylvester
derivative without choosing continuous eigenbases.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableGlobalRootContinuity4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusPositiveDiagonalizableSylvesterInverse4D
open P0EFTJanusPositiveDiagonalizableGlobalRootRegularity4D
open P0EFTJanusPositiveDiagonalizableRootCoefficientRegularity4D
open P0EFTJanusPositiveRootTraceContinuity4D

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

private theorem positiveRootReconstructionDenominator_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootReconstructionDenominator target.1
        (positiveRootCharpolyCoefficients target)) := by
  unfold positiveRootReconstructionDenominator
  exact (((continuous_apply 3).comp
      positiveRootCharpolyCoefficients_continuous).neg.smul
        continuous_subtype_val).sub
    (((continuous_apply 1).comp
      positiveRootCharpolyCoefficients_continuous).smul continuous_const)

private theorem positiveRootReconstructionNumerator_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootReconstructionNumerator target.1
        (positiveRootCharpolyCoefficients target)) := by
  unfold positiveRootReconstructionNumerator
  exact ((continuous_subtype_val.matrix_mul continuous_subtype_val).add
    (((continuous_apply 2).comp
      positiveRootCharpolyCoefficients_continuous).smul
        continuous_subtype_val)).add
    (((continuous_apply 0).comp
      positiveRootCharpolyCoefficients_continuous).smul continuous_const)

/-- The inverse reconstruction denominator varies continuously on the whole
positive diagonalizable locus. -/
theorem positiveRootReconstructionDenominator_inv_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      (positiveRootReconstructionDenominator target.1
        (positiveRootCharpolyCoefficients target))⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro target
  have hScalarInverse :
      ContinuousAt Ring.inverse
        (positiveRootReconstructionDenominator target.1
          (positiveRootCharpolyCoefficients target)).det := by
    simpa only [Ring.inverse_eq_inv'] using
      continuousAt_inv₀
        (positiveRootReconstructionDenominator_det_ne_zero target)
  exact ContinuousAt.comp'
    (f := fun candidate : positiveDiagonalizableLocus =>
      positiveRootReconstructionDenominator candidate.1
        (positiveRootCharpolyCoefficients candidate))
    (g := fun matrix : Matrix4 => matrix⁻¹)
    (continuousAt_matrix_inv
      (positiveRootReconstructionDenominator target.1
        (positiveRootCharpolyCoefficients target)) hScalarInverse)
    positiveRootReconstructionDenominator_continuous.continuousAt

/-- The rational Cayley--Hamilton reconstruction is continuous on the actual
positive diagonalizable locus. -/
theorem positiveRootReconstruction_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootReconstruction target.1
        (positiveRootCharpolyCoefficients target)) := by
  unfold positiveRootReconstruction
  exact positiveRootReconstructionDenominator_inv_continuous.matrix_mul
    positiveRootReconstructionNumerator_continuous

/-- The presentation-independent global positive root selector is
continuous. -/
theorem positiveDiagonalizableGlobalRoot_continuous :
    Continuous positiveDiagonalizableGlobalRoot := by
  have hReconstruction :
      (fun target : positiveDiagonalizableLocus =>
        positiveRootReconstruction target.1
          (positiveRootCharpolyCoefficients target)) =
        positiveDiagonalizableGlobalRoot := by
    funext target
    exact positiveRootReconstruction_eq_globalRoot target
  rw [← hReconstruction]
  exact positiveRootReconstruction_continuous

/-- Global continuity closes the local IFT-stability frontier. -/
theorem positiveDiagonalizableGlobalRoot_locallyStable :
    PositiveDiagonalizableGlobalRootLocallyStable :=
  positiveDiagonalizableGlobalRoot_continuous_iff_localIFTStable.mp
    positiveDiagonalizableGlobalRoot_continuous

/-- At every positive diagonalization, the derivative of the global selector
within its locus is the inverse Sylvester operator. -/
theorem positiveDiagonalizableGlobalRoot_hasFDerivWithinAt
    (data : PositiveDiagonalizableRelativeMatrix) :
    HasFDerivWithinAt positiveDiagonalizableGlobalRootOn
      (positiveDiagonalizableSylvesterInverseCLM data)
      positiveDiagonalizableLocus data.target :=
  positiveDiagonalizableGlobalRootOn_hasFDerivWithinAt_of_continuous
    positiveDiagonalizableGlobalRoot_continuous data

end

end P0EFTJanusPositiveDiagonalizableGlobalRootContinuity4D
end JanusFormal
