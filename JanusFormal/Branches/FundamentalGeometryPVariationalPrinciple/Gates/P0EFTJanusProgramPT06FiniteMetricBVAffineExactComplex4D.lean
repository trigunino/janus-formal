import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FiniteMetricBVJetProlongation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AffineSecondOrderBRSTNaturality4D

/-!
# Finite metric-BV realization of the affine exact T06 complex

The nonzero finite metric-BV differential is upgraded to a continuous
square-zero fiber differential and inserted into the exact affine
second-order variational complex.  Its jet prolongation agrees with the
coefficientwise construction, commutes with `dH`, and intertwines Euler.

This realizes those statements on the finite metric-BV phase only, not on the
complete eleven-component T02 carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FiniteMetricBVAffineExactComplex4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusProgramPT06AffineSecondOrderExactness4D
open P0EFTJanusProgramPT06FiniteMetricBVJetProlongation4D
open P0EFTJanusProgramPT06AffineSecondOrderBRSTNaturality4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Continuous form of the finite-dimensional physical metric-BV
differential. -/
def programPT06FiniteMetricBVContinuousBRST :
    FiniteMetricBVPhase →L[Real] FiniteMetricBVPhase :=
  finiteMetricBVBRST.toContinuousLinearMap

/-- The finite physical metric-BV phase supplies the square-zero fiber datum
used by the affine T06 complex. -/
def programPT06FiniteMetricBVSquareZeroDifferential :
    ProgramPT06SquareZeroContinuousFiberDifferential4D
      (Fiber := FiniteMetricBVPhase) where
  differential := programPT06FiniteMetricBVContinuousBRST
  square_zero := finiteMetricBVBRST_square_zero

/-- The generic continuous prolongation agrees with the independently defined
finite metric-BV jet differential. -/
theorem programPT06FiniteMetricBVJetProlongation_agrees
    (order : Nat) :
    (programPT06ContinuousFiberDifferentialJetProlongation
        programPT06FiniteMetricBVSquareZeroDifferential order).toLinearMap =
      programPT06FiniteMetricBVJetBRST order := by
  apply LinearMap.ext
  intro jet
  funext index
  rfl

/-- The physical finite metric-BV density differential is square-zero on the
affine second-order carrier. -/
theorem programPT06FiniteMetricBVAffineDensityBRST_square_zero
    (density : ProgramPT06AffineSecondOrderLocalDensity4D
      (Fiber := FiniteMetricBVPhase)) :
    programPT06AffineSecondOrderDensityBRST
        programPT06FiniteMetricBVSquareZeroDifferential
        (programPT06AffineSecondOrderDensityBRST
          programPT06FiniteMetricBVSquareZeroDifferential density) = 0 :=
  programPT06AffineSecondOrderDensityBRST_square_zero
    programPT06FiniteMetricBVSquareZeroDifferential density

/-- The physical finite metric-BV differential commutes with the affine
horizontal differential. -/
theorem programPT06FiniteMetricBVBRST_commutes_augmentedDH
    (input : Real ×
      ProgramPT06LinearFirstOrderHorizontalCurrent4D
        (Fiber := FiniteMetricBVPhase)) :
    programPT06AffineSecondOrderDensityBRST
        programPT06FiniteMetricBVSquareZeroDifferential
        (programPT06AffineSecondOrderAugmentedDH
          (Fiber := FiniteMetricBVPhase) input) =
      programPT06AffineSecondOrderAugmentedDH
        (Fiber := FiniteMetricBVPhase)
        (0, programPT06AffineSecondOrderCurrentBRST
          programPT06FiniteMetricBVSquareZeroDifferential input.2) :=
  programPT06AffineSecondOrderBRST_commutes_augmentedDH
    programPT06FiniteMetricBVSquareZeroDifferential input

/-- The finite metric-BV density differential intertwines the affine Euler
map with the physical BV differential. -/
theorem programPT06FiniteMetricBVLocalEuler_BRST_natural
    (density : ProgramPT06AffineSecondOrderLocalDensity4D
      (Fiber := FiniteMetricBVPhase)) :
    programPT06AffineSecondOrderLocalEuler (Fiber := FiniteMetricBVPhase)
        (programPT06AffineSecondOrderDensityBRST
          programPT06FiniteMetricBVSquareZeroDifferential density) =
      (programPT06AffineSecondOrderLocalEuler
        (Fiber := FiniteMetricBVPhase) density).comp
          programPT06FiniteMetricBVContinuousBRST :=
  programPT06AffineSecondOrderLocalEuler_BRST_natural
    programPT06FiniteMetricBVSquareZeroDifferential density

/-- The exact affine null-Lagrangian classification holds on the same
physical finite metric-BV carrier. -/
theorem programPT06FiniteMetricBV_affineEuler_ker_eq_augmentedDH_range :
    LinearMap.ker
        (programPT06AffineSecondOrderLocalEuler
          (Fiber := FiniteMetricBVPhase)) =
      LinearMap.range
        (programPT06AffineSecondOrderAugmentedDH
          (Fiber := FiniteMetricBVPhase)) :=
  programPT06_affineSecondOrderLocalEuler_ker_eq_augmentedDH_range
    (Fiber := FiniteMetricBVPhase)

end
end P0EFTJanusProgramPT06FiniteMetricBVAffineExactComplex4D
end JanusFormal
