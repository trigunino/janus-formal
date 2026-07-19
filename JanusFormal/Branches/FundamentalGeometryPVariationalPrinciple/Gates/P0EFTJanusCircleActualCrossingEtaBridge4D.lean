import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleEtaSpectralFlowBridge4D
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleBoundedTransformSpectralFlow

/-!
# Actual circle crossing/eta bridge

This gate identifies the abstract unit spectral-flow integer used by the
zero-mode eta representative with the oriented crossing already proved for
the actual norm-continuous bounded circle Dirac family.  Consequently, its eta
jump is minus twice the exact eigenvalue increment along the fundamental
holonomy interval.

The result is confined to the normalized circle family with primitive
crossing multiplicity.  It supplies no APS theorem, global Janus family index,
Quillen/Bismut--Freed identification, or bulk inflow class.
-/

namespace JanusFormal
namespace P0EFTJanusCircleActualCrossingEtaBridge4D

set_option autoImplicit false

open P0EFTJanusCircleHolonomyEta
open P0EFTJanusHolonomySpectralFlow
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleBoundedTransformSpectralFlow
open P0EFTJanusCircleEtaSpectralFlowBridge4D

/-- The unit spectral flow with the primitive fold index is exactly the
oriented crossing of the actual bounded circle family. -/
theorem actualCircleFundamentalCrossing_eq_unit_spectralFlow
    (fold : Fold) :
    spectralFlow (circleFundamentalCrossing fold) 1 =
      circleFundamentalCrossing fold := by
  exact unit_winding_spectral_flow (circleFundamentalCrossing fold)

/-- The eta jump for either actual primitive fold is minus twice its oriented
bounded-family crossing. -/
theorem zeroModeEta_unit_jump_eq_neg_two_actualCircleCrossing
    (fold : Fold) (holonomy : ℝ) :
    zeroModeEta (circleFundamentalCrossing fold) (holonomy + 1) -
        zeroModeEta (circleFundamentalCrossing fold) holonomy =
      -2 * (circleFundamentalCrossing fold : ℝ) := by
  calc
    zeroModeEta (circleFundamentalCrossing fold) (holonomy + 1) -
          zeroModeEta (circleFundamentalCrossing fold) holonomy =
        -2 * (spectralFlow (circleFundamentalCrossing fold) 1 : ℝ) :=
      zeroModeEta_unit_jump_eq_neg_two_spectralFlow
        (circleFundamentalCrossing fold) holonomy
    _ = -2 * (circleFundamentalCrossing fold : ℝ) := by
      rw [actualCircleFundamentalCrossing_eq_unit_spectralFlow]

/-- For every Fourier label, the same eta jump is minus twice the exact
eigenvalue increment of the actual affine circle Dirac path. -/
theorem zeroModeEta_unit_jump_eq_neg_two_actualEigenvalueIncrement
    (fold : Fold) (holonomy : ℝ) (mode : ℤ) :
    zeroModeEta (circleFundamentalCrossing fold) (holonomy + 1) -
        zeroModeEta (circleFundamentalCrossing fold) holonomy =
      -2 * (diracEigenvalue fold unitCircleTwist mode -
        diracEigenvalue fold periodicTwist mode) := by
  rw [zeroModeEta_unit_jump_eq_neg_two_actualCircleCrossing,
    fundamental_holonomy_eigenvalue_increment]

/-- The eta jumps of the two actual PT-related primitive circle folds cancel. -/
theorem actualPtPaired_zeroModeEta_unit_jumps_cancel
    (holonomy : ℝ) :
    (zeroModeEta (circleFundamentalCrossing .positive) (holonomy + 1) -
        zeroModeEta (circleFundamentalCrossing .positive) holonomy) +
      (zeroModeEta (circleFundamentalCrossing .pt) (holonomy + 1) -
        zeroModeEta (circleFundamentalCrossing .pt) holonomy) = 0 := by
  simpa using
    (ptPaired_zeroModeEta_unit_jumps_cancel (1 : ℤ) holonomy)

end P0EFTJanusCircleActualCrossingEtaBridge4D
end JanusFormal
