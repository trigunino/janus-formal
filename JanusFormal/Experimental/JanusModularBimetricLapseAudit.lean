import JanusFormal.Experimental.JanusTwoQubitModularClock
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWSecondaryConstraint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterCurvatureFLRWConstraintBranch

/-!
# Modular-clock versus bimetric-lapse audit

This isolated module compares the reciprocal two-qubit modular rate with the
only exact reduced lapse-ratio witness currently available in Program P/B.
-/

namespace JanusFormal
namespace ExperimentalJanusModularBimetricLapseAudit

set_option autoImplicit false

open ExperimentalJanusTwoQubitModularClock
open P0EFTJanusReducedFLRWSecondaryConstraint

noncomputable section

def lapseRatio (lapsePlus lapseMinus : ℝ) : ℝ :=
  lapseMinus / lapsePlus

def modularRateRatio (p : ℝ) : ℝ :=
  |modularGap (1 - p)| / |modularGap p|

def ModularLapseCompatible
    (p lapsePlus lapseMinus : ℝ) : Prop :=
  lapseRatio lapsePlus lapseMinus = modularRateRatio p

/-- Reciprocal PT modular flow requires a unit lapse ratio whenever the state
is faithful and the modular gap is nonzero. -/
theorem reciprocal_modular_compatibility_requires_unit_ratio
    (p lapsePlus lapseMinus : ℝ)
    (hP : p ≠ 0)
    (hOneMinusP : 1 - p ≠ 0)
    (hGap : modularGap p ≠ 0)
    (hCompatible : ModularLapseCompatible p lapsePlus lapseMinus) :
    lapseRatio lapsePlus lapseMinus = 1 := by
  unfold ModularLapseCompatible modularRateRatio at hCompatible
  rw [pt_modular_rate_ratio_is_one p hP hOneMinusP hGap] at hCompatible
  exact hCompatible

/-- The synchronized unit-lapse ansatz is compatible with every nontrivial
reciprocal modular state. -/
theorem unit_lapses_are_modular_compatible
    (p : ℝ)
    (hP : p ≠ 0)
    (hOneMinusP : 1 - p ≠ 0)
    (hGap : modularGap p ≠ 0) :
    ModularLapseCompatible p 1 1 := by
  unfold ModularLapseCompatible lapseRatio modularRateRatio
  rw [pt_modular_rate_ratio_is_one p hP hOneMinusP hGap]
  norm_num

/-- Program P's exact local secondary-preservation witness fixes ratio two,
so it cannot be calibrated by the exact reciprocal modular state.  This
witness lies outside the PT-flat family and is not a physical-branch no-go. -/
theorem nonpt_lapse_witness_is_not_reciprocal_modular
    (p lapsePlus lapseMinus : ℝ)
    (hP : p ≠ 0)
    (hOneMinusP : 1 - p ≠ 0)
    (hGap : modularGap p ≠ 0)
    (hLapsePlus : lapsePlus ≠ 0)
    (hPreserve :
      canonicalPoisson (secondaryDifferential witnessParameters witnessPoint)
          (hamiltonianDifferential lapsePlus lapseMinus witnessParameters
            witnessPoint) = 0) :
    ¬ ModularLapseCompatible p lapsePlus lapseMinus := by
  intro hCompatible
  have hUnit := reciprocal_modular_compatibility_requires_unit_ratio
    p lapsePlus lapseMinus hP hOneMinusP hGap hCompatible
  have hTwo := witness_secondary_preservation_fixes_lapse_ratio
    lapsePlus lapseMinus hPreserve
  unfold lapseRatio at hUnit
  rw [hTwo] at hUnit
  field_simp [hLapsePlus] at hUnit
  norm_num at hUnit

/-- The new positive PT-flat dust-supported witness fixes equal lapses and is
exactly compatible with every faithful nontrivial reciprocal modular state. -/
theorem pt_dust_witness_is_reciprocal_modular
    (p lapsePlus lapseMinus : ℝ)
    (hP : p ≠ 0)
    (hOneMinusP : 1 - p ≠ 0)
    (hGap : modularGap p ≠ 0)
    (hLapsePlus : lapsePlus ≠ 0)
    (hPreserve :
      P0EFTJanusReducedFLRWSecondaryConstraint.canonicalPoisson
          (P0EFTJanusReducedFLRWSecondaryConstraint.secondaryDifferential
            P0EFTJanusMatterCurvatureFLRWConstraintBranch.witnessParameters.base
            P0EFTJanusMatterCurvatureFLRWConstraintBranch.witnessPoint)
          (P0EFTJanusMatterCurvatureFLRWConstraintBranch.extendedHamiltonianDifferential
            lapsePlus lapseMinus
            P0EFTJanusMatterCurvatureFLRWConstraintBranch.witnessParameters
            P0EFTJanusMatterCurvatureFLRWConstraintBranch.witnessPoint) = 0) :
    ModularLapseCompatible p lapsePlus lapseMinus := by
  have hEqual :=
    P0EFTJanusMatterCurvatureFLRWConstraintBranch.witness_secondary_preservation_fixes_lapse_ratio
      lapsePlus lapseMinus hPreserve
  unfold ModularLapseCompatible lapseRatio modularRateRatio
  rw [hEqual, pt_modular_rate_ratio_is_one p hP hOneMinusP hGap]
  exact div_self hLapsePlus

end

end ExperimentalJanusModularBimetricLapseAudit
end JanusFormal
