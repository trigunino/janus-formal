import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatVacuumFLRWConstraintNoGo

/-!
# Matter/curvature FLRW constraint branch

This gate adds a fixed comoving dust energy and the standard scale-linear
spatial-curvature contribution to each reduced FLRW lapse constraint.  At an
exact positive PT-flat point, positive dust energy supports nonzero momenta,
both primary constraints vanish, the primary covectors are independent, and
the reduced secondary constraint has an independent differential.  Its
preservation fixes the local lapse ratio.

This is a finite-dimensional minisuperspace result for the displayed input
Hamiltonians.  It does not derive a covariant matter action, a functional ADM
constraint algebra, or a Boulware--Deser conclusion.
-/

namespace JanusFormal
namespace P0EFTJanusMatterCurvatureFLRWConstraintBranch

set_option autoImplicit false

noncomputable section

open P0EFTJanusReducedFLRWSecondaryConstraint
open P0EFTJanusPTFlatVacuumFLRWConstraintNoGo

/-- Reduced source data.  `dustPlus` and `dustMinus` are fixed comoving dust
energies; `curvaturePlus` and `curvatureMinus` are the normalized FLRW spatial
curvatures. -/
structure MatterCurvatureParameters where
  base : ReducedParameters
  dustPlus : ℝ
  dustMinus : ℝ
  curvaturePlus : ℝ
  curvatureMinus : ℝ

/-- Plus-sector dust and spatial-curvature Hamiltonian contribution. -/
def plusSourceEnergy
    (parameters : MatterCurvatureParameters) (x : PhasePoint) : ℝ :=
  parameters.dustPlus -
    3 * parameters.base.planckPlusSq * parameters.curvaturePlus * x.aPlus

/-- Minus-sector dust and spatial-curvature Hamiltonian contribution. -/
def minusSourceEnergy
    (parameters : MatterCurvatureParameters) (x : PhasePoint) : ℝ :=
  parameters.dustMinus -
    3 * parameters.base.planckMinusSq * parameters.curvatureMinus * x.aMinus

/-- Plus lapse constraint including the displayed matter/curvature source. -/
def extendedPlusConstraint
    (parameters : MatterCurvatureParameters) (x : PhasePoint) : ℝ :=
  plusConstraint parameters.base x + plusSourceEnergy parameters x

/-- Minus lapse constraint including the displayed matter/curvature source. -/
def extendedMinusConstraint
    (parameters : MatterCurvatureParameters) (x : PhasePoint) : ℝ :=
  minusConstraint parameters.base x + minusSourceEnergy parameters x

/-- Coordinate differential of the extended plus constraint. -/
def extendedPlusDifferential
    (parameters : MatterCurvatureParameters) (x : PhasePoint) :
    CanonicalCovector :=
  let vacuum := plusDifferential parameters.base x
  { aPlus := vacuum.aPlus -
      3 * parameters.base.planckPlusSq * parameters.curvaturePlus
    pPlus := vacuum.pPlus
    aMinus := vacuum.aMinus
    pMinus := vacuum.pMinus }

/-- Coordinate differential of the extended minus constraint. -/
def extendedMinusDifferential
    (parameters : MatterCurvatureParameters) (x : PhasePoint) :
    CanonicalCovector :=
  let vacuum := minusDifferential parameters.base x
  { aPlus := vacuum.aPlus
    pPlus := vacuum.pPlus
    aMinus := vacuum.aMinus -
      3 * parameters.base.planckMinusSq * parameters.curvatureMinus
    pMinus := vacuum.pMinus }

theorem extendedPlusConstraint_phaseLine_hasDerivAt
    (parameters : MatterCurvatureParameters) (x variation : PhasePoint)
    (hPlanckPlus : parameters.base.planckPlusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) :
    HasDerivAt
      (fun t => extendedPlusConstraint parameters (phaseLine x variation t))
      (covectorApply (extendedPlusDifferential parameters x) variation) 0 := by
  have hVacuum := plusConstraint_phaseLine_hasDerivAt parameters.base x
    variation hPlanckPlus haPlus
  have hScale := affineCoordinate_hasDerivAt x.aPlus variation.aPlus
  have hCurvature :=
    hScale.const_mul
      (-3 * parameters.base.planckPlusSq * parameters.curvaturePlus)
  have hSource := hCurvature.const_add parameters.dustPlus
  have hTotal := hVacuum.add hSource
  refine (hTotal.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · simp [covectorApply, extendedPlusDifferential]
    ring
  · intro t
    simp [extendedPlusConstraint, plusSourceEnergy, phaseLine]
    ring

theorem extendedMinusConstraint_phaseLine_hasDerivAt
    (parameters : MatterCurvatureParameters) (x variation : PhasePoint)
    (hPlanckMinus : parameters.base.planckMinusSq ≠ 0)
    (haMinus : x.aMinus ≠ 0) :
    HasDerivAt
      (fun t => extendedMinusConstraint parameters (phaseLine x variation t))
      (covectorApply (extendedMinusDifferential parameters x) variation) 0 := by
  have hVacuum := minusConstraint_phaseLine_hasDerivAt parameters.base x
    variation hPlanckMinus haMinus
  have hScale := affineCoordinate_hasDerivAt x.aMinus variation.aMinus
  have hCurvature :=
    hScale.const_mul
      (-3 * parameters.base.planckMinusSq * parameters.curvatureMinus)
  have hSource := hCurvature.const_add parameters.dustMinus
  have hTotal := hVacuum.add hSource
  refine (hTotal.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · simp [covectorApply, extendedMinusDifferential]
    ring
  · intro t
    simp [extendedMinusConstraint, minusSourceEnergy, phaseLine]
    ring

/-- Sector-local dust and curvature shift the primary values but do not add a
cross-sector Poisson term.  The secondary constraint is therefore still the
actual canonical bracket of the two displayed primary differentials. -/
theorem extended_primary_poisson_eq_secondary
    (parameters : MatterCurvatureParameters) (x : PhasePoint)
    (hPlanckPlus : parameters.base.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.base.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) (haMinus : x.aMinus ≠ 0) :
    canonicalPoisson (extendedPlusDifferential parameters x)
        (extendedMinusDifferential parameters x) =
      secondaryConstraint parameters.base x := by
  rw [← primary_poisson_bracket_factorization parameters.base x
    hPlanckPlus hPlanckMinus haPlus haMinus]
  simp [canonicalPoisson, extendedPlusDifferential,
    extendedMinusDifferential, plusDifferential, minusDifferential]

/-- Differential of the extended total reduced Hamiltonian. -/
def extendedHamiltonianDifferential
    (lapsePlus lapseMinus : ℝ)
    (parameters : MatterCurvatureParameters) (x : PhasePoint) :
    CanonicalCovector :=
  let plus := extendedPlusDifferential parameters x
  let minus := extendedMinusDifferential parameters x
  { aPlus := lapsePlus * plus.aPlus + lapseMinus * minus.aPlus
    pPlus := lapsePlus * plus.pPlus + lapseMinus * minus.pPlus
    aMinus := lapsePlus * plus.aMinus + lapseMinus * minus.aMinus
    pMinus := lapsePlus * plus.pMinus + lapseMinus * minus.pMinus }

/-- Positive PT-flat gravitational data with positive comoving dust and flat
spatial slices. -/
def witnessParameters : MatterCurvatureParameters :=
  { base := ptFlatParameters 1 0 1 1 1
    dustPlus := 1 / 12
    dustMinus := 1 / 12
    curvaturePlus := 0
    curvatureMinus := 0 }

/-- Exact nonzero-momentum phase point supported by dust energy. -/
def witnessPoint : PhasePoint :=
  { aPlus := 1
    pPlus := 1
    aMinus := 1
    pMinus := 1 }

theorem witness_has_positive_scales_and_dust :
    0 < witnessPoint.aPlus ∧ 0 < witnessPoint.aMinus ∧
      0 < witnessParameters.dustPlus ∧
      0 < witnessParameters.dustMinus := by
  norm_num [witnessPoint, witnessParameters]

theorem witness_lies_on_both_primary_constraints :
    extendedPlusConstraint witnessParameters witnessPoint = 0 ∧
      extendedMinusConstraint witnessParameters witnessPoint = 0 := by
  norm_num [extendedPlusConstraint, extendedMinusConstraint,
    plusSourceEnergy, minusSourceEnergy, plusConstraint, minusConstraint,
    plusPotential, minusPotential, witnessParameters, witnessPoint,
    ptFlatParameters, ptFlatCoefficients]

theorem witness_lies_on_dynamical_secondary_branch :
    potentialFactor witnessParameters.base witnessPoint = 2 ∧
      secondaryConstraint witnessParameters.base witnessPoint = 0 := by
  norm_num [potentialFactor, secondaryConstraint, kinematicFactor,
    witnessParameters, witnessPoint, ptFlatParameters, ptFlatCoefficients]

theorem witness_primary_covectors_exact :
    extendedPlusDifferential witnessParameters witnessPoint =
        { aPlus := -(71 / 12), pPlus := -(1 / 6),
          aMinus := 6, pMinus := 0 } ∧
      extendedMinusDifferential witnessParameters witnessPoint =
        { aPlus := 6, pPlus := 0,
          aMinus := -(71 / 12), pMinus := -(1 / 6) } := by
  norm_num [extendedPlusDifferential, extendedMinusDifferential,
    plusDifferential, minusDifferential, witnessParameters, witnessPoint,
    ptFlatParameters, ptFlatCoefficients]

/-- Elementary coordinate definition of independence for two canonical
covectors. -/
def CovectorsIndependent (first second : CanonicalCovector) : Prop :=
  ∀ u v : ℝ,
    u * first.aPlus + v * second.aPlus = 0 →
    u * first.pPlus + v * second.pPlus = 0 →
    u * first.aMinus + v * second.aMinus = 0 →
    u * first.pMinus + v * second.pMinus = 0 →
    u = 0 ∧ v = 0

theorem witness_primary_covectors_independent :
    CovectorsIndependent
      (extendedPlusDifferential witnessParameters witnessPoint)
      (extendedMinusDifferential witnessParameters witnessPoint) := by
  intro u v _haPlus hpPlus _haMinus hpMinus
  norm_num [extendedPlusDifferential, extendedMinusDifferential,
    plusDifferential, minusDifferential, witnessParameters, witnessPoint,
    ptFlatParameters, ptFlatCoefficients] at hpPlus hpMinus
  exact ⟨hpPlus, hpMinus⟩

/-- Minor of `d(C_plus,C_minus,S)` in the `(aPlus,pPlus,aMinus)` columns. -/
def extendedConstraintJacobianMinor
    (parameters : MatterCurvatureParameters) (x : PhasePoint) : ℝ :=
  det3
    (extendedPlusDifferential parameters x).aPlus
    (extendedPlusDifferential parameters x).pPlus
    (extendedPlusDifferential parameters x).aMinus
    (extendedMinusDifferential parameters x).aPlus
    (extendedMinusDifferential parameters x).pPlus
    (extendedMinusDifferential parameters x).aMinus
    (secondaryDifferential parameters.base x).aPlus
    (secondaryDifferential parameters.base x).pPlus
    (secondaryDifferential parameters.base x).aMinus

theorem witness_constraintJacobianMinor_exact :
    extendedConstraintJacobianMinor witnessParameters witnessPoint =
      (145 / 144 : ℝ) := by
  norm_num [extendedConstraintJacobianMinor, det3,
    extendedPlusDifferential, extendedMinusDifferential, plusDifferential,
    minusDifferential, secondaryDifferential, kinematicFactor,
    potentialFactor, witnessParameters, witnessPoint, ptFlatParameters,
    ptFlatCoefficients]

theorem witness_constraintJacobianMinor_nonzero :
    extendedConstraintJacobianMinor witnessParameters witnessPoint ≠ 0 := by
  rw [witness_constraintJacobianMinor_exact]
  norm_num

/-- Actual preservation bracket of the secondary differential at the exact
matter-supported constrained point. -/
theorem witness_secondary_preservation_relation
    (lapsePlus lapseMinus : ℝ) :
    canonicalPoisson
        (secondaryDifferential witnessParameters.base witnessPoint)
        (extendedHamiltonianDifferential lapsePlus lapseMinus
          witnessParameters witnessPoint) =
      (145 / 12 : ℝ) * lapsePlus - (145 / 12 : ℝ) * lapseMinus := by
  norm_num [canonicalPoisson, secondaryDifferential,
    extendedHamiltonianDifferential, extendedPlusDifferential,
    extendedMinusDifferential, plusDifferential, minusDifferential,
    kinematicFactor, potentialFactor, witnessParameters, witnessPoint,
    ptFlatParameters, ptFlatCoefficients]
  ring

theorem witness_secondary_preservation_fixes_lapse_ratio
    (lapsePlus lapseMinus : ℝ)
    (hPreserve :
      canonicalPoisson
          (secondaryDifferential witnessParameters.base witnessPoint)
          (extendedHamiltonianDifferential lapsePlus lapseMinus
            witnessParameters witnessPoint) = 0) :
    lapseMinus = lapsePlus := by
  rw [witness_secondary_preservation_relation] at hPreserve
  linarith

end

end P0EFTJanusMatterCurvatureFLRWConstraintBranch
end JanusFormal
