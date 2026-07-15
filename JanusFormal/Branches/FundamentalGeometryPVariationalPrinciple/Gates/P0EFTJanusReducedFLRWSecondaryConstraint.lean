import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCandidateMinisuperspaceLapseConstraint

/-!
An exact bracket factorization and local Dirac-chain witness for the diagonal,
spatially flat FLRW reduction of Candidate A.  The two Hamiltonian constraint
formulas below are reduced-model inputs: this file does not derive their
Legendre transform from the covariant action.  The local rank and lapse-ratio
witness uses unrestricted reduced parameters outside the PT/exchange-flat
family.  In particular, this file contains no shift redefinition, functional
ADM bracket, generic or global rank theorem, or Boulware--Deser closure claim.
-/

namespace JanusFormal
namespace P0EFTJanusReducedFLRWSecondaryConstraint

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential

noncomputable section

/-- Diagonal FLRW phase point `(a₊,p₊,a₋,p₋)`. -/
structure PhasePoint where
  aPlus : ℝ
  pPlus : ℝ
  aMinus : ℝ
  pMinus : ℝ

/-- Parameters of the vacuum reduced Hamiltonian.  `planckPlusSq` and
`planckMinusSq` denote the positive Einstein--Hilbert coefficients; positivity
is not needed for the algebraic identities. -/
structure ReducedParameters where
  coefficients : PotentialCoefficients
  interactionScale : ℝ
  planckPlusSq : ℝ
  planckMinusSq : ℝ

/-- A coordinate covector on the reduced phase space. -/
structure CanonicalCovector where
  aPlus : ℝ
  pPlus : ℝ
  aMinus : ℝ
  pMinus : ℝ

/-- Affine line through a reduced phase point in a coordinate direction. -/
def phaseLine (x variation : PhasePoint) (t : ℝ) : PhasePoint :=
  { aPlus := x.aPlus + t * variation.aPlus
    pPlus := x.pPlus + t * variation.pPlus
    aMinus := x.aMinus + t * variation.aMinus
    pMinus := x.pMinus + t * variation.pMinus }

/-- Evaluation of a displayed coordinate covector on a phase-space
direction. -/
def covectorApply (df : CanonicalCovector) (variation : PhasePoint) : ℝ :=
  df.aPlus * variation.aPlus + df.pPlus * variation.pPlus +
    df.aMinus * variation.aMinus + df.pMinus * variation.pMinus

theorem affineCoordinate_hasDerivAt
    (base variation : ℝ) :
    HasDerivAt (fun t : ℝ => base + t * variation) variation 0 := by
  have h : HasDerivAt (fun t : ℝ => base + t * variation)
      (1 * variation) 0 :=
    (hasDerivAt_id 0).mul_const variation |>.const_add base
  exact h.congr_deriv (one_mul variation)

/-- Canonical Poisson pairing of two coordinate differentials. -/
def canonicalPoisson (df dg : CanonicalCovector) : ℝ :=
  df.aPlus * dg.pPlus - df.pPlus * dg.aPlus +
    df.aMinus * dg.pMinus - df.pMinus * dg.aMinus

/-- Plus-lapse interaction polynomial after clearing `r=a₋/a₊`. -/
def plusPotential (parameters : ReducedParameters) (x : PhasePoint) : ℝ :=
  parameters.coefficients.beta0 * x.aPlus ^ 3 +
    3 * parameters.coefficients.beta1 * x.aPlus ^ 2 * x.aMinus +
    3 * parameters.coefficients.beta2 * x.aPlus * x.aMinus ^ 2 +
    parameters.coefficients.beta3 * x.aMinus ^ 3

/-- Minus-lapse interaction polynomial after clearing `r=a₋/a₊`. -/
def minusPotential (parameters : ReducedParameters) (x : PhasePoint) : ℝ :=
  parameters.coefficients.beta1 * x.aPlus ^ 3 +
    3 * parameters.coefficients.beta2 * x.aPlus ^ 2 * x.aMinus +
    3 * parameters.coefficients.beta3 * x.aPlus * x.aMinus ^ 2 +
    parameters.coefficients.beta4 * x.aMinus ^ 3

/-- Candidate-A plus Hamiltonian constraint in the vacuum FLRW reduction. -/
def plusConstraint (parameters : ReducedParameters) (x : PhasePoint) : ℝ :=
  -(x.pPlus ^ 2) / (12 * parameters.planckPlusSq * x.aPlus) +
    parameters.interactionScale * plusPotential parameters x

/-- Candidate-A minus Hamiltonian constraint in the vacuum FLRW reduction. -/
def minusConstraint (parameters : ReducedParameters) (x : PhasePoint) : ℝ :=
  -(x.pMinus ^ 2) / (12 * parameters.planckMinusSq * x.aMinus) +
    parameters.interactionScale * minusPotential parameters x

/-- Coordinate differential formula of `plusConstraint` on its regular domain. -/
def plusDifferential
    (parameters : ReducedParameters) (x : PhasePoint) : CanonicalCovector :=
  { aPlus :=
      x.pPlus ^ 2 / (12 * parameters.planckPlusSq * x.aPlus ^ 2) +
        parameters.interactionScale *
          (3 * parameters.coefficients.beta0 * x.aPlus ^ 2 +
            6 * parameters.coefficients.beta1 * x.aPlus * x.aMinus +
            3 * parameters.coefficients.beta2 * x.aMinus ^ 2)
    pPlus := -x.pPlus / (6 * parameters.planckPlusSq * x.aPlus)
    aMinus :=
      parameters.interactionScale *
        (3 * parameters.coefficients.beta1 * x.aPlus ^ 2 +
          6 * parameters.coefficients.beta2 * x.aPlus * x.aMinus +
          3 * parameters.coefficients.beta3 * x.aMinus ^ 2)
    pMinus := 0 }

/-- Coordinate differential formula of `minusConstraint` on its regular domain. -/
def minusDifferential
    (parameters : ReducedParameters) (x : PhasePoint) : CanonicalCovector :=
  { aPlus :=
      parameters.interactionScale *
        (3 * parameters.coefficients.beta1 * x.aPlus ^ 2 +
          6 * parameters.coefficients.beta2 * x.aPlus * x.aMinus +
          3 * parameters.coefficients.beta3 * x.aMinus ^ 2)
    pPlus := 0
    aMinus :=
      x.pMinus ^ 2 / (12 * parameters.planckMinusSq * x.aMinus ^ 2) +
        parameters.interactionScale *
          (3 * parameters.coefficients.beta2 * x.aPlus ^ 2 +
            6 * parameters.coefficients.beta3 * x.aPlus * x.aMinus +
            3 * parameters.coefficients.beta4 * x.aMinus ^ 2)
    pMinus := -x.pMinus / (6 * parameters.planckMinusSq * x.aMinus) }

/-- The displayed plus covector is the actual directional derivative of the
input plus Hamiltonian along every affine phase-space line in its regular
domain. -/
theorem plusConstraint_phaseLine_hasDerivAt
    (parameters : ReducedParameters) (x variation : PhasePoint)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) :
    HasDerivAt
      (fun t => plusConstraint parameters (phaseLine x variation t))
      (covectorApply (plusDifferential parameters x) variation) 0 := by
  let ap : ℝ → ℝ := fun t => x.aPlus + t * variation.aPlus
  let pp : ℝ → ℝ := fun t => x.pPlus + t * variation.pPlus
  let am : ℝ → ℝ := fun t => x.aMinus + t * variation.aMinus
  have hap : HasDerivAt ap variation.aPlus 0 :=
    affineCoordinate_hasDerivAt x.aPlus variation.aPlus
  have hpp : HasDerivAt pp variation.pPlus 0 :=
    affineCoordinate_hasDerivAt x.pPlus variation.pPlus
  have ham : HasDerivAt am variation.aMinus 0 :=
    affineCoordinate_hasDerivAt x.aMinus variation.aMinus
  have hden : HasDerivAt
      (fun t => 12 * parameters.planckPlusSq * ap t)
      (12 * parameters.planckPlusSq * variation.aPlus) 0 :=
    hap.const_mul (12 * parameters.planckPlusSq)
  have hden0 : 12 * parameters.planckPlusSq * ap 0 ≠ 0 := by
    simp [ap, hPlanckPlus, haPlus]
  have hKinetic := ((hpp.pow 2).div hden hden0).neg
  have hPotential :=
    ((hap.pow 3).const_mul parameters.coefficients.beta0).add
      (((hap.pow 2).mul ham).const_mul
        (3 * parameters.coefficients.beta1)) |>.add
      ((hap.mul (ham.pow 2)).const_mul
        (3 * parameters.coefficients.beta2)) |>.add
      ((ham.pow 3).const_mul parameters.coefficients.beta3)
  have hTotal := hKinetic.add
    (hPotential.const_mul parameters.interactionScale)
  refine (hTotal.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · simp [covectorApply, plusDifferential, ap, pp, am]
    field_simp [hPlanckPlus, haPlus]
    ring
  · intro t
    simp [plusConstraint, plusPotential, phaseLine, ap, pp, am]
    ring

/-- The displayed minus covector is the actual directional derivative of the
input minus Hamiltonian along every affine phase-space line in its regular
domain. -/
theorem minusConstraint_phaseLine_hasDerivAt
    (parameters : ReducedParameters) (x variation : PhasePoint)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haMinus : x.aMinus ≠ 0) :
    HasDerivAt
      (fun t => minusConstraint parameters (phaseLine x variation t))
      (covectorApply (minusDifferential parameters x) variation) 0 := by
  let ap : ℝ → ℝ := fun t => x.aPlus + t * variation.aPlus
  let am : ℝ → ℝ := fun t => x.aMinus + t * variation.aMinus
  let pm : ℝ → ℝ := fun t => x.pMinus + t * variation.pMinus
  have hap : HasDerivAt ap variation.aPlus 0 :=
    affineCoordinate_hasDerivAt x.aPlus variation.aPlus
  have ham : HasDerivAt am variation.aMinus 0 :=
    affineCoordinate_hasDerivAt x.aMinus variation.aMinus
  have hpm : HasDerivAt pm variation.pMinus 0 :=
    affineCoordinate_hasDerivAt x.pMinus variation.pMinus
  have hden : HasDerivAt
      (fun t => 12 * parameters.planckMinusSq * am t)
      (12 * parameters.planckMinusSq * variation.aMinus) 0 :=
    ham.const_mul (12 * parameters.planckMinusSq)
  have hden0 : 12 * parameters.planckMinusSq * am 0 ≠ 0 := by
    simp [am, hPlanckMinus, haMinus]
  have hKinetic := ((hpm.pow 2).div hden hden0).neg
  have hPotential :=
    ((hap.pow 3).const_mul parameters.coefficients.beta1).add
      (((hap.pow 2).mul ham).const_mul
        (3 * parameters.coefficients.beta2)) |>.add
      ((hap.mul (ham.pow 2)).const_mul
        (3 * parameters.coefficients.beta3)) |>.add
      ((ham.pow 3).const_mul parameters.coefficients.beta4)
  have hTotal := hKinetic.add
    (hPotential.const_mul parameters.interactionScale)
  refine (hTotal.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · simp [covectorApply, minusDifferential, ap, am, pm]
    field_simp [hPlanckMinus, haMinus]
    ring
  · intro t
    simp [minusConstraint, minusPotential, phaseLine, ap, am, pm]
    ring

/-- Kinematic factor of the reduced secondary constraint. -/
def kinematicFactor (parameters : ReducedParameters) (x : PhasePoint) : ℝ :=
  parameters.planckMinusSq * x.aMinus * x.pPlus -
    parameters.planckPlusSq * x.aPlus * x.pMinus

/-- Potential factor selecting the dynamical rather than algebraic FLRW
branch. -/
def potentialFactor (parameters : ReducedParameters) (x : PhasePoint) : ℝ :=
  parameters.coefficients.beta1 * x.aPlus ^ 2 +
    2 * parameters.coefficients.beta2 * x.aPlus * x.aMinus +
    parameters.coefficients.beta3 * x.aMinus ^ 2

/-- Reduced secondary candidate `S={C₊,C₋}` in factorized form. -/
def secondaryConstraint
    (parameters : ReducedParameters) (x : PhasePoint) : ℝ :=
  parameters.interactionScale * kinematicFactor parameters x *
      potentialFactor parameters x /
    (2 * parameters.planckPlusSq * parameters.planckMinusSq *
      x.aPlus * x.aMinus)

/-- Exact factorization of the canonical bracket of the two reduced
Hamiltonian constraints. -/
theorem primary_poisson_bracket_factorization
    (parameters : ReducedParameters) (x : PhasePoint)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) (haMinus : x.aMinus ≠ 0) :
    canonicalPoisson (plusDifferential parameters x)
        (minusDifferential parameters x) =
      secondaryConstraint parameters x := by
  unfold canonicalPoisson plusDifferential minusDifferential
    secondaryConstraint kinematicFactor potentialFactor
  field_simp [hPlanckPlus, hPlanckMinus, haPlus, haMinus]
  ring

/-- On the regular dynamical branch, `S=0` is exactly the kinematic FLRW
relation.  The excluded `potentialFactor=0` locus is the algebraic branch. -/
theorem secondary_eq_zero_iff_kinematic_on_dynamical_branch
    (parameters : ReducedParameters) (x : PhasePoint)
    (hScale : parameters.interactionScale ≠ 0)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) (haMinus : x.aMinus ≠ 0)
    (hPotential : potentialFactor parameters x ≠ 0) :
    secondaryConstraint parameters x = 0 ↔
      kinematicFactor parameters x = 0 := by
  unfold secondaryConstraint
  simp [hScale, hPlanckPlus, hPlanckMinus, haPlus, haMinus, hPotential]

theorem algebraic_branch_annihilates_secondary
    (parameters : ReducedParameters) (x : PhasePoint)
    (hPotential : potentialFactor parameters x = 0) :
    secondaryConstraint parameters x = 0 := by
  simp [secondaryConstraint, hPotential]

/-- Coordinate differential is linear under formation of the total reduced
Hamiltonian `H=N₊C₊+N₋C₋`. -/
def hamiltonianDifferential
    (lapsePlus lapseMinus : ℝ)
    (parameters : ReducedParameters) (x : PhasePoint) : CanonicalCovector :=
  { aPlus :=
      lapsePlus * (plusDifferential parameters x).aPlus +
        lapseMinus * (minusDifferential parameters x).aPlus
    pPlus :=
      lapsePlus * (plusDifferential parameters x).pPlus +
        lapseMinus * (minusDifferential parameters x).pPlus
    aMinus :=
      lapsePlus * (plusDifferential parameters x).aMinus +
        lapseMinus * (minusDifferential parameters x).aMinus
    pMinus :=
      lapsePlus * (plusDifferential parameters x).pMinus +
        lapseMinus * (minusDifferential parameters x).pMinus }

theorem preserve_plus_is_lapseMinus_times_secondary
    (lapsePlus lapseMinus : ℝ)
    (parameters : ReducedParameters) (x : PhasePoint)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) (haMinus : x.aMinus ≠ 0) :
    canonicalPoisson (plusDifferential parameters x)
        (hamiltonianDifferential lapsePlus lapseMinus parameters x) =
      lapseMinus * secondaryConstraint parameters x := by
  rw [← primary_poisson_bracket_factorization parameters x hPlanckPlus
    hPlanckMinus haPlus haMinus]
  unfold canonicalPoisson hamiltonianDifferential
  ring

theorem preserve_minus_is_neg_lapsePlus_times_secondary
    (lapsePlus lapseMinus : ℝ)
    (parameters : ReducedParameters) (x : PhasePoint)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) (haMinus : x.aMinus ≠ 0) :
    canonicalPoisson (minusDifferential parameters x)
        (hamiltonianDifferential lapsePlus lapseMinus parameters x) =
      -lapsePlus * secondaryConstraint parameters x := by
  rw [← primary_poisson_bracket_factorization parameters x hPlanckPlus
    hPlanckMinus haPlus haMinus]
  unfold canonicalPoisson hamiltonianDifferential
  ring

/-- For nonzero lapses, preservation of the two lapse constraints forces the
reduced secondary constraint. -/
theorem secondary_constraint_of_primary_preservation
    (lapsePlus lapseMinus : ℝ)
    (parameters : ReducedParameters) (x : PhasePoint)
    (_hLapsePlus : lapsePlus ≠ 0) (hLapseMinus : lapseMinus ≠ 0)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) (haMinus : x.aMinus ≠ 0)
    (hPreservePlus :
      canonicalPoisson (plusDifferential parameters x)
          (hamiltonianDifferential lapsePlus lapseMinus parameters x) = 0)
    (_hPreserveMinus :
      canonicalPoisson (minusDifferential parameters x)
          (hamiltonianDifferential lapsePlus lapseMinus parameters x) = 0) :
    secondaryConstraint parameters x = 0 := by
  rw [preserve_plus_is_lapseMinus_times_secondary lapsePlus lapseMinus
    parameters x hPlanckPlus hPlanckMinus haPlus haMinus] at hPreservePlus
  exact (mul_eq_zero.mp hPreservePlus).resolve_left hLapseMinus

/-- Coordinate differential of the factorized secondary constraint on the
regular domain where both Planck coefficients and both scale factors are
nonzero. -/
def secondaryDifferential
    (parameters : ReducedParameters) (x : PhasePoint) : CanonicalCovector :=
  let scale := parameters.interactionScale /
    (2 * parameters.planckPlusSq * parameters.planckMinusSq)
  let k := kinematicFactor parameters x
  let q := potentialFactor parameters x
  { aPlus := scale *
      (((-parameters.planckPlusSq * x.pMinus) * q +
          k * (2 * parameters.coefficients.beta1 * x.aPlus +
            2 * parameters.coefficients.beta2 * x.aMinus)) /
        (x.aPlus * x.aMinus) - k * q / (x.aPlus ^ 2 * x.aMinus))
    pPlus := scale *
      (parameters.planckMinusSq * x.aMinus * q /
        (x.aPlus * x.aMinus))
    aMinus := scale *
      (((parameters.planckMinusSq * x.pPlus) * q +
          k * (2 * parameters.coefficients.beta2 * x.aPlus +
            2 * parameters.coefficients.beta3 * x.aMinus)) /
        (x.aPlus * x.aMinus) - k * q / (x.aPlus * x.aMinus ^ 2))
    pMinus := scale *
      ((-parameters.planckPlusSq * x.aPlus) * q /
        (x.aPlus * x.aMinus)) }

/-- The displayed secondary covector is the actual directional derivative of
the factorized secondary constraint along every affine phase-space line in its
regular domain. -/
theorem secondaryConstraint_phaseLine_hasDerivAt
    (parameters : ReducedParameters) (x variation : PhasePoint)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) (haMinus : x.aMinus ≠ 0) :
    HasDerivAt
      (fun t => secondaryConstraint parameters (phaseLine x variation t))
      (covectorApply (secondaryDifferential parameters x) variation) 0 := by
  let ap : ℝ → ℝ := fun t => x.aPlus + t * variation.aPlus
  let pp : ℝ → ℝ := fun t => x.pPlus + t * variation.pPlus
  let am : ℝ → ℝ := fun t => x.aMinus + t * variation.aMinus
  let pm : ℝ → ℝ := fun t => x.pMinus + t * variation.pMinus
  have hap : HasDerivAt ap variation.aPlus 0 :=
    affineCoordinate_hasDerivAt x.aPlus variation.aPlus
  have hpp : HasDerivAt pp variation.pPlus 0 :=
    affineCoordinate_hasDerivAt x.pPlus variation.pPlus
  have ham : HasDerivAt am variation.aMinus 0 :=
    affineCoordinate_hasDerivAt x.aMinus variation.aMinus
  have hpm : HasDerivAt pm variation.pMinus 0 :=
    affineCoordinate_hasDerivAt x.pMinus variation.pMinus
  have hk :=
    (((ham.const_mul parameters.planckMinusSq).mul hpp).sub
      ((hap.const_mul parameters.planckPlusSq).mul hpm))
  have hq :=
    ((hap.pow 2).const_mul parameters.coefficients.beta1).add
      ((hap.mul ham).const_mul (2 * parameters.coefficients.beta2)) |>.add
      ((ham.pow 2).const_mul parameters.coefficients.beta3)
  have hden :=
    (hap.const_mul
      (2 * parameters.planckPlusSq * parameters.planckMinusSq)).mul ham
  have hden0 :
      2 * parameters.planckPlusSq * parameters.planckMinusSq * ap 0 * am 0 ≠ 0 := by
    simp [ap, am, hPlanckPlus, hPlanckMinus, haPlus, haMinus]
  have hTotal :=
    (((hk.mul hq).const_mul parameters.interactionScale).div hden hden0)
  refine (hTotal.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · simp [covectorApply, secondaryDifferential, kinematicFactor,
      potentialFactor, ap, pp, am, pm]
    field_simp [hPlanckPlus, hPlanckMinus, haPlus, haMinus]
    ring
  · intro t
    simp [secondaryConstraint, kinematicFactor, potentialFactor, phaseLine,
      ap, pp, am, pm]
    ring

/-- Determinant of a `3×3` matrix, used as a rank surrogate. -/
def det3
    (a b c d e f g h i : ℝ) : ℝ :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- Minor of `d(C₊,C₋,S)` in the `(a₊,p₊,a₋)` columns. -/
def constraintJacobianMinor
    (parameters : ReducedParameters) (x : PhasePoint) : ℝ :=
  det3
    (plusDifferential parameters x).aPlus
    (plusDifferential parameters x).pPlus
    (plusDifferential parameters x).aMinus
    (minusDifferential parameters x).aPlus
    (minusDifferential parameters x).pPlus
    (minusDifferential parameters x).aMinus
    (secondaryDifferential parameters x).aPlus
    (secondaryDifferential parameters x).pPlus
    (secondaryDifferential parameters x).aMinus

/-- Exact local-rank witness parameters.  They deliberately lie outside the
PT/exchange-flat family: the result below is evidence in the unrestricted
reduced parameter space, not at the committed symmetric flat branch. -/
def witnessParameters : ReducedParameters :=
  { coefficients :=
      { beta0 := -(1061 / 28 : ℝ)
        beta1 := 1
        beta2 := 2
        beta3 := 1
        beta4 := -(2417 / 784 : ℝ) }
    interactionScale := 1
    planckPlusSq := 7
    planckMinusSq := 11 }

def witnessPoint : PhasePoint :=
  { aPlus := 1
    pPlus := 3
    aMinus := 2
    pMinus := 66 / 7 }

theorem witness_potentialFactor_exact :
    potentialFactor witnessParameters witnessPoint = 13 := by
  norm_num [potentialFactor, witnessParameters, witnessPoint]

theorem witness_is_regular_dynamical_branch :
    witnessParameters.interactionScale ≠ 0 ∧
      witnessParameters.planckPlusSq ≠ 0 ∧
      witnessParameters.planckMinusSq ≠ 0 ∧
      witnessPoint.aPlus ≠ 0 ∧ witnessPoint.aMinus ≠ 0 ∧
      potentialFactor witnessParameters witnessPoint ≠ 0 := by
  norm_num [potentialFactor, witnessParameters, witnessPoint]

theorem witness_is_outside_pt_exchange_flat_family :
    witnessParameters.coefficients.beta0 ≠
        witnessParameters.coefficients.beta4 ∧
      witnessParameters.coefficients.beta0 ≠
        -4 * witnessParameters.coefficients.beta1 -
          3 * witnessParameters.coefficients.beta2 := by
  norm_num [witnessParameters]

theorem witness_lies_on_constraint_surface :
    plusConstraint witnessParameters witnessPoint = 0 ∧
      minusConstraint witnessParameters witnessPoint = 0 ∧
      secondaryConstraint witnessParameters witnessPoint = 0 := by
  norm_num [plusConstraint, minusConstraint, plusPotential, minusPotential,
    secondaryConstraint, kinematicFactor, potentialFactor, witnessParameters,
    witnessPoint]

theorem witness_constraintJacobianMinor_exact :
    constraintJacobianMinor witnessParameters witnessPoint =
      (270855 / 4802 : ℝ) := by
  norm_num [constraintJacobianMinor, det3, plusDifferential,
    minusDifferential, secondaryDifferential, kinematicFactor,
    potentialFactor, witnessParameters, witnessPoint]

theorem witness_constraintJacobianMinor_nonzero :
    constraintJacobianMinor witnessParameters witnessPoint ≠ 0 := by
  rw [witness_constraintJacobianMinor_exact]
  norm_num

/-- The three constraint covectors are linearly independent at the exact
rational witness.  This is local evidence only, not a global rank theorem. -/
theorem witness_constraint_differentials_independent
    (u v w : ℝ)
    (haPlus :
      u * (plusDifferential witnessParameters witnessPoint).aPlus +
        v * (minusDifferential witnessParameters witnessPoint).aPlus +
        w * (secondaryDifferential witnessParameters witnessPoint).aPlus = 0)
    (hpPlus :
      u * (plusDifferential witnessParameters witnessPoint).pPlus +
        v * (minusDifferential witnessParameters witnessPoint).pPlus +
        w * (secondaryDifferential witnessParameters witnessPoint).pPlus = 0)
    (haMinus :
      u * (plusDifferential witnessParameters witnessPoint).aMinus +
        v * (minusDifferential witnessParameters witnessPoint).aMinus +
        w * (secondaryDifferential witnessParameters witnessPoint).aMinus = 0) :
    u = 0 ∧ v = 0 ∧ w = 0 := by
  norm_num [plusDifferential, minusDifferential, secondaryDifferential,
    kinematicFactor, potentialFactor, witnessParameters, witnessPoint] at haPlus hpPlus haMinus
  constructor
  · linarith
  constructor <;> linarith

/-- At the same exact constrained point, preservation of `S` is nontrivial
and fixes `N₋=2N₊`.  The covector used here is the reduced differential above. -/
theorem witness_secondary_preservation_relation
    (lapsePlus lapseMinus : ℝ) :
    canonicalPoisson (secondaryDifferential witnessParameters witnessPoint)
        (hamiltonianDifferential lapsePlus lapseMinus witnessParameters
          witnessPoint) =
      (90285 / 1078 : ℝ) * lapsePlus -
        (90285 / 2156 : ℝ) * lapseMinus := by
  norm_num [canonicalPoisson, secondaryDifferential, hamiltonianDifferential,
    plusDifferential, minusDifferential, kinematicFactor, potentialFactor,
    witnessParameters, witnessPoint]
  ring

theorem witness_secondary_preservation_fixes_lapse_ratio
    (lapsePlus lapseMinus : ℝ)
    (hPreserve :
      canonicalPoisson (secondaryDifferential witnessParameters witnessPoint)
          (hamiltonianDifferential lapsePlus lapseMinus witnessParameters
            witnessPoint) = 0) :
    lapseMinus = 2 * lapsePlus := by
  rw [witness_secondary_preservation_relation] at hPreserve
  linarith

end

end P0EFTJanusReducedFLRWSecondaryConstraint
end JanusFormal
