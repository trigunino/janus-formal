import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWSecondaryConstraint

/-!
# Finite-site functional Poisson lift of the Candidate-A FLRW chain

This gate replaces one reduced phase point by a field of phase points over an
arbitrary finite set of spatial sites.  Functionals and their differentials are
genuine finite sums, and the canonical bracket is the sum of the four-coordinate
Poisson pairing at every site.  The displayed differential arrays are proved to
be the actual derivatives along arbitrary field lines.

The computed mixed-primary bracket is ultralocal: the bracket of smeared plus
and minus constraints is the weighted sum of the reduced secondary
constraints, and the displayed primary-preservation equations localize at
every site.  A two-site constrained witness proves independence of the three
local constraint covectors at both sites and fixes two lapse ratios
independently.  The Jacobi theorem below concerns only affine functionals with
constant differentials; it is not a closure theorem for the nonlinear
constraint algebra.

This is a finite lattice lift of the spatially flat FLRW model.  It contains no
spatial derivatives, continuum functional analysis, ADM shift, hypersurface-
deformation algebra, nonlinear constraint-algebra closure, or claim of
Boulware--Deser closure in the full theory.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteSpatialFunctionalPoisson

set_option autoImplicit false

noncomputable section

open P0EFTJanusReducedFLRWSecondaryConstraint

/-- A reduced Janus phase-space field over spatial sites. -/
abbrev SpatialField (Site : Type*) := Site → PhasePoint

/-- A coordinate functional differential, represented site by site. -/
abbrev FunctionalDifferential (Site : Type*) := Site → CanonicalCovector

/-- Zero coordinate covector. -/
def zeroCovector : CanonicalCovector :=
  { aPlus := 0, pPlus := 0, aMinus := 0, pMinus := 0 }

/-- Pointwise sum of coordinate covectors. -/
def addCovector (df dg : CanonicalCovector) : CanonicalCovector :=
  { aPlus := df.aPlus + dg.aPlus
    pPlus := df.pPlus + dg.pPlus
    aMinus := df.aMinus + dg.aMinus
    pMinus := df.pMinus + dg.pMinus }

/-- Scalar multiplication of a coordinate covector. -/
def scaleCovector (c : ℝ) (df : CanonicalCovector) : CanonicalCovector :=
  { aPlus := c * df.aPlus
    pPlus := c * df.pPlus
    aMinus := c * df.aMinus
    pMinus := c * df.pMinus }

/-- Pointwise zero functional differential. -/
def zeroDifferential {Site : Type*} : FunctionalDifferential Site :=
  fun _ => zeroCovector

/-- Pointwise addition of functional differentials. -/
def addDifferential {Site : Type*}
    (dF dG : FunctionalDifferential Site) : FunctionalDifferential Site :=
  fun i => addCovector (dF i) (dG i)

/-- Pointwise scalar multiplication of a functional differential. -/
def scaleDifferential {Site : Type*}
    (c : ℝ) (dF : FunctionalDifferential Site) : FunctionalDifferential Site :=
  fun i => scaleCovector c (dF i)

/-- Evaluation of a functional differential on a field variation. -/
def differentialApply {Site : Type*} [Fintype Site]
    (dF : FunctionalDifferential Site) (variation : SpatialField Site) : ℝ :=
  ∑ i, covectorApply (dF i) (variation i)

/-- Canonical functional Poisson bracket on a finite spatial lattice. -/
def finitePoisson {Site : Type*} [Fintype Site]
    (dF dG : FunctionalDifferential Site) : ℝ :=
  ∑ i, canonicalPoisson (dF i) (dG i)

theorem finitePoisson_add_left {Site : Type*} [Fintype Site]
    (dF dG dH : FunctionalDifferential Site) :
    finitePoisson (addDifferential dF dG) dH =
      finitePoisson dF dH + finitePoisson dG dH := by
  simp only [finitePoisson, addDifferential, canonicalPoisson, addCovector]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finitePoisson_add_right {Site : Type*} [Fintype Site]
    (dF dG dH : FunctionalDifferential Site) :
    finitePoisson dF (addDifferential dG dH) =
      finitePoisson dF dG + finitePoisson dF dH := by
  simp only [finitePoisson, addDifferential, canonicalPoisson, addCovector]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finitePoisson_scale_left {Site : Type*} [Fintype Site]
    (c : ℝ) (dF dG : FunctionalDifferential Site) :
    finitePoisson (scaleDifferential c dF) dG =
      c * finitePoisson dF dG := by
  simp only [finitePoisson, scaleDifferential, canonicalPoisson, scaleCovector,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finitePoisson_scale_right {Site : Type*} [Fintype Site]
    (c : ℝ) (dF dG : FunctionalDifferential Site) :
    finitePoisson dF (scaleDifferential c dG) =
      c * finitePoisson dF dG := by
  simp only [finitePoisson, scaleDifferential, canonicalPoisson, scaleCovector,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finitePoisson_antisymmetric {Site : Type*} [Fintype Site]
    (dF dG : FunctionalDifferential Site) :
    finitePoisson dF dG = -finitePoisson dG dF := by
  unfold finitePoisson
  calc
    ∑ i, canonicalPoisson (dF i) (dG i) =
        ∑ i, -canonicalPoisson (dG i) (dF i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [canonicalPoisson]
      ring
    _ = -∑ i, canonicalPoisson (dG i) (dF i) :=
      by
        exact Finset.sum_neg_distrib (s := Finset.univ)
          (fun i : Site => canonicalPoisson (dG i) (dF i))

theorem finitePoisson_self {Site : Type*} [Fintype Site]
    (dF : FunctionalDifferential Site) : finitePoisson dF dF = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [canonicalPoisson]
  ring

theorem canonicalPoisson_scale_both
    (c d : ℝ) (df dg : CanonicalCovector) :
    canonicalPoisson (scaleCovector c df) (scaleCovector d dg) =
      c * d * canonicalPoisson df dg := by
  simp only [canonicalPoisson, scaleCovector]
  ring

/-- Affine finite-site functional.  Its differential is field-independent. -/
structure AffineFunctional (Site : Type*) where
  constant : ℝ
  differential : FunctionalDifferential Site

/-- Canonical bracket of affine functionals; it is a constant functional. -/
def affinePoisson {Site : Type*} [Fintype Site]
    (F G : AffineFunctional Site) : AffineFunctional Site :=
  { constant := finitePoisson F.differential G.differential
    differential := zeroDifferential }

/-- The constant zero affine functional. -/
def zeroAffine {Site : Type*} : AffineFunctional Site :=
  { constant := 0, differential := zeroDifferential }

/-- Jacobi holds exactly on the affine subalgebra.  Each inner bracket is
constant, so every nested bracket vanishes. -/
theorem affine_poisson_jacobi {Site : Type*} [Fintype Site]
    (F G H : AffineFunctional Site) :
    (affinePoisson F (affinePoisson G H)).constant +
        (affinePoisson G (affinePoisson H F)).constant +
        (affinePoisson H (affinePoisson F G)).constant = 0 := by
  simp [affinePoisson, finitePoisson, zeroDifferential, zeroCovector,
    canonicalPoisson]

/-- Affine line through an entire finite-site field. -/
def fieldLine {Site : Type*}
    (x variation : SpatialField Site) (t : ℝ) : SpatialField Site :=
  fun i => phaseLine (x i) (variation i) t

/-- Smeared plus primary constraint functional. -/
def plusFunctional {Site : Type*} [Fintype Site]
    (weight : Site → ℝ) (parameters : ReducedParameters)
    (x : SpatialField Site) : ℝ :=
  ∑ i, weight i * plusConstraint parameters (x i)

/-- Smeared minus primary constraint functional. -/
def minusFunctional {Site : Type*} [Fintype Site]
    (weight : Site → ℝ) (parameters : ReducedParameters)
    (x : SpatialField Site) : ℝ :=
  ∑ i, weight i * minusConstraint parameters (x i)

/-- Actual differential array of the smeared plus constraint. -/
def plusFunctionalDifferential {Site : Type*}
    (weight : Site → ℝ) (parameters : ReducedParameters)
    (x : SpatialField Site) : FunctionalDifferential Site :=
  fun i => scaleCovector (weight i) (plusDifferential parameters (x i))

/-- Actual differential array of the smeared minus constraint. -/
def minusFunctionalDifferential {Site : Type*}
    (weight : Site → ℝ) (parameters : ReducedParameters)
    (x : SpatialField Site) : FunctionalDifferential Site :=
  fun i => scaleCovector (weight i) (minusDifferential parameters (x i))

theorem plusFunctional_fieldLine_hasDerivAt
    {Site : Type*} [Fintype Site]
    (weight : Site → ℝ) (parameters : ReducedParameters)
    (x variation : SpatialField Site)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (haPlus : ∀ i, (x i).aPlus ≠ 0) :
    HasDerivAt
      (fun t => plusFunctional weight parameters (fieldLine x variation t))
      (differentialApply (plusFunctionalDifferential weight parameters x)
        variation) 0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ =>
      (plusConstraint_phaseLine_hasDerivAt parameters (x i) (variation i)
        hPlanckPlus (haPlus i)).const_mul (weight i))
  have hDerivative :
      (∑ i, weight i *
        covectorApply (plusDifferential parameters (x i)) (variation i)) =
        differentialApply (plusFunctionalDifferential weight parameters x)
          variation := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [plusFunctionalDifferential, covectorApply,
      scaleCovector]
    ring
  simpa [plusFunctional, fieldLine] using hsum.congr_deriv hDerivative

theorem minusFunctional_fieldLine_hasDerivAt
    {Site : Type*} [Fintype Site]
    (weight : Site → ℝ) (parameters : ReducedParameters)
    (x variation : SpatialField Site)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haMinus : ∀ i, (x i).aMinus ≠ 0) :
    HasDerivAt
      (fun t => minusFunctional weight parameters (fieldLine x variation t))
      (differentialApply (minusFunctionalDifferential weight parameters x)
        variation) 0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ =>
      (minusConstraint_phaseLine_hasDerivAt parameters (x i) (variation i)
        hPlanckMinus (haMinus i)).const_mul (weight i))
  have hDerivative :
      (∑ i, weight i *
        covectorApply (minusDifferential parameters (x i)) (variation i)) =
        differentialApply (minusFunctionalDifferential weight parameters x)
          variation := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [minusFunctionalDifferential, covectorApply,
      scaleCovector]
    ring
  simpa [minusFunctional, fieldLine] using hsum.congr_deriv hDerivative

/-- The finite functional bracket is the weighted sum of local secondary
constraints, rather than a supplied scalar bracket. -/
theorem plus_minus_functional_poisson_eq_secondary_sum
    {Site : Type*} [Fintype Site]
    (weightPlus weightMinus : Site → ℝ)
    (parameters : ReducedParameters) (x : SpatialField Site)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : ∀ i, (x i).aPlus ≠ 0)
    (haMinus : ∀ i, (x i).aMinus ≠ 0) :
    finitePoisson (plusFunctionalDifferential weightPlus parameters x)
        (minusFunctionalDifferential weightMinus parameters x) =
      ∑ i, weightPlus i * weightMinus i *
        secondaryConstraint parameters (x i) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [plusFunctionalDifferential, minusFunctionalDifferential]
  rw [canonicalPoisson_scale_both]
  rw [primary_poisson_bracket_factorization parameters (x i) hPlanckPlus
    hPlanckMinus (haPlus i) (haMinus i)]

/-- The unsmeared all-site primary bracket is the sum of local secondaries. -/
theorem all_site_primary_poisson_eq_secondary_sum
    {Site : Type*} [Fintype Site]
    (parameters : ReducedParameters) (x : SpatialField Site)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : ∀ i, (x i).aPlus ≠ 0)
    (haMinus : ∀ i, (x i).aMinus ≠ 0) :
    finitePoisson (plusFunctionalDifferential (fun _ => 1) parameters x)
        (minusFunctionalDifferential (fun _ => 1) parameters x) =
      ∑ i, secondaryConstraint parameters (x i) := by
  simpa using plus_minus_functional_poisson_eq_secondary_sum
    (fun _ : Site => 1) (fun _ : Site => 1) parameters x hPlanckPlus
      hPlanckMinus haPlus haMinus

/-- Differential of the lapse-weighted total Hamiltonian, site by site. -/
def totalHamiltonianDifferential {Site : Type*}
    (lapsePlus lapseMinus : Site → ℝ)
    (parameters : ReducedParameters) (x : SpatialField Site) :
    FunctionalDifferential Site :=
  fun i => hamiltonianDifferential (lapsePlus i) (lapseMinus i)
    parameters (x i)

/-- Kronecker-supported local functional differential. -/
def singleSiteDifferential {Site : Type*} [DecidableEq Site]
    (site : Site) (df : CanonicalCovector) : FunctionalDifferential Site :=
  fun i => if i = site then df else zeroCovector

theorem local_plus_preservation
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    (site : Site) (lapsePlus lapseMinus : Site → ℝ)
    (parameters : ReducedParameters) (x : SpatialField Site)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : (x site).aPlus ≠ 0)
    (haMinus : (x site).aMinus ≠ 0) :
    finitePoisson
        (singleSiteDifferential site (plusDifferential parameters (x site)))
        (totalHamiltonianDifferential lapsePlus lapseMinus parameters x) =
      lapseMinus site * secondaryConstraint parameters (x site) := by
  rw [finitePoisson, Finset.sum_eq_single site]
  · simpa [singleSiteDifferential, totalHamiltonianDifferential] using
      preserve_plus_is_lapseMinus_times_secondary
        (lapsePlus site) (lapseMinus site) parameters (x site)
          hPlanckPlus hPlanckMinus haPlus haMinus
  · intro j _ hji
    simp [singleSiteDifferential, hji, canonicalPoisson, zeroCovector]
  · simp

theorem local_minus_preservation
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    (site : Site) (lapsePlus lapseMinus : Site → ℝ)
    (parameters : ReducedParameters) (x : SpatialField Site)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : (x site).aPlus ≠ 0)
    (haMinus : (x site).aMinus ≠ 0) :
    finitePoisson
        (singleSiteDifferential site (minusDifferential parameters (x site)))
        (totalHamiltonianDifferential lapsePlus lapseMinus parameters x) =
      -lapsePlus site * secondaryConstraint parameters (x site) := by
  rw [finitePoisson, Finset.sum_eq_single site]
  · simpa [singleSiteDifferential, totalHamiltonianDifferential] using
      preserve_minus_is_neg_lapsePlus_times_secondary
        (lapsePlus site) (lapseMinus site) parameters (x site)
          hPlanckPlus hPlanckMinus haPlus haMinus
  · intro j _ hji
    simp [singleSiteDifferential, hji, canonicalPoisson, zeroCovector]
  · simp

/-- Nonzero minus lapse and local preservation force the secondary constraint
at that same site, without cancellation between sites. -/
theorem secondary_at_site_of_local_primary_preservation
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    (site : Site) (lapsePlus lapseMinus : Site → ℝ)
    (parameters : ReducedParameters) (x : SpatialField Site)
    (hLapseMinus : lapseMinus site ≠ 0)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : (x site).aPlus ≠ 0)
    (haMinus : (x site).aMinus ≠ 0)
    (hPreserve :
      finitePoisson
          (singleSiteDifferential site (plusDifferential parameters (x site)))
          (totalHamiltonianDifferential lapsePlus lapseMinus parameters x) = 0) :
    secondaryConstraint parameters (x site) = 0 := by
  rw [local_plus_preservation site lapsePlus lapseMinus parameters x
    hPlanckPlus hPlanckMinus haPlus haMinus] at hPreserve
  exact (mul_eq_zero.mp hPreserve).resolve_left hLapseMinus

/-- Linear combination of the three local constraint covectors. -/
def constraintCovectorCombination
    (u v w : ℝ) (parameters : ReducedParameters) (x : PhasePoint) :
    CanonicalCovector :=
  { aPlus := u * (plusDifferential parameters x).aPlus +
      v * (minusDifferential parameters x).aPlus +
      w * (secondaryDifferential parameters x).aPlus
    pPlus := u * (plusDifferential parameters x).pPlus +
      v * (minusDifferential parameters x).pPlus +
      w * (secondaryDifferential parameters x).pPlus
    aMinus := u * (plusDifferential parameters x).aMinus +
      v * (minusDifferential parameters x).aMinus +
      w * (secondaryDifferential parameters x).aMinus
    pMinus := u * (plusDifferential parameters x).pMinus +
      v * (minusDifferential parameters x).pMinus +
      w * (secondaryDifferential parameters x).pMinus }

/-- Exact two-site constrained field used for the independence audit. -/
def twoSiteWitness : SpatialField (Fin 2) := fun _ => witnessPoint

theorem twoSiteWitness_lies_on_local_constraint_surfaces (i : Fin 2) :
    plusConstraint witnessParameters (twoSiteWitness i) = 0 ∧
      minusConstraint witnessParameters (twoSiteWitness i) = 0 ∧
      secondaryConstraint witnessParameters (twoSiteWitness i) = 0 := by
  simpa [twoSiteWitness] using witness_lies_on_constraint_surface

/-- The six local covectors (three at either site) are independent at the
two-site witness.  Independence follows at each support, not from a summed
scalar rank surrogate. -/
theorem twoSiteWitness_local_constraint_covectors_independent
    (u v w : Fin 2 → ℝ)
    (hCombination :
      (fun i => constraintCovectorCombination (u i) (v i) (w i)
        witnessParameters (twoSiteWitness i)) = zeroDifferential) :
    ∀ i, u i = 0 ∧ v i = 0 ∧ w i = 0 := by
  intro i
  have hi := congrFun hCombination i
  apply witness_constraint_differentials_independent (u i) (v i) (w i)
  · simpa [constraintCovectorCombination, twoSiteWitness, zeroDifferential,
      zeroCovector] using congrArg CanonicalCovector.aPlus hi
  · simpa [constraintCovectorCombination, twoSiteWitness, zeroDifferential,
      zeroCovector] using congrArg CanonicalCovector.pPlus hi
  · simpa [constraintCovectorCombination, twoSiteWitness, zeroDifferential,
      zeroCovector] using congrArg CanonicalCovector.aMinus hi

/-- At the same two-site constrained field, secondary preservation fixes one
lapse ratio at each site independently. -/
theorem twoSiteWitness_secondary_preservation_fixes_each_lapse_ratio
    (lapsePlus lapseMinus : Fin 2 → ℝ)
    (hPreserve : ∀ i,
      canonicalPoisson
          (secondaryDifferential witnessParameters (twoSiteWitness i))
          (totalHamiltonianDifferential lapsePlus lapseMinus witnessParameters
            twoSiteWitness i) = 0) :
    ∀ i, lapseMinus i = 2 * lapsePlus i := by
  intro i
  have hi := hPreserve i
  change canonicalPoisson
      (secondaryDifferential witnessParameters witnessPoint)
      (hamiltonianDifferential (lapsePlus i) (lapseMinus i)
        witnessParameters witnessPoint) = 0 at hi
  exact witness_secondary_preservation_fixes_lapse_ratio
    (lapsePlus i) (lapseMinus i) hi

end

end P0EFTJanusFiniteSpatialFunctionalPoisson
end JanusFormal
