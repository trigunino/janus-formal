import Mathlib

/-!
# Finite periodic holonomic scalar variation

On a finite site type equipped with a permutation, the discrete forward
gradient is induced from one scalar field.  The kinetic-plus-mass action is a
genuine finite sum.  Its derivative is proved along every scalar-field line,
so the gradient variation is necessarily the gradient of the field variation.
Reindexing by the inverse permutation gives summation by parts and a strong
nearest-neighbour Euler expression.

This is a finite periodic network model.  It is not a continuum covariant
matter PDE, a spacetime stress tensor, or a continuum boundary theorem.
-/

namespace JanusFormal
namespace P0EFTJanusFinitePeriodicHolonomicScalarVariation

set_option autoImplicit false

noncomputable section

/-- A scalar field on the finite periodic site set. -/
abbrev ScalarField (Site : Type*) := Site -> Real

/-- Forward difference induced by the scalar field and the site permutation. -/
def discreteGradient {Site : Type*} (shift : Equiv.Perm Site)
    (field : ScalarField Site) : ScalarField Site :=
  fun site => field (shift site) - field site

/-- The only admitted variation curve: an affine line in scalar-field space. -/
def fieldLine {Site : Type*} (field variation : ScalarField Site)
    (epsilon : Real) : ScalarField Site :=
  fun site => field site + epsilon * variation site

theorem discreteGradient_fieldLine {Site : Type*}
    (shift : Equiv.Perm Site) (field variation : ScalarField Site)
    (epsilon : Real) :
    discreteGradient shift (fieldLine field variation epsilon) =
      fieldLine (discreteGradient shift field)
        (discreteGradient shift variation) epsilon := by
  funext site
  simp [discreteGradient, fieldLine]
  ring

/-- Finite kinetic-plus-mass scalar action. -/
def scalarAction {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (kinetic massSquared : Real)
    (field : ScalarField Site) : Real :=
  ∑ site, (kinetic / 2 * (discreteGradient shift field site) ^ 2 +
    massSquared / 2 * (field site) ^ 2)

/-- First variation with the holonomically induced gradient variation. -/
def scalarActionFirstVariation {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (kinetic massSquared : Real)
    (field variation : ScalarField Site) : Real :=
  ∑ site, (
    kinetic * discreteGradient shift field site *
        discreteGradient shift variation site +
      massSquared * field site * variation site)

private theorem affineLine_hasDerivAt (base tangent : Real) :
    HasDerivAt (fun epsilon : Real => base + epsilon * tangent) tangent 0 := by
  simpa using
    ((hasDerivAt_id (x := (0 : Real))).mul_const tangent).const_add base

theorem discreteGradient_fieldLine_hasDerivAt {Site : Type*}
    (shift : Equiv.Perm Site) (field variation : ScalarField Site)
    (site : Site) :
    HasDerivAt
      (fun epsilon =>
        discreteGradient shift (fieldLine field variation epsilon) site)
      (discreteGradient shift variation site) 0 := by
  have h := affineLine_hasDerivAt
    (discreteGradient shift field site)
    (discreteGradient shift variation site)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro epsilon
  simp [discreteGradient, fieldLine]
  ring

/-- The displayed first variation is the actual derivative along every field
variation; no independent gradient tangent is supplied. -/
theorem scalarAction_fieldLine_hasDerivAt {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (kinetic massSquared : Real)
    (field variation : ScalarField Site) :
    HasDerivAt
      (fun epsilon => scalarAction shift kinetic massSquared
        (fieldLine field variation epsilon))
      (scalarActionFirstVariation shift kinetic massSquared field variation) 0 := by
  unfold scalarAction scalarActionFirstVariation
  apply HasDerivAt.fun_sum
  intro site _
  have hGradient := discreteGradient_fieldLine_hasDerivAt
    shift field variation site
  have hField := affineLine_hasDerivAt (field site) (variation site)
  have hRaw :=
    ((hGradient.mul hGradient).const_mul (kinetic / 2)).add
      ((hField.mul hField).const_mul (massSquared / 2))
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [pow_two, fieldLine]
  · simp [discreteGradient, fieldLine]
    ring

/-- Periodic summation by parts, obtained by reindexing the forward term with
the inverse permutation. -/
theorem discrete_summation_by_parts {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (field variation : ScalarField Site) :
    (∑ site, discreteGradient shift field site *
        discreteGradient shift variation site) =
      ∑ site,
        (discreteGradient shift field (shift.symm site) -
          discreteGradient shift field site) * variation site := by
  have hReindex :
      (∑ site, discreteGradient shift field site * variation (shift site)) =
        ∑ site,
          discreteGradient shift field (shift.symm site) * variation site := by
    refine Fintype.sum_equiv shift
      (fun site => discreteGradient shift field site * variation (shift site))
      (fun site =>
        discreteGradient shift field (shift.symm site) * variation site) ?_
    intro site
    simp
  calc
    (∑ site, discreteGradient shift field site *
        discreteGradient shift variation site) =
        (∑ site, discreteGradient shift field site * variation (shift site)) -
          ∑ site, discreteGradient shift field site * variation site := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro site _
      simp [discreteGradient]
      ring
    _ = (∑ site,
          discreteGradient shift field (shift.symm site) * variation site) -
          ∑ site, discreteGradient shift field site * variation site := by
      rw [hReindex]
    _ = ∑ site,
        (discreteGradient shift field (shift.symm site) -
          discreteGradient shift field site) * variation site := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro site _
      ring

/-- Strong discrete Euler expression, with the backward neighbour supplied by
the inverse permutation. -/
def strongEuler {Site : Type*} (shift : Equiv.Perm Site)
    (kinetic massSquared : Real) (field : ScalarField Site) :
    ScalarField Site :=
  fun site =>
    kinetic *
        (discreteGradient shift field (shift.symm site) -
          discreteGradient shift field site) +
      massSquared * field site

theorem strongEuler_eq_nearestNeighbour {Site : Type*}
    (shift : Equiv.Perm Site) (kinetic massSquared : Real)
    (field : ScalarField Site) (site : Site) :
    strongEuler shift kinetic massSquared field site =
      kinetic *
          (2 * field site - field (shift site) - field (shift.symm site)) +
        massSquared * field site := by
  unfold strongEuler discreteGradient
  rw [shift.apply_symm_apply]
  ring

/-- Weak first variation equals the pairing with the strong Euler expression. -/
theorem scalarActionFirstVariation_eq_strongEuler_pairing
    {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (kinetic massSquared : Real)
    (field variation : ScalarField Site) :
    scalarActionFirstVariation shift kinetic massSquared field variation =
      ∑ site, strongEuler shift kinetic massSquared field site * variation site := by
  unfold scalarActionFirstVariation
  calc
    (∑ site, (
      kinetic * discreteGradient shift field site *
          discreteGradient shift variation site +
        massSquared * field site * variation site)) =
        kinetic *
            (∑ site, discreteGradient shift field site *
              discreteGradient shift variation site) +
          massSquared * (∑ site, field site * variation site) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    _ = kinetic *
          (∑ site,
            (discreteGradient shift field (shift.symm site) -
              discreteGradient shift field site) * variation site) +
          massSquared * (∑ site, field site * variation site) := by
      rw [discrete_summation_by_parts shift field variation]
    _ = ∑ site,
        strongEuler shift kinetic massSquared field site * variation site := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro site _
      simp [strongEuler]
      ring

/-- Vanishing against every scalar variation is equivalent to the strong
finite-site Euler equation. -/
theorem stationary_iff_strongEuler_eq_zero
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    (shift : Equiv.Perm Site) (kinetic massSquared : Real)
    (field : ScalarField Site) :
    (∀ variation : ScalarField Site,
      scalarActionFirstVariation shift kinetic massSquared field variation = 0) ↔
      strongEuler shift kinetic massSquared field = 0 := by
  constructor
  · intro hStationary
    funext site
    have hSite := hStationary (fun index => if index = site then 1 else 0)
    rw [scalarActionFirstVariation_eq_strongEuler_pairing] at hSite
    simpa using hSite
  · intro hEuler variation
    rw [scalarActionFirstVariation_eq_strongEuler_pairing, hEuler]
    simp

/-- Sum of two independent periodic scalar sectors. -/
def twoSectorAction {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site)
    (plusKinetic plusMassSquared minusKinetic minusMassSquared : Real)
    (plusField minusField : ScalarField Site) : Real :=
  scalarAction shift plusKinetic plusMassSquared plusField +
    scalarAction shift minusKinetic minusMassSquared minusField

theorem twoSectorAction_fieldLines_hasDerivAt
    {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site)
    (plusKinetic plusMassSquared minusKinetic minusMassSquared : Real)
    (plusField minusField plusVariation minusVariation : ScalarField Site) :
    HasDerivAt
      (fun epsilon => twoSectorAction shift
        plusKinetic plusMassSquared minusKinetic minusMassSquared
        (fieldLine plusField plusVariation epsilon)
        (fieldLine minusField minusVariation epsilon))
      (scalarActionFirstVariation shift plusKinetic plusMassSquared
          plusField plusVariation +
        scalarActionFirstVariation shift minusKinetic minusMassSquared
          minusField minusVariation) 0 := by
  exact (scalarAction_fieldLine_hasDerivAt shift plusKinetic plusMassSquared
    plusField plusVariation).add
      (scalarAction_fieldLine_hasDerivAt shift minusKinetic minusMassSquared
        minusField minusVariation)

/-- Exact zero mixed finite response of the two independent sectors. -/
theorem twoSector_mixed_increment_eq_zero
    {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site)
    (plusKinetic plusMassSquared minusKinetic minusMassSquared : Real)
    (plusField minusField plusVariation minusVariation : ScalarField Site) :
    (twoSectorAction shift
        plusKinetic plusMassSquared minusKinetic minusMassSquared
        (fieldLine plusField plusVariation 1)
        (fieldLine minusField minusVariation 1) -
      twoSectorAction shift
        plusKinetic plusMassSquared minusKinetic minusMassSquared
        (fieldLine plusField plusVariation 1) minusField) -
    (twoSectorAction shift
        plusKinetic plusMassSquared minusKinetic minusMassSquared
        plusField (fieldLine minusField minusVariation 1) -
      twoSectorAction shift
        plusKinetic plusMassSquared minusKinetic minusMassSquared
        plusField minusField) = 0 := by
  simp [twoSectorAction]

end

end P0EFTJanusFinitePeriodicHolonomicScalarVariation
end JanusFormal
