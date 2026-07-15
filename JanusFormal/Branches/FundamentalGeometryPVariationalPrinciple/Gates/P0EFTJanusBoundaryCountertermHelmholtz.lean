import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction

/-!
Conditional boundary-counterterm reconstruction on a real normed vector
space.  The boundary flux, trace, and Helmholtz hypotheses are supplied data.
Nothing here constructs or identifies a physical GHY, null-boundary, corner,
or Janus junction functional.
-/

namespace JanusFormal
namespace P0EFTJanusBoundaryCountertermHelmholtz

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusConvexHelmholtzReconstruction

universe u v

variable {Boundary : Type u}
variable [NormedAddCommGroup Boundary] [NormedSpace ℝ Boundary]

/-- Boundary Euler/flux one-form on the declared boundary-data space. -/
abbrev BoundaryFlux (Boundary : Type u)
    [NormedAddCommGroup Boundary] [NormedSpace ℝ Boundary] :=
  EulerOneForm Boundary

/-- Canonical zero-normalized counterterm obtained by negating the radial
primitive of the supplied boundary flux. -/
noncomputable def boundaryCounterterm
    (base : Boundary) (flux : BoundaryFlux Boundary)
    (boundary : Boundary) : ℝ :=
  -radialAction base flux boundary

/-- Under the explicit global Helmholtz/conservativity hypotheses, the
counterterm has genuine Frechet derivative equal to the negative flux. -/
theorem boundaryCounterterm_hasFDerivAt
    (flux : BoundaryFlux Boundary)
    (hDifferentiable : Differentiable ℝ flux)
    (hHelmholtz : ∀ boundary, HelmholtzJacobianAt flux boundary)
    (base boundary : Boundary) :
    HasFDerivAt (boundaryCounterterm base flux) (-flux boundary) boundary := by
  change HasFDerivAt
    (fun point => -radialAction base flux point) (-flux boundary) boundary
  exact (radial_action_hasFDerivAt flux hDifferentiable hHelmholtz
    base boundary).neg

/-- Exact derivative of the reconstructed counterterm. -/
theorem boundaryCounterterm_fderiv
    (flux : BoundaryFlux Boundary)
    (hDifferentiable : Differentiable ℝ flux)
    (hHelmholtz : ∀ boundary, HelmholtzJacobianAt flux boundary)
    (base boundary : Boundary) :
    fderiv ℝ (boundaryCounterterm base flux) boundary = -flux boundary :=
  (boundaryCounterterm_hasFDerivAt flux hDifferentiable hHelmholtz
    base boundary).fderiv

/-- The radial choice fixes the additive ambiguity at the selected base. -/
@[simp]
theorem boundaryCounterterm_at_base
    (base : Boundary) (flux : BoundaryFlux Boundary) :
    boundaryCounterterm base flux base = 0 := by
  simp [boundaryCounterterm]

/-- Existing boundary action plus the reconstructed cancelling counterterm. -/
noncomputable def completedBoundaryAction
    (boundaryAction : Boundary → ℝ)
    (base : Boundary) (flux : BoundaryFlux Boundary)
    (boundary : Boundary) : ℝ :=
  boundaryAction boundary + boundaryCounterterm base flux boundary

/-- If the supplied flux is the actual derivative of the original boundary
action, the completed boundary action has genuine zero derivative. -/
theorem completedBoundaryAction_hasFDerivAt_zero
    (boundaryAction : Boundary → ℝ)
    (flux : BoundaryFlux Boundary)
    (hDifferentiable : Differentiable ℝ flux)
    (hHelmholtz : ∀ boundary, HelmholtzJacobianAt flux boundary)
    (hBoundaryAction : ∀ boundary,
      HasFDerivAt boundaryAction (flux boundary) boundary)
    (base boundary : Boundary) :
    HasFDerivAt (completedBoundaryAction boundaryAction base flux)
      (0 : Boundary →L[ℝ] ℝ) boundary := by
  change HasFDerivAt
    (fun point => boundaryAction point + boundaryCounterterm base flux point)
    (0 : Boundary →L[ℝ] ℝ) boundary
  exact ((hBoundaryAction boundary).add
    (boundaryCounterterm_hasFDerivAt flux hDifferentiable hHelmholtz
      base boundary)).congr_fderiv (add_neg_cancel (flux boundary))

/-- The completed boundary action is constant on the whole boundary-data
space.  Its value is the original boundary action at the normalization base. -/
theorem completedBoundaryAction_eq_base_value
    (boundaryAction : Boundary → ℝ)
    (flux : BoundaryFlux Boundary)
    (hDifferentiable : Differentiable ℝ flux)
    (hHelmholtz : ∀ boundary, HelmholtzJacobianAt flux boundary)
    (hBoundaryAction : ∀ boundary,
      HasFDerivAt boundaryAction (flux boundary) boundary)
    (base boundary : Boundary) :
    completedBoundaryAction boundaryAction base flux boundary =
      boundaryAction base := by
  have hConstant :=
    convex_actions_same_euler_difference_eq_base_difference
      (domain := Set.univ)
      (euler := fun _ => (0 : Boundary →L[ℝ] ℝ))
      (firstAction := completedBoundaryAction boundaryAction base flux)
      (secondAction := fun _ => (0 : ℝ))
      convex_univ
      (by
        intro point _
        exact completedBoundaryAction_hasFDerivAt_zero
          boundaryAction flux hDifferentiable hHelmholtz
          hBoundaryAction base point)
      (by
        intro point _
        exact hasFDerivAt_const (0 : ℝ) point)
      (Set.mem_univ base) (Set.mem_univ boundary)
  simpa [completedBoundaryAction] using hConstant

variable {Field : Type v}
variable [NormedAddCommGroup Field] [NormedSpace ℝ Field]

/-- Bulk action completed by the original boundary action and its cancelling
counterterm after a supplied continuous-linear trace. -/
noncomputable def completedSectorAction
    (trace : Field →L[ℝ] Boundary)
    (bulkAction : Field → ℝ)
    (boundaryAction : Boundary → ℝ)
    (base : Boundary) (flux : BoundaryFlux Boundary)
    (field : Field) : ℝ :=
  bulkAction field +
    completedBoundaryAction boundaryAction base flux (trace field)

/-- Exact bulk-plus-boundary completion: after counterterm cancellation, the
genuine Frechet derivative is precisely the supplied bulk Euler functional. -/
theorem completedSectorAction_hasFDerivAt_bulk
    (trace : Field →L[ℝ] Boundary)
    (bulkAction : Field → ℝ)
    (boundaryAction : Boundary → ℝ)
    (base : Boundary) (flux : BoundaryFlux Boundary)
    (field : Field)
    (bulkEuler : Field →L[ℝ] ℝ)
    (hBulk : HasFDerivAt bulkAction bulkEuler field)
    (hBoundaryAction : ∀ boundary,
      HasFDerivAt boundaryAction (flux boundary) boundary)
    (hDifferentiable : Differentiable ℝ flux)
    (hHelmholtz : ∀ boundary, HelmholtzJacobianAt flux boundary) :
    HasFDerivAt
      (completedSectorAction trace bulkAction boundaryAction base flux)
      bulkEuler field := by
  have hCompletedBoundary := completedBoundaryAction_hasFDerivAt_zero
    boundaryAction flux hDifferentiable hHelmholtz hBoundaryAction
    base (trace field)
  have hTotal := hBulk.add
    (hCompletedBoundary.comp field trace.hasFDerivAt)
  change HasFDerivAt
    (fun point => bulkAction point +
      completedBoundaryAction boundaryAction base flux (trace point))
    bulkEuler field
  exact hTotal.congr_fderiv (by simp)

/-- Any two actual cancelling counterterms differ by an additive constant. -/
theorem cancelling_counterterms_differ_by_constant
    (flux : BoundaryFlux Boundary)
    (firstCounterterm secondCounterterm : Boundary → ℝ)
    (hFirst : ∀ boundary,
      HasFDerivAt firstCounterterm (-flux boundary) boundary)
    (hSecond : ∀ boundary,
      HasFDerivAt secondCounterterm (-flux boundary) boundary) :
    ∃ constant : ℝ, ∀ boundary,
      firstCounterterm boundary = secondCounterterm boundary + constant := by
  simpa using
    (convex_actions_same_euler_differ_by_constant
      (domain := Set.univ)
      (euler := fun boundary => -flux boundary)
      (firstAction := firstCounterterm)
      (secondAction := secondCounterterm)
      convex_univ Set.univ_nonempty
      (by intro boundary _; exact hFirst boundary)
      (by intro boundary _; exact hSecond boundary))

/-- Base normalization removes the additive ambiguity: the reconstructed
counterterm is the unique actual cancelling action vanishing at the base. -/
theorem normalized_boundaryCounterterm_unique
    (flux : BoundaryFlux Boundary)
    (hDifferentiable : Differentiable ℝ flux)
    (hHelmholtz : ∀ boundary, HelmholtzJacobianAt flux boundary)
    (base : Boundary)
    (candidate : Boundary → ℝ)
    (hCandidate : ∀ boundary,
      HasFDerivAt candidate (-flux boundary) boundary)
    (hCandidateBase : candidate base = 0) :
    candidate = boundaryCounterterm base flux := by
  have hCanonical : ∀ boundary,
      HasFDerivAt (boundaryCounterterm base flux)
        (-flux boundary) boundary :=
    boundaryCounterterm_hasFDerivAt flux hDifferentiable hHelmholtz base
  have hBaseEquality :
      candidate base = boundaryCounterterm base flux base := by
    rw [hCandidateBase, boundaryCounterterm_at_base]
  have hEqOn := convex_actions_same_euler_eqOn_of_eq_at_base
    (domain := Set.univ)
    (euler := fun boundary => -flux boundary)
    (firstAction := candidate)
    (secondAction := boundaryCounterterm base flux)
    convex_univ
    (by intro boundary _; exact hCandidate boundary)
    (by intro boundary _; exact hCanonical boundary)
    (Set.mem_univ base) hBaseEquality
  funext boundary
  exact hEqOn (Set.mem_univ boundary)

/-- Necessity of Helmholtz symmetry for any twice-differentiable actual
cancelling counterterm. -/
theorem actual_smooth_counterterm_implies_helmholtz_at
    (flux : BoundaryFlux Boundary)
    (boundary : Boundary)
    (hFluxDifferentiable : DifferentiableAt ℝ flux boundary)
    (counterterm : Boundary → ℝ)
    (hCountertermSmooth : ContDiffAt ℝ 2 counterterm boundary)
    (hCounterterm : ∀ point,
      HasFDerivAt counterterm (-flux point) point) :
    HelmholtzJacobianAt flux boundary := by
  have hGradientEquality :
      actionGradient counterterm = fun point => -flux point := by
    funext point
    exact (hCounterterm point).fderiv
  have hCountertermHelmholtz :=
    action_gradient_helmholtz_at counterterm boundary hCountertermSmooth
  rw [hGradientEquality] at hCountertermHelmholtz
  have hNegativeDerivative :
      fderiv ℝ (fun point => -flux point) boundary =
        -fderiv ℝ flux boundary :=
    hFluxDifferentiable.hasFDerivAt.neg.fderiv
  intro first second
  have hSymmetric := hCountertermHelmholtz first second
  rw [hNegativeDerivative] at hSymmetric
  simpa using hSymmetric

/-- A differentiable flux whose actual Jacobian is non-Helmholtz at one point
cannot be cancelled by any globally actual, twice-differentiable counterterm. -/
theorem nonhelmholtz_flux_blocks_smooth_counterterm
    (flux : BoundaryFlux Boundary)
    (boundary : Boundary)
    (hFluxDifferentiable : DifferentiableAt ℝ flux boundary)
    (hNonHelmholtz : ¬ HelmholtzJacobianAt flux boundary) :
    ¬ ∃ counterterm : Boundary → ℝ,
      ContDiffAt ℝ 2 counterterm boundary ∧
      ∀ point, HasFDerivAt counterterm (-flux point) point := by
  rintro ⟨counterterm, hSmooth, hCounterterm⟩
  exact hNonHelmholtz
    (actual_smooth_counterterm_implies_helmholtz_at
      flux boundary hFluxDifferentiable counterterm hSmooth hCounterterm)

end

end P0EFTJanusBoundaryCountertermHelmholtz
end JanusFormal
