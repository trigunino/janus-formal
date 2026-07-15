import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction

namespace JanusFormal
namespace P0EFTJanusReducedCrossMatterIntegrability

set_option autoImplicit false

noncomputable section

open P0EFTJanusConvexHelmholtzReconstruction

variable {Configuration : Type*}
variable [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]

/-- Three independent reduced directions: one in each metric sector and one
matter direction.  This is a chart-level audit device, not a full Janus field
space. -/
structure ThreeSectorReducedChart (Configuration : Type*)
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration] where
  plusCoordinate : Configuration →L[ℝ] ℝ
  minusCoordinate : Configuration →L[ℝ] ℝ
  matterCoordinate : Configuration →L[ℝ] ℝ
  plusVariation : Configuration
  minusVariation : Configuration
  matterVariation : Configuration
  plus_on_plus : plusCoordinate plusVariation = 1
  plus_on_minus : plusCoordinate minusVariation = 0
  plus_on_matter : plusCoordinate matterVariation = 0
  minus_on_plus : minusCoordinate plusVariation = 0
  minus_on_minus : minusCoordinate minusVariation = 1
  minus_on_matter : minusCoordinate matterVariation = 0
  matter_on_plus : matterCoordinate plusVariation = 0
  matter_on_minus : matterCoordinate minusVariation = 0
  matter_on_matter : matterCoordinate matterVariation = 1

attribute [simp]
  ThreeSectorReducedChart.plus_on_plus
  ThreeSectorReducedChart.plus_on_minus
  ThreeSectorReducedChart.plus_on_matter
  ThreeSectorReducedChart.minus_on_plus
  ThreeSectorReducedChart.minus_on_minus
  ThreeSectorReducedChart.minus_on_matter
  ThreeSectorReducedChart.matter_on_plus
  ThreeSectorReducedChart.matter_on_minus
  ThreeSectorReducedChart.matter_on_matter

/-- Linear cross-source coefficients.  Each ordered pair is kept separately
until common-action integrability proves reciprocity. -/
structure ReducedCrossSources where
  plusFromMinus : ℝ
  minusFromPlus : ℝ
  plusFromMatter : ℝ
  matterFromPlus : ℝ
  minusFromMatter : ℝ
  matterFromMinus : ℝ

/-- In this rank-one reduced chart, adjointness of each pair of cross blocks
is equality of the two scalar coefficients. -/
def CrossBlocksAdjoint (sources : ReducedCrossSources) : Prop :=
  sources.plusFromMinus = sources.minusFromPlus ∧
    sources.plusFromMatter = sources.matterFromPlus ∧
    sources.minusFromMatter = sources.matterFromMinus

/-- Constant Jacobian of the proposed cross-source one-form. -/
def crossJacobian
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    Configuration →L[ℝ] Configuration →L[ℝ] ℝ :=
  ((sources.plusFromMinus • chart.minusCoordinate).smulRight
      chart.plusCoordinate) +
  ((sources.minusFromPlus • chart.plusCoordinate).smulRight
      chart.minusCoordinate) +
  ((sources.plusFromMatter • chart.matterCoordinate).smulRight
      chart.plusCoordinate) +
  ((sources.matterFromPlus • chart.plusCoordinate).smulRight
      chart.matterCoordinate) +
  ((sources.minusFromMatter • chart.matterCoordinate).smulRight
      chart.minusCoordinate) +
  ((sources.matterFromMinus • chart.minusCoordinate).smulRight
      chart.matterCoordinate)

/-- Linear Euler one-form assembled from the six ordered cross sources. -/
def crossEuler
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) : EulerOneForm Configuration :=
  fun q => crossJacobian chart sources q

theorem crossEuler_hasFDerivAt
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) (q : Configuration) :
    HasFDerivAt (crossEuler chart sources)
      (crossJacobian chart sources) q := by
  exact (crossJacobian chart sources).hasFDerivAt

@[simp]
theorem crossEuler_fderiv
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) (q : Configuration) :
    fderiv ℝ (crossEuler chart sources) q =
      crossJacobian chart sources :=
  (crossEuler_hasFDerivAt chart sources q).fderiv

@[simp]
theorem crossJacobian_minus_plus
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    crossJacobian chart sources chart.minusVariation chart.plusVariation =
      sources.plusFromMinus := by
  simp [crossJacobian]

@[simp]
theorem crossJacobian_plus_minus
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    crossJacobian chart sources chart.plusVariation chart.minusVariation =
      sources.minusFromPlus := by
  simp [crossJacobian]

@[simp]
theorem crossJacobian_matter_plus
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    crossJacobian chart sources chart.matterVariation chart.plusVariation =
      sources.plusFromMatter := by
  simp [crossJacobian]

@[simp]
theorem crossJacobian_plus_matter
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    crossJacobian chart sources chart.plusVariation chart.matterVariation =
      sources.matterFromPlus := by
  simp [crossJacobian]

@[simp]
theorem crossJacobian_matter_minus
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    crossJacobian chart sources chart.matterVariation chart.minusVariation =
      sources.minusFromMatter := by
  simp [crossJacobian]

@[simp]
theorem crossJacobian_minus_matter
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    crossJacobian chart sources chart.minusVariation chart.matterVariation =
      sources.matterFromMinus := by
  simp [crossJacobian]

/-- A common twice differentiable action whose genuine gradient is the stated
cross-source one-form. -/
def HasCommonCrossAction
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) : Prop :=
  ∃ action : Configuration → ℝ,
    ContDiff ℝ 2 action ∧
      ∀ q, HasFDerivAt action (crossEuler chart sources q) q

/-- Necessity: the symmetry of the actual Hessian of one common action forces
all three reduced cross blocks to be adjoint. -/
theorem common_action_forces_cross_blocks_adjoint
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources)
    (action : Configuration → ℝ)
    (hSmooth : ContDiff ℝ 2 action)
    (hGradient : ∀ q, HasFDerivAt action (crossEuler chart sources q) q) :
    CrossBlocksAdjoint sources := by
  have hGradientEq : actionGradient action = crossEuler chart sources := by
    funext q
    exact (hGradient q).fderiv
  have hHelmholtz := action_gradient_helmholtz_at action (0 : Configuration)
    hSmooth.contDiffAt
  rw [hGradientEq] at hHelmholtz
  have hPlusMinus :=
    hHelmholtz chart.minusVariation chart.plusVariation
  have hPlusMatter :=
    hHelmholtz chart.matterVariation chart.plusVariation
  have hMinusMatter :=
    hHelmholtz chart.matterVariation chart.minusVariation
  simp only [crossEuler_fderiv] at hPlusMinus hPlusMatter hMinusMatter
  exact ⟨by simpa using hPlusMinus,
    by simpa using hPlusMatter,
    by simpa using hMinusMatter⟩

/-- Explicit common metric--metric--matter cross action when the ordered
blocks obey reciprocity. -/
def commonCrossAction
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) : Configuration → ℝ :=
  ((fun q => sources.plusFromMinus *
      ((chart.plusCoordinate : Configuration → ℝ) *
        (chart.minusCoordinate : Configuration → ℝ)) q) +
    (fun q => sources.plusFromMatter *
      ((chart.plusCoordinate : Configuration → ℝ) *
        (chart.matterCoordinate : Configuration → ℝ)) q)) +
  (fun q => sources.minusFromMatter *
    ((chart.minusCoordinate : Configuration → ℝ) *
      (chart.matterCoordinate : Configuration → ℝ)) q)

/-- The common cross action has the proposed cross-source one-form as its
genuine Fréchet derivative. -/
theorem commonCrossAction_hasFDerivAt
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources)
    (hAdjoint : CrossBlocksAdjoint sources)
    (q : Configuration) :
    HasFDerivAt (commonCrossAction chart sources)
      (crossEuler chart sources q) q := by
  rcases hAdjoint with ⟨hPlusMinus, hPlusMatter, hMinusMatter⟩
  have hPlus := chart.plusCoordinate.hasFDerivAt (x := q)
  have hMinus := chart.minusCoordinate.hasFDerivAt (x := q)
  have hMatter := chart.matterCoordinate.hasFDerivAt (x := q)
  have hMetricCross :=
    (hPlus.mul hMinus).const_mul sources.plusFromMinus
  have hPlusMatterCross :=
    (hPlus.mul hMatter).const_mul sources.plusFromMatter
  have hMinusMatterCross :=
    (hMinus.mul hMatter).const_mul sources.minusFromMatter
  have hAction := (hMetricCross.add hPlusMatterCross).add hMinusMatterCross
  change HasFDerivAt (commonCrossAction chart sources)
    (crossEuler chart sources q) q
  refine hAction.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro variation
  change _ = crossJacobian chart sources q variation
  unfold crossJacobian
  rw [← hPlusMinus, ← hPlusMatter, ← hMinusMatter]
  simp
  ring

theorem commonCrossAction_contDiff_two
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    ContDiff ℝ 2 (commonCrossAction chart sources) := by
  have hPointwise : commonCrossAction chart sources =
      fun q : Configuration =>
        sources.plusFromMinus * chart.plusCoordinate q * chart.minusCoordinate q +
          sources.plusFromMatter * chart.plusCoordinate q *
            chart.matterCoordinate q +
          sources.minusFromMatter * chart.minusCoordinate q *
            chart.matterCoordinate q := by
    funext q
    simp [commonCrossAction]
    ring
  rw [hPointwise]
  fun_prop

/-- Exact reduced integrability criterion: reciprocal cross blocks are
equivalent to existence of a common C² action with the stated actual gradient. -/
theorem cross_blocks_adjoint_iff_common_action
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources) :
    CrossBlocksAdjoint sources ↔ HasCommonCrossAction chart sources := by
  constructor
  · intro hAdjoint
    exact ⟨commonCrossAction chart sources,
      commonCrossAction_contDiff_two chart sources,
      commonCrossAction_hasFDerivAt chart sources hAdjoint⟩
  · rintro ⟨action, hSmooth, hGradient⟩
    exact common_action_forces_cross_blocks_adjoint
      chart sources action hSmooth hGradient

/-- No-go: a supplied mismatch in any ordered cross block rules out one common
twice differentiable action.  This does not assert that an unspecified model
has such a mismatch. -/
theorem nonadjoint_cross_blocks_no_common_action
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources)
    (hNonAdjoint : ¬ CrossBlocksAdjoint sources) :
    ¬ HasCommonCrossAction chart sources := by
  intro hAction
  exact hNonAdjoint
    ((cross_blocks_adjoint_iff_common_action chart sources).mpr hAction)

/-- In particular, unequal metric--metric cross coefficients already obstruct
one common action, independently of the matter pairs. -/
theorem metric_cross_mismatch_no_common_action
    (chart : ThreeSectorReducedChart Configuration)
    (sources : ReducedCrossSources)
    (hMismatch : sources.plusFromMinus ≠ sources.minusFromPlus) :
    ¬ HasCommonCrossAction chart sources := by
  apply nonadjoint_cross_blocks_no_common_action chart sources
  intro hAdjoint
  exact hMismatch hAdjoint.1

/- A presentation that leaves the cross functionals and their matter
dependence unspecified supplies no `ReducedCrossSources` to which this
criterion can be applied.  The gate therefore does not assign a mismatch to
such a model and does not claim a contradiction. -/

end

end P0EFTJanusReducedCrossMatterIntegrability
end JanusFormal
