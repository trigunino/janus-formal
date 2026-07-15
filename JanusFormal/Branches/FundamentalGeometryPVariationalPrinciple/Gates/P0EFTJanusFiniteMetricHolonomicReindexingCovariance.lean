import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteMetricHolonomicScalarVariation

/-!
# Finite metric-holonomic covariance under site reindexing

This gate treats an equivalence of finite site types as a discrete change of
labels.  The periodic shift is transported by conjugation, while fields and
variations are transported by precomposition with the inverse equivalence.
The metric-holonomic action, its first variation, its strong Euler equation,
and stationarity are exactly invariant or covariant under this transport.

This is only covariance under a bijection of a finite periodic site set.  It
is not spacetime diffeomorphism covariance, a continuum tensorial statement,
or a local conservation law.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteMetricHolonomicReindexingCovariance

set_option autoImplicit false

noncomputable section

open P0EFTJanusFinitePeriodicHolonomicScalarVariation
open P0EFTJanusFiniteMetricHolonomicScalarVariation

/-- Conjugation of a periodic shift by a bijection of finite site types. -/
def transportShift {Site Target : Type*} (reindex : Site ≃ Target)
    (shift : Equiv.Perm Site) : Equiv.Perm Target :=
  reindex.symm.trans (shift.trans reindex)

/-- Transport a scalar field from the source sites to the relabelled sites. -/
def transportField {Site Target : Type*} (reindex : Site ≃ Target)
    (field : ScalarField Site) : ScalarField Target :=
  fun target => field (reindex.symm target)

/-- Pull a scalar field on the relabelled sites back to the source sites. -/
def pullbackField {Site Target : Type*} (reindex : Site ≃ Target)
    (field : ScalarField Target) : ScalarField Site :=
  fun site => field (reindex site)

@[simp] theorem transportShift_apply {Site Target : Type*}
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site) (site : Site) :
    transportShift reindex shift (reindex site) = reindex (shift site) := by
  simp [transportShift]

@[simp] theorem transportShift_symm {Site Target : Type*}
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site) :
    (transportShift reindex shift).symm =
      transportShift reindex shift.symm := by
  ext target
  simp [transportShift]

@[simp] theorem transportField_apply {Site Target : Type*}
    (reindex : Site ≃ Target) (field : ScalarField Site) (site : Site) :
    transportField reindex field (reindex site) = field site := by
  simp [transportField]

@[simp] theorem pullback_transportField {Site Target : Type*}
    (reindex : Site ≃ Target) (field : ScalarField Site) :
    pullbackField reindex (transportField reindex field) = field := by
  funext site
  simp [pullbackField, transportField]

@[simp] theorem transport_pullbackField {Site Target : Type*}
    (reindex : Site ≃ Target) (field : ScalarField Target) :
    transportField reindex (pullbackField reindex field) = field := by
  funext target
  simp [pullbackField, transportField]

/-- The transported discrete gradient is the transport of the original
discrete gradient. -/
theorem discreteGradient_transport {Site Target : Type*}
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site)
    (field : ScalarField Site) :
    discreteGradient (transportShift reindex shift)
        (transportField reindex field) =
      transportField reindex (discreteGradient shift field) := by
  funext target
  simp [discreteGradient, transportShift, transportField]

theorem discreteGradient_transport_apply {Site Target : Type*}
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site)
    (field : ScalarField Site) (site : Site) :
    discreteGradient (transportShift reindex shift)
        (transportField reindex field) (reindex site) =
      discreteGradient shift field site := by
  rw [discreteGradient_transport]
  simp [transportField]

/-- Exact invariance of the metric-holonomic action under finite relabelling. -/
theorem metricHolonomicAction_transport {Site Target : Type*}
    [Fintype Site] [Fintype Target]
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site)
    (massSquared metric : ℝ) (field : ScalarField Site) :
    metricHolonomicAction (transportShift reindex shift) massSquared metric
        (transportField reindex field) =
      metricHolonomicAction shift massSquared metric field := by
  unfold metricHolonomicAction scalarAction
  simpa [discreteGradient, transportShift, transportField] using
    (reindex.symm.sum_comp
      (fun site =>
        metricKineticWeight metric / 2 *
            (discreteGradient shift field site) ^ 2 +
          metricMassWeight metric massSquared / 2 * (field site) ^ 2))

/-- Exact covariance of the simultaneous metric/field first variation. -/
theorem metricHolonomicFirstVariation_transport {Site Target : Type*}
    [Fintype Site] [Fintype Target]
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site)
    (massSquared metric metricVariation : ℝ)
    (field variation : ScalarField Site) :
    metricHolonomicFirstVariation (transportShift reindex shift) massSquared
        metric metricVariation (transportField reindex field)
          (transportField reindex variation) =
      metricHolonomicFirstVariation shift massSquared metric metricVariation
        field variation := by
  unfold metricHolonomicFirstVariation
  simpa [discreteGradient, transportShift, transportField] using
    (reindex.symm.sum_comp
      (fun site =>
        metricKineticWeightVariation metric metricVariation / 2 *
              (discreteGradient shift field site) ^ 2 +
            metricKineticWeight metric * discreteGradient shift field site *
              discreteGradient shift variation site +
          metricMassWeightVariation metric metricVariation massSquared / 2 *
              (field site) ^ 2 +
            metricMassWeight metric massSquared * field site * variation site))

/-- The fixed-metric strong Euler field is equivariant under relabelling. -/
theorem strongEuler_transport {Site Target : Type*}
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site)
    (massSquared metric : ℝ) (field : ScalarField Site) :
    strongEuler (transportShift reindex shift)
        (metricKineticWeight metric) (metricMassWeight metric massSquared)
          (transportField reindex field) =
      transportField reindex
        (strongEuler shift (metricKineticWeight metric)
          (metricMassWeight metric massSquared) field) := by
  funext target
  simp [strongEuler, discreteGradient, transportShift, transportField]

theorem strongEuler_transport_apply {Site Target : Type*}
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site)
    (massSquared metric : ℝ) (field : ScalarField Site) (site : Site) :
    strongEuler (transportShift reindex shift)
        (metricKineticWeight metric) (metricMassWeight metric massSquared)
          (transportField reindex field) (reindex site) =
      strongEuler shift (metricKineticWeight metric)
        (metricMassWeight metric massSquared) field site := by
  rw [strongEuler_transport]
  simp [transportField]

/-- Fixed-metric stationarity is independent of the names of the finite
sites. -/
theorem fixedMetric_stationary_transport_iff {Site Target : Type*}
    [Fintype Site] [Fintype Target]
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site)
    (massSquared metric : ℝ) (field : ScalarField Site) :
    (∀ variation : ScalarField Target,
      metricHolonomicFirstVariation (transportShift reindex shift)
          massSquared metric 0 (transportField reindex field) variation = 0) ↔
      ∀ variation : ScalarField Site,
        metricHolonomicFirstVariation shift massSquared metric 0
          field variation = 0 := by
  constructor
  · intro h variation
    rw [← metricHolonomicFirstVariation_transport reindex shift massSquared
      metric 0 field variation]
    exact h (transportField reindex variation)
  · intro h variation
    calc
      metricHolonomicFirstVariation (transportShift reindex shift)
          massSquared metric 0 (transportField reindex field) variation =
        metricHolonomicFirstVariation (transportShift reindex shift)
          massSquared metric 0 (transportField reindex field)
            (transportField reindex (pullbackField reindex variation)) := by
              rw [transport_pullbackField]
      _ = metricHolonomicFirstVariation shift massSquared metric 0 field
          (pullbackField reindex variation) :=
            metricHolonomicFirstVariation_transport reindex shift massSquared
              metric 0 field (pullbackField reindex variation)
      _ = 0 := h (pullbackField reindex variation)

/-- Combined finite reindexing gate: action invariance, first-variation
covariance, strong-Euler covariance, and stationarity equivalence. -/
theorem finiteMetricHolonomicReindexingCovariance_gate
    {Site Target : Type*} [Fintype Site] [Fintype Target]
    (reindex : Site ≃ Target) (shift : Equiv.Perm Site)
    (massSquared metric metricVariation : ℝ)
    (field variation : ScalarField Site) :
    metricHolonomicAction (transportShift reindex shift) massSquared metric
          (transportField reindex field) =
        metricHolonomicAction shift massSquared metric field ∧
      metricHolonomicFirstVariation (transportShift reindex shift) massSquared
          metric metricVariation (transportField reindex field)
            (transportField reindex variation) =
        metricHolonomicFirstVariation shift massSquared metric metricVariation
          field variation ∧
      strongEuler (transportShift reindex shift)
          (metricKineticWeight metric) (metricMassWeight metric massSquared)
            (transportField reindex field) =
        transportField reindex
          (strongEuler shift (metricKineticWeight metric)
            (metricMassWeight metric massSquared) field) := by
  exact ⟨metricHolonomicAction_transport reindex shift massSquared metric field,
    metricHolonomicFirstVariation_transport reindex shift massSquared metric
      metricVariation field variation,
    strongEuler_transport reindex shift massSquared metric field⟩

end

end P0EFTJanusFiniteMetricHolonomicReindexingCovariance
end JanusFormal
