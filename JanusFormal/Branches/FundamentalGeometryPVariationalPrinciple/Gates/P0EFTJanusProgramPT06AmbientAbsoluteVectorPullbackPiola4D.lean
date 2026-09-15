import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D

/-!
# Ambient absolute vector-pullback Piola law

Gate 1050 proves the signed ambient Piola law.  This gate uses continuity and
nonvanishing of the local transition determinant to split its germ into the
positive and negative cases.  The absolute vector-density pullback therefore
has divergence equal to the positive Jacobian density times target divergence.

The absolute pullback preserves signed face flux only under the explicit
orientation condition `det J > 0`; that sign does not follow from the current
transition datum.  All results remain point-local and coordinate-volume based.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Module Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D
open P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D

/-- Absolute vector-density pullback through ambient coordinate maps. -/
def programPT06AmbientAbsoluteVectorPullback
    (forward reverse current : ProgramPT06AmbientCurrent4D) :
    ProgramPT06AmbientCurrent4D :=
  fun coordinate =>
    |LinearMap.det (fderiv Real forward coordinate).toLinearMap| •
      fderiv Real reverse (forward coordinate) (current (forward coordinate))

/-- Ambient coordinate divergence depends only on the germ of a current. -/
theorem programPT06AmbientCoordinateDivergence_congr
    {first second : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hCurrents : first =ᶠ[𝓝 coordinate] second) :
    programPT06AmbientCoordinateDivergence first coordinate =
      programPT06AmbientCoordinateDivergence second coordinate := by
  unfold programPT06AmbientCoordinateDivergence
  rw [hCurrents.fderiv_eq]

/-- Ambient coordinate divergence changes sign under pointwise negation. -/
theorem programPT06AmbientCoordinateDivergence_neg
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientCoordinateDivergence (fun nearby => -current nearby)
        coordinate =
      -programPT06AmbientCoordinateDivergence current coordinate := by
  simp [programPT06AmbientCoordinateDivergence, fderiv_fun_neg]

variable (period : Real) (hPeriod : period ≠ 0)

/-- Absolute pullback through Gate 1048's collar transition and its chosen
local inverse. -/
def programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D) : ProgramPT06AmbientCurrent4D :=
  programPT06AmbientAbsoluteVectorPullback datum.transition
    (programPT06WarpedNullCollarInverseTransition period hPeriod datum) current

/-- The nonzero transition determinant has a constant strict sign throughout
a neighborhood of the selected face point. -/
theorem programPT06WarpedNullCollarTransitionSignedJacobian_sign_eventually
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    (0 < programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum ∧
        ∀ᶠ nearby in 𝓝 (programPT06WarpedNullHyperplaneEmbedding source),
          0 < LinearMap.det
            (fderiv Real datum.transition nearby).toLinearMap) ∨
      (programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum < 0 ∧
        ∀ᶠ nearby in 𝓝 (programPT06WarpedNullHyperplaneEmbedding source),
          LinearMap.det
            (fderiv Real datum.transition nearby).toLinearMap < 0) := by
  let coordinate := programPT06WarpedNullHyperplaneEmbedding source
  let determinant := fun nearby =>
    LinearMap.det (fderiv Real datum.transition nearby).toLinearMap
  have hForward : ContDiffAt Real 2 datum.transition coordinate :=
    (datum.transition_isLocalDiffeomorphAt.contMDiffAt.contDiffAt).of_le
      (by norm_num)
  have hJacobian : ContDiffAt Real 1
      (fderiv Real datum.transition) coordinate :=
    hForward.fderiv_right (m := 1) (by norm_num)
  have hDeterminant : ContinuousAt determinant coordinate :=
    ((programPT06AmbientEndomorphismDeterminant_contDiff.contDiffAt.of_le
      (by norm_num)).comp coordinate hJacobian).continuousAt
  have hValue : determinant coordinate =
      programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum := by
    exact (programPT06WarpedNullCollarTransitionSignedJacobian_eq_fderiv
      period hPeriod datum).symm
  have hNonzero : determinant coordinate ≠ 0 := by
    rw [hValue]
    have hAbsPositive :
        0 < |programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum| := by
      rw [programPT06WarpedNullCollarTransitionSignedJacobian_abs
        period hPeriod datum]
      exact programPT06WarpedNullCollarTransitionJacobianDensity_pos
        period hPeriod datum
    exact abs_pos.mp hAbsPositive
  change
    (0 < programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum ∧
        ∀ᶠ nearby in 𝓝 coordinate, 0 < determinant nearby) ∨
      (programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum < 0 ∧
        ∀ᶠ nearby in 𝓝 coordinate, determinant nearby < 0)
  rcases hNonzero.lt_or_gt with hNegative | hPositive
  · exact Or.inr ⟨by rwa [← hValue],
      hDeterminant.eventually (gt_mem_nhds hNegative)⟩
  · exact Or.inl ⟨by rwa [← hValue],
      hDeterminant.eventually (lt_mem_nhds hPositive)⟩

/-- Absolute ambient Piola law for the point-local collar transition. -/
theorem programPT06WarpedNullCollarTransitionAbsolutePullback_divergence
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06AmbientCoordinateDivergence
        (programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullCollarTransitionJacobianDensity
          period hPeriod datum *
        programPT06AmbientCoordinateDivergence current
          (programPT06WarpedNullHyperplaneEmbedding source) := by
  rcases programPT06WarpedNullCollarTransitionSignedJacobian_sign_eventually
      period hPeriod datum with
    ⟨hPositive, hEventuallyPositive⟩ |
    ⟨hNegative, hEventuallyNegative⟩
  · have hPullback :
        programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
            period hPeriod datum current =ᶠ[
          𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
        programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum current :=
      hEventuallyPositive.mono fun nearby hNearby => by
        unfold programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
          programPT06AmbientAbsoluteVectorPullback
          programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          programPT06AmbientSignedVectorPullback
        rw [abs_eq_self.mpr hNearby.le]
    calc
      _ = programPT06AmbientCoordinateDivergence
          (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
            period hPeriod datum current)
          (programPT06WarpedNullHyperplaneEmbedding source) :=
        programPT06AmbientCoordinateDivergence_congr hPullback
      _ = programPT06WarpedNullCollarTransitionSignedJacobian
            period hPeriod datum *
          programPT06AmbientCoordinateDivergence current
            (programPT06WarpedNullHyperplaneEmbedding source) :=
        programPT06WarpedNullCollarTransition_divergence_eq_signedJacobian_mul
          period hPeriod datum current hCurrent
      _ = _ := by
        rw [← programPT06WarpedNullCollarTransitionSignedJacobian_abs
          period hPeriod datum, abs_eq_self.mpr hPositive.le]
  · have hPullback :
        programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
            period hPeriod datum current =ᶠ[
          𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
        fun nearby =>
          -programPT06WarpedNullCollarTransitionSignedPullbackCurrent
            period hPeriod datum current nearby :=
      hEventuallyNegative.mono fun nearby hNearby => by
        unfold programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
          programPT06AmbientAbsoluteVectorPullback
          programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          programPT06AmbientSignedVectorPullback
        rw [abs_eq_neg_self.mpr hNearby.le, neg_smul]
    calc
      _ = programPT06AmbientCoordinateDivergence
          (fun nearby =>
            -programPT06WarpedNullCollarTransitionSignedPullbackCurrent
              period hPeriod datum current nearby)
          (programPT06WarpedNullHyperplaneEmbedding source) :=
        programPT06AmbientCoordinateDivergence_congr hPullback
      _ = -programPT06AmbientCoordinateDivergence
          (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
            period hPeriod datum current)
          (programPT06WarpedNullHyperplaneEmbedding source) :=
        programPT06AmbientCoordinateDivergence_neg _ _
      _ = -(programPT06WarpedNullCollarTransitionSignedJacobian
            period hPeriod datum *
          programPT06AmbientCoordinateDivergence current
            (programPT06WarpedNullHyperplaneEmbedding source)) := by
        rw [programPT06WarpedNullCollarTransition_divergence_eq_signedJacobian_mul
          period hPeriod datum current hCurrent]
      _ = _ := by
        rw [← programPT06WarpedNullCollarTransitionSignedJacobian_abs
          period hPeriod datum, abs_eq_neg_self.mpr hNegative.le]
        ring

/-- For an orientation-preserving transition, absolute and signed pullbacks
agree throughout the face-point germ. -/
theorem programPT06WarpedNullCollarTransitionAbsolute_eventuallyEq_signed
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D)
    (hOrientation : 0 <
      programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum) :
    programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
        period hPeriod datum current =ᶠ[
      𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
      programPT06WarpedNullCollarTransitionSignedPullbackCurrent
        period hPeriod datum current := by
  rcases programPT06WarpedNullCollarTransitionSignedJacobian_sign_eventually
      period hPeriod datum with
    ⟨_, hEventuallyPositive⟩ | ⟨hNegative, _⟩
  · exact hEventuallyPositive.mono fun nearby hNearby => by
      unfold programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
        programPT06AmbientAbsoluteVectorPullback
        programPT06WarpedNullCollarTransitionSignedPullbackCurrent
        programPT06AmbientSignedVectorPullback
      rw [abs_eq_self.mpr hNearby.le]
  · exact (lt_asymm hOrientation hNegative).elim

/-- Under positive orientation, the absolute pullback preserves the signed
face-flux coefficient. -/
theorem programPT06WarpedNullCollarTransitionAbsolute_fluxRestriction_eq
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D)
    (hOrientation : 0 <
      programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum) :
    programPT06WarpedNullHyperplaneFluxRestriction
        (programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
          period hPeriod datum current) source =
      programPT06WarpedNullHyperplaneFluxRestriction current source := by
  have hPullback :=
    programPT06WarpedNullCollarTransitionAbsolute_eventuallyEq_signed
      period hPeriod datum current hOrientation
  calc
    _ = programPT06WarpedNullHyperplaneFluxRestriction
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum current) source := by
      simp only [programPT06WarpedNullHyperplaneFluxRestriction_apply]
      unfold programPT06NullFaceFluxPullback programPT06ThreeFormPullback
        programPT06AmbientFluxThreeForm
      rw [hPullback.eq_of_nhds]
    _ = _ := programPT06WarpedNullCollarTransition_fluxRestriction_eq
      period hPeriod datum current

/-- The absolute pullback of the affine collar current has positive-Jacobian
divergence density. -/
theorem programPT06WarpedNullCollarTransitionAbsolute_affineDivergence
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (hDensity : DifferentiableAt Real density source) :
    programPT06AmbientCoordinateDivergence
        (programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
          period hPeriod datum
          (programPT06WarpedNullCollarAffineFluxExtension density))
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullCollarTransitionJacobianDensity
        period hPeriod datum * density source := by
  have hAffine : DifferentiableAt Real
      (programPT06WarpedNullCollarAffineFluxExtension density)
      (programPT06WarpedNullHyperplaneEmbedding source) := by
    rw [← programPT06WarpedNullCollar_zeroSlice source]
    exact (programPT06WarpedNullCollarAffineFluxExtension_hasFDerivAt
      (coordinate := (source, 0)) hDensity).differentiableAt
  calc
    _ = programPT06WarpedNullCollarTransitionJacobianDensity
          period hPeriod datum *
        programPT06AmbientCoordinateDivergence
          (programPT06WarpedNullCollarAffineFluxExtension density)
          (programPT06WarpedNullHyperplaneEmbedding source) :=
      programPT06WarpedNullCollarTransitionAbsolutePullback_divergence
        period hPeriod datum _ hAffine
    _ = _ := by
      rw [← programPT06WarpedNullCollar_zeroSlice source,
        programPT06WarpedNullCollarAffineFluxExtension_divergence
          (radius := 0) hDensity]

/-- Oriented absolute gate bundle for the affine collar current. -/
theorem programPT06WarpedNullCollarTransitionAbsoluteAffine_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (hDensity : DifferentiableAt Real density source)
    (hOrientation : 0 <
      programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum) :
    programPT06AmbientCoordinateDivergence
        (programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
          period hPeriod datum
          (programPT06WarpedNullCollarAffineFluxExtension density))
        (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06WarpedNullCollarTransitionJacobianDensity
          period hPeriod datum * density source ∧
      programPT06WarpedNullHyperplaneFluxRestriction
          (programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
            period hPeriod datum
            (programPT06WarpedNullCollarAffineFluxExtension density)) source =
        density source := by
  refine ⟨programPT06WarpedNullCollarTransitionAbsolute_affineDivergence
      period hPeriod datum density hDensity, ?_⟩
  rw [programPT06WarpedNullCollarTransitionAbsolute_fluxRestriction_eq
    period hPeriod datum _ hOrientation]
  exact congrFun
    (programPT06WarpedNullCollarAffineFluxExtension_rightInverse density)
    source

end
end P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
end JanusFormal
