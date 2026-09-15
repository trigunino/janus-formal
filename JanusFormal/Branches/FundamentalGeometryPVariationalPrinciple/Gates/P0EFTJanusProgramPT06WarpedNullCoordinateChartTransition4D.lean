import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarBand4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCoordinateIncidence4D

/-!
# Warped-null transition for an adapted physical coordinate

This gate transports the point-local collar-transition datum to the freely
selected physical coordinate of Gate 1064.  The canonical first-sheet datum
uses the actual identity transition: its adapted coordinate on the true
collar is the explicit warped coordinate as a germ.  Consequently the signed
Jacobian of this transition, rather than that of a coordinate/inverse round
trip, is exactly `+1`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCoordinateChartTransition4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutCollarTubularNormalLift4D
open P0EFTJanusMappingTorusCutCollarTubularSpacetimeDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06TrueCutCollarNormalAlignment4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D
open P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateLocalDiffeomorph4D
open P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarBand4D
open P0EFTJanusProgramPT06WarpedNullCoordinateIncidence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveBulk :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance canonicalLatitudeSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance canonicalLatitudeSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2))
      (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- A local transition from the explicit warped collar coordinate to a freely
selected physical coordinate. -/
structure ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) where
  transition : ProgramPT06AmbientCoordinate4 → ProgramPT06AmbientCoordinate4
  transition_isLocalDiffeomorphAt :
    IsLocalDiffeomorphAt
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 3 transition
      (programPT06WarpedNullHyperplaneEmbedding source)
  collar_eventuallyEq :
    transition ∘ programPT06WarpedNullClosedHalfCollarEmbedding =ᶠ[
        𝓝 (programPT06WarpedNullZeroFace source)]
      programPT06WarpedNullCoordinateChartCoordinate
        period hPeriod incidence

/-- The transition fixes the selected face point. -/
theorem ProgramPT06WarpedNullCoordinateChartTransitionGermDatum.transition_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    datum.transition (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  calc
    datum.transition (programPT06WarpedNullHyperplaneEmbedding source) =
        (datum.transition ∘ programPT06WarpedNullClosedHalfCollarEmbedding)
          (programPT06WarpedNullZeroFace source) := by simp
    _ = programPT06WarpedNullCoordinateChartCoordinate period hPeriod incidence
          (programPT06WarpedNullZeroFace source) :=
      datum.collar_eventuallyEq.eq_of_nhds
    _ = programPT06WarpedNullHyperplaneEmbedding source :=
      programPT06WarpedNullCoordinateChartCoordinate_face
        period hPeriod incidence source hSource

/-- Invertible Jacobian of the adapted-coordinate transition at the face. -/
def programPT06WarpedNullCoordinateTransitionJacobian
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ProgramPT06AmbientCoordinate4 ≃L[Real] ProgramPT06AmbientCoordinate4 :=
  datum.transition_isLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (by norm_num)

theorem programPT06WarpedNullCoordinateTransitionJacobian_coe
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    (programPT06WarpedNullCoordinateTransitionJacobian
        period hPeriod datum :
      ProgramPT06AmbientCoordinate4 →L[Real]
        ProgramPT06AmbientCoordinate4) =
      mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        datum.transition (programPT06WarpedNullHyperplaneEmbedding source) :=
  datum.transition_isLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
    (by norm_num)

/-- Signed determinant of the actual coordinate transition. -/
def programPT06WarpedNullCoordinateTransitionSignedJacobian
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) : Real :=
  LinearMap.det
    (programPT06WarpedNullCoordinateTransitionJacobian
      period hPeriod datum).toLinearEquiv.toLinearMap

theorem programPT06WarpedNullCoordinateTransitionSignedJacobian_ne_zero
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullCoordinateTransitionSignedJacobian
      period hPeriod datum ≠ 0 := by
  exact (LinearEquiv.isUnit_det'
    (programPT06WarpedNullCoordinateTransitionJacobian
      period hPeriod datum).toLinearEquiv).ne_zero

/-- Absolute Jacobian density of the adapted-coordinate transition. -/
def programPT06WarpedNullCoordinateTransitionJacobianDensity
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) : Real :=
  |programPT06WarpedNullCoordinateTransitionSignedJacobian
    period hPeriod datum|

theorem programPT06WarpedNullCoordinateTransitionJacobianDensity_pos
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    0 < programPT06WarpedNullCoordinateTransitionJacobianDensity
      period hPeriod datum := by
  rw [programPT06WarpedNullCoordinateTransitionJacobianDensity, abs_pos]
  exact programPT06WarpedNullCoordinateTransitionSignedJacobian_ne_zero
    period hPeriod datum

/-- Differential form of the commutative adapted collar germ. -/
theorem ProgramPT06WarpedNullCoordinateChartTransitionGermDatum.mfderiv_eq_transition_comp
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06WarpedNullCoordinateChartCoordinate
          period hPeriod incidence)
        (programPT06WarpedNullZeroFace source) =
      (mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          datum.transition
          (programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source))).comp
        (mfderiv programPT06NullFaceCollarModelWithCorners
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          programPT06WarpedNullClosedHalfCollarEmbedding
          (programPT06WarpedNullZeroFace source)) := by
  have hWarped : MDifferentiableAt
      programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      programPT06WarpedNullClosedHalfCollarEmbedding
      (programPT06WarpedNullZeroFace source) :=
    contMDiff_programPT06WarpedNullClosedHalfCollarEmbedding.mdifferentiableAt
      (by simp)
  have hTransition : MDifferentiableAt
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      datum.transition
      (programPT06WarpedNullClosedHalfCollarEmbedding
        (programPT06WarpedNullZeroFace source)) := by
    rw [programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace]
    exact datum.transition_isLocalDiffeomorphAt.mdifferentiableAt (by norm_num)
  calc
    _ = mfderiv programPT06NullFaceCollarModelWithCorners
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (datum.transition ∘
            programPT06WarpedNullClosedHalfCollarEmbedding)
          (programPT06WarpedNullZeroFace source) :=
      datum.collar_eventuallyEq.mfderiv_eq.symm
    _ = _ := mfderiv_comp (programPT06WarpedNullZeroFace source)
      hTransition hWarped

/-- The adapted true-collar coordinate sends its positive interval tangent
to the transition Jacobian applied to the warped radial basis vector. -/
theorem ProgramPT06WarpedNullCoordinateChartTransitionGermDatum.unitNormal_mfderiv
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCoordinateChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06WarpedNullCoordinateChartCoordinate
          period hPeriod incidence)
        (programPT06WarpedNullZeroFace source)
        (programPT06LocalC3NullCollarUnitNormal
          (programPT06WarpedNullZeroFace source)) =
      programPT06WarpedNullCoordinateTransitionJacobian period hPeriod datum
        (programPT06AmbientCoordinateBasis 3) := by
  have hDerivative := congrArg
    (fun derivative => derivative
      (programPT06LocalC3NullCollarUnitNormal
        (programPT06WarpedNullZeroFace source)))
    (datum.mfderiv_eq_transition_comp period hPeriod)
  calc
    _ = ((mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            datum.transition
            (programPT06WarpedNullClosedHalfCollarEmbedding
              (programPT06WarpedNullZeroFace source))).comp
          (mfderiv programPT06NullFaceCollarModelWithCorners
            (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source)))
          (programPT06LocalC3NullCollarUnitNormal
            (programPT06WarpedNullZeroFace source)) := hDerivative
    _ = mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          datum.transition
          (programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source))
          (mfderiv programPT06NullFaceCollarModelWithCorners
            (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source)
            (programPT06LocalC3NullCollarUnitNormal
              (programPT06WarpedNullZeroFace source))) := rfl
    _ = _ := by
      rw [programPT06WarpedNullClosedHalfCollarEmbedding_unitNormal_mfderiv]
      rw [programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace]
      rw [← programPT06WarpedNullCoordinateTransitionJacobian_coe]
      rfl

/-- The reassociated canonical full-collar representative depends smoothly
on the source and finite normal. -/
theorem programPT06CanonicalFirstSheetFullCollarBandPoint_contMDiff
    (pole : StandardEquatorialTwoSphere) :
    ContMDiff programPT06NullFaceCollarModelWithCorners
      coverModelWithCorners ∞
      (fun parameter : ProgramPT06WarpedNullClosedHalfCollar =>
        programPT06CanonicalFirstSheetFullCollarBandPoint pole
          parameter.1 parameter.2) := by
  have hScreen : ContMDiff programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ∞
      (fun parameter : ProgramPT06WarpedNullClosedHalfCollar =>
        parameter.1.2) :=
    ((ContinuousLinearMap.snd Real Real FiniteNullFaceScreenCoordinate2)
      |>.contDiff.contMDiff).comp contMDiff_fst
  have hSphere : ContMDiff programPT06NullFaceCollarModelWithCorners
      (𝓡 2) ∞
      (fun parameter : ProgramPT06WarpedNullClosedHalfCollar =>
        equatorialTwoSphereHomeomorph.symm
          (standardEquatorialStereographicInverse pole parameter.1.2)) :=
    (chartedSpacePullback_invFun_contMDiff (𝓡 2) ∞
      equatorialTwoSphereHomeomorph).comp
        ((standardEquatorialStereographicInverse_contMDiff pole).comp hScreen)
  have hTime : ContMDiff programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun parameter : ProgramPT06WarpedNullClosedHalfCollar =>
        parameter.1.1) :=
    ((ContinuousLinearMap.fst Real Real FiniteNullFaceScreenCoordinate2)
      |>.contDiff.contMDiff).comp contMDiff_fst
  have hParameter : ContMDiff programPT06NullFaceCollarModelWithCorners
      (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
        (modelWithCornersEuclideanHalfSpace 1)) ∞
      (fun parameter : ProgramPT06WarpedNullClosedHalfCollar =>
        ((equatorialTwoSphereHomeomorph.symm
            (standardEquatorialStereographicInverse pole parameter.1.2),
          parameter.1.1), parameter.2)) :=
    (hSphere.prodMk hTime).prodMk contMDiff_snd
  exact cutCollarTubularSpacetimeMap_contMDiff.comp hParameter

@[simp] theorem programPT06CanonicalFirstSheetFullCollarBandPoint_zeroFace
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) :
    programPT06CanonicalFirstSheetFullCollarBandPoint pole source
        (⊥ : CutCollarInterval) =
      programPT06CanonicalFirstSheetBandPoint pole source := by
  have hNormal : cutCollarTubularNormalLift (⊥ : CutCollarInterval) =
      programPT06ZeroTubularNormal := by
    apply Subtype.ext
    rfl
  rw [programPT06CanonicalFirstSheetFullCollarBandPoint_eq, hNormal]
  rfl

/-- Whenever the explicit full-collar representative lies in the selected
tubular inverse target, its true adapted coordinate is exactly the warped
closed-half-collar coordinate. -/
theorem programPT06CanonicalFirstSheetCoordinateChart_fullCollar
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3)
    (parameter : ProgramPT06WarpedNullClosedHalfCollar)
    (hBand : programPT06CanonicalFirstSheetFullCollarBandPoint pole
        parameter.1 parameter.2 ∈
      (programPT06CanonicalFirstSheetTubularLocalInverse
        period hPeriod pole anchor).target) :
    programPT06WarpedNullCoordinateChartCoordinate period hPeriod
        (programPT06CanonicalFirstSheetWarpedNullCoordinateIncidence
          period hPeriod input pole anchor) parameter =
      programPT06WarpedNullClosedHalfCollarEmbedding parameter := by
  change programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
      period hPeriod pole anchor
      (cutBulkFiniteCollarToAmbient period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole parameter.1, parameter.2)) = _
  rw [programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_apply]
  rw [← programPT06CanonicalFirstSheetFullCollarBandPoint_toAmbient
    period hPeriod pole parameter.1 parameter.2]
  unfold programPT06CanonicalFirstSheetAdaptedBulkCoordinate
  have hInverse :
      programPT06CanonicalFirstSheetTubularLocalInverse period hPeriod pole anchor
          (tubularBandSpacetimeToAmbient period hPeriod
            (programPT06CanonicalFirstSheetFullCollarBandPoint pole
              parameter.1 parameter.2)) =
        programPT06CanonicalFirstSheetFullCollarBandPoint pole
          parameter.1 parameter.2 := by
    simpa [programPT06CanonicalFirstSheetTubularLocalInverse] using
      ((tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod
        (programPT06CanonicalFirstSheetBandPoint pole anchor)).localInverse_left_inv
          hBand)
  rw [hInverse]
  exact programPT06WarpedNullBandCoordinate_fullCollar
    pole parameter.1 parameter.2

/-- On a neighborhood of the anchor zero face, the true adapted collar
coordinate and the explicit warped collar coordinate are equal. -/
theorem programPT06CanonicalFirstSheetCoordinateChart_collar_eventuallyEq
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullCoordinateChartCoordinate period hPeriod
          (programPT06CanonicalFirstSheetWarpedNullCoordinateIncidence
          period hPeriod input pole anchor) =ᶠ[
        𝓝 (programPT06WarpedNullZeroFace anchor)]
      programPT06WarpedNullClosedHalfCollarEmbedding := by
  let hLocal :=
    tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod
      (programPT06CanonicalFirstSheetBandPoint pole anchor)
  have hAt : programPT06CanonicalFirstSheetFullCollarBandPoint pole anchor
        (⊥ : CutCollarInterval) ∈ hLocal.localInverse.target := by
    rw [programPT06CanonicalFirstSheetFullCollarBandPoint_zeroFace]
    exact hLocal.localInverse_mem_target
  have hEventually : ∀ᶠ parameter in
      𝓝 (programPT06WarpedNullZeroFace anchor),
      programPT06CanonicalFirstSheetFullCollarBandPoint pole
          parameter.1 parameter.2 ∈ hLocal.localInverse.target :=
    (programPT06CanonicalFirstSheetFullCollarBandPoint_contMDiff pole)
      |>.continuous.continuousAt
      (hLocal.localInverse.open_target.mem_nhds hAt)
  filter_upwards [hEventually] with parameter hParameter
  exact programPT06CanonicalFirstSheetCoordinateChart_fullCollar
    period hPeriod input pole anchor parameter hParameter

theorem programPT06CanonicalFirstSheetWarpedNullCoordinateIncidence_anchor_mem
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    anchor ∈
      (programPT06CanonicalFirstSheetWarpedNullCoordinateIncidence
        period hPeriod input pole anchor).sourceDomain := by
  exact programPT06CanonicalFirstSheetAdaptedSourceDomain_anchor_mem
    period hPeriod pole anchor

/-- The canonical first-sheet transition is the actual identity coordinate
change on the true collar germ. -/
def programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    ProgramPT06WarpedNullCoordinateChartTransitionGermDatum period hPeriod
      (programPT06CanonicalFirstSheetWarpedNullCoordinateIncidence
        period hPeriod input pole anchor)
      anchor
      (programPT06CanonicalFirstSheetWarpedNullCoordinateIncidence_anchor_mem
        period hPeriod input pole anchor) where
  transition := id
  transition_isLocalDiffeomorphAt := by
    simpa using
      ((Diffeomorph.refl
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        ProgramPT06AmbientCoordinate4 3).isLocalDiffeomorph
        (programPT06WarpedNullHyperplaneEmbedding anchor))
  collar_eventuallyEq := by
    simpa [Function.comp_def] using
      (programPT06CanonicalFirstSheetCoordinateChart_collar_eventuallyEq
        period hPeriod input pole anchor).symm

@[simp] theorem
    programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition_transition
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    (programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition
      period hPeriod input pole anchor).transition = id :=
  rfl

/-- The Jacobian of the actual canonical collar transition is the identity. -/
theorem programPT06CanonicalFirstSheetCoordinateTransitionJacobian_coe
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    (programPT06WarpedNullCoordinateTransitionJacobian period hPeriod
        (programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition
          period hPeriod input pole anchor) :
      ProgramPT06AmbientCoordinate4 →L[Real]
        ProgramPT06AmbientCoordinate4) =
      ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4 := by
  rw [programPT06WarpedNullCoordinateTransitionJacobian_coe]
  rw [programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition_transition]
  exact mfderiv_id

/-- The signed determinant of the actual canonical transition is `+1`. -/
theorem programPT06CanonicalFirstSheetCoordinateTransitionSignedJacobian_eq_one
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullCoordinateTransitionSignedJacobian period hPeriod
        (programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition
          period hPeriod input pole anchor) = 1 := by
  unfold programPT06WarpedNullCoordinateTransitionSignedJacobian
  have hLinear :
      (programPT06WarpedNullCoordinateTransitionJacobian period hPeriod
        (programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition
          period hPeriod input pole anchor)).toLinearEquiv.toLinearMap =
        LinearMap.id := by
    apply LinearMap.ext
    intro vector
    simpa using DFunLike.congr_fun
      (programPT06CanonicalFirstSheetCoordinateTransitionJacobian_coe
        period hPeriod input pole anchor) vector
  rw [hLinear]
  exact LinearMap.det_id

/-- The canonical adapted collar sends its positive tangent to `e₃`. -/
theorem programPT06CanonicalFirstSheetCoordinateChart_unitNormal_mfderiv
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06WarpedNullCoordinateChartCoordinate period hPeriod
          (programPT06CanonicalFirstSheetWarpedNullCoordinateIncidence
            period hPeriod input pole anchor))
        (programPT06WarpedNullZeroFace anchor)
        (programPT06LocalC3NullCollarUnitNormal
          (programPT06WarpedNullZeroFace anchor)) =
      programPT06AmbientCoordinateBasis 3 := by
  rw [(programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition
    period hPeriod input pole anchor).unitNormal_mfderiv period hPeriod]
  change (programPT06WarpedNullCoordinateTransitionJacobian period hPeriod
      (programPT06CanonicalFirstSheetWarpedNullCoordinateChartTransition
        period hPeriod input pole anchor) :
    ProgramPT06AmbientCoordinate4 →L[Real]
      ProgramPT06AmbientCoordinate4)
      (programPT06AmbientCoordinateBasis 3) = _
  rw [programPT06CanonicalFirstSheetCoordinateTransitionJacobian_coe]
  rfl

end
end P0EFTJanusProgramPT06WarpedNullCoordinateChartTransition4D
end JanusFormal
