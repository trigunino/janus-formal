import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

/-!
# Levi--Civita law for one fixed holonomic transition germ

The canonical pointwise transition law is re-anchored at every nearby
coordinate.  This gate identifies those re-anchored local inverses with the
single local inverse chosen at the original overlap, as germs, and therefore
upgrades the Christoffel law to an `EventuallyEq` for that fixed transition.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaGerm4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem fixedTransition_isLocalDiffeomorphAt_of_mem
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate current : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hCurrent : current ∈
      holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint) :
    IsLocalDiffeomorphAt (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Vector4) ∞
      (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint)
      current := by
  have firstLocal :=
    firstPatch.coordinateMap_isLocalDiffeomorph current
  have inverseLocal :
      IsLocalDiffeomorphAt coverModelWithCorners
        (modelWithCornersSelf Real Vector4) ∞
        (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate
          |>.localInverse)
        (firstPatch.coordinateMap current) :=
    (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
      |>.localInverse.isLocalDiffeomorphAt _ _ _ hCurrent
  simpa only [holonomicCoordinateTransitionAt] using
    (IsLocalDiffeomorphAt.comp
      (K := modelWithCornersSelf Real Vector4)
      (P := Vector4) firstLocal inverseLocal)

private theorem fixedTransition_eventuallyEq_reanchored_of_mem
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate current : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hCurrent : current ∈
      holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint)
    (samePointCurrent :
      firstPatch.coordinateMap current =
        secondPatch.coordinateMap
          (holonomicCoordinateTransitionAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint current)) :
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint =ᶠ[𝓝 current]
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        current
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint current)
        samePointCurrent := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  let target := transition current
  let reanchoredLocal :=
    secondPatch.coordinateMap_isLocalDiffeomorph target
  have transitionTendsto :
      Tendsto transition (𝓝 current) (𝓝 target) :=
    (fixedTransition_isLocalDiffeomorphAt_of_mem period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate current samePoint hCurrent)
      |>.contMDiffAt.continuousAt
  have leftInverse :=
    reanchoredLocal.localInverse_eventuallyEq_left.comp_tendsto
      transitionTendsto
  have reconstruct :
      (fun coordinate =>
        secondPatch.coordinateMap (transition coordinate)) =ᶠ[𝓝 current]
        firstPatch.coordinateMap := by
    apply Filter.eventuallyEq_of_mem
      ((holonomicCoordinateTransitionDomainAt_isOpen period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint).mem_nhds
          hCurrent)
    intro coordinate hCoordinate
    exact holonomicCoordinateTransitionAt_reconstructs_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate coordinate
      samePoint hCoordinate
  filter_upwards [leftInverse, reconstruct] with coordinate hLeft hReconstruct
  change transition coordinate =
    reanchoredLocal.localInverse (firstPatch.coordinateMap coordinate)
  rw [← hReconstruct]
  simpa only [Function.comp_apply, id_eq] using hLeft.symm

/-- Pointwise form of the fixed-germ Christoffel law on the selected inverse
domain.  The proof compares the fixed inverse germ with the inverse re-anchored
at the current coordinate and then applies the canonical pointwise law. -/
theorem fixedHolonomicTransition_leviCivita_of_mem
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate current : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hCurrent : current ∈
      holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint)
    (first second : Index4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    fderiv Real transition current
        (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
          current (Pi.single first 1) (Pi.single second 1)) =
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          (transition current)
          (fderiv Real transition current (Pi.single first 1))
          (fderiv Real transition current (Pi.single second 1)) +
        fderiv Real (fderiv Real transition) current
          (Pi.single first 1) (Pi.single second 1) := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  have samePointCurrent :
      firstPatch.coordinateMap current =
        secondPatch.coordinateMap (transition current) :=
    (holonomicCoordinateTransitionAt_reconstructs_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current samePoint
      hCurrent).symm
  let reanchored :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      current (transition current) samePointCurrent
  have germEquality :
      transition =ᶠ[𝓝 current] reanchored := by
    simpa only [transition, reanchored] using
      fixedTransition_eventuallyEq_reanchored_of_mem period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate current samePoint hCurrent
        samePointCurrent
  have firstDerivative :
      fderiv Real transition current =
        fderiv Real reanchored current :=
    germEquality.fderiv_eq
  have secondDerivative :
      fderiv Real (fderiv Real transition) current =
        fderiv Real (fderiv Real reanchored) current :=
    germEquality.fderiv.fderiv_eq
  have pointwise :=
    (canonicalHolonomicLeviCivitaTransitionAgreement period hPeriod metric
      firstPatch secondPatch current (transition current) samePointCurrent)
      |>.christoffel_transform first second
  have linearApply (vector : Vector4) :
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch current (transition current) samePointCurrent vector =
        fderiv Real
          (holonomicCoordinateTransitionAt period hPeriod firstPatch
            secondPatch current (transition current) samePointCurrent)
          current vector := by
    have derivativeEquality :=
      holonomicCoordinateTransitionLinearEquivAt_coe period hPeriod firstPatch
        secondPatch current (transition current) samePointCurrent
    have applied := congrArg
      (fun derivative : Vector4 →L[Real] Vector4 => derivative vector)
      derivativeEquality
    exact applied
  simp only [linearApply] at pointwise
  have pointwise' :
      fderiv Real reanchored current
          (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            current (Pi.single first 1) (Pi.single second 1)) =
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            (transition current)
            (fderiv Real reanchored current (Pi.single first 1))
            (fderiv Real reanchored current (Pi.single second 1)) +
          fderiv Real (fderiv Real reanchored) current
            (Pi.single first 1) (Pi.single second 1) := by
    simpa only [reanchored,
      holonomicCoordinateTransitionSecondDerivativeAt] using pointwise
  dsimp only
  rw [firstDerivative, secondDerivative]
  exact pointwise'

/-- The exact Levi--Civita/Christoffel transformation law holds as an
`EventuallyEq` for the one transition function fixed at the original overlap.
In particular, no new choice of local inverse appears in the statement. -/
theorem fixedHolonomicTransition_leviCivita_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    (fun current =>
      fderiv Real transition current
        (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
          current (Pi.single first 1) (Pi.single second 1))) =ᶠ[
        𝓝 firstCoordinate]
      fun current =>
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            (transition current)
            (fderiv Real transition current (Pi.single first 1))
            (fderiv Real transition current (Pi.single second 1)) +
          fderiv Real (fderiv Real transition) current
            (Pi.single first 1) (Pi.single second 1) := by
  filter_upwards [
    (holonomicCoordinateTransitionDomainAt_isOpen period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).mem_nhds
      (firstCoordinate_mem_holonomicCoordinateTransitionDomainAt period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)]
    with current hCurrent
  exact fixedHolonomicTransition_leviCivita_of_mem period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate current samePoint
    hCurrent first second

end

end P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaGerm4D
end JanusFormal
