import Mathlib.Topology.Instances.Matrix
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LiftedFrameDeck4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ReflectionFrameDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalFrameNoGo4D

/-! The actual globally framed metric input is empty on the reflected D8 mapping
torus. This is an obstruction to that input type, not a terminal T12 certificate. -/
namespace JanusFormal.P0EFTJanusProgramPT12RegularMetricFrameNoGo4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D
open P0EFTJanusMappingTorusLocalFrameNoGo4D
open P0EFTJanusProgramPT12LiftedFrameContinuity4D
open P0EFTJanusProgramPT12LiftedFrameDeck4D
open P0EFTJanusProgramPT12ReflectionFrameDeterminant4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveCover := MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def equatorPoint : EquatorialTwoSphere :=
  ⟨fun i => if i = (1 : Fin 4) then 1 else 0, by
    constructor
    · simp [OnUnitThreeSphere, radiusSquared]
    · simp⟩

private def equatorCurve (time : Real) : EffectiveCover period hPeriod :=
  ⟨equatorialSphereInclusion equatorPoint, time⟩

private theorem equatorCurve_continuous : Continuous (equatorCurve period hPeriod) :=
  (coverHomeomorphProd (reflectedSphereData period hPeriod)).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

private theorem equatorCurve_period (time : Real) :
    equatorCurve period hPeriod (time + period) =
      (1 : Int) +ᵥ equatorCurve period hPeriod time := by
  apply MappingTorusCover.ext
  · change equatorialSphereInclusion equatorPoint =
      (sphereReflection ^ (1 : Int)) (equatorialSphereInclusion equatorPoint)
    simp
  · change time + period = time + ((1 : Int) : Real) * period
    simp

/-- The hypothetical regular frame, lifted through the genuine quotient derivative. -/
def regularFrameRadialDeterminant (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveCover period hPeriod) : Real :=
  (frameColumnMatrix (fun index =>
    liftedQuotientRadialCoordinates period hPeriod (metric.frame index) point)).det

theorem regularFrameRadialDeterminant_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Continuous (regularFrameRadialDeterminant period hPeriod metric) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact (PiLp.continuous_apply 2 (fun _ : Fin 4 => Real) row).comp
    (liftedQuotientRadialCoordinates_continuous period hPeriod (metric.frame column))

theorem regularFrameRadialDeterminant_ne_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveCover period hPeriod) :
    regularFrameRadialDeterminant period hPeriod metric point ≠ 0 := by
  let equiv : (Fin 4 → Real) ≃L[Real] EuclideanR4 :=
    ((metric.frameEquiv (mappingTorusMk (reflectedSphereData period hPeriod) point)).trans
      (quotientProjectionDerivativeEquiv period hPeriod point).symm).trans
        (genuineStableRadialTangentEquiv period hPeriod point)
  have hColumns : (fun index =>
      liftedQuotientRadialCoordinates period hPeriod (metric.frame index) point) =
      (fun index => equiv ((Pi.basisFun Real (Fin 4)) index)) := by
    funext index
    unfold liftedQuotientRadialCoordinates
    rw [liftedQuotientTangentField_apply, metric.frame_eq_basisFun]
    rfl
  unfold regularFrameRadialDeterminant
  rw [hColumns]
  exact frameColumnMatrix_equiv_det_ne_zero equiv

theorem regularFrameRadialDeterminant_deckGenerator
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveCover period hPeriod) :
    regularFrameRadialDeterminant period hPeriod metric ((1 : Int) +ᵥ point) =
      -regularFrameRadialDeterminant period hPeriod metric point := by
  unfold regularFrameRadialDeterminant
  simp_rw [liftedQuotientRadialCoordinates_deckGenerator]
  exact frameColumnMatrix_reflection_det _

/-- No globally smooth tangent basis exists as required by `RegularGeneralLorentzMetric`.
This theorem does not declare the metric tensor itself impossible. -/
theorem regularGeneralLorentzMetric_isEmpty :
    IsEmpty (RegularGeneralLorentzMetric period hPeriod) := by
  constructor
  intro metric
  apply (no_antiPeriodicFrameDeterminant period).false
  exact {
    determinant := fun time => regularFrameRadialDeterminant period hPeriod metric
      (equatorCurve period hPeriod time)
    continuous := (regularFrameRadialDeterminant_continuous period hPeriod metric).comp
      (equatorCurve_continuous period hPeriod)
    nowhereZero := fun time => regularFrameRadialDeterminant_ne_zero period hPeriod metric _
    antiPeriodic := fun time => by
      rw [equatorCurve_period, regularFrameRadialDeterminant_deckGenerator] }

end
end JanusFormal.P0EFTJanusProgramPT12RegularMetricFrameNoGo4D
