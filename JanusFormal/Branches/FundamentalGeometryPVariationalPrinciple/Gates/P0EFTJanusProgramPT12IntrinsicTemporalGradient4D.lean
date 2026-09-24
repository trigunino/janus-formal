import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalStereographicIntrinsicMetric4D
import Mathlib.Algebra.Ring.Periodic

/-! The raised differential of a periodic temporal scalar for the actual
intrinsic Lorentz metric. The stereographic source uses spatial coordinates
first and time last. No frame or operator identification is assumed. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalGradient4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusCanonicalHolonomicStereographicInverse4D
open P0EFTJanusCanonicalStereographicIntrinsicMetric4D

private abbrev Space3 := EuclideanSpace Real (Fin 3)
private abbrev Coordinates := Space3 × Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Cover := MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev QuotientSpace := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Cover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Cover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod
local instance : ChartedSpace CoverModel (QuotientSpace period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (QuotientSpace period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def periodicTemporalCoverScalar (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period) :
    SmoothDeckInvariantField period hPeriod Real where
  toFun := fun point => profile point.time
  contMDiff_toFun := by
    have hTime : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point : Cover period hPeriod => point.time) := by
      simpa using (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
        (coverHomeomorphProd (reflectedSphereData period hPeriod))).snd
    exact hSmooth.contMDiff.comp hTime
  deck_invariant := by
    intro winding point
    exact hPeriodic.int_mul winding point.time

/-- A spatially constant periodic profile descended to the actual quotient. -/
def periodicTemporalScalar (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period) :
    P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D.SmoothScalarField period hPeriod :=
  descendSmooth period hPeriod Real
    (periodicTemporalCoverScalar period hPeriod profile hSmooth hPeriodic)

@[simp] theorem periodicTemporalScalar_stereographic (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period)
    (shift : Real) (pole : StandardSphere) (point : Coordinates) :
    periodicTemporalScalar period hPeriod profile hSmooth hPeriodic
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point) =
      profile (point.2 + shift) := rfl

theorem periodicTemporalScalar_differential (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period)
    (shift : Real) (pole : StandardSphere) (point vector : Coordinates) :
    scalarDifferential period hPeriod
        (periodicTemporalScalar period hPeriod profile hSmooth hPeriodic)
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) point vector) =
      deriv profile (point.2 + shift) * vector.2 := by
  have hDerivative : HasFDerivAt (fun current : Coordinates => profile (current.2 + shift))
      (deriv profile (point.2 + shift) • ContinuousLinearMap.snd Real Space3 Real) point :=
    ((hSmooth.differentiable (by simp) (point.2 + shift)).hasDerivAt).comp_hasFDerivAt
      point ((hasFDerivAt_snd).add_const shift)
  have hModel : mfderiv coverModelWithCorners 𝓘(Real, Real)
      (fun current : Coordinates => profile (current.2 + shift)) point =
      deriv profile (point.2 + shift) • ContinuousLinearMap.snd Real Space3 Real := by
    have hSelf : mfderiv (modelWithCornersSelf Real Coordinates) 𝓘(Real, Real)
        (fun current : Coordinates => profile (current.2 + shift)) point =
        deriv profile (point.2 + shift) • ContinuousLinearMap.snd Real Space3 Real := by
      rw [mfderiv_eq_fderiv]
      exact hDerivative.fderiv
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hSelf
    exact hSelf
  have hFunction :
      (periodicTemporalScalar period hPeriod profile hSmooth hPeriodic :
          QuotientSpace period hPeriod → Real) ∘
        shiftedStereographicPhysicalMapAmbient period hPeriod shift pole =
      fun current : Coordinates => profile (current.2 + shift) := by
    funext current
    exact periodicTemporalScalar_stereographic period hPeriod profile hSmooth hPeriodic
      shift pole current
  have hChain := mfderiv_comp point
    ((periodicTemporalScalar period hPeriod profile hSmooth hPeriodic).contMDiff_toFun.mdifferentiableAt
      (by simp))
    ((shiftedStereographicPhysicalMapAmbient_contMDiff period hPeriod shift pole).mdifferentiableAt
      (by simp))
  rw [hFunction, hModel] at hChain
  have hApply := (congrArg (fun derivative => derivative vector) hChain).symm
  change scalarDifferential period hPeriod
      (periodicTemporalScalar period hPeriod profile hSmooth hPeriodic)
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) point vector) =
    deriv profile (point.2 + shift) * vector.2 at hApply
  exact hApply

/-- Uniqueness of the metric musical inverse gives the negative time gradient. -/
theorem periodicTemporalScalar_intrinsic_sharp (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period)
    (shift : Real) (pole : StandardSphere) (point : Coordinates) :
    inverseMetricSharp period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point)
        (scalarDifferential period hPeriod
          (periodicTemporalScalar period hPeriod profile hSmooth hPeriodic)
          (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point)) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) point
        (0, -deriv profile (point.2 + shift)) := by
  let metric := intrinsicSmoothGeneralLorentzMetric period hPeriod
  let chart := shiftedStereographicPhysicalMapAmbient period hPeriod shift pole
  apply (metric.musical (chart point)).injective
  rw [metric_flat_inverseMetricSharp]
  ext tangent
  obtain ⟨source, hSource⟩ :=
    ((shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph_smooth
      period hPeriod shift pole).mfderivToContinuousLinearEquiv (by simp) point).surjective tangent
  change mfderiv coverModelWithCorners coverModelWithCorners chart point source = tangent at hSource
  rw [← hSource]
  change scalarDifferential period hPeriod
      (periodicTemporalScalar period hPeriod profile hSmooth hPeriodic) (chart point)
      (mfderiv coverModelWithCorners coverModelWithCorners chart point source) =
    (metric.musical (chart point)).toContinuousLinearMap
      (mfderiv coverModelWithCorners coverModelWithCorners chart point
        (0, -deriv profile (point.2 + shift)))
      (mfderiv coverModelWithCorners coverModelWithCorners chart point source)
  rw [metric.musical_eq_tensor]
  rw [periodicTemporalScalar_differential,
    shiftedStereographicPhysicalMapAmbient_intrinsic_metric]
  simp

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalGradient4D
