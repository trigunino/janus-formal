import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowRadialGenerator4D

/-! # A global ten-flow generating frame on the physical quotient -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowFrame4D

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set Module MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumePreservingFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowEuclideanSpan4D
open P0EFTJanusMappingTorusCanonicalTenFlowRadialGenerator4D
open P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Intrinsic tangent generator indexed by the ten canonical flows. -/
def canonicalTenFlowGeneratorAt
    (point : EffectiveQuotient period hPeriod)
    (index : CanonicalFlowIndex) :
    TangentSpace coverModelWithCorners point :=
  canonicalFlowGenerator period hPeriod
    (canonicalVolumePreservingFlow period hPeriod index) point

private theorem canonicalTenFlowGeneratorAt_spans_mk
    (point : EffectiveCover period hPeriod) :
    Submodule.span Real
        (Set.range (canonicalTenFlowGeneratorAt period hPeriod
          (mappingTorusMk (sphereData period hPeriod) point))) = ⊤ := by
  let generator := canonicalTenFlowGeneratorAt period hPeriod
    (mappingTorusMk (sphereData period hPeriod) point)
  let euclideanGenerator := canonicalEuclideanFlowGenerator period point.time
    (coverRadialMap period hPeriod point)
  let derivative := canonicalQuotientRadialDerivativeEquiv period hPeriod point
  have hImage : derivative.toLinearMap '' Set.range generator =
      Set.range euclideanGenerator := by
    ext vector
    constructor
    · rintro ⟨_, ⟨index, rfl⟩, rfl⟩
      exact ⟨index, (canonicalQuotientRadialDerivativeEquiv_generator
        period hPeriod index point).symm⟩
    · rintro ⟨index, rfl⟩
      exact ⟨generator index, ⟨index, rfl⟩,
        canonicalQuotientRadialDerivativeEquiv_generator
          period hPeriod index point⟩
  have hMapped :
      (Submodule.span Real (Set.range generator)).map derivative.toLinearMap =
        ⊤ := by
    rw [Submodule.map_span, hImage]
    exact canonicalEuclideanFlowGenerator_spans period point.time
      (coverRadialMap period hPeriod point)
      (coverRadialMap_ne_zero period hPeriod point)
  apply top_unique
  intro vector _
  have hVector : derivative vector ∈
      (Submodule.span Real (Set.range generator)).map derivative.toLinearMap := by
    rw [hMapped]
    exact Submodule.mem_top
  rcases hVector with ⟨preimage, hPreimage, hEqual⟩
  have hPreimageEq : preimage = vector := derivative.injective hEqual
  simpa [hPreimageEq] using hPreimage

theorem canonicalTenFlowGeneratorAt_spans
    (point : EffectiveQuotient period hPeriod) :
    Submodule.span Real
      (Set.range (canonicalTenFlowGeneratorAt period hPeriod point)) = ⊤ := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  exact canonicalTenFlowGeneratorAt_spans_mk period hPeriod anchor

/-- Fixed enumeration of the ten canonical flow indices. -/
def canonicalFlowIndexEquivFinTen : CanonicalFlowIndex ≃ Fin 10 :=
  (Fintype.equivFin CanonicalFlowIndex).trans
    (finCongr canonicalFlowIndex_card)

/-- Concrete global smooth generating family whose members all preserve the
canonical Lorentz volume. -/
def canonicalTenFlowFrame : SmoothD8Frame period hPeriod where
  count := 10
  vectorAt point index := canonicalTenFlowGeneratorAt period hPeriod point
    ((canonicalFlowIndexEquivFinTen).symm index)
  spansAt := by
    intro point
    have hRange : Set.range (fun index : Fin 10 =>
        canonicalTenFlowGeneratorAt period hPeriod point
          ((canonicalFlowIndexEquivFinTen).symm index)) =
        Set.range (canonicalTenFlowGeneratorAt period hPeriod point) := by
      ext vector
      constructor
      · rintro ⟨index, rfl⟩
        exact ⟨(canonicalFlowIndexEquivFinTen).symm index, rfl⟩
      · rintro ⟨index, rfl⟩
        exact ⟨canonicalFlowIndexEquivFinTen index, by simp⟩
    rw [hRange]
    exact canonicalTenFlowGeneratorAt_spans period hPeriod point
  contMDiff_vector := by
    intro index
    change ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (fun point =>
        (⟨point, canonicalFlowGenerator period hPeriod
          (canonicalVolumePreservingFlow period hPeriod
            ((canonicalFlowIndexEquivFinTen).symm index)) point⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod)))
    convert canonicalFlowGenerator_contMDiff period hPeriod
      (canonicalVolumePreservingFlow period hPeriod
        ((canonicalFlowIndexEquivFinTen).symm index)) using 1

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

theorem canonicalTenFlowFrame_frameDerivative
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) (index : Fin 10) :
    frameDerivative period hPeriod Fiber
        (canonicalTenFlowFrame period hPeriod) field point index =
      canonicalFlowDirectionalDerivative period hPeriod Fiber
        ((canonicalFlowIndexEquivFinTen).symm index) field point := by
  rfl

/-- Exact global IPP for every member of the concrete spanning frame. -/
theorem canonicalTenFlowFrame_integral_inner_derivative_eq_neg
    {InnerFiber : Type*} [NormedAddCommGroup InnerFiber]
    [InnerProductSpace Real InnerFiber]
    (index : Fin 10)
    (first second : SmoothQuotientField period hPeriod InnerFiber) :
    (∫ point, inner Real (first point)
        (frameDerivative period hPeriod InnerFiber
          (canonicalTenFlowFrame period hPeriod) second point index)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      -∫ point, inner Real
        (frameDerivative period hPeriod InnerFiber
          (canonicalTenFlowFrame period hPeriod) first point index)
        (second point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  simpa only [canonicalTenFlowFrame_frameDerivative] using
    canonicalTenFlow_integral_inner_derivative_eq_neg period hPeriod
      ((canonicalFlowIndexEquivFinTen).symm index) first second

/-- Gate marker: a concrete smooth ten-section frame spans every physical
tangent fiber and all ten derivatives satisfy boundaryless IPP. -/
theorem canonical_ten_flow_frame_gate :
    (canonicalTenFlowFrame period hPeriod).count = 10 ∧
    (∀ point : EffectiveQuotient period hPeriod,
      Submodule.span Real
        (Set.range ((canonicalTenFlowFrame period hPeriod).vectorAt point)) = ⊤) ∧
    (∀ (index : Fin 10)
      (first second : SmoothQuotientField period hPeriod Real),
      (∫ point, inner Real (first point)
          (frameDerivative period hPeriod Real
            (canonicalTenFlowFrame period hPeriod) second point index)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
        -∫ point, inner Real
          (frameDerivative period hPeriod Real
            (canonicalTenFlowFrame period hPeriod) first point index)
          (second point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) := by
  refine ⟨rfl, (canonicalTenFlowFrame period hPeriod).spansAt, ?_⟩
  exact canonicalTenFlowFrame_integral_inner_derivative_eq_neg period hPeriod

end
end P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
end JanusFormal
