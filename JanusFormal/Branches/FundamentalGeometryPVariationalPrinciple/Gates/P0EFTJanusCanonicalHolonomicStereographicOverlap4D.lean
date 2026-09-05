import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalStereographicCoordinateTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

/-! # Concrete stereographic-to-holonomic overlaps

Local inverses of the supplied holonomic charts construct the coordinate
transition. The measured stereographic strips provide a neighborhood at every
point; smoothness, injectivity, and physical-map agreement are proved.
-/

namespace JanusFormal
namespace P0EFTJanusCanonicalHolonomicStereographicOverlap4D

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

private abbrev Coordinates := EuclideanSpace Real (Fin 3) × Real
private abbrev Vector4 := Fin 4 → Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem shiftedStereographicPhysicalMapAmbient_injOn_strip
    (shift : Real) (pole : StandardSphere) :
    InjOn (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole)
      (range (canonicalInteriorStereographicCoordinateInclusion period)) := by
  rintro first ⟨firstSource, rfl⟩ second ⟨secondSource, rfl⟩ hEqual
  have hSource := (shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
    period hPeriod shift pole).injective hEqual
  exact congrArg (canonicalInteriorStereographicCoordinateInclusion period) hSource

def holonomicCoordinateLocalInverse
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    PartialDiffeomorph coverModelWithCorners (modelWithCornersSelf Real Vector4)
      (EffectiveQuotient period hPeriod) Vector4 ∞ :=
  (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse

def stereographicHolonomicOverlapDomain
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) : Set Coordinates :=
  range (canonicalInteriorStereographicCoordinateInclusion period) ∩
    (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) ⁻¹'
      (holonomicCoordinateLocalInverse period hPeriod patch coordinate).source

def stereographicToHolonomicTransition
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) : Coordinates → Vector4 :=
  holonomicCoordinateLocalInverse period hPeriod patch coordinate ∘
    shiftedStereographicPhysicalMapAmbient period hPeriod shift pole

theorem stereographicHolonomicOverlapDomain_isOpen
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) :
    IsOpen (stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole) :=
  (canonicalInteriorStereographicCoordinateInclusion_isOpenEmbedding period).isOpen_range.inter
    ((holonomicCoordinateLocalInverse period hPeriod patch coordinate).open_source.preimage
      (shiftedStereographicPhysicalMapAmbient_contMDiff period hPeriod shift pole).continuous)

theorem stereographicToHolonomicTransition_physical_agreement
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    patch.coordinateMap (stereographicToHolonomicTransition
      period hPeriod patch coordinate shift pole point) =
      shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point :=
  (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_right_inv hPoint.2

theorem stereographicToHolonomicTransition_contMDiffOn
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) :
    ContMDiffOn coverModelWithCorners (modelWithCornersSelf Real Vector4) ∞
      (stereographicToHolonomicTransition period hPeriod patch coordinate shift pole)
      (stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole) := by
  exact (holonomicCoordinateLocalInverse period hPeriod patch coordinate).contMDiffOn_toFun.comp
    ((shiftedStereographicPhysicalMapAmbient_contMDiff period hPeriod shift pole).of_le
      (by simp)).contMDiffOn (fun _ hPoint => hPoint.2)

theorem stereographicToHolonomicTransition_injOn
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) :
    InjOn (stereographicToHolonomicTransition period hPeriod patch coordinate shift pole)
      (stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole) := by
  intro first hFirst second hSecond hEqual
  have hPhysical := congrArg patch.coordinateMap hEqual
  rw [stereographicToHolonomicTransition_physical_agreement period hPeriod patch coordinate
      shift pole first hFirst,
    stereographicToHolonomicTransition_physical_agreement period hPeriod patch coordinate
      shift pole second hSecond] at hPhysical
  exact shiftedStereographicPhysicalMapAmbient_injOn_strip period hPeriod shift pole
    hFirst.1 hSecond.1 hPhysical

/-- Every point of every holonomic chart has an actual smooth injective
stereographic overlap containing a preimage of that exact coordinate. -/
theorem canonical_holonomic_stereographic_overlap_gate
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    ∃ (shift : Real) (pole : StandardSphere) (point : Coordinates),
      point ∈ stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole ∧
      stereographicToHolonomicTransition period hPeriod patch coordinate shift pole point =
        coordinate ∧
      IsOpen (stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole) ∧
      ContMDiffOn coverModelWithCorners (modelWithCornersSelf Real Vector4) ∞
        (stereographicToHolonomicTransition period hPeriod patch coordinate shift pole)
        (stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole) ∧
      InjOn (stereographicToHolonomicTransition period hPeriod patch coordinate shift pole)
        (stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole) := by
  obtain ⟨shift, pole, source, hSource⟩ := exists_shiftedStereographicChart_mem period hPeriod
    (patch.coordinateMap coordinate)
  let point := canonicalInteriorStereographicCoordinateInclusion period source
  refine ⟨shift, pole, point, ?_, ?_,
    stereographicHolonomicOverlapDomain_isOpen period hPeriod patch coordinate shift pole,
    stereographicToHolonomicTransition_contMDiffOn period hPeriod patch coordinate shift pole,
    stereographicToHolonomicTransition_injOn period hPeriod patch coordinate shift pole⟩
  · refine ⟨⟨source, rfl⟩, ?_⟩
    change shiftedCanonicalInteriorStereographicPhysicalMap period hPeriod shift pole source ∈
      (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse.source
    rw [hSource]
    exact (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_mem_source
  · change (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
      (shiftedCanonicalInteriorStereographicPhysicalMap period hPeriod shift pole source) = _
    rw [hSource]
    exact (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_left_inv
      (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_mem_target

/-- Exact derivative compatibility on the constructed overlap, derived from
the physical-map identity on an open neighborhood. -/
theorem stereographicToHolonomicTransition_mfderiv
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap
      (stereographicToHolonomicTransition period hPeriod patch coordinate shift pole point)).comp
        (mfderiv coverModelWithCorners (modelWithCornersSelf Real Vector4)
          (stereographicToHolonomicTransition period hPeriod patch coordinate shift pole) point) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) point := by
  have hNeighborhood := (stereographicHolonomicOverlapDomain_isOpen
    period hPeriod patch coordinate shift pole).mem_nhds hPoint
  have hAt := (stereographicToHolonomicTransition_contMDiffOn
    period hPeriod patch coordinate shift pole).contMDiffAt hNeighborhood
  have hAgreement : patch.coordinateMap ∘
      stereographicToHolonomicTransition period hPeriod patch coordinate shift pole =ᶠ[𝓝 point]
        shiftedStereographicPhysicalMapAmbient period hPeriod shift pole :=
    Filter.eventuallyEq_of_mem hNeighborhood (fun current hCurrent =>
      stereographicToHolonomicTransition_physical_agreement
        period hPeriod patch coordinate shift pole current hCurrent)
  rw [← mfderiv_comp point
    (patch.coordinateMap_contMDiff.mdifferentiableAt (by simp))
    (hAt.mdifferentiableAt (by simp))]
  exact hAgreement.mfderiv_eq

end
end P0EFTJanusCanonicalHolonomicStereographicOverlap4D
end JanusFormal
