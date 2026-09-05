import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalHolonomicStereographicOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchVolumeComparison4D

/-! # Smooth inverse of the concrete holonomic overlap

The existing analytic stereographic local diffeomorphism makes the overlap
of Gate572 locally invertible. Its inverse is restricted to a neighborhood
whose image stays in the measured strip and the original holonomic overlap.
-/

namespace JanusFormal
namespace P0EFTJanusCanonicalHolonomicStereographicInverse4D

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchVolumeComparison4D
open P0EFTJanusCanonicalHolonomicStereographicOverlap4D

private abbrev Coordinates := EuclideanSpace Real (Fin 3) × Real
private abbrev Vector4 := Fin 4 → Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph_smooth
    (shift : Real) (pole : StandardSphere) :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) := by
  intro point
  obtain ⟨chart, hPoint, hAgreement⟩ :=
    shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph period hPeriod shift pole point
  let smoothChart : PartialDiffeomorph coverModelWithCorners coverModelWithCorners
      Coordinates (EffectiveQuotient period hPeriod) ∞ := {
    toPartialEquiv := chart.toPartialEquiv
    open_source := chart.open_source
    open_target := chart.open_target
    contMDiffOn_toFun := chart.contMDiffOn_toFun.of_le (by simp)
    contMDiffOn_invFun := chart.contMDiffOn_invFun.of_le (by simp) }
  exact ⟨smoothChart, hPoint, hAgreement⟩

theorem stereographicToHolonomicTransition_isLocalDiffeomorphAt
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    IsLocalDiffeomorphAt coverModelWithCorners (modelWithCornersSelf Real Vector4) ∞
      (stereographicToHolonomicTransition period hPeriod patch coordinate shift pole) point := by
  exact IsLocalDiffeomorphAt.comp (K := modelWithCornersSelf Real Vector4)
    (P := Vector4)
    (shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph_smooth
      period hPeriod shift pole point)
      ((holonomicCoordinateLocalInverse period hPeriod patch coordinate).isLocalDiffeomorphAt
        _ _ _ hPoint.2)

def holonomicToStereographicLocalInverse
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    PartialDiffeomorph (modelWithCornersSelf Real Vector4) coverModelWithCorners
      Vector4 Coordinates ∞ :=
  (stereographicToHolonomicTransition_isLocalDiffeomorphAt
    period hPeriod patch coordinate shift pole point hPoint).localInverse

def holonomicToStereographicDomain
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) : Set Vector4 :=
  (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint).source ∩
    (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint) ⁻¹'
      stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole

theorem holonomicToStereographicDomain_isOpen
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    IsOpen (holonomicToStereographicDomain period hPeriod patch coordinate shift pole point hPoint) :=
  (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint).contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint).open_source
      (stereographicHolonomicOverlapDomain_isOpen period hPeriod patch coordinate shift pole)

theorem holonomicToStereographicDomain_base_mem
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    stereographicToHolonomicTransition period hPeriod patch coordinate shift pole point ∈
      holonomicToStereographicDomain period hPeriod patch coordinate shift pole point hPoint := by
  let hLocal := stereographicToHolonomicTransition_isLocalDiffeomorphAt
    period hPeriod patch coordinate shift pole point hPoint
  refine ⟨hLocal.localInverse_mem_source, ?_⟩
  change hLocal.localInverse
    (stereographicToHolonomicTransition period hPeriod patch coordinate shift pole point) ∈
      stereographicHolonomicOverlapDomain period hPeriod patch coordinate shift pole
  rw [hLocal.localInverse_left_inv hLocal.localInverse_mem_target]
  exact hPoint

theorem holonomicToStereographicLocalInverse_contDiffOn
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    ContDiffOn Real ∞
      (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint)
      (holonomicToStereographicDomain period hPeriod patch coordinate shift pole point hPoint) := by
  have hSmooth := (holonomicToStereographicLocalInverse
    period hPeriod patch coordinate shift pole point hPoint).contMDiffOn_toFun.mono
      (show holonomicToStereographicDomain period hPeriod patch coordinate shift pole point hPoint ⊆
        (holonomicToStereographicLocalInverse
          period hPeriod patch coordinate shift pole point hPoint).source from inter_subset_left)
  have hSelf : ContMDiffOn (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Coordinates) ∞
      (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint)
      (holonomicToStereographicDomain period hPeriod patch coordinate shift pole point hPoint) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hSmooth
  exact hSelf.contDiffOn

theorem holonomicToStereographicLocalInverse_injOn
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    InjOn (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint)
      (holonomicToStereographicDomain period hPeriod patch coordinate shift pole point hPoint) :=
  (holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint).toPartialEquiv.injOn.mono inter_subset_left

theorem holonomicToStereographicLocalInverse_physical_agreement
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole)
    (current : Vector4)
    (hCurrent : current ∈ holonomicToStereographicDomain
      period hPeriod patch coordinate shift pole point hPoint) :
    shiftedStereographicPhysicalMapAmbient period hPeriod shift pole
        (holonomicToStereographicLocalInverse
          period hPeriod patch coordinate shift pole point hPoint current) =
      patch.coordinateMap current := by
  have hPhysical := stereographicToHolonomicTransition_physical_agreement period hPeriod patch
    coordinate shift pole _ hCurrent.2
  have hInverse := (stereographicToHolonomicTransition_isLocalDiffeomorphAt
    period hPeriod patch coordinate shift pole point hPoint).localInverse_right_inv hCurrent.1
  change stereographicToHolonomicTransition period hPeriod patch coordinate shift pole
    (holonomicToStereographicLocalInverse
      period hPeriod patch coordinate shift pole point hPoint current) = current at hInverse
  rw [hInverse] at hPhysical
  exact hPhysical.symm

/-- The inverse direction also has the exact physical differential. -/
theorem holonomicToStereographicLocalInverse_mfderiv
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole)
    (current : Vector4)
    (hCurrent : current ∈ holonomicToStereographicDomain
      period hPeriod patch coordinate shift pole point hPoint) :
    (mfderiv coverModelWithCorners coverModelWithCorners
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole)
      (holonomicToStereographicLocalInverse
        period hPeriod patch coordinate shift pole point hPoint current)).comp
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          (holonomicToStereographicLocalInverse
            period hPeriod patch coordinate shift pole point hPoint) current) =
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap current := by
  let inverse := holonomicToStereographicLocalInverse
    period hPeriod patch coordinate shift pole point hPoint
  have hNeighborhood := (holonomicToStereographicDomain_isOpen
    period hPeriod patch coordinate shift pole point hPoint).mem_nhds hCurrent
  have hAgreement : shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘
      inverse =ᶠ[𝓝 current] patch.coordinateMap :=
    Filter.eventuallyEq_of_mem hNeighborhood (fun next hNext =>
      holonomicToStereographicLocalInverse_physical_agreement
        period hPeriod patch coordinate shift pole point hPoint next hNext)
  rw [← mfderiv_comp current
    ((shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph_smooth
      period hPeriod shift pole (inverse current)).mdifferentiableAt (by simp))
    ((inverse.contMDiffOn_toFun.contMDiffAt
      (inverse.open_source.mem_nhds hCurrent.1)).mdifferentiableAt (by simp))]
  exact hAgreement.mfderiv_eq

/-- A genuine smooth coordinate change into the measured strip exists around
every holonomic coordinate, with the physical-map identity on its whole domain. -/
theorem canonical_holonomic_stereographic_inverse_gate
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    ∃ (shift : Real) (pole : StandardSphere) (domain : Set Vector4)
        (transition : Vector4 → Coordinates),
      coordinate ∈ domain ∧ IsOpen domain ∧ ContDiffOn Real ∞ transition domain ∧
      InjOn transition domain ∧
      MapsTo transition domain (range (canonicalInteriorStereographicCoordinateInclusion period)) ∧
      EqOn (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘ transition)
        patch.coordinateMap domain := by
  obtain ⟨shift, pole, point, hPoint, hBase, _⟩ :=
    canonical_holonomic_stereographic_overlap_gate period hPeriod patch coordinate
  refine ⟨shift, pole,
    holonomicToStereographicDomain period hPeriod patch coordinate shift pole point hPoint,
    holonomicToStereographicLocalInverse period hPeriod patch coordinate shift pole point hPoint,
    ?_, holonomicToStereographicDomain_isOpen
      period hPeriod patch coordinate shift pole point hPoint,
    holonomicToStereographicLocalInverse_contDiffOn
      period hPeriod patch coordinate shift pole point hPoint,
    holonomicToStereographicLocalInverse_injOn
      period hPeriod patch coordinate shift pole point hPoint,
    fun _ hCurrent => hCurrent.2.1,
    fun current hCurrent => holonomicToStereographicLocalInverse_physical_agreement
      period hPeriod patch coordinate shift pole point hPoint current hCurrent⟩
  have hMem := holonomicToStereographicDomain_base_mem
    period hPeriod patch coordinate shift pole point hPoint
  rwa [hBase] at hMem

end
end P0EFTJanusCanonicalHolonomicStereographicInverse4D
end JanusFormal
