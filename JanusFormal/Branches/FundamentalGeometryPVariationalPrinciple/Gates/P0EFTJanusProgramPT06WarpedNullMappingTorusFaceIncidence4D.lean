import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCompactSupportedStokes4D

/-!
# Warped-null mapping-torus face incidence

This gate specializes Gate 1034's conditional local incidence datum to the
explicit warped-null hyperplane.  On its source patch, the zero face of the
genuine cut-bulk collar has exactly the warped embedding as its bulk-chart
coordinate.  Consequently the coordinate current, flux, and metric-density
formulas already proved for the warped model hold on that true boundary face.

This identifies only the zero face in one chart.  It does not identify the
full collars or transport their normal, metric, volume, or integrated Stokes
data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullCollarOrientation4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Gate 1034's conditional incidence datum specialized to the explicit
warped-null singleton face. -/
abbrev ProgramPT06WarpedNullLocalC3IncidenceDatum
    (input : FiniteNullFacePhysicalHilbert Unit) :=
  ProgramPT06LocalC3NullIncidenceDatum period hPeriod
    (programPT06ExplicitWarpedNullHyperplaneGeometry Unit) input ()

/-- The actual mapping-torus bulk point selected by the incidence datum on the
true cut-boundary face. -/
def programPT06WarpedNullTrueBoundaryPoint
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3) :
    ProgramPT06EffectiveBulk period hPeriod :=
  cutThroatBoundaryToBulk period hPeriod (incidence.boundaryMap source)

/-- The zero slice of the local genuine collar is the selected true boundary
point. -/
@[simp] theorem programPT06WarpedNullLocalAmbientMap_zeroFace
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3) :
    programPT06LocalC3NullAmbientMap period hPeriod incidence
        (programPT06WarpedNullZeroFace source) =
      programPT06WarpedNullTrueBoundaryPoint period hPeriod incidence source := by
  simp [programPT06WarpedNullZeroFace,
    programPT06WarpedNullTrueBoundaryPoint]

/-- On the incidence patch, the true boundary point has the explicit warped
null embedding as its bulk-chart coordinate. -/
theorem programPT06WarpedNullTrueBoundaryPoint_chartCoordinate
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06EffectiveBulkChartCoordinate period hPeriod incidence.chartAnchor
        (programPT06WarpedNullTrueBoundaryPoint
          period hPeriod incidence source) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  rw [← programPT06WarpedNullLocalAmbientMap_zeroFace
    period hPeriod incidence source]
  exact programPT06LocalC3NullChartCoordinate_face
    period hPeriod incidence source hSource

/-- The same incidence square expressed with Gate 1045's closed-half-collar
embedding. -/
theorem programPT06WarpedNullTrueBoundaryPoint_chartCoordinate_eq_closedHalfCollar
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06EffectiveBulkChartCoordinate period hPeriod incidence.chartAnchor
        (programPT06WarpedNullTrueBoundaryPoint
          period hPeriod incidence source) =
      programPT06WarpedNullClosedHalfCollarEmbedding
        (programPT06WarpedNullZeroFace source) := by
  rw [programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace]
  exact programPT06WarpedNullTrueBoundaryPoint_chartCoordinate
    period hPeriod incidence source hSource

/-- The selected actual boundary points are injective on the incidence patch. -/
theorem programPT06WarpedNullTrueBoundaryPoint_injOn
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input) :
    Set.InjOn
      (programPT06WarpedNullTrueBoundaryPoint period hPeriod incidence)
      incidence.sourceDomain := by
  intro first hFirst second hSecond hEqual
  apply programPT06WarpedNullHyperplaneEmbedding_injective
  rw [← programPT06WarpedNullTrueBoundaryPoint_chartCoordinate
      period hPeriod incidence first hFirst,
    ← programPT06WarpedNullTrueBoundaryPoint_chartCoordinate
      period hPeriod incidence second hSecond,
    hEqual]

/-- Gate 1042's coordinate current has its prescribed value at the true
mapping-torus boundary point in the selected chart. -/
theorem programPT06WarpedNullTrueBoundaryPoint_affineCurrent
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06WarpedNullCollarAffineFluxExtension density
        (programPT06EffectiveBulkChartCoordinate period hPeriod
          incidence.chartAnchor
          (programPT06WarpedNullTrueBoundaryPoint
            period hPeriod incidence source)) =
      density source • programPT06WarpedNullCollarZeroBoundaryOutward := by
  rw [programPT06WarpedNullTrueBoundaryPoint_chartCoordinate
      period hPeriod incidence source hSource,
    programPT06WarpedNullCollarAffineFluxExtension_zeroSlice]

/-- The true face therefore carries the prescribed coordinate flux in Gate
1041's fixed convention. -/
theorem programPT06WarpedNullTrueBoundaryPoint_affineCurrent_flux
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06WarpedNullCollarAffineFluxExtension density
          (programPT06EffectiveBulkChartCoordinate period hPeriod
            incidence.chartAnchor
            (programPT06WarpedNullTrueBoundaryPoint
              period hPeriod incidence source)))
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) = density source := by
  rw [programPT06WarpedNullTrueBoundaryPoint_affineCurrent
    period hPeriod density incidence source hSource]
  simp only [map_smul, ContinuousAlternatingMap.smul_apply]
  rw [programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_one]
  simp

/-- The chart coordinate of the true face carries the warped metric-volume
density `exp u`. -/
theorem programPT06WarpedNullTrueBoundaryPoint_metricVolumeDensity
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06WarpedNullAmbientMetricVolumeDensity
        (programPT06EffectiveBulkChartCoordinate period hPeriod
          incidence.chartAnchor
          (programPT06WarpedNullTrueBoundaryPoint
            period hPeriod incidence source)) =
      Real.exp source.1 := by
  rw [programPT06WarpedNullTrueBoundaryPoint_chartCoordinate
      period hPeriod incidence source hSource,
    ← programPT06WarpedNullCollar_zeroSlice source,
    programPT06WarpedNullAmbientMetricVolumeDensity_collar]

/-- Gate bundle for the conditional zero-face incidence. -/
theorem programPT06WarpedNullMappingTorusFaceIncidence_bundle
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input) :
    Set.InjOn
        (programPT06WarpedNullTrueBoundaryPoint period hPeriod incidence)
        incidence.sourceDomain ∧
      (∀ source, source ∈ incidence.sourceDomain →
        programPT06EffectiveBulkChartCoordinate period hPeriod
            incidence.chartAnchor
            (programPT06WarpedNullTrueBoundaryPoint
              period hPeriod incidence source) =
          programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source)) ∧
      (∀ source, source ∈ incidence.sourceDomain →
        programPT06AmbientSignedVolume.curryLeft
            (programPT06WarpedNullCollarAffineFluxExtension density
              (programPT06EffectiveBulkChartCoordinate period hPeriod
                incidence.chartAnchor
                (programPT06WarpedNullTrueBoundaryPoint
                  period hPeriod incidence source)))
            (programPT06FiniteNullFaceGeometricTangentFrame
              (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
              0 () source) = density source) ∧
      (∀ source, source ∈ incidence.sourceDomain →
        programPT06WarpedNullAmbientMetricVolumeDensity
            (programPT06EffectiveBulkChartCoordinate period hPeriod
              incidence.chartAnchor
              (programPT06WarpedNullTrueBoundaryPoint
                period hPeriod incidence source)) =
          Real.exp source.1) := by
  exact ⟨programPT06WarpedNullTrueBoundaryPoint_injOn
      period hPeriod incidence,
    programPT06WarpedNullTrueBoundaryPoint_chartCoordinate_eq_closedHalfCollar
      period hPeriod incidence,
    programPT06WarpedNullTrueBoundaryPoint_affineCurrent_flux
      period hPeriod density incidence,
    programPT06WarpedNullTrueBoundaryPoint_metricVolumeDensity
      period hPeriod incidence⟩

end
end P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
end JanusFormal
