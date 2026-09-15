import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateLocalDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D

/-!
# Warped-null incidence in an adapted physical coordinate

This gate replaces the fixed atlas chart in the conditional incidence datum
by an arbitrary smooth partial diffeomorphism from the effective bulk to the
four ambient coordinates.  Only validity at the zero face is recorded.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCoordinateIncidence4D

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
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D
open P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateLocalDiffeomorph4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance finiteCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
  cutThroatFiniteCollarChartedSpace period hPeriod

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Incidence of the warped-null face in a freely selected physical
coordinate chart.  Chart validity is required only on the face. -/
structure ProgramPT06WarpedNullCoordinateIncidenceDatum
    (input : FiniteNullFacePhysicalHilbert Unit) where
  input_mem_domain :
    input ∈ (programPT06ExplicitWarpedNullHyperplaneGeometry Unit).domain
  sourceDomain : Set ProgramPT06NullFaceSource3
  sourceDomain_isOpen : IsOpen sourceDomain
  sourceDomain_nonempty : sourceDomain.Nonempty
  boundaryMap : ProgramPT06NullFaceSource3 →
    CutThroatBoundary period hPeriod
  boundaryMap_contMDiffOn :
    ContMDiffOn (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      throatCoverModelWithCorners 3 boundaryMap sourceDomain
  coordinateChart : PartialDiffeomorph coverModelWithCorners
    (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
    (ProgramPT06EffectiveBulk period hPeriod)
    ProgramPT06AmbientCoordinate4 ∞
  face_mem_chart : ∀ source, source ∈ sourceDomain →
    cutThroatBoundaryToBulk period hPeriod (boundaryMap source) ∈
      coordinateChart.source
  face_coordinate : ∀ source, source ∈ sourceDomain →
    coordinateChart
        (cutThroatBoundaryToBulk period hPeriod (boundaryMap source)) =
      programPT06WarpedNullHyperplaneEmbedding source

/-- The selected physical point on the true cut boundary. -/
def programPT06WarpedNullCoordinateTrueBoundaryPoint
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3) :
    ProgramPT06EffectiveBulk period hPeriod :=
  cutThroatBoundaryToBulk period hPeriod (incidence.boundaryMap source)

/-- The selected source patch times the finite normal interval. -/
def programPT06WarpedNullCoordinateCollarDomain
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input) :
    Set ProgramPT06NullFaceFiniteCollar :=
  incidence.sourceDomain ×ˢ Set.univ

theorem programPT06WarpedNullCoordinateCollarDomain_isOpen
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input) :
    IsOpen (programPT06WarpedNullCoordinateCollarDomain
      period hPeriod incidence) :=
  incidence.sourceDomain_isOpen.prod isOpen_univ

/-- Source collar parameters mapped to the genuine cut collar. -/
def programPT06WarpedNullCoordinateCollarMap
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input) :
    ProgramPT06NullFaceFiniteCollar → CutThroatFiniteCollar period hPeriod :=
  fun parameter => (incidence.boundaryMap parameter.1, parameter.2)

theorem programPT06WarpedNullCoordinateCollarMap_contMDiffOn
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input) :
    ContMDiffOn programPT06NullFaceCollarModelWithCorners
      cutCollarModelWithCorners 3
      (programPT06WarpedNullCoordinateCollarMap period hPeriod incidence)
      (programPT06WarpedNullCoordinateCollarDomain
        period hPeriod incidence) := by
  exact (incidence.boundaryMap_contMDiffOn.comp contMDiffOn_fst
    (fun _ hParameter => hParameter.1)).prodMk contMDiffOn_snd

/-- Source collar parameters mapped into the genuine effective bulk. -/
def programPT06WarpedNullCoordinateAmbientMap
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input) :
    ProgramPT06NullFaceFiniteCollar →
      ProgramPT06EffectiveBulk period hPeriod :=
  cutBulkFiniteCollarToAmbient period hPeriod ∘
    programPT06WarpedNullCoordinateCollarMap period hPeriod incidence

theorem programPT06WarpedNullCoordinateAmbientMap_contMDiffOn
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input) :
    ContMDiffOn programPT06NullFaceCollarModelWithCorners
      coverModelWithCorners 3
      (programPT06WarpedNullCoordinateAmbientMap period hPeriod incidence)
      (programPT06WarpedNullCoordinateCollarDomain
        period hPeriod incidence) := by
  exact ((cutBulkFiniteCollarToAmbient_contMDiff period hPeriod).of_le
    (WithTop.coe_le_coe.mpr le_top)).comp_contMDiffOn
    (programPT06WarpedNullCoordinateCollarMap_contMDiffOn
      period hPeriod incidence)

@[simp] theorem programPT06WarpedNullCoordinateAmbientMap_zeroFace
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullCoordinateAmbientMap period hPeriod incidence
        (programPT06WarpedNullZeroFace source) =
      programPT06WarpedNullCoordinateTrueBoundaryPoint
        period hPeriod incidence source := by
  change cutBulkFiniteCollarToAmbient period hPeriod
      (cutThroatFace period hPeriod (incidence.boundaryMap source)) = _
  unfold cutBulkFiniteCollarToAmbient
    programPT06WarpedNullCoordinateTrueBoundaryPoint
  rw [cutCollarAttachment_cutThroatFace,
    cutBulkToAmbient_cutBoundaryInclusion]

/-- Adapted ambient coordinates of the genuine collar. -/
def programPT06WarpedNullCoordinateChartCoordinate
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input) :
    ProgramPT06NullFaceFiniteCollar → ProgramPT06AmbientCoordinate4 :=
  incidence.coordinateChart ∘
    programPT06WarpedNullCoordinateAmbientMap period hPeriod incidence

@[simp] theorem programPT06WarpedNullCoordinateChartCoordinate_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06WarpedNullCoordinateChartCoordinate period hPeriod incidence
        (programPT06WarpedNullZeroFace source) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  rw [programPT06WarpedNullCoordinateChartCoordinate,
    Function.comp_apply,
    programPT06WarpedNullCoordinateAmbientMap_zeroFace]
  exact incidence.face_coordinate source hSource

theorem programPT06WarpedNullCoordinateWarpedFace_mem_chartTarget
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06WarpedNullHyperplaneEmbedding source ∈
      incidence.coordinateChart.target := by
  rw [← incidence.face_coordinate source hSource]
  exact incidence.coordinateChart.map_source
    (incidence.face_mem_chart source hSource)

theorem programPT06WarpedNullCoordinateChartInverse_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    incidence.coordinateChart.symm
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullCoordinateTrueBoundaryPoint
        period hPeriod incidence source := by
  rw [← incidence.face_coordinate source hSource]
  exact incidence.coordinateChart.left_inv
    (incidence.face_mem_chart source hSource)

/-- The installed extended bulk chart as a smooth partial diffeomorphism. -/
def programPT06InstalledBulkExtChartPartialDiffeomorph
    (anchor : ProgramPT06EffectiveBulk period hPeriod) :
    PartialDiffeomorph coverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates)
      (ProgramPT06EffectiveBulk period hPeriod)
      CoverCoordinates ∞ where
  toPartialEquiv := extChartAt coverModelWithCorners anchor
  open_source := isOpen_extChartAt_source anchor
  open_target := isOpen_extChartAt_target anchor
  contMDiffOn_toFun := by
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm anchor

/-- Linear conversion from installed cover coordinates to ambient
coordinates. -/
def programPT06InstalledCoverToAmbientPartialDiffeomorph :
    PartialDiffeomorph
      (modelWithCornersSelf Real CoverCoordinates)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      CoverCoordinates ProgramPT06AmbientCoordinate4 ∞ :=
  (holonomicCoordinateEquiv.trans
    programPT06AmbientHolonomicEquiv.symm).toDiffeomorph.toPartialDiffeomorph

/-- The atlas chart used by Gate 1034, bundled as a smooth partial
diffeomorphism into the ambient coordinates. -/
def programPT06InstalledBulkCoordinatePartialDiffeomorph
    (anchor : ProgramPT06EffectiveBulk period hPeriod) :
    PartialDiffeomorph coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (ProgramPT06EffectiveBulk period hPeriod)
      ProgramPT06AmbientCoordinate4 ∞ :=
  (programPT06InstalledBulkExtChartPartialDiffeomorph
    period hPeriod anchor).trans
      programPT06InstalledCoverToAmbientPartialDiffeomorph

@[simp] theorem programPT06InstalledBulkCoordinatePartialDiffeomorph_apply
    (anchor point : ProgramPT06EffectiveBulk period hPeriod) :
    programPT06InstalledBulkCoordinatePartialDiffeomorph
        period hPeriod anchor point =
      programPT06EffectiveBulkChartCoordinate period hPeriod anchor point := by
  rfl

@[simp] theorem programPT06InstalledBulkCoordinatePartialDiffeomorph_source
    (anchor : ProgramPT06EffectiveBulk period hPeriod) :
    (programPT06InstalledBulkCoordinatePartialDiffeomorph
      period hPeriod anchor).source =
      (chartAt CoverModel anchor).source := by
  rw [show
    (programPT06InstalledBulkCoordinatePartialDiffeomorph
      period hPeriod anchor).source =
      (programPT06InstalledBulkExtChartPartialDiffeomorph
          period hPeriod anchor).source ∩
        (programPT06InstalledBulkExtChartPartialDiffeomorph
          period hPeriod anchor) ⁻¹'
          programPT06InstalledCoverToAmbientPartialDiffeomorph.source by rfl]
  rw [show programPT06InstalledCoverToAmbientPartialDiffeomorph.source =
    Set.univ by rfl, Set.preimage_univ, Set.inter_univ]
  exact extChartAt_source (I := coverModelWithCorners) anchor

/-- Every old warped specialization of Gate 1034 supplies the revised
coordinate incidence datum. -/
def ProgramPT06LocalC3NullIncidenceDatum.toWarpedNullCoordinateIncidence
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06LocalC3NullIncidenceDatum period hPeriod
      (programPT06ExplicitWarpedNullHyperplaneGeometry Unit) input ()) :
    ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input where
  input_mem_domain := incidence.input_mem_domain
  sourceDomain := incidence.sourceDomain
  sourceDomain_isOpen := incidence.sourceDomain_isOpen
  sourceDomain_nonempty := incidence.sourceDomain_nonempty
  boundaryMap := incidence.boundaryMap
  boundaryMap_contMDiffOn := incidence.boundaryMap_contMDiffOn
  coordinateChart := programPT06InstalledBulkCoordinatePartialDiffeomorph
    period hPeriod incidence.chartAnchor
  face_mem_chart := by
    intro source hSource
    rw [programPT06InstalledBulkCoordinatePartialDiffeomorph_source,
      ← programPT06LocalC3NullAmbientMap_face_toBulk
        period hPeriod incidence source]
    simpa [programPT06LocalC3NullAmbientMap,
      programPT06LocalC3NullCollarMap] using
      incidence.collar_image_mem_chart source hSource
        (⊥ : CutCollarInterval)
  face_coordinate := by
    intro source hSource
    rw [programPT06InstalledBulkCoordinatePartialDiffeomorph_apply,
      ← programPT06LocalC3NullAmbientMap_face_toBulk
        period hPeriod incidence source]
    exact programPT06LocalC3NullChartCoordinate_face
      period hPeriod incidence source hSource

/-- Canonical inhabitant supplied by the first-sheet adapted coordinate. -/
def programPT06CanonicalFirstSheetWarpedNullCoordinateIncidence
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input where
  input_mem_domain := by
    change input ∈ (Set.univ : Set (FiniteNullFacePhysicalHilbert Unit))
    exact Set.mem_univ input
  sourceDomain := programPT06CanonicalFirstSheetAdaptedSourceDomain
    period hPeriod pole anchor
  sourceDomain_isOpen :=
    programPT06CanonicalFirstSheetAdaptedSourceDomain_isOpen
      period hPeriod pole anchor
  sourceDomain_nonempty :=
    programPT06CanonicalFirstSheetAdaptedSourceDomain_nonempty
      period hPeriod pole anchor
  boundaryMap := programPT06CanonicalFirstSheetBoundaryMap
    period hPeriod pole
  boundaryMap_contMDiffOn :=
    programPT06CanonicalFirstSheetBoundaryMap_contMDiffOn_three
      period hPeriod pole
      (programPT06CanonicalFirstSheetAdaptedSourceDomain
        period hPeriod pole anchor)
  coordinateChart :=
    programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
      period hPeriod pole anchor
  face_mem_chart := by
    intro source hSource
    rw [programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_source]
    exact programPT06CanonicalFirstSheet_mem_adaptedBulkDomain
      period hPeriod pole anchor source hSource
  face_coordinate := by
    intro source hSource
    rw [programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_apply]
    exact programPT06CanonicalFirstSheetAdaptedBulkCoordinate_face
      period hPeriod pole anchor source hSource

end
end P0EFTJanusProgramPT06WarpedNullCoordinateIncidence4D
end JanusFormal
