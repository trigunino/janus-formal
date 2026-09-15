import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RegularRadialProductCollarDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D

/-!
# Local C3 incidence between a null face and the cut-bulk collar

This gate packages the missing compatibility datum between one genuine mobile
null-face embedding and the existing finite collar of the cut bulk.  Under
that datum, a nonempty open source patch times the finite normal interval has
a `C³` representative in one bulk chart and its zero face is exactly the
supplied null embedding.  Every `C¹` ambient coordinate-current component
function composes regularly with this collar representative.  Gate 1032's
normalized boundary current then retains its exact prescribed null flux on
that same zero face.

The datum is conditional: no global parametrization of the cut boundary by a
finite null-face source is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
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
open P0EFTJanusProgramPT06RegularRadialProductCollarDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev ProgramPT06EffectiveBulk :=
  MappingTorus (reflectedSphereData period hPeriod)

abbrev ProgramPT06NullFaceFiniteCollar :=
  ProgramPT06NullFaceSource3 × CutCollarInterval

abbrev ProgramPT06NullFaceCollarCoordinates :=
  ProgramPT06NullFaceSource3 × EuclideanSpace Real (Fin 1)

abbrev ProgramPT06NullFaceCollarModel :=
  ModelProd ProgramPT06NullFaceSource3 (EuclideanHalfSpace 1)

abbrev programPT06NullFaceCollarModelWithCorners :
    ModelWithCorners Real ProgramPT06NullFaceCollarCoordinates
      ProgramPT06NullFaceCollarModel :=
  (modelWithCornersSelf Real ProgramPT06NullFaceSource3).prod
    (modelWithCornersEuclideanHalfSpace 1)

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

/-- Holonomic Euclidean coordinates in one extended chart of the effective
bulk. -/
def programPT06EffectiveBulkChartCoordinate
    (anchor point : ProgramPT06EffectiveBulk period hPeriod) :
    ProgramPT06AmbientCoordinate4 :=
  programPT06AmbientHolonomicEquiv.symm
    (holonomicCoordinateEquiv
      (extChartAt coverModelWithCorners anchor point))

/-- Conditional compatibility between one finite null face and one charted
finite collar of the true cut bulk. -/
structure ProgramPT06LocalC3NullIncidenceDatum
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace) where
  input_mem_domain : input ∈ geometry.domain
  sourceDomain : Set ProgramPT06NullFaceSource3
  sourceDomain_isOpen : IsOpen sourceDomain
  sourceDomain_nonempty : sourceDomain.Nonempty
  boundaryMap : ProgramPT06NullFaceSource3 →
    CutThroatBoundary period hPeriod
  boundaryMap_contMDiffOn :
    ContMDiffOn (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      throatCoverModelWithCorners 3 boundaryMap sourceDomain
  chartAnchor : ProgramPT06EffectiveBulk period hPeriod
  collar_image_mem_chart : ∀ source, source ∈ sourceDomain → ∀ normal,
    cutBulkFiniteCollarToAmbient period hPeriod (boundaryMap source, normal) ∈
      (chartAt CoverModel chartAnchor).source
  face_coordinate : ∀ source, source ∈ sourceDomain →
    programPT06EffectiveBulkChartCoordinate period hPeriod chartAnchor
        (cutBulkFiniteCollarToAmbient period hPeriod
          (boundaryMap source, (⊥ : CutCollarInterval))) =
      geometry.embedding input face source

/-- The selected source patch times the full finite normal interval. -/
def programPT06LocalC3NullCollarDomain
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    Set ProgramPT06NullFaceFiniteCollar :=
  datum.sourceDomain ×ˢ Set.univ

theorem programPT06LocalC3NullCollarDomain_isOpen
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    IsOpen (programPT06LocalC3NullCollarDomain period hPeriod datum) :=
  datum.sourceDomain_isOpen.prod isOpen_univ

theorem programPT06LocalC3NullCollarDomain_nonempty
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    (programPT06LocalC3NullCollarDomain period hPeriod datum).Nonempty := by
  rcases datum.sourceDomain_nonempty with ⟨source, hSource⟩
  exact ⟨(source, (⊥ : CutCollarInterval)), hSource, Set.mem_univ _⟩

/-- Map source collar coordinates into the genuine finite cut collar. -/
def programPT06LocalC3NullCollarMap
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    ProgramPT06NullFaceFiniteCollar →
      CutThroatFiniteCollar period hPeriod :=
  fun parameter => (datum.boundaryMap parameter.1, parameter.2)

theorem programPT06LocalC3NullCollarMap_contMDiffOn
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    ContMDiffOn programPT06NullFaceCollarModelWithCorners
      cutCollarModelWithCorners 3
      (programPT06LocalC3NullCollarMap period hPeriod datum)
      (programPT06LocalC3NullCollarDomain period hPeriod datum) := by
  exact (datum.boundaryMap_contMDiffOn.comp contMDiffOn_fst
    (fun _ hParameter => hParameter.1)).prodMk contMDiffOn_snd

/-- The source collar mapped through the existing genuine cut-bulk collar. -/
def programPT06LocalC3NullAmbientMap
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    ProgramPT06NullFaceFiniteCollar →
      ProgramPT06EffectiveBulk period hPeriod :=
  cutBulkFiniteCollarToAmbient period hPeriod ∘
    programPT06LocalC3NullCollarMap period hPeriod datum

theorem programPT06LocalC3NullAmbientMap_contMDiffOn
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    ContMDiffOn programPT06NullFaceCollarModelWithCorners
      coverModelWithCorners 3
      (programPT06LocalC3NullAmbientMap period hPeriod datum)
      (programPT06LocalC3NullCollarDomain period hPeriod datum) := by
  exact ((cutBulkFiniteCollarToAmbient_contMDiff period hPeriod).of_le
    (WithTop.coe_le_coe.mpr le_top)).comp_contMDiffOn
    (programPT06LocalC3NullCollarMap_contMDiffOn period hPeriod datum)

/-- The zero slice is the actual cut-boundary inclusion into the bulk. -/
@[simp]
theorem programPT06LocalC3NullAmbientMap_face_toBulk
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (source : ProgramPT06NullFaceSource3) :
    programPT06LocalC3NullAmbientMap period hPeriod datum
        (source, (⊥ : CutCollarInterval)) =
      cutThroatBoundaryToBulk period hPeriod (datum.boundaryMap source) := by
  change cutBulkFiniteCollarToAmbient period hPeriod
      (cutThroatFace period hPeriod (datum.boundaryMap source)) = _
  unfold cutBulkFiniteCollarToAmbient
  rw [cutCollarAttachment_cutThroatFace,
    cutBulkToAmbient_cutBoundaryInclusion]

/-- `C³` ambient-coordinate representative of the genuine cut collar. -/
def programPT06LocalC3NullChartCoordinate
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    ProgramPT06NullFaceFiniteCollar → ProgramPT06AmbientCoordinate4 :=
  programPT06EffectiveBulkChartCoordinate period hPeriod datum.chartAnchor ∘
    programPT06LocalC3NullAmbientMap period hPeriod datum

theorem programPT06LocalC3NullChartCoordinate_contMDiffOn
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    ContMDiffOn programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 3
      (programPT06LocalC3NullChartCoordinate period hPeriod datum)
      (programPT06LocalC3NullCollarDomain period hPeriod datum) := by
  have hChart : ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates) 3
      (extChartAt coverModelWithCorners datum.chartAnchor)
      (chartAt CoverModel datum.chartAnchor).source :=
    contMDiffOn_extChartAt
  have hCoordinate : ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 3
      (programPT06EffectiveBulkChartCoordinate
        period hPeriod datum.chartAnchor)
      (chartAt CoverModel datum.chartAnchor).source :=
    programPT06AmbientHolonomicEquiv.symm.contDiff.contMDiff.comp_contMDiffOn
      (holonomicCoordinateEquiv.contDiff.contMDiff.comp_contMDiffOn hChart)
  exact hCoordinate.comp
    (programPT06LocalC3NullAmbientMap_contMDiffOn period hPeriod datum)
    (fun parameter hParameter => by
      simpa [programPT06LocalC3NullAmbientMap,
        programPT06LocalC3NullCollarMap] using
        datum.collar_image_mem_chart parameter.1 hParameter.1 parameter.2)

@[simp]
theorem programPT06LocalC3NullChartCoordinate_face
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ datum.sourceDomain) :
    programPT06LocalC3NullChartCoordinate period hPeriod datum
        (source, (⊥ : CutCollarInterval)) =
    geometry.embedding input face source := by
  simpa [programPT06LocalC3NullChartCoordinate,
    programPT06LocalC3NullAmbientMap, programPT06LocalC3NullCollarMap] using
    datum.face_coordinate source hSource

/-- Coordinate map induced on the zero slice of the true cut collar. -/
def programPT06LocalC3NullFaceCoordinate
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    ProgramPT06NullFaceSource3 → ProgramPT06AmbientCoordinate4 :=
  fun source =>
    programPT06LocalC3NullChartCoordinate period hPeriod datum
      (source, (⊥ : CutCollarInterval))

@[simp]
theorem programPT06LocalC3NullFaceCoordinate_eq
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ datum.sourceDomain) :
    programPT06LocalC3NullFaceCoordinate period hPeriod datum source =
      geometry.embedding input face source :=
  programPT06LocalC3NullChartCoordinate_face
    period hPeriod datum source hSource

theorem programPT06LocalC3NullFaceCoordinate_contMDiffOn
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    ContMDiffOn (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 3
      (programPT06LocalC3NullFaceCoordinate period hPeriod datum)
      datum.sourceDomain := by
  have hZero : ContMDiff
      (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      programPT06NullFaceCollarModelWithCorners 3
      (fun source : ProgramPT06NullFaceSource3 =>
        (source, (⊥ : CutCollarInterval))) :=
    contMDiff_id.prodMk contMDiff_const
  exact (programPT06LocalC3NullChartCoordinate_contMDiffOn
    period hPeriod datum).comp hZero.contMDiffOn
      (fun _ hSource => ⟨hSource, Set.mem_univ _⟩)

theorem programPT06LocalC3NullFaceCoordinate_eqOn_embedding
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    Set.EqOn (programPT06LocalC3NullFaceCoordinate period hPeriod datum)
      (geometry.embedding input face) datum.sourceDomain :=
  fun source hSource =>
    programPT06LocalC3NullFaceCoordinate_eq
      period hPeriod datum source hSource

theorem ProgramPT06LocalC3NullIncidenceDatum.boundaryMap_injOn
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    Set.InjOn datum.boundaryMap datum.sourceDomain := by
  intro first hFirst second hSecond hEqual
  apply geometry.embedding_injective input datum.input_mem_domain face
  calc
    geometry.embedding input face first =
        programPT06EffectiveBulkChartCoordinate period hPeriod datum.chartAnchor
          (cutBulkFiniteCollarToAmbient period hPeriod
            (datum.boundaryMap first, (⊥ : CutCollarInterval))) :=
      (datum.face_coordinate first hFirst).symm
    _ = programPT06EffectiveBulkChartCoordinate period hPeriod datum.chartAnchor
          (cutBulkFiniteCollarToAmbient period hPeriod
            (datum.boundaryMap second, (⊥ : CutCollarInterval))) := by
      rw [hEqual]
    _ = geometry.embedding input face second :=
      datum.face_coordinate second hSecond

theorem ProgramPT06LocalC3NullIncidenceDatum.collarMap_injOn
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) :
    Set.InjOn (programPT06LocalC3NullCollarMap period hPeriod datum)
      (programPT06LocalC3NullCollarDomain period hPeriod datum) := by
  rintro ⟨firstSource, firstNormal⟩ hFirst
    ⟨secondSource, secondNormal⟩ hSecond hEqual
  apply Prod.ext
  · apply datum.boundaryMap_injOn period hPeriod hFirst.1 hSecond.1
    simpa [programPT06LocalC3NullCollarMap] using
      congrArg (fun point : CutThroatFiniteCollar period hPeriod => point.1) hEqual
  · simpa [programPT06LocalC3NullCollarMap] using
      congrArg (fun point : CutThroatFiniteCollar period hPeriod => point.2) hEqual

/-- An ambient coordinate-current component function evaluated along the true
cut collar's chart representative. -/
def programPT06LocalC3NullCurrent
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (current : ProgramPT06AmbientCurrent4D) :
    ProgramPT06NullFaceFiniteCollar → ProgramPT06AmbientCoordinate4 :=
  current ∘ programPT06LocalC3NullChartCoordinate period hPeriod datum

theorem programPT06LocalC3NullCurrent_contMDiffOn_one
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : ContDiff Real 1 current) :
    ContMDiffOn programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 1
      (programPT06LocalC3NullCurrent period hPeriod datum current)
      (programPT06LocalC3NullCollarDomain period hPeriod datum) := by
  exact hCurrent.contMDiff.comp_contMDiffOn
    ((programPT06LocalC3NullChartCoordinate_contMDiffOn
      period hPeriod datum).of_le (by norm_num))

/-- Gate 1032's boundary extension is regular on the selected collar patch whenever
its supplied ambient current is `C¹`. -/
theorem programPT06LocalC3NullExtensionCurrent_contMDiffOn_one
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (radial : ProgramPT06NullFaceSource3 → ThroatCoverCoordinates)
    (density : ProgramPT06NullFaceSource3 → Real)
    (extension : ProgramPT06RadialAmbientExtensionDatum
      geometry input face radial density)
    (hExtension : ContDiff Real 1 extension.current) :
    ContMDiffOn programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 1
      (programPT06LocalC3NullCurrent
        period hPeriod datum extension.current)
      (programPT06LocalC3NullCollarDomain period hPeriod datum) :=
  programPT06LocalC3NullCurrent_contMDiffOn_one
    period hPeriod datum extension.current hExtension

/-- Gate 1033's regular product-split current read along the selected collar patch. -/
def programPT06LocalC3RegularRadialCurrent
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real) :
    ProgramPT06NullFaceFiniteCollar → ProgramPT06AmbientCoordinate4 :=
  programPT06LocalC3NullCurrent period hPeriod datum
    (programPT06RegularAmbientCollarCurrent throatCurrent normalDensity)

theorem programPT06LocalC3RegularRadialCurrent_contMDiffOn_one
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    (hThroat : ContDiff Real 1 throatCurrent)
    (hNormal : ContDiff Real 1 normalDensity) :
    ContMDiffOn programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 1
      (programPT06LocalC3RegularRadialCurrent period hPeriod datum
        throatCurrent normalDensity)
      (programPT06LocalC3NullCollarDomain period hPeriod datum) := by
  exact programPT06LocalC3NullCurrent_contMDiffOn_one period hPeriod datum _
    (programPT06RegularAmbientCollarCurrent_contDiff_one hThroat hNormal)

@[simp]
theorem programPT06LocalC3RegularRadialCurrent_face
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ datum.sourceDomain) :
    programPT06LocalC3RegularRadialCurrent period hPeriod datum
        throatCurrent normalDensity (source, (⊥ : CutCollarInterval)) =
      programPT06RegularAmbientCollarCurrent throatCurrent normalDensity
        (geometry.embedding input face source) := by
  change programPT06RegularAmbientCollarCurrent throatCurrent normalDensity
      (programPT06LocalC3NullChartCoordinate period hPeriod datum
        (source, (⊥ : CutCollarInterval))) = _
  rw [programPT06LocalC3NullChartCoordinate_face _ _ _ _ hSource]

theorem programPT06LocalC3NullCurrent_on_face
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (radial : ProgramPT06NullFaceSource3 → ThroatCoverCoordinates)
    (density : ProgramPT06NullFaceSource3 → Real)
    (extension : ProgramPT06RadialAmbientExtensionDatum
      geometry input face radial density)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ datum.sourceDomain) :
    programPT06LocalC3NullCurrent period hPeriod datum extension.current
        (source, (⊥ : CutCollarInterval)) =
      programPT06RadialTangentialBoundaryLift
          (programPT06FiniteNullFaceGeometricTangentFrame
            geometry input face source)
          (radial source) +
        density source • extension.transverse source := by
  rw [programPT06LocalC3NullCurrent, Function.comp_apply,
    programPT06LocalC3NullChartCoordinate_face _ _ _ _ hSource]
  exact extension.current_on_face source

/-- The charted cut-collar zero face has the same prescribed Gate-1032
coordinate scalar flux as the genuine finite null-face embedding. -/
theorem programPT06LocalC3NullCurrent_flux_eq_density
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (radial : ProgramPT06NullFaceSource3 → ThroatCoverCoordinates)
    (density : ProgramPT06NullFaceSource3 → Real)
    (extension : ProgramPT06RadialAmbientExtensionDatum
      geometry input face radial density)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ datum.sourceDomain) :
    programPT06NullFaceFluxPullback
        (programPT06LocalC3NullFaceCoordinate period hPeriod datum)
        extension.current source programPT06NullFaceSourceFrame =
      density source := by
  have hEventually :
      programPT06LocalC3NullFaceCoordinate period hPeriod datum =ᶠ[nhds source]
        geometry.embedding input face := by
    filter_upwards [datum.sourceDomain_isOpen.mem_nhds hSource] with current hCurrent
    exact programPT06LocalC3NullFaceCoordinate_eq
      period hPeriod datum current hCurrent
  calc
    _ = programPT06NullFaceFluxPullback
          (geometry.embedding input face) extension.current source
          programPT06NullFaceSourceFrame := by
      unfold programPT06NullFaceFluxPullback programPT06ThreeFormPullback
      rw [hEventually.eq_of_nhds, hEventually.fderiv_eq]
    _ = density source :=
      programPT06RadialAmbientExtensionDatum_flux_eq_density
        geometry input datum.input_mem_domain face radial density extension source

/-- If Gate 1032's normalized extension is the regular current of Gate 1033,
that same regular current has the prescribed coordinate flux on the selected
collar face. -/
theorem programPT06LocalC3RegularRadialCurrent_flux_eq_density_of_eq
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (radial : ProgramPT06NullFaceSource3 → ThroatCoverCoordinates)
    (density : ProgramPT06NullFaceSource3 → Real)
    (extension : ProgramPT06RadialAmbientExtensionDatum
      geometry input face radial density)
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real)
    (hCurrent : extension.current =
      programPT06RegularAmbientCollarCurrent throatCurrent normalDensity)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ datum.sourceDomain) :
    programPT06NullFaceFluxPullback
        (programPT06LocalC3NullFaceCoordinate period hPeriod datum)
        (programPT06RegularAmbientCollarCurrent
          throatCurrent normalDensity)
        source programPT06NullFaceSourceFrame = density source := by
  rw [← hCurrent]
  exact programPT06LocalC3NullCurrent_flux_eq_density
    period hPeriod datum radial density extension source hSource

end
end P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
end JanusFormal
