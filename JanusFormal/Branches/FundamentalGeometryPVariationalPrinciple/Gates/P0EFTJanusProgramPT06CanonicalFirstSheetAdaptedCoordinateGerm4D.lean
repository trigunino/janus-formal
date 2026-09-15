import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D

/-!
# Adapted coordinate germ on the canonical first sheet

Around every stereographically parametrized point of the canonical first
sheet, the tubular-band map has a smooth local inverse.  Reading its
equatorial base, time, and signed latitude normal and then applying the
warped shear `(u,x,y,r) ↦ (u,x,y,u+r)` gives a smooth ambient coordinate
germ whose zero face is exactly `(u,x,y,u)`.

The construction is point-local.  Its source patch contains the selected
face point, but no claim is made that one inverse patch contains the full
finite normal interval `[0,1]`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
open P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveBulk :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev BandSpacetime := equatorialSphericalBandOpen × Real

local instance canonicalLatitudeSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance canonicalLatitudeSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2))
      (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- Zero in the open tubular-normal interval. -/
def programPT06ZeroTubularNormal : equatorialTubularNormalOpen :=
  ⟨0, by
    constructor <;> nlinarith [Real.pi_pos]⟩

/-- The tubular-band representative of the canonical first-sheet point
labelled by `(u,x,y)`. -/
def programPT06CanonicalFirstSheetBandPoint
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) : BandSpacetime :=
  (equatorialTubularSmoothMap
      (equatorialTwoSphereHomeomorph.symm
          (standardEquatorialStereographicInverse pole source.2),
        programPT06ZeroTubularNormal),
    source.1)

theorem programPT06CanonicalFirstSheetBandPoint_contMDiff
    (pole : StandardEquatorialTwoSphere) :
    ContMDiff (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      coverModelWithCorners ∞
      (programPT06CanonicalFirstSheetBandPoint pole) := by
  have hSphere : ContMDiff
      (modelWithCornersSelf Real ProgramPT06NullFaceSource3) (𝓡 2) ∞
      (fun source : ProgramPT06NullFaceSource3 =>
        equatorialTwoSphereHomeomorph.symm
          (standardEquatorialStereographicInverse pole source.2)) :=
    (chartedSpacePullback_invFun_contMDiff (𝓡 2) ∞
      equatorialTwoSphereHomeomorph).comp
        ((standardEquatorialStereographicInverse_contMDiff pole).comp
          ((ContinuousLinearMap.snd Real Real
            FiniteNullFaceScreenCoordinate2).contDiff.contMDiff))
  have hBand : ContMDiff
      (modelWithCornersSelf Real ProgramPT06NullFaceSource3) (𝓡 3) ∞
      (fun source : ProgramPT06NullFaceSource3 =>
        equatorialTubularSmoothMap
          (equatorialTwoSphereHomeomorph.symm
              (standardEquatorialStereographicInverse pole source.2),
            programPT06ZeroTubularNormal)) :=
    equatorialTubularSmoothMap_contMDiff.comp
      (hSphere.prodMk contMDiff_const)
  have hTime : ContMDiff
      (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      (modelWithCornersSelf Real Real) ∞
      (fun source : ProgramPT06NullFaceSource3 => source.1) :=
    (ContinuousLinearMap.fst Real Real FiniteNullFaceScreenCoordinate2)
      |>.contDiff.contMDiff
  exact hBand.prodMk hTime

/-- The true first-sheet point is represented by the zero-normal tubular-band
point in the effective bulk. -/
theorem programPT06CanonicalFirstSheetBandPoint_toAmbient
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) :
    tubularBandSpacetimeToAmbient period hPeriod
        (programPT06CanonicalFirstSheetBandPoint pole source) =
      cutThroatBoundaryToBulk period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole source) := by
  rw [programPT06CanonicalFirstSheetBoundaryMap_eq_mk]
  simp only [cutThroatBoundaryToBulk, Function.comp_apply]
  rw [orientationDoubleToThroat_mk, fixedThroatQuotientInclusion_mk]
  unfold tubularBandSpacetimeToAmbient
  apply congrArg (mappingTorusMk (reflectedSphereData period hPeriod))
  unfold tubularBandSpacetimeToAmbientCover
  simp only [programPT06CanonicalFirstSheetBandPoint,
    programPT06ZeroTubularNormal, equatorialTubularSmoothMap,
    equatorialLatitude_zero]
  change (coverHomeomorphProd (reflectedSphereData period hPeriod)).symm
      (equatorialSphereInclusion
          (equatorialTwoSphereHomeomorph.symm
            (standardEquatorialStereographicInverse pole source.2)),
        source.1) =
    fixedThroatCoverInclusion period hPeriod
      ((orientationDoubleCoverHomeomorph period hPeriod)
        ⟨equatorialTwoSphereHomeomorph.symm
            (standardEquatorialStereographicInverse pole source.2),
          source.1⟩)
  rfl

/-- Stereographic coordinates on the standard equatorial sphere, packaged as
a smooth partial diffeomorphism. -/
private def standardEquatorialStereographicPartialDiffeomorph
    (pole : StandardEquatorialTwoSphere) :
    PartialDiffeomorph
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)
      StandardEquatorialTwoSphere FiniteNullFaceScreenCoordinate2 ∞ where
  toPartialEquiv := (stereographic' 2 pole).toPartialEquiv
  open_source := (stereographic' 2 pole).open_source
  open_target := (stereographic' 2 pole).open_target
  contMDiffOn_toFun := by
    have hChartEq :
        chartAt (EuclideanSpace Real (Fin 2)) (-pole) =
          stereographic' 2 pole := by
      change stereographic' 2 (- -pole) = stereographic' 2 pole
      rw [neg_neg]
    have hChartAt :
        chartAt (EuclideanSpace Real (Fin 2)) (-pole) ∈
          IsManifold.maximalAtlas
            (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ω
            StandardEquatorialTwoSphere :=
      IsManifold.chart_mem_maximalAtlas
        (I := modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) (-pole)
    rw [hChartEq] at hChartAt
    exact (contMDiffOn_of_mem_maximalAtlas hChartAt).of_le (by simp)
  contMDiffOn_invFun := by
    have hChartEq :
        chartAt (EuclideanSpace Real (Fin 2)) (-pole) =
          stereographic' 2 pole := by
      change stereographic' 2 (- -pole) = stereographic' 2 pole
      rw [neg_neg]
    have hChartAt :
        chartAt (EuclideanSpace Real (Fin 2)) (-pole) ∈
          IsManifold.maximalAtlas
            (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ω
            StandardEquatorialTwoSphere :=
      IsManifold.chart_mem_maximalAtlas
        (I := modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) (-pole)
    rw [hChartEq] at hChartAt
    exact (contMDiffOn_symm_of_mem_maximalAtlas hChartAt).of_le (by simp)

/-- Tubular-band points on which the selected stereographic screen coordinate
is valid. -/
def programPT06WarpedNullBandCoordinateDomain
    (pole : StandardEquatorialTwoSphere) : Set BandSpacetime :=
  { point |
    (equatorialBandCanonicalParameter point).1.1 ∈
      (stereographic' 2 pole).source }

theorem programPT06WarpedNullBandCoordinateDomain_isOpen
    (pole : StandardEquatorialTwoSphere) :
    IsOpen (programPT06WarpedNullBandCoordinateDomain pole) := by
  have hBase : ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ∞
      (fun point : BandSpacetime =>
        (equatorialBandCanonicalParameter point).1.1) :=
    contMDiff_fst.comp
      (contMDiff_fst.comp equatorialBandCanonicalParameter_contMDiff)
  exact hBase.continuous.isOpen_preimage _
    (standardEquatorialStereographicPartialDiffeomorph pole).open_source

/-- Read `(u,x,y,r)` from tubular-band coordinates and shear the last
coordinate to `u+r`. -/
def programPT06WarpedNullBandCoordinate
    (pole : StandardEquatorialTwoSphere)
    (point : BandSpacetime) : ProgramPT06AmbientCoordinate4 :=
  let parameter := equatorialBandCanonicalParameter point
  programPT06WarpedNullCollarEquiv
    ((parameter.1.2, (stereographic' 2 pole) parameter.1.1), parameter.2)

theorem programPT06WarpedNullBandCoordinate_contMDiffOn
    (pole : StandardEquatorialTwoSphere) :
    ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) ∞
      (programPT06WarpedNullBandCoordinate pole)
      (programPT06WarpedNullBandCoordinateDomain pole) := by
  have hParameter := equatorialBandCanonicalParameter_contMDiff
  have hSphere : ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ∞
      (fun point : BandSpacetime =>
        (equatorialBandCanonicalParameter point).1.1) :=
    contMDiff_fst.comp (contMDiff_fst.comp hParameter)
  have hScreen : ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ∞
      (fun point : BandSpacetime =>
        (stereographic' 2 pole)
          (equatorialBandCanonicalParameter point).1.1)
      (programPT06WarpedNullBandCoordinateDomain pole) :=
    (standardEquatorialStereographicPartialDiffeomorph pole).contMDiffOn_toFun.comp
      hSphere.contMDiffOn (fun _ hPoint => hPoint)
  have hTime : ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun point : BandSpacetime =>
        (equatorialBandCanonicalParameter point).1.2) :=
    contMDiff_snd.comp (contMDiff_fst.comp hParameter)
  have hNormal : ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun point : BandSpacetime =>
        (equatorialBandCanonicalParameter point).2) :=
    contMDiff_snd.comp hParameter
  have hCoordinate : ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06WarpedNullCollarCoordinate4) ∞
      (fun point : BandSpacetime =>
        (((equatorialBandCanonicalParameter point).1.2,
            (stereographic' 2 pole)
              (equatorialBandCanonicalParameter point).1.1),
          (equatorialBandCanonicalParameter point).2))
      (programPT06WarpedNullBandCoordinateDomain pole) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (hTime.contMDiffOn.prodMk hScreen).prodMk hNormal.contMDiffOn
  exact programPT06WarpedNullCollarEquiv.contDiff.contMDiff.comp_contMDiffOn
    hCoordinate

theorem programPT06CanonicalFirstSheetBandPoint_mem_coordinateDomain
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) :
    programPT06CanonicalFirstSheetBandPoint pole source ∈
      programPT06WarpedNullBandCoordinateDomain pole := by
  change (equatorialBandCanonicalParameter
    (programPT06CanonicalFirstSheetBandPoint pole source)).1.1 ∈
      (stereographic' 2 pole).source
  unfold programPT06CanonicalFirstSheetBandPoint
    equatorialBandCanonicalParameter
  rw [equatorialTubularSmoothInverse_map]
  change (stereographic' 2 pole).symm source.2 ∈
    (stereographic' 2 pole).source
  exact (stereographic' 2 pole).map_target (by simp)

/-- On the canonical first sheet the adapted tubular coordinate is exactly
the explicit warped null hyperplane embedding. -/
@[simp] theorem programPT06WarpedNullBandCoordinate_firstSheet
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullBandCoordinate pole
        (programPT06CanonicalFirstSheetBandPoint pole source) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  unfold programPT06WarpedNullBandCoordinate
    programPT06CanonicalFirstSheetBandPoint
    equatorialBandCanonicalParameter
  rw [equatorialTubularSmoothInverse_map]
  simp [programPT06ZeroTubularNormal,
    standardEquatorialStereographicInverse]

/-- The selected local inverse of the tubular-band map at one first-sheet
point. -/
def programPT06CanonicalFirstSheetTubularLocalInverse
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    PartialDiffeomorph coverModelWithCorners coverModelWithCorners
      (EffectiveBulk period hPeriod) BandSpacetime ∞ :=
  ((tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod)
    (programPT06CanonicalFirstSheetBandPoint pole anchor)).localInverse

/-- Ambient domain on which the local inverse lands in the selected
stereographic tubular coordinate. -/
def programPT06CanonicalFirstSheetAdaptedBulkDomain
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) : Set (EffectiveBulk period hPeriod) :=
  let inverse := programPT06CanonicalFirstSheetTubularLocalInverse
    period hPeriod pole anchor
  inverse.source ∩ inverse ⁻¹'
    programPT06WarpedNullBandCoordinateDomain pole

theorem programPT06CanonicalFirstSheetAdaptedBulkDomain_isOpen
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    IsOpen (programPT06CanonicalFirstSheetAdaptedBulkDomain
      period hPeriod pole anchor) := by
  let inverse := programPT06CanonicalFirstSheetTubularLocalInverse
    period hPeriod pole anchor
  exact inverse.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    inverse.open_source (programPT06WarpedNullBandCoordinateDomain_isOpen pole)

/-- The sheared coordinate read through the tubular local inverse. -/
def programPT06CanonicalFirstSheetAdaptedBulkCoordinate
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3)
    (point : EffectiveBulk period hPeriod) : ProgramPT06AmbientCoordinate4 :=
  programPT06WarpedNullBandCoordinate pole
    (programPT06CanonicalFirstSheetTubularLocalInverse
      period hPeriod pole anchor point)

theorem programPT06CanonicalFirstSheetAdaptedBulkCoordinate_contMDiffOn
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) ∞
      (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
        period hPeriod pole anchor)
      (programPT06CanonicalFirstSheetAdaptedBulkDomain
        period hPeriod pole anchor) := by
  let inverse := programPT06CanonicalFirstSheetTubularLocalInverse
    period hPeriod pole anchor
  exact (programPT06WarpedNullBandCoordinate_contMDiffOn pole).comp
    (inverse.contMDiffOn_toFun.mono inter_subset_left)
    (fun _ hPoint => hPoint.2)

/-- Source points whose tubular representatives stay in the chosen local
inverse target.  This is a face patch; it imposes no full-collar claim. -/
def programPT06CanonicalFirstSheetAdaptedSourceDomain
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) : Set ProgramPT06NullFaceSource3 :=
  programPT06CanonicalFirstSheetBandPoint pole ⁻¹'
    (programPT06CanonicalFirstSheetTubularLocalInverse
      period hPeriod pole anchor).target

theorem programPT06CanonicalFirstSheetAdaptedSourceDomain_isOpen
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    IsOpen (programPT06CanonicalFirstSheetAdaptedSourceDomain
      period hPeriod pole anchor) :=
  (programPT06CanonicalFirstSheetBandPoint_contMDiff pole).continuous.isOpen_preimage _
    (programPT06CanonicalFirstSheetTubularLocalInverse
      period hPeriod pole anchor).open_target

theorem programPT06CanonicalFirstSheetAdaptedSourceDomain_anchor_mem
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    anchor ∈ programPT06CanonicalFirstSheetAdaptedSourceDomain
      period hPeriod pole anchor := by
  exact ((tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod)
    (programPT06CanonicalFirstSheetBandPoint pole anchor)).localInverse_mem_target

theorem programPT06CanonicalFirstSheetAdaptedSourceDomain_nonempty
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    (programPT06CanonicalFirstSheetAdaptedSourceDomain
      period hPeriod pole anchor).Nonempty :=
  ⟨anchor,
    programPT06CanonicalFirstSheetAdaptedSourceDomain_anchor_mem
      period hPeriod pole anchor⟩

/-- Every selected first-sheet point lies in the ambient adapted-coordinate
domain. -/
theorem programPT06CanonicalFirstSheet_mem_adaptedBulkDomain
    (pole : StandardEquatorialTwoSphere)
    (anchor source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ programPT06CanonicalFirstSheetAdaptedSourceDomain
      period hPeriod pole anchor) :
    cutThroatBoundaryToBulk period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole source) ∈
      programPT06CanonicalFirstSheetAdaptedBulkDomain
        period hPeriod pole anchor := by
  rw [← programPT06CanonicalFirstSheetBandPoint_toAmbient
    period hPeriod pole source]
  let hLocal := (tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod)
    (programPT06CanonicalFirstSheetBandPoint pole anchor)
  change programPT06CanonicalFirstSheetBandPoint pole source ∈
    hLocal.localInverse.target at hSource
  change tubularBandSpacetimeToAmbient period hPeriod
      (programPT06CanonicalFirstSheetBandPoint pole source) ∈
    hLocal.localInverse.source ∩
      hLocal.localInverse ⁻¹' programPT06WarpedNullBandCoordinateDomain pole
  refine ⟨?_, ?_⟩
  · rw [hLocal.choose_spec.2 hSource]
    exact hLocal.localInverse.map_target hSource
  · change hLocal.localInverse
        (tubularBandSpacetimeToAmbient period hPeriod
          (programPT06CanonicalFirstSheetBandPoint pole source)) ∈
        programPT06WarpedNullBandCoordinateDomain pole
    rw [hLocal.localInverse_left_inv hSource]
    exact programPT06CanonicalFirstSheetBandPoint_mem_coordinateDomain pole source

/-- Exact zero-face incidence in the adapted physical coordinate germ. -/
theorem programPT06CanonicalFirstSheetAdaptedBulkCoordinate_face
    (pole : StandardEquatorialTwoSphere)
    (anchor source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ programPT06CanonicalFirstSheetAdaptedSourceDomain
      period hPeriod pole anchor) :
    programPT06CanonicalFirstSheetAdaptedBulkCoordinate
        period hPeriod pole anchor
        (cutThroatBoundaryToBulk period hPeriod
          (programPT06CanonicalFirstSheetBoundaryMap
            period hPeriod pole source)) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  rw [← programPT06CanonicalFirstSheetBandPoint_toAmbient
    period hPeriod pole source]
  unfold programPT06CanonicalFirstSheetAdaptedBulkCoordinate
  let hLocal := (tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod)
    (programPT06CanonicalFirstSheetBandPoint pole anchor)
  change programPT06CanonicalFirstSheetBandPoint pole source ∈
    hLocal.localInverse.target at hSource
  change programPT06WarpedNullBandCoordinate pole
      (hLocal.localInverse
        (tubularBandSpacetimeToAmbient period hPeriod
          (programPT06CanonicalFirstSheetBandPoint pole source))) = _
  rw [hLocal.localInverse_left_inv hSource]
  exact programPT06WarpedNullBandCoordinate_firstSheet pole source

/-- Gate bundle: the concrete adapted coordinate has open ambient and source
domains, the source contains its anchor, and the canonical first sheet is the
warped null hyperplane on that patch. -/
theorem programPT06CanonicalFirstSheetAdaptedCoordinateGerm_bundle
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    IsOpen (programPT06CanonicalFirstSheetAdaptedBulkDomain
        period hPeriod pole anchor) ∧
      IsOpen (programPT06CanonicalFirstSheetAdaptedSourceDomain
        period hPeriod pole anchor) ∧
      anchor ∈ programPT06CanonicalFirstSheetAdaptedSourceDomain
        period hPeriod pole anchor ∧
      (∀ source ∈ programPT06CanonicalFirstSheetAdaptedSourceDomain
          period hPeriod pole anchor,
        cutThroatBoundaryToBulk period hPeriod
            (programPT06CanonicalFirstSheetBoundaryMap
              period hPeriod pole source) ∈
          programPT06CanonicalFirstSheetAdaptedBulkDomain
            period hPeriod pole anchor) ∧
      ContMDiffOn coverModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) ∞
        (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
          period hPeriod pole anchor)
        (programPT06CanonicalFirstSheetAdaptedBulkDomain
          period hPeriod pole anchor) ∧
      ∀ source ∈ programPT06CanonicalFirstSheetAdaptedSourceDomain
          period hPeriod pole anchor,
        programPT06CanonicalFirstSheetAdaptedBulkCoordinate
            period hPeriod pole anchor
            (cutThroatBoundaryToBulk period hPeriod
              (programPT06CanonicalFirstSheetBoundaryMap
                period hPeriod pole source)) =
          programPT06WarpedNullHyperplaneEmbedding source := by
  exact ⟨programPT06CanonicalFirstSheetAdaptedBulkDomain_isOpen
      period hPeriod pole anchor,
    programPT06CanonicalFirstSheetAdaptedSourceDomain_isOpen
      period hPeriod pole anchor,
    programPT06CanonicalFirstSheetAdaptedSourceDomain_anchor_mem
      period hPeriod pole anchor,
    programPT06CanonicalFirstSheet_mem_adaptedBulkDomain
      period hPeriod pole anchor,
    programPT06CanonicalFirstSheetAdaptedBulkCoordinate_contMDiffOn
      period hPeriod pole anchor,
    programPT06CanonicalFirstSheetAdaptedBulkCoordinate_face
      period hPeriod pole anchor⟩

end
end P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D
end JanusFormal
