import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientNullFluxPullback4D

/-!
# Smooth canonical first-sheet boundary parametrization

This gate upgrades the canonical latitude first-sheet lift from continuity to
smoothness for the installed mapping-torus atlases.  An inverse stereographic
screen chart then gives a concrete smooth PT06 map from `(u,x,y)` into the
true first sheet of the cut boundary, with exact formulas before and after the
mapping-torus quotient.

This supplies the smooth `boundaryMap` part of the future adapted incidence
construction.  It does not choose an adapted bulk chart or prove the warped
face-coordinate identity required by the old Gate 1034 datum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

local instance canonicalLatitudeSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance canonicalLatitudeSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2))
      (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance canonicalLatitudeBaseChartedSpace :
    ChartedSpace CanonicalLatitudeBaseModel CanonicalLatitudeBase := inferInstance

local instance boundaryCoverChartedSpace :
    ChartedSpace ThroatCoverModel (BoundaryCover period hPeriod) :=
  fixedThroatCoverChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance boundaryCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (BoundaryCover period hPeriod) :=
  fixedThroatCover_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  fixedThroatQuotientChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance boundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  fixedThroatQuotient_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- The canonical first-sheet lift is `C∞` for the installed atlases. -/
theorem canonicalLatitudeCutBoundaryFirstLift_contMDiff :
    ContMDiff canonicalLatitudeBaseModelWithCorners
      throatCoverModelWithCorners ∞
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod) := by
  have hSphere : ContMDiff
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2)))
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      equatorialTwoSphereHomeomorph.symm :=
    chartedSpacePullback_invFun_contMDiff
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
        equatorialTwoSphereHomeomorph
  have hProduct : ContMDiff canonicalLatitudeBaseModelWithCorners
      throatCoverModelWithCorners ∞
      (fun base : CanonicalLatitudeBase ↦
        (equatorialTwoSphereHomeomorph.symm base.1, base.2)) :=
    (hSphere.comp contMDiff_fst).prodMk contMDiff_snd
  have hCover : ContMDiff canonicalLatitudeBaseModelWithCorners
      throatCoverModelWithCorners ∞
      (fun base : CanonicalLatitudeBase ↦
        (⟨equatorialTwoSphereHomeomorph.symm base.1, base.2⟩ :
          BoundaryCover period hPeriod)) :=
    ((chartedSpacePullback_invFun_contMDiff throatCoverModelWithCorners ∞
      (coverHomeomorphProd (orientationDoubleData period hPeriod))).comp
        hProduct).congr fun _ ↦ rfl
  have hProjection : IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (mappingTorusMk (orientationDoubleData period hPeriod)) :=
    fixedThroat_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  exact
    ((hProjection.contMDiff.of_le (m := ∞) (by simp)).comp hCover).congr
      fun _ ↦ rfl

/-- Global inverse stereographic parametrization of the standard equatorial
two-sphere, omitting the selected pole. -/
def standardEquatorialStereographicInverse
    (pole : StandardEquatorialTwoSphere)
    (screen : FiniteNullFaceScreenCoordinate2) :
    StandardEquatorialTwoSphere :=
  (stereographic' 2 pole).symm screen

theorem standardEquatorialStereographicInverse_contMDiff
    (pole : StandardEquatorialTwoSphere) :
    ContMDiff
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ∞
      (standardEquatorialStereographicInverse pole) := by
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
  have hSmooth := contMDiffOn_symm_of_mem_maximalAtlas hChartAt
  rw [stereographic'_target, contMDiffOn_univ] at hSmooth
  exact hSmooth.of_le (m := ∞) (by simp)

/-- Swap the PT06 generator/screen coordinates into canonical latitude
coordinates, using one inverse stereographic chart on the screen. -/
def programPT06CanonicalStereographicLatitudeBase
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) : CanonicalLatitudeBase :=
  (standardEquatorialStereographicInverse pole source.2, source.1)

theorem programPT06CanonicalStereographicLatitudeBase_contMDiff
    (pole : StandardEquatorialTwoSphere) :
    ContMDiff (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      canonicalLatitudeBaseModelWithCorners ∞
      (programPT06CanonicalStereographicLatitudeBase pole) := by
  have hScreen : ContMDiff
      (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ∞
      (fun source : ProgramPT06NullFaceSource3 ↦ source.2) :=
    (ContinuousLinearMap.snd Real Real FiniteNullFaceScreenCoordinate2)
      |>.contDiff.contMDiff
  have hTime : ContMDiff
      (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      (modelWithCornersSelf Real Real) ∞
      (fun source : ProgramPT06NullFaceSource3 ↦ source.1) :=
    (ContinuousLinearMap.fst Real Real FiniteNullFaceScreenCoordinate2)
      |>.contDiff.contMDiff
  exact
    ((standardEquatorialStereographicInverse_contMDiff pole).comp hScreen).prodMk
      hTime

/-- PT06 source coordinates mapped to the canonical first sheet of the cut
boundary. -/
def programPT06CanonicalFirstSheetBoundaryMap
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) :
    CutThroatBoundary period hPeriod :=
  canonicalLatitudeCutBoundaryFirstLift period hPeriod
    (programPT06CanonicalStereographicLatitudeBase pole source)

theorem programPT06CanonicalFirstSheetBoundaryMap_contMDiff
    (pole : StandardEquatorialTwoSphere) :
    ContMDiff (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      throatCoverModelWithCorners ∞
      (programPT06CanonicalFirstSheetBoundaryMap period hPeriod pole) :=
  (canonicalLatitudeCutBoundaryFirstLift_contMDiff period hPeriod).comp
    (programPT06CanonicalStereographicLatitudeBase_contMDiff pole)

theorem programPT06CanonicalFirstSheetBoundaryMap_contMDiffOn_three
    (pole : StandardEquatorialTwoSphere)
    (sourceDomain : Set ProgramPT06NullFaceSource3) :
    ContMDiffOn (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      throatCoverModelWithCorners 3
      (programPT06CanonicalFirstSheetBoundaryMap period hPeriod pole)
      sourceDomain :=
  ((programPT06CanonicalFirstSheetBoundaryMap_contMDiff
    period hPeriod pole).of_le (m := 3)
      (WithTop.coe_le_coe.mpr le_top)).contMDiffOn

@[simp] theorem programPT06CanonicalFirstSheetBoundaryMap_eq_firstLift
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) :
    programPT06CanonicalFirstSheetBoundaryMap period hPeriod pole source =
      canonicalLatitudeCutBoundaryFirstLift period hPeriod
        (programPT06CanonicalStereographicLatitudeBase pole source) :=
  rfl

theorem programPT06CanonicalFirstSheetBoundaryMap_eq_mk
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) :
    programPT06CanonicalFirstSheetBoundaryMap period hPeriod pole source =
      mappingTorusMk (orientationDoubleData period hPeriod)
        ⟨equatorialTwoSphereHomeomorph.symm
            (standardEquatorialStereographicInverse pole source.2),
          source.1⟩ :=
  rfl

end
end P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
end JanusFormal
