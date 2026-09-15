import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D

/-!
# Local-diffeomorphism certificate for the adapted first-sheet coordinate

The adapted tubular-band coordinate from Gate 1061 is a smooth local
diffeomorphism throughout its stereographic domain.  Composing it with the
selected tubular local inverse therefore gives a genuine coordinate chart at
the chosen physical face point.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateLocalDiffeomorph4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
open P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D

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

/-- The pulled-back equatorial-sphere identification is a diffeomorphism. -/
private def equatorialToStandardDiffeomorph :
    EquatorialTwoSphere ≃ₘ^∞⟮
      modelWithCornersSelf Real (EuclideanSpace Real (Fin 2)),
      modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))⟯
      StandardEquatorialTwoSphere where
  toEquiv := equatorialTwoSphereHomeomorph.toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      equatorialTwoSphereHomeomorph
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      equatorialTwoSphereHomeomorph

/-- Reorder tubular parameters as `((time, standard equator), normal)`.
No orientation sign is assigned to this permutation here. -/
private def programPT06BandParameterReassociation :
    ((EquatorialTwoSphere × equatorialTubularNormalOpen) × Real) ≃ₘ^∞⟮
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)).prod
          (modelWithCornersSelf Real Real),
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2)))).prod
          (modelWithCornersSelf Real Real)⟯
      ((Real × StandardEquatorialTwoSphere) ×
        equatorialTubularNormalOpen) where
  toFun parameter :=
    ((parameter.2, equatorialToStandardDiffeomorph parameter.1.1),
      parameter.1.2)
  invFun parameter :=
    ((equatorialToStandardDiffeomorph.symm parameter.1.2, parameter.2),
      parameter.1.1)
  left_inv parameter := by
    rcases parameter with ⟨⟨sphere, normal⟩, time⟩
    simp
  right_inv parameter := by
    rcases parameter with ⟨⟨time, sphere⟩, normal⟩
    simp
  contMDiff_toFun :=
    (contMDiff_snd.prodMk
      (equatorialToStandardDiffeomorph.contMDiff.comp
        (contMDiff_fst.comp contMDiff_fst))).prodMk
      (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun :=
    ((equatorialToStandardDiffeomorph.symm.contMDiff.comp
        (contMDiff_snd.comp contMDiff_fst)).prodMk contMDiff_snd).prodMk
      (contMDiff_fst.comp contMDiff_fst)

/-- Global tubular parameterization before applying the stereographic chart. -/
private def programPT06BandParameterDiffeomorph :
    BandSpacetime ≃ₘ^∞⟮coverModelWithCorners,
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2)))).prod
          (modelWithCornersSelf Real Real)⟯
      ((Real × StandardEquatorialTwoSphere) ×
        equatorialTubularNormalOpen) :=
  (equatorialTubularDiffeomorph.symm.prodCongr
      (Diffeomorph.refl (modelWithCornersSelf Real Real) Real ∞)).trans
    programPT06BandParameterReassociation

/-- Stereographic coordinates as a smooth partial diffeomorphism. -/
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

/-- Product of time, stereographic screen, and open normal coordinates. -/
private def programPT06WarpedNullCollarCoordinatePartialDiffeomorph
    (pole : StandardEquatorialTwoSphere) :
    PartialDiffeomorph
      (((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)).prod
          (modelWithCornersSelf Real Real))
      (((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)).prod
          (modelWithCornersSelf Real Real))
      ((Real × StandardEquatorialTwoSphere) × equatorialTubularNormalOpen)
      ProgramPT06WarpedNullCollarCoordinate4 ∞ := by
  let timeMap :=
    (Diffeomorph.refl (modelWithCornersSelf Real Real) Real ∞).toPartialDiffeomorph
  let screenMap := standardEquatorialStereographicPartialDiffeomorph pole
  let normalMap := openSubtypePartialDiffeomorph
    (modelWithCornersSelf Real Real) equatorialTubularNormalOpen
      programPT06ZeroTubularNormal
  exact partialDiffeomorphProd
    (partialDiffeomorphProd timeMap screenMap) normalMap

/-- The linear shear typed from the explicit product model. -/
private def programPT06WarpedNullShearPartialDiffeomorph :
    PartialDiffeomorph
      (((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)).prod
          (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      ProgramPT06WarpedNullCollarCoordinate4
      ProgramPT06AmbientCoordinate4 ∞ where
  toPartialEquiv :=
    programPT06WarpedNullCollarEquiv.toDiffeomorph.toPartialDiffeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    have hTime : ContMDiff
        (((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)).prod
            (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) ∞
        (fun coordinate : ProgramPT06WarpedNullCollarCoordinate4 =>
          coordinate.1.1) := contMDiff_fst.comp contMDiff_fst
    have hScreen : ContMDiff
        (((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)).prod
            (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ∞
        (fun coordinate : ProgramPT06WarpedNullCollarCoordinate4 =>
          coordinate.1.2) := contMDiff_snd.comp contMDiff_fst
    have hScreenCoordinates : ContMDiff
        (((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)).prod
            (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real (Fin 2 → Real)) ∞
        (fun coordinate : ProgramPT06WarpedNullCollarCoordinate4 =>
          EuclideanSpace.equiv (Fin 2) Real coordinate.1.2) :=
      (EuclideanSpace.equiv (Fin 2) Real).toContinuousLinearMap.contDiff.contMDiff.comp
        hScreen
    have hNormal : ContMDiff
        (((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)).prod
            (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) ∞
        (fun coordinate : ProgramPT06WarpedNullCollarCoordinate4 =>
          coordinate.2) := contMDiff_snd
    have hRaw : ContMDiff
        (((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2)).prod
            (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real (Fin 4 → Real)) ∞
        (fun coordinate : ProgramPT06WarpedNullCollarCoordinate4 =>
          ![coordinate.1.1, coordinate.1.2 0, coordinate.1.2 1,
            coordinate.1.1 + coordinate.2]) := by
      rw [contMDiff_pi_space]
      intro direction
      fin_cases direction
      · exact hTime
      · exact (contMDiff_pi_space.mp hScreenCoordinates) 0
      · exact (contMDiff_pi_space.mp hScreenCoordinates) 1
      · exact hTime.add hNormal
    exact ((EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap
      |>.contDiff.contMDiff.comp hRaw).contMDiffOn
  contMDiffOn_invFun := by
    have hCoordinates : ContMDiff
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (modelWithCornersSelf Real (Fin 4 → Real)) ∞
        (fun point : ProgramPT06AmbientCoordinate4 =>
          EuclideanSpace.equiv (Fin 4) Real point) :=
      (EuclideanSpace.equiv (Fin 4) Real).toContinuousLinearMap.contDiff.contMDiff
    have hCoordinate (direction : Fin 4) : ContMDiff
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (modelWithCornersSelf Real Real) ∞
        (fun point : ProgramPT06AmbientCoordinate4 => point direction) :=
      (contMDiff_pi_space.mp hCoordinates) direction
    have hScreenRaw : ContMDiff
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (modelWithCornersSelf Real (Fin 2 → Real)) ∞
        (fun point : ProgramPT06AmbientCoordinate4 => ![point 1, point 2]) := by
      rw [contMDiff_pi_space]
      intro direction
      fin_cases direction
      · exact hCoordinate 1
      · exact hCoordinate 2
    have hScreen : ContMDiff
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (modelWithCornersSelf Real FiniteNullFaceScreenCoordinate2) ∞
        (fun point : ProgramPT06AmbientCoordinate4 =>
          (EuclideanSpace.equiv (Fin 2) Real).symm ![point 1, point 2]) :=
      (EuclideanSpace.equiv (Fin 2) Real).symm.toContinuousLinearMap.contDiff.contMDiff.comp
        hScreenRaw
    exact (((hCoordinate 0).prodMk hScreen).prodMk
      ((hCoordinate 3).sub (hCoordinate 0))).contMDiffOn

/-- The Gate 1061 band coordinate, bundled on exactly its natural open
stereographic and tubular-normal domain. -/
def programPT06WarpedNullBandCoordinatePartialDiffeomorph
    (pole : StandardEquatorialTwoSphere) :
    PartialDiffeomorph coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      BandSpacetime ProgramPT06AmbientCoordinate4 ∞ :=
  (programPT06BandParameterDiffeomorph.toPartialDiffeomorph).trans
    ((programPT06WarpedNullCollarCoordinatePartialDiffeomorph pole).trans
      programPT06WarpedNullShearPartialDiffeomorph)

theorem programPT06WarpedNullBandCoordinatePartialDiffeomorph_apply
    (pole : StandardEquatorialTwoSphere) (point : BandSpacetime) :
    programPT06WarpedNullBandCoordinatePartialDiffeomorph pole point =
      programPT06WarpedNullBandCoordinate pole point := by
  change programPT06WarpedNullCollarEquiv
      ((point.2,
        (stereographic' 2 pole)
          (equatorialTwoSphereHomeomorph
            (equatorialTubularSmoothInverse point.1).1)),
        (equatorialTubularSmoothInverse point.1).2.1) =
    programPT06WarpedNullBandCoordinate pole point
  rfl

theorem programPT06WarpedNullBandCoordinatePartialDiffeomorph_source
    (pole : StandardEquatorialTwoSphere) :
    (programPT06WarpedNullBandCoordinatePartialDiffeomorph pole).source =
      programPT06WarpedNullBandCoordinateDomain pole := by
  ext point
  simp [programPT06WarpedNullBandCoordinatePartialDiffeomorph,
    programPT06BandParameterDiffeomorph,
    programPT06BandParameterReassociation,
    equatorialToStandardDiffeomorph,
    programPT06WarpedNullBandCoordinateDomain,
    equatorialBandCanonicalParameter,
    programPT06WarpedNullCollarCoordinatePartialDiffeomorph,
    programPT06WarpedNullShearPartialDiffeomorph,
    partialDiffeomorphProd, openSubtypePartialDiffeomorph,
    Diffeomorph.toPartialDiffeomorph, PartialDiffeomorph.trans,
    Function.comp_def]
  change equatorialTwoSphereHomeomorph
      (equatorialTubularSmoothInverse point.1).1 ∈
        (stereographic' 2 pole).source ↔
    ¬equatorialTwoSphereHomeomorph
      (equatorialTubularSmoothInverse point.1).1 = pole
  simp

/-- The adapted band coordinate is locally diffeomorphic at every point of
its natural domain. -/
theorem programPT06WarpedNullBandCoordinate_isLocalDiffeomorphAt
    (pole : StandardEquatorialTwoSphere) (point : BandSpacetime)
    (hPoint : point ∈ programPT06WarpedNullBandCoordinateDomain pole) :
    IsLocalDiffeomorphAt coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) ∞
      (programPT06WarpedNullBandCoordinate pole) point := by
  rw [← funext (programPT06WarpedNullBandCoordinatePartialDiffeomorph_apply pole)]
  exact (programPT06WarpedNullBandCoordinatePartialDiffeomorph pole).isLocalDiffeomorphAt
    _ _ _
    (by rwa [programPT06WarpedNullBandCoordinatePartialDiffeomorph_source])

/-- Explicit adapted bulk chart obtained by composing the selected tubular
inverse with the adapted band coordinate. -/
def programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    PartialDiffeomorph coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (EffectiveBulk period hPeriod) ProgramPT06AmbientCoordinate4 ∞ :=
  (programPT06CanonicalFirstSheetTubularLocalInverse
      period hPeriod pole anchor).trans
    (programPT06WarpedNullBandCoordinatePartialDiffeomorph pole)

theorem programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_apply
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3)
    (point : EffectiveBulk period hPeriod) :
    programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
        period hPeriod pole anchor point =
      programPT06CanonicalFirstSheetAdaptedBulkCoordinate
        period hPeriod pole anchor point := by
  unfold programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
    programPT06CanonicalFirstSheetAdaptedBulkCoordinate
  change programPT06WarpedNullBandCoordinatePartialDiffeomorph pole
      (programPT06CanonicalFirstSheetTubularLocalInverse
        period hPeriod pole anchor point) = _
  rw [programPT06WarpedNullBandCoordinatePartialDiffeomorph_apply]

theorem programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_source
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    (programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
      period hPeriod pole anchor).source =
      programPT06CanonicalFirstSheetAdaptedBulkDomain
        period hPeriod pole anchor := by
  unfold programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
    programPT06CanonicalFirstSheetAdaptedBulkDomain
  change (programPT06CanonicalFirstSheetTubularLocalInverse
      period hPeriod pole anchor).source ∩
      (programPT06CanonicalFirstSheetTubularLocalInverse
        period hPeriod pole anchor) ⁻¹'
        (programPT06WarpedNullBandCoordinatePartialDiffeomorph pole).source =
    (programPT06CanonicalFirstSheetTubularLocalInverse
      period hPeriod pole anchor).source ∩
      (programPT06CanonicalFirstSheetTubularLocalInverse
        period hPeriod pole anchor) ⁻¹'
        programPT06WarpedNullBandCoordinateDomain pole
  rw [programPT06WarpedNullBandCoordinatePartialDiffeomorph_source]

/-- The explicit inverse partial diffeomorphism of the adapted bulk chart. -/
def programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    PartialDiffeomorph
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      coverModelWithCorners ProgramPT06AmbientCoordinate4
      (EffectiveBulk period hPeriod) ∞ :=
  (programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
    period hPeriod pole anchor).symm

@[simp] theorem
    programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph_source
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    (programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph
      period hPeriod pole anchor).source =
      (programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
        period hPeriod pole anchor).target :=
  rfl

@[simp] theorem
    programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph_target
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    (programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph
      period hPeriod pole anchor).target =
      programPT06CanonicalFirstSheetAdaptedBulkDomain
        period hPeriod pole anchor := by
  exact programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_source
    period hPeriod pole anchor

theorem programPT06CanonicalFirstSheetAdaptedBulkInverse_left_inv
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3)
    (point : EffectiveBulk period hPeriod)
    (hPoint : point ∈ programPT06CanonicalFirstSheetAdaptedBulkDomain
      period hPeriod pole anchor) :
    programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph
        period hPeriod pole anchor
        (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
          period hPeriod pole anchor point) = point := by
  unfold programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph
  rw [← programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_apply]
  exact (programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
    period hPeriod pole anchor).left_inv
      (by rwa [programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_source])

theorem programPT06CanonicalFirstSheetAdaptedBulkInverse_right_inv
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      (programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
        period hPeriod pole anchor).target) :
    programPT06CanonicalFirstSheetAdaptedBulkCoordinate
        period hPeriod pole anchor
        (programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph
          period hPeriod pole anchor coordinate) = coordinate := by
  unfold programPT06CanonicalFirstSheetAdaptedBulkInversePartialDiffeomorph
  rw [← programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_apply]
  exact (programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
    period hPeriod pole anchor).right_inv hCoordinate

/-- At the selected physical face point, the adapted ambient coordinate is a
genuine local diffeomorphism. -/
theorem programPT06CanonicalFirstSheetAdaptedBulkCoordinate_isLocalDiffeomorphAt_anchor
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    IsLocalDiffeomorphAt coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) ∞
      (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
        period hPeriod pole anchor)
      (cutThroatBoundaryToBulk period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole anchor)) := by
  let bandPoint := programPT06CanonicalFirstSheetBandPoint pole anchor
  let hTubular :=
    tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod bandPoint
  have hPhysical : tubularBandSpacetimeToAmbient period hPeriod bandPoint =
      cutThroatBoundaryToBulk period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole anchor) :=
    programPT06CanonicalFirstSheetBandPoint_toAmbient
      period hPeriod pole anchor
  have hSource : cutThroatBoundaryToBulk period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole anchor) ∈ hTubular.localInverse.source := by
    rw [← hPhysical]
    exact hTubular.localInverse_mem_source
  have hInversePoint : hTubular.localInverse
        (cutThroatBoundaryToBulk period hPeriod
          (programPT06CanonicalFirstSheetBoundaryMap
            period hPeriod pole anchor)) = bandPoint := by
    rw [← hPhysical]
    exact hTubular.localInverse_left_inv hTubular.localInverse_mem_target
  have hBandSource : bandPoint ∈
      (programPT06WarpedNullBandCoordinatePartialDiffeomorph pole).source := by
    rw [programPT06WarpedNullBandCoordinatePartialDiffeomorph_source]
    exact programPT06CanonicalFirstSheetBandPoint_mem_coordinateDomain pole anchor
  rw [← funext
    (programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph_apply
      period hPeriod pole anchor)]
  apply (programPT06CanonicalFirstSheetAdaptedBulkPartialDiffeomorph
    period hPeriod pole anchor).isLocalDiffeomorphAt _ _ _
  exact ⟨hSource, by
    change hTubular.localInverse
        (cutThroatBoundaryToBulk period hPeriod
          (programPT06CanonicalFirstSheetBoundaryMap
            period hPeriod pole anchor)) ∈
      (programPT06WarpedNullBandCoordinatePartialDiffeomorph pole).source
    rw [hInversePoint]
    exact hBandSource⟩

/-- Selected forward inverse of the adapted coordinate at the anchor. -/
def programPT06CanonicalFirstSheetAdaptedBulkCoordinateLocalInverse
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    PartialDiffeomorph
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      coverModelWithCorners ProgramPT06AmbientCoordinate4
      (EffectiveBulk period hPeriod) ∞ :=
  (programPT06CanonicalFirstSheetAdaptedBulkCoordinate_isLocalDiffeomorphAt_anchor
    period hPeriod pole anchor).localInverse

/-- Coordinate followed by its selected forward inverse is the identity germ
at the adapted anchor coordinate. -/
theorem programPT06CanonicalFirstSheetAdaptedBulkCoordinate_localInverse_eventuallyEq
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    programPT06CanonicalFirstSheetAdaptedBulkCoordinate
          period hPeriod pole anchor ∘
        programPT06CanonicalFirstSheetAdaptedBulkCoordinateLocalInverse
          period hPeriod pole anchor =ᶠ[
      𝓝 (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
        period hPeriod pole anchor
        (cutThroatBoundaryToBulk period hPeriod
          (programPT06CanonicalFirstSheetBoundaryMap
            period hPeriod pole anchor)))] id :=
  (programPT06CanonicalFirstSheetAdaptedBulkCoordinate_isLocalDiffeomorphAt_anchor
    period hPeriod pole anchor).localInverse_eventuallyEq_right

/-- The derivative of that transition germ is the identity. -/
theorem programPT06CanonicalFirstSheetAdaptedBulkCoordinate_localInverse_fderiv
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    fderiv Real
        (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
            period hPeriod pole anchor ∘
          programPT06CanonicalFirstSheetAdaptedBulkCoordinateLocalInverse
            period hPeriod pole anchor)
        (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
          period hPeriod pole anchor
          (cutThroatBoundaryToBulk period hPeriod
            (programPT06CanonicalFirstSheetBoundaryMap
              period hPeriod pole anchor))) =
      ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4 := by
  rw [Filter.EventuallyEq.fderiv_eq
    (programPT06CanonicalFirstSheetAdaptedBulkCoordinate_localInverse_eventuallyEq
      period hPeriod pole anchor), fderiv_id]

/-- The round trip through the selected inverse has determinant one.  This
does not determine orientation relative to a different physical chart. -/
theorem programPT06CanonicalFirstSheetAdaptedBulkCoordinate_localInverse_det
    (pole : StandardEquatorialTwoSphere)
    (anchor : ProgramPT06NullFaceSource3) :
    LinearMap.det
        (fderiv Real
          (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
              period hPeriod pole anchor ∘
            programPT06CanonicalFirstSheetAdaptedBulkCoordinateLocalInverse
              period hPeriod pole anchor)
          (programPT06CanonicalFirstSheetAdaptedBulkCoordinate
            period hPeriod pole anchor
            (cutThroatBoundaryToBulk period hPeriod
              (programPT06CanonicalFirstSheetBoundaryMap
                period hPeriod pole anchor)))).toLinearMap = 1 := by
  rw [programPT06CanonicalFirstSheetAdaptedBulkCoordinate_localInverse_fderiv]
  exact LinearMap.det_id

end
end P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateLocalDiffeomorph4D
end JanusFormal
