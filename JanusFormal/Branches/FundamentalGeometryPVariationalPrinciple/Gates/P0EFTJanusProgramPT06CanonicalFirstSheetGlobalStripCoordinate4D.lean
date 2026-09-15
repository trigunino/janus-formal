import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateLocalDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarBand4D

/-!
# One adapted coordinate on the canonical first-sheet fundamental strip

Restricting tubular-band points to the open fundamental time interval removes
the mapping-torus deck ambiguity.  For a fixed stereographic pole this gives
one adapted physical coordinate whose source contains the full finite normal
collar over every first-sheet source with time in that interval.

The source omits the temporal gluing seam and the selected stereographic pole.
No chart covering the whole quotient or the whole sphere is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D

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
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
open P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D
open P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateLocalDiffeomorph4D
open P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarBand4D

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

/-- Natural band-coordinate domain, restricted to one open fundamental time
strip. -/
def programPT06CanonicalFirstSheetGlobalStripBandDomain
    (pole : StandardEquatorialTwoSphere) : Set BandSpacetime :=
  programPT06WarpedNullBandCoordinateDomain pole ∩
    {point | point.2 ∈ canonicalLorentzInteriorTime period}

theorem programPT06CanonicalFirstSheetGlobalStripBandDomain_isOpen
    (pole : StandardEquatorialTwoSphere) :
    IsOpen (programPT06CanonicalFirstSheetGlobalStripBandDomain period pole) := by
  apply (programPT06WarpedNullBandCoordinateDomain_isOpen pole).inter
  unfold canonicalLorentzInteriorTime
  exact isOpen_Ioo.preimage continuous_snd

private def programPT06CanonicalFirstSheetGlobalStripBandOpen
    (pole : StandardEquatorialTwoSphere) : TopologicalSpace.Opens BandSpacetime :=
  ⟨programPT06CanonicalFirstSheetGlobalStripBandDomain period pole,
    programPT06CanonicalFirstSheetGlobalStripBandDomain_isOpen period pole⟩

private abbrev GlobalStripBand
    (pole : StandardEquatorialTwoSphere) :=
  programPT06CanonicalFirstSheetGlobalStripBandOpen period pole

private def programPT06CanonicalFirstSheetGlobalStripMidpoint : Real :=
  (min 0 period + max 0 period) / 2

private theorem programPT06CanonicalFirstSheetGlobalStripMidpoint_mem
    (hPeriod : period ≠ 0) :
    programPT06CanonicalFirstSheetGlobalStripMidpoint period ∈
      canonicalLorentzInteriorTime period := by
  have hEndpoints : min 0 period < max 0 period :=
    min_lt_max.mpr (Ne.symm hPeriod)
  unfold programPT06CanonicalFirstSheetGlobalStripMidpoint
    canonicalLorentzInteriorTime
  constructor <;> linarith

private def programPT06CanonicalFirstSheetGlobalStripBaseSource :
    ProgramPT06NullFaceSource3 :=
  (programPT06CanonicalFirstSheetGlobalStripMidpoint period, 0)

private def programPT06CanonicalFirstSheetGlobalStripBandBase
    (hPeriod : period ≠ 0)
    (pole : StandardEquatorialTwoSphere) : GlobalStripBand period pole :=
  ⟨programPT06CanonicalFirstSheetBandPoint pole
      (programPT06CanonicalFirstSheetGlobalStripBaseSource period),
    programPT06CanonicalFirstSheetBandPoint_mem_coordinateDomain pole _,
    programPT06CanonicalFirstSheetGlobalStripMidpoint_mem period hPeriod⟩

/-- The associated round-sphere point and subtype-valued fundamental time. -/
def programPT06CanonicalFirstSheetGlobalStripParameter
    (pole : StandardEquatorialTwoSphere)
    (point : GlobalStripBand period pole) :
    CanonicalLorentzInteriorParameter period :=
  (unitThreeSphereHomeomorph point.1.1,
    ⟨point.1.2, point.2.2⟩)

/-- On the fundamental strip, the tubular physical map is the canonical
interior physical map. -/
theorem programPT06CanonicalFirstSheetGlobalStripPhysical_eq_canonical
    (pole : StandardEquatorialTwoSphere)
    (point : GlobalStripBand period pole) :
    tubularBandSpacetimeToAmbient period hPeriod point.1 =
      canonicalLorentzInteriorPhysicalMap period hPeriod
        (programPT06CanonicalFirstSheetGlobalStripParameter
          period pole point) := by
  change mappingTorusMk (reflectedSphereData period hPeriod)
      ((coverHomeomorphProd (reflectedSphereData period hPeriod)).symm
        (point.1.1, point.1.2)) =
    mappingTorusMk (reflectedSphereData period hPeriod)
      ((coverHomeomorphProd (reflectedSphereData period hPeriod)).symm
        (unitThreeSphereHomeomorph.symm
          (unitThreeSphereHomeomorph point.1.1), point.1.2))
  rw [unitThreeSphereHomeomorph.symm_apply_apply]

/-- Physical parametrization of the selected band and time strip. -/
def programPT06CanonicalFirstSheetGlobalStripPhysicalMap
    (pole : StandardEquatorialTwoSphere)
    (point : GlobalStripBand period pole) : EffectiveBulk period hPeriod :=
  tubularBandSpacetimeToAmbient period hPeriod point.1

theorem programPT06CanonicalFirstSheetGlobalStripPhysicalMap_injective
    (pole : StandardEquatorialTwoSphere) :
    Function.Injective
      (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole) := by
  intro first second hEqual
  have hCanonical :
      canonicalLorentzInteriorPhysicalMap period hPeriod
          (programPT06CanonicalFirstSheetGlobalStripParameter
            period pole first) =
        canonicalLorentzInteriorPhysicalMap period hPeriod
          (programPT06CanonicalFirstSheetGlobalStripParameter
            period pole second) := by
    simpa [programPT06CanonicalFirstSheetGlobalStripPhysicalMap,
      programPT06CanonicalFirstSheetGlobalStripPhysical_eq_canonical]
      using hEqual
  have hParameter :=
    canonicalLorentzInteriorPhysicalMap_injective period hPeriod hCanonical
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply unitThreeSphereHomeomorph.injective
    exact congrArg Prod.fst hParameter
  · exact congrArg Subtype.val (congrArg Prod.snd hParameter)

private def programPT06CanonicalFirstSheetGlobalStripBandInclusion
    (hPeriod : period ≠ 0) (pole : StandardEquatorialTwoSphere) :
    PartialDiffeomorph coverModelWithCorners coverModelWithCorners
      (GlobalStripBand period pole) BandSpacetime ∞ :=
  openSubtypePartialDiffeomorph coverModelWithCorners
    (programPT06CanonicalFirstSheetGlobalStripBandOpen period pole)
    (programPT06CanonicalFirstSheetGlobalStripBandBase
      period hPeriod pole)

private theorem programPT06CanonicalFirstSheetGlobalStripBandInclusion_isLocalDiffeomorph
    (hPeriod : period ≠ 0)
    (pole : StandardEquatorialTwoSphere) :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (Subtype.val : GlobalStripBand period pole → BandSpacetime) := by
  intro point
  refine ⟨programPT06CanonicalFirstSheetGlobalStripBandInclusion
      period hPeriod pole, ?_, ?_⟩
  · exact Set.mem_univ point
  · intro source _
    rfl

theorem programPT06CanonicalFirstSheetGlobalStripPhysicalMap_isLocalDiffeomorph
    (pole : StandardEquatorialTwoSphere) :
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ∞
      (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole) := by
  intro point
  have hFirst :=
    (programPT06CanonicalFirstSheetGlobalStripBandInclusion_isLocalDiffeomorph
      period hPeriod pole) point
  have hSecond :=
    (tubularBandSpacetimeToAmbient_isLocalDiffeomorph
      period hPeriod) point.1
  exact hFirst.comp coverModelWithCorners _ hSecond

theorem programPT06CanonicalFirstSheetGlobalStripPhysicalMap_isOpenEmbedding
    (pole : StandardEquatorialTwoSphere) :
    IsOpenEmbedding
      (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole) :=
  (programPT06CanonicalFirstSheetGlobalStripPhysicalMap_isLocalDiffeomorph
      period hPeriod pole).isLocalHomeomorph.isOpenEmbedding_of_injective
    (programPT06CanonicalFirstSheetGlobalStripPhysicalMap_injective
      period hPeriod pole)

private theorem contMDiffOn_openEmbeddingInverse_of_isLocalDiffeomorph
    {KField E H E' H' M N : Type*} [NontriviallyNormedField KField]
    [NormedAddCommGroup E] [NormedSpace KField E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace KField E'] [TopologicalSpace H']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    [Nonempty M]
    {I : ModelWithCorners KField E H}
    {J : ModelWithCorners KField E' H'}
    {n : ℕ∞ω} {f : M → N}
    (hOpen : IsOpenEmbedding f)
    (hLocal : IsLocalDiffeomorph I J n f) :
    ContMDiffOn J I n (hOpen.toOpenPartialHomeomorph f).symm
      (Set.range f) := by
  intro target hTarget
  rcases hTarget with ⟨source, rfl⟩
  obtain ⟨Φ, hSource, hEq⟩ := hLocal source
  have hImage : f source ∈ Φ.target := by
    rw [hEq hSource]
    exact Φ.map_source hSource
  have hAt : ContMDiffAt J I n Φ.symm (f source) := by
    rw [hEq hSource]
    exact Φ.symm.contMDiffOn.contMDiffAt
      (Φ.open_target.mem_nhds (Φ.map_source hSource))
  apply (hAt.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [Φ.open_target.mem_nhds hImage] with target hTarget
  apply hOpen.injective
  have hTargetRange : target ∈ Set.range f :=
    ⟨Φ.symm.toFun target, by
      calc
        f (Φ.symm.toFun target) =
            Φ.toFun (Φ.symm.toFun target) :=
          hEq (Φ.map_target hTarget)
        _ = target := Φ.right_inv hTarget⟩
  rw [hOpen.toOpenPartialHomeomorph_right_inv f hTargetRange]
  symm
  calc
    f (Φ.symm.toFun target) =
        Φ.toFun (Φ.symm.toFun target) :=
      hEq (Φ.map_target hTarget)
    _ = target := Φ.right_inv hTarget

private def programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph
    (pole : StandardEquatorialTwoSphere) :
    PartialDiffeomorph coverModelWithCorners coverModelWithCorners
      (GlobalStripBand period pole) (EffectiveBulk period hPeriod) ∞ := by
  letI : Nonempty (GlobalStripBand period pole) :=
    ⟨programPT06CanonicalFirstSheetGlobalStripBandBase
      period hPeriod pole⟩
  let hOpen :=
    programPT06CanonicalFirstSheetGlobalStripPhysicalMap_isOpenEmbedding
      period hPeriod pole
  let hLocal :=
    programPT06CanonicalFirstSheetGlobalStripPhysicalMap_isLocalDiffeomorph
      period hPeriod pole
  exact
    { __ := hOpen.toOpenPartialHomeomorph
        (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
          period hPeriod pole)
      contMDiffOn_toFun :=
        hLocal.contMDiff.contMDiffOn
      contMDiffOn_invFun := by
        rw [PartialEquiv.invFun_as_coe,
          IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact contMDiffOn_openEmbeddingInverse_of_isLocalDiffeomorph
          hOpen hLocal }

private theorem programPT06CanonicalFirstSheetGlobalStripBandInclusion_source
    (pole : StandardEquatorialTwoSphere) :
    (programPT06CanonicalFirstSheetGlobalStripBandInclusion
      period hPeriod pole).source = Set.univ := by
  simp [programPT06CanonicalFirstSheetGlobalStripBandInclusion,
    openSubtypePartialDiffeomorph]

private theorem programPT06CanonicalFirstSheetGlobalStripBandInclusion_target
    (pole : StandardEquatorialTwoSphere) :
    (programPT06CanonicalFirstSheetGlobalStripBandInclusion
      period hPeriod pole).target =
      programPT06CanonicalFirstSheetGlobalStripBandDomain period pole := by
  simp [programPT06CanonicalFirstSheetGlobalStripBandInclusion,
    openSubtypePartialDiffeomorph,
    programPT06CanonicalFirstSheetGlobalStripBandOpen]

private theorem programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph_source
    (pole : StandardEquatorialTwoSphere) :
    (programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph
      period hPeriod pole).source = Set.univ := by
  simp [programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph]

private theorem programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph_target
    (pole : StandardEquatorialTwoSphere) :
    (programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph
      period hPeriod pole).target =
      Set.range (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole) := by
  simp [programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph]

/-- Tubular band mapped injectively to the quotient on the chosen fundamental
time strip. -/
def programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
    (pole : StandardEquatorialTwoSphere) :
    PartialDiffeomorph coverModelWithCorners coverModelWithCorners
      BandSpacetime (EffectiveBulk period hPeriod) ∞ :=
  (programPT06CanonicalFirstSheetGlobalStripBandInclusion
      period hPeriod pole).symm.trans
    (programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph
      period hPeriod pole)

/-- One quotient coordinate obtained by inverting the physical band map and
then reading the adapted warped-null band coordinate. -/
def programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
    (pole : StandardEquatorialTwoSphere) :
    PartialDiffeomorph coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (EffectiveBulk period hPeriod) ProgramPT06AmbientCoordinate4 ∞ :=
  (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
      period hPeriod pole).symm.trans
    (programPT06WarpedNullBandCoordinatePartialDiffeomorph pole)

/-- Explicit open target of the global-strip coordinate. -/
def programPT06CanonicalFirstSheetGlobalStripCoordinateTarget :
    Set ProgramPT06AmbientCoordinate4 :=
  {coordinate |
    coordinate 0 ∈ canonicalLorentzInteriorTime period ∧
    coordinate 3 - coordinate 0 ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)}

theorem programPT06CanonicalFirstSheetGlobalStripCoordinateTarget_isOpen :
    IsOpen (programPT06CanonicalFirstSheetGlobalStripCoordinateTarget period) := by
  unfold programPT06CanonicalFirstSheetGlobalStripCoordinateTarget
    canonicalLorentzInteriorTime
  have hCoordinates : Continuous
      (fun coordinate : ProgramPT06AmbientCoordinate4 ↦
        EuclideanSpace.equiv (Fin 4) Real coordinate) :=
    (EuclideanSpace.equiv (Fin 4) Real).toContinuousLinearMap.continuous
  have hZero : Continuous
      (fun coordinate : ProgramPT06AmbientCoordinate4 ↦ coordinate 0) :=
    (continuous_apply 0).comp hCoordinates
  have hThree : Continuous
      (fun coordinate : ProgramPT06AmbientCoordinate4 ↦ coordinate 3) :=
    (continuous_apply 3).comp hCoordinates
  exact (isOpen_Ioo.preimage hZero).inter
    (isOpen_Ioo.preimage (hThree.sub hZero))

@[simp] theorem programPT06WarpedNullBandCoordinate_time
    (pole : StandardEquatorialTwoSphere) (point : BandSpacetime) :
    programPT06WarpedNullBandCoordinate pole point 0 = point.2 := by
  simp [programPT06WarpedNullBandCoordinate,
    equatorialBandCanonicalParameter]

@[simp] theorem programPT06WarpedNullBandCoordinate_normal
    (pole : StandardEquatorialTwoSphere) (point : BandSpacetime) :
    programPT06WarpedNullBandCoordinate pole point 3 -
        programPT06WarpedNullBandCoordinate pole point 0 =
      (equatorialTubularSmoothInverse point.1).2.1 := by
  simp [programPT06WarpedNullBandCoordinate,
    equatorialBandCanonicalParameter]

private def programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate
    (pole : StandardEquatorialTwoSphere)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06CanonicalFirstSheetGlobalStripCoordinateTarget period) :
    BandSpacetime :=
  (equatorialTubularSmoothMap
      (equatorialTwoSphereHomeomorph.symm
          (standardEquatorialStereographicInverse pole
            ((EuclideanSpace.equiv (Fin 2) Real).symm
              ![coordinate 1, coordinate 2])),
        ⟨coordinate 3 - coordinate 0, hCoordinate.2⟩),
    coordinate 0)

private theorem programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate_mem
    (pole : StandardEquatorialTwoSphere)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06CanonicalFirstSheetGlobalStripCoordinateTarget period) :
    programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate
        period pole coordinate hCoordinate ∈
      programPT06CanonicalFirstSheetGlobalStripBandDomain period pole := by
  constructor
  · change (equatorialBandCanonicalParameter
      (programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate
        period pole coordinate hCoordinate)).1.1 ∈
        (stereographic' 2 pole).source
    unfold programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate
      equatorialBandCanonicalParameter
    rw [equatorialTubularSmoothInverse_map]
    change (stereographic' 2 pole).symm _ ∈
      (stereographic' 2 pole).source
    exact (stereographic' 2 pole).map_target (by simp)
  · exact hCoordinate.1

private theorem programPT06WarpedNullBandCoordinate_bandPointOfCoordinate
    (pole : StandardEquatorialTwoSphere)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06CanonicalFirstSheetGlobalStripCoordinateTarget period) :
    programPT06WarpedNullBandCoordinate pole
        (programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate
          period pole coordinate hCoordinate) = coordinate := by
  unfold programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate
    programPT06WarpedNullBandCoordinate equatorialBandCanonicalParameter
  rw [equatorialTubularSmoothInverse_map]
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext direction
  fin_cases direction <;>
    simp [standardEquatorialStereographicInverse]

theorem programPT06WarpedNullBandCoordinate_image_globalStripBandDomain
    (pole : StandardEquatorialTwoSphere) :
    programPT06WarpedNullBandCoordinate pole ''
        programPT06CanonicalFirstSheetGlobalStripBandDomain period pole =
      programPT06CanonicalFirstSheetGlobalStripCoordinateTarget period := by
  ext coordinate
  constructor
  · rintro ⟨point, hPoint, rfl⟩
    constructor
    · simpa using hPoint.2
    · rw [programPT06WarpedNullBandCoordinate_normal]
      exact (equatorialTubularSmoothInverse point.1).2.2
  · intro hCoordinate
    exact ⟨programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate
        period pole coordinate hCoordinate,
      programPT06CanonicalFirstSheetGlobalStripBandPointOfCoordinate_mem
        period pole coordinate hCoordinate,
      programPT06WarpedNullBandCoordinate_bandPointOfCoordinate
        period pole coordinate hCoordinate⟩

private theorem programPT06CanonicalFirstSheetGlobalStripPhysicalBand_source
    (pole : StandardEquatorialTwoSphere) :
    (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
      period hPeriod pole).source =
      programPT06CanonicalFirstSheetGlobalStripBandDomain period pole := by
  change (programPT06CanonicalFirstSheetGlobalStripBandInclusion
      period hPeriod pole).target ∩
      (programPT06CanonicalFirstSheetGlobalStripBandInclusion
        period hPeriod pole).symm ⁻¹'
        (programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph
          period hPeriod pole).source = _
  rw [programPT06CanonicalFirstSheetGlobalStripBandInclusion_target,
    programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph_source]
  simp

private theorem programPT06CanonicalFirstSheetGlobalStripPhysicalBand_target
    (pole : StandardEquatorialTwoSphere) :
    (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
      period hPeriod pole).target =
      Set.range (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole) := by
  change (programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph
      period hPeriod pole).target ∩
      (programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph
        period hPeriod pole).symm ⁻¹'
        (programPT06CanonicalFirstSheetGlobalStripBandInclusion
          period hPeriod pole).source = _
  rw [programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph_target,
    programPT06CanonicalFirstSheetGlobalStripBandInclusion_source]
  simp

private theorem programPT06CanonicalFirstSheetGlobalStripPhysicalBand_apply
    (pole : StandardEquatorialTwoSphere)
    (point : GlobalStripBand period pole) :
    programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
        period hPeriod pole point.1 =
      programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole point := by
  let inclusion := programPT06CanonicalFirstSheetGlobalStripBandInclusion
    period hPeriod pole
  have hPointSource : point ∈ inclusion.source := by
    rw [programPT06CanonicalFirstSheetGlobalStripBandInclusion_source]
    trivial
  have hInverse := inclusion.left_inv hPointSource
  change inclusion.symm point.1 = point at hInverse
  change programPT06CanonicalFirstSheetGlobalStripPhysicalPartialDiffeomorph
      period hPeriod pole (inclusion.symm point.1) = _
  rw [hInverse]
  rfl

theorem programPT06CanonicalFirstSheetGlobalStripCoordinate_source
    (pole : StandardEquatorialTwoSphere) :
    (programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole).source =
      Set.range (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole) := by
  ext point
  constructor
  · intro hPoint
    have hTarget : point ∈
        (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
          period hPeriod pole).target := by
      change point ∈
        (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
          period hPeriod pole).symm.source
      exact hPoint.1
    rwa [programPT06CanonicalFirstSheetGlobalStripPhysicalBand_target
      period hPeriod pole] at hTarget
  · rintro ⟨bandPoint, rfl⟩
    have hBandSource : bandPoint.1 ∈
        (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
          period hPeriod pole).source := by
      rw [programPT06CanonicalFirstSheetGlobalStripPhysicalBand_source
        period hPeriod pole]
      exact bandPoint.2
    have hPhysical :=
      programPT06CanonicalFirstSheetGlobalStripPhysicalBand_apply
        period hPeriod pole bandPoint
    have hInverse :
        (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
          period hPeriod pole).symm.toPartialEquiv
            ((programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
              period hPeriod pole).toPartialEquiv bandPoint.1) = bandPoint.1 :=
      (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
        period hPeriod pole).toPartialEquiv.left_inv hBandSource
    constructor
    · change programPT06CanonicalFirstSheetGlobalStripPhysicalMap
          period hPeriod pole bandPoint ∈
        (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
          period hPeriod pole).target
      rw [← hPhysical]
      exact (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
        period hPeriod pole).map_source hBandSource
    · change
        (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
          period hPeriod pole).symm
            (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
              period hPeriod pole bandPoint) ∈
          (programPT06WarpedNullBandCoordinatePartialDiffeomorph pole).source
      rw [← hPhysical, hInverse,
        programPT06WarpedNullBandCoordinatePartialDiffeomorph_source]
      exact bandPoint.2.1

theorem programPT06CanonicalFirstSheetGlobalStripCoordinate_apply_physical
    (pole : StandardEquatorialTwoSphere)
    (point : GlobalStripBand period pole) :
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
        period hPeriod pole
        (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
          period hPeriod pole point) =
      programPT06WarpedNullBandCoordinate pole point.1 := by
  have hBandSource : point.1 ∈
      (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
        period hPeriod pole).source := by
    rw [programPT06CanonicalFirstSheetGlobalStripPhysicalBand_source
      period hPeriod pole]
    exact point.2
  have hPhysical :=
    programPT06CanonicalFirstSheetGlobalStripPhysicalBand_apply
      period hPeriod pole point
  have hInverse :
      (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
        period hPeriod pole).symm.toPartialEquiv
          ((programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
            period hPeriod pole).toPartialEquiv point.1) = point.1 :=
    (programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
      period hPeriod pole).toPartialEquiv.left_inv hBandSource
  unfold programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
  change programPT06WarpedNullBandCoordinatePartialDiffeomorph pole
      ((programPT06CanonicalFirstSheetGlobalStripPhysicalBandPartialDiffeomorph
        period hPeriod pole).symm
          (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
            period hPeriod pole point)) = _
  rw [← hPhysical, hInverse,
    programPT06WarpedNullBandCoordinatePartialDiffeomorph_apply]

theorem programPT06CanonicalFirstSheetGlobalStripCoordinate_target
    (pole : StandardEquatorialTwoSphere) :
    (programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole).target =
      programPT06CanonicalFirstSheetGlobalStripCoordinateTarget period := by
  rw [← programPT06WarpedNullBandCoordinate_image_globalStripBandDomain
    period pole]
  rw [← (programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
    period hPeriod pole).image_source_eq_target]
  ext coordinate
  constructor
  · rintro ⟨physical, hPhysical, rfl⟩
    rw [programPT06CanonicalFirstSheetGlobalStripCoordinate_source
      period hPeriod pole] at hPhysical
    rcases hPhysical with ⟨point, rfl⟩
    exact ⟨point.1, point.2,
      programPT06CanonicalFirstSheetGlobalStripCoordinate_apply_physical
        period hPeriod pole point |>.symm⟩
  · rintro ⟨point, hPoint, rfl⟩
    let stripPoint : GlobalStripBand period pole := ⟨point, hPoint⟩
    refine ⟨programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole stripPoint, ?_, ?_⟩
    · rw [programPT06CanonicalFirstSheetGlobalStripCoordinate_source
        period hPeriod pole]
      exact ⟨stripPoint, rfl⟩
    · exact programPT06CanonicalFirstSheetGlobalStripCoordinate_apply_physical
        period hPeriod pole stripPoint

theorem programPT06CanonicalFirstSheetFullCollarBandPoint_mem_globalStrip
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval)
    (hTime : source.1 ∈ canonicalLorentzInteriorTime period) :
    programPT06CanonicalFirstSheetFullCollarBandPoint pole source normal ∈
      programPT06CanonicalFirstSheetGlobalStripBandDomain period pole := by
  exact ⟨programPT06CanonicalFirstSheetFullCollarBandPoint_mem_coordinateDomain
      pole source normal, by
    rw [programPT06CanonicalFirstSheetFullCollarBandPoint_eq]
    exact hTime⟩

/-- Every normal in `[0,1]` over an interior-time first-sheet source lies in
the source of this one quotient coordinate. -/
theorem programPT06CanonicalFirstSheetFullCollar_mem_globalStripCoordinate
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval)
    (hTime : source.1 ∈ canonicalLorentzInteriorTime period) :
    cutBulkFiniteCollarToAmbient period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole source, normal) ∈
      (programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
        period hPeriod pole).source := by
  rw [programPT06CanonicalFirstSheetGlobalStripCoordinate_source
    period hPeriod pole]
  let bandPoint : GlobalStripBand period pole :=
    ⟨programPT06CanonicalFirstSheetFullCollarBandPoint pole source normal,
      programPT06CanonicalFirstSheetFullCollarBandPoint_mem_globalStrip
        period pole source normal hTime⟩
  refine ⟨bandPoint, ?_⟩
  rw [programPT06CanonicalFirstSheetGlobalStripPhysicalMap,
    programPT06CanonicalFirstSheetFullCollarBandPoint_toAmbient]

/-- On the whole finite normal interval, the single physical coordinate is
exactly the explicit warped closed-half-collar coordinate. -/
@[simp] theorem programPT06CanonicalFirstSheetGlobalStripCoordinate_fullCollar
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval)
    (hTime : source.1 ∈ canonicalLorentzInteriorTime period) :
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
        period hPeriod pole
        (cutBulkFiniteCollarToAmbient period hPeriod
          (programPT06CanonicalFirstSheetBoundaryMap
            period hPeriod pole source, normal)) =
      programPT06WarpedNullClosedHalfCollarEmbedding (source, normal) := by
  let bandPoint : GlobalStripBand period pole :=
    ⟨programPT06CanonicalFirstSheetFullCollarBandPoint pole source normal,
      programPT06CanonicalFirstSheetFullCollarBandPoint_mem_globalStrip
        period pole source normal hTime⟩
  rw [← programPT06CanonicalFirstSheetFullCollarBandPoint_toAmbient
    period hPeriod pole source normal]
  change programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
      (programPT06CanonicalFirstSheetGlobalStripPhysicalMap
        period hPeriod pole bandPoint) = _
  rw [programPT06CanonicalFirstSheetGlobalStripCoordinate_apply_physical,
    programPT06WarpedNullBandCoordinate_fullCollar]

end
end P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D
end JanusFormal
