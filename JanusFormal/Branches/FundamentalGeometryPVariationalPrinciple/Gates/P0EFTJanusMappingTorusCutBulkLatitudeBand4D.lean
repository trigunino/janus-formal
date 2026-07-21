import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D

/-!
# Exact latitude band of the attached cut collar

Because the cut-bulk monodromy is the identity, the first spherical
coordinate descends to the quotient.  The attached collar is exactly its
closed band from `0` to `sin 1`, and the artificial outer face is exactly the
level `sin 1`.  This identifies the topological gluing locus without asserting
global smooth Stokes data.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkLatitudeBand4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem refl_zpow_apply {X : Type} [TopologicalSpace X]
    (winding : Int) (point : X) :
    ((Homeomorph.refl X) ^ winding) point = point := by
  rw [show ((Homeomorph.refl X) ^ winding) point =
      ((Homeomorph.refl X) ^ winding).toEquiv point from rfl,
    homeomorph_toEquiv_zpow]
  rw [show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
  rfl

/-- The positive latitude coordinate is presentation-independent on the cut
bulk because its monodromy is the identity. -/
def cutBulkLatitudeCoordinate :
    PositiveHemisphereCutBulk period hPeriod → Real :=
  Quotient.lift (fun point : MappingTorusCover (cutBulkData period hPeriod) =>
    point.fiber.1.1 0) (by
      intro first second hOrbit
      change AddAction.orbitRel Int
        (MappingTorusCover (cutBulkData period hPeriod)) first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, rfl⟩
      change (((Homeomorph.refl ClosedPositiveHemisphere) ^ winding)
        second.fiber).1.1 0 = second.fiber.1.1 0
      rw [refl_zpow_apply])

theorem continuous_cutBulkLatitudeCoordinate :
    Continuous (cutBulkLatitudeCoordinate period hPeriod) := by
  apply (show Continuous (fun point :
      MappingTorusCover (cutBulkData period hPeriod) => point.fiber.1.1 0) from
    (continuous_apply 0).comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp (continuous_fiber _)))).quotient_lift

theorem cutBulkLatitudeCoordinate_cutCollarAttachment
    (parameter : CutThroatFiniteCollar period hPeriod) :
    cutBulkLatitudeCoordinate period hPeriod
        (cutCollarAttachment period hPeriod parameter) =
      Real.sin parameter.2.1 := by
  rcases parameter with ⟨boundary, normal⟩
  refine Quotient.inductionOn boundary ?_
  intro representative
  rfl

private theorem sin_one_lt_one : Real.sin 1 < 1 := by
  have hOne : (1 : Real) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hPi : Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  simpa using Real.strictMonoOn_sin hOne hPi
    (by linarith [Real.pi_gt_three])

private theorem sin_mem_unitIcc
    {normal : Real} (hNormal : normal ∈ Icc (0 : Real) 1) :
    Real.sin normal ∈ Icc (0 : Real) (Real.sin 1) := by
  have hZero : (0 : Real) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hNormalRange : normal ∈
      Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hNormal.1, hNormal.2, Real.pi_gt_three]
  have hOne : (1 : Real) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_three]
  constructor
  · simpa using Real.monotoneOn_sin hZero hNormalRange hNormal.1
  · exact Real.monotoneOn_sin hNormalRange hOne hNormal.2

private theorem arcsin_mem_unitIcc
    {coordinate : Real}
    (hCoordinate : coordinate ∈ Icc (0 : Real) (Real.sin 1)) :
    Real.arcsin coordinate ∈ Icc (0 : Real) 1 := by
  constructor
  · exact Real.arcsin_nonneg.mpr hCoordinate.1
  · have hBound := Real.arcsin_le_arcsin hCoordinate.2
    have hArcSinOne : Real.arcsin (Real.sin 1) = 1 :=
      Real.arcsin_sin (by linarith [Real.pi_gt_three])
        (by linarith [Real.pi_gt_three])
    rwa [hArcSinOne] at hBound

/-- The closed collar image is exactly the quotient latitude band. -/
theorem range_cutCollarAttachment :
    Set.range (cutCollarAttachment period hPeriod) =
      (cutBulkLatitudeCoordinate period hPeriod) ⁻¹'
        Icc (0 : Real) (Real.sin 1) := by
  ext bulk
  constructor
  · rintro ⟨parameter, rfl⟩
    rw [mem_preimage, cutBulkLatitudeCoordinate_cutCollarAttachment]
    exact sin_mem_unitIcc parameter.2.2
  · intro hBulk
    refine Quotient.inductionOn bulk ?_ hBulk
    intro representative hCoordinate
    change representative.fiber.1.1 0 ∈ Icc (0 : Real) (Real.sin 1)
      at hCoordinate
    let spherePoint : UnitThreeSphere := representative.fiber.1
    have hBand : spherePoint ∈ EquatorialSphericalBand := by
      change |spherePoint.1 0| < 1
      rw [abs_of_nonneg hCoordinate.1]
      exact hCoordinate.2.trans_lt sin_one_lt_one
    let base : EquatorialTwoSphere := equatorialBandBase spherePoint hBand
    let normal : CutCollarInterval :=
      ⟨Real.arcsin (spherePoint.1 0), arcsin_mem_unitIcc hCoordinate⟩
    let boundaryRepresentative :
        MappingTorusCover (orientationDoubleData period hPeriod) :=
      ⟨base, representative.time⟩
    let boundary : CutThroatBoundary period hPeriod :=
      mappingTorusMk (orientationDoubleData period hPeriod)
        boundaryRepresentative
    refine ⟨(boundary, normal), ?_⟩
    change mappingTorusMk (cutBulkData period hPeriod)
        (cutCollarCoverAttachment period hPeriod
          (boundaryRepresentative, normal)) =
      mappingTorusMk (cutBulkData period hPeriod) representative
    apply congrArg (mappingTorusMk (cutBulkData period hPeriod))
    apply MappingTorusCover.ext
    · apply Subtype.ext
      simpa [cutCollarCoverAttachment, positiveLatitudeFiber, base, normal,
        boundaryRepresentative, equatorialTubularMap,
        equatorialBandNormal] using
          (equatorialTubularMap_equatorialBandParameter spherePoint hBand)
    · rfl

/-- The artificial outer gluing face is exactly latitude `sin 1`. -/
theorem range_cutOuterLatitudeInclusion :
    Set.range (cutOuterLatitudeInclusion period hPeriod) =
      {bulk | cutBulkLatitudeCoordinate period hPeriod bulk = Real.sin 1} := by
  ext bulk
  constructor
  · rintro ⟨boundary, rfl⟩
    change cutBulkLatitudeCoordinate period hPeriod
        (cutCollarAttachment period hPeriod
          (cutOuterFace period hPeriod boundary)) = Real.sin 1
    rw [cutBulkLatitudeCoordinate_cutCollarAttachment]
    rfl
  · intro hLevel
    change cutBulkLatitudeCoordinate period hPeriod bulk = Real.sin 1 at hLevel
    have hSinOne : Real.sin 1 ∈ Icc (0 : Real) (Real.sin 1) := by
      exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
        (by linarith [Real.pi_gt_three]), le_rfl⟩
    have hBand : bulk ∈ Set.range (cutCollarAttachment period hPeriod) := by
      rw [range_cutCollarAttachment]
      change cutBulkLatitudeCoordinate period hPeriod bulk ∈
        Icc (0 : Real) (Real.sin 1)
      rw [hLevel]
      exact hSinOne
    rcases hBand with ⟨⟨boundary, normal⟩, hBulk⟩
    have hSin : Real.sin normal.1 = Real.sin 1 := by
      have hCoordinate :=
        cutBulkLatitudeCoordinate_cutCollarAttachment period hPeriod
          (boundary, normal)
      rw [hBulk] at hCoordinate
      exact hCoordinate.symm.trans hLevel
    have hNormalRange : normal.1 ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [normal.2.1, normal.2.2, Real.pi_gt_three]
    have hOneRange : (1 : Real) ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_gt_three]
    have hNormal : normal = (⊤ : CutCollarInterval) := by
      apply Subtype.ext
      exact Real.injOn_sin hNormalRange hOneRange hSin
    refine ⟨boundary, ?_⟩
    rw [cutOuterLatitudeInclusion, ← hBulk]
    apply congrArg (cutCollarAttachment period hPeriod)
    exact Prod.ext rfl hNormal.symm

end
end P0EFTJanusMappingTorusCutBulkLatitudeBand4D
end JanusFormal
