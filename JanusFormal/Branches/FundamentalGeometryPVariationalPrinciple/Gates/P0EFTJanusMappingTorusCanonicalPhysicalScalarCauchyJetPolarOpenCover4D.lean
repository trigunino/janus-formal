import Mathlib.Analysis.Real.Pi.Bounds
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetOpenCoverSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D

/-!
# The canonical tubular--polar open cover

The square of the signed latitude coordinate descends globally.  Its value lies
in `[0,1]`.  The absolute latitude angle

`theta(point) = arcsin (sqrt normalSquare(point))`

is therefore a continuous global function.  On a tubular point represented by
normal coordinate `nu`, it is exactly `|nu|`.

Use the two open regions

* `normalSquare < 1`, the non-polar tubular region;
* `1 < theta`, the outer polar region.

They cover the physical mapping torus because at the missing poles `theta =
pi/2 > 1`.  The explicit Cauchy candidate vanishes on the polar region since
its profiles are zero for `|nu| >= 1`.  Consequently global smoothness is
reduced to smoothness at points of the single tubular region.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPolarOpenCover4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open Set Topology Filter
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetSupport4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalCandidate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetOpenCoverSmoothness4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The descended squared normal coordinate is nonnegative. -/
theorem canonicalLatitudeQuotientNormalSquare_nonnegative
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ canonicalLatitudeQuotientNormalSquare period hPeriod point := by
  refine Quotient.inductionOn point ?_
  intro representative
  rw [canonicalLatitudeQuotientNormalSquare_mk]
  exact sq_nonneg _

/-- The descended squared normal coordinate is at most one. -/
theorem canonicalLatitudeQuotientNormalSquare_le_one
    (point : EffectiveQuotient period hPeriod) :
    canonicalLatitudeQuotientNormalSquare period hPeriod point ≤ 1 := by
  refine Quotient.inductionOn point ?_
  intro representative
  rw [canonicalLatitudeQuotientNormalSquare_mk]
  change representative.fiber.1 0 ^ 2 ≤ 1
  have hSphere := representative.fiber.2
  unfold OnUnitThreeSphere radiusSquared at hSphere
  rw [Fin.sum_univ_succ] at hSphere
  have hTail : 0 ≤ ∑ index : Fin 3,
      representative.fiber.1 index.succ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

/-- Global absolute latitude angle. -/
def canonicalLatitudeQuotientNormalAbsAngle
    (point : EffectiveQuotient period hPeriod) : Real :=
  Real.arcsin
    (Real.sqrt (canonicalLatitudeQuotientNormalSquare period hPeriod point))

/-- Continuity of the global absolute latitude angle. -/
theorem canonicalLatitudeQuotientNormalAbsAngle_continuous :
    Continuous (canonicalLatitudeQuotientNormalAbsAngle period hPeriod) :=
  Real.continuous_arcsin.comp
    (Real.continuous_sqrt.comp
      (canonicalLatitudeQuotientNormalSquare period hPeriod)
        |>.contMDiff_toFun.continuous)

/-- Absolute arcsine reconstructs the absolute normal coordinate inside the
latitude band. -/
theorem arcsin_abs_sin_eq_abs
    (normal : CanonicalLatitudeTubularNormal) :
    Real.arcsin |Real.sin normal.1| = |normal.1| := by
  have hAbsLeHalf : |normal.1| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨normal.2.1.le, normal.2.2.le⟩
  have hAbsLePi : |normal.1| ≤ Real.pi :=
    hAbsLeHalf.trans (half_le_self Real.pi_pos.le)
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hAbsLePi]
  exact Real.arcsin_sin
    (by linarith [abs_nonneg normal.1]) hAbsLeHalf

/-- On a physical tubular representative the global absolute angle is exactly
`|nu|`. -/
theorem canonicalLatitudeQuotientNormalAbsAngle_tubularPhysicalMap
    (parameter : CanonicalLatitudeTubularCollar) :
    canonicalLatitudeQuotientNormalAbsAngle period hPeriod
        (canonicalLatitudeTubularPhysicalMap period hPeriod parameter) =
      |parameter.2.1| := by
  unfold canonicalLatitudeQuotientNormalAbsAngle
  unfold canonicalLatitudeTubularPhysicalMap canonicalLatitudeTubularCoverMap
  rw [canonicalLatitudeQuotientNormalSquare_mk]
  change Real.arcsin (Real.sqrt (Real.sin parameter.2.1 ^ 2)) = _
  rw [Real.sqrt_sq_eq_abs]
  exact arcsin_abs_sin_eq_abs parameter.2

/-- Absolute angle transported to the tubular collar quotient. -/
def canonicalLatitudeTubularNormalAbsAngle
    (point : CanonicalLatitudeTubularCollarQuotient period) : Real :=
  canonicalLatitudeQuotientNormalAbsAngle period hPeriod
    (canonicalLatitudeTubularCollarToBulk period hPeriod point)

@[simp] theorem canonicalLatitudeTubularNormalAbsAngle_mk
    (parameter : CanonicalLatitudeTubularCollar) :
    canonicalLatitudeTubularNormalAbsAngle period hPeriod
        (canonicalLatitudeTubularCollarMk period parameter) =
      |parameter.2.1| :=
  canonicalLatitudeQuotientNormalAbsAngle_tubularPhysicalMap
    period hPeriod parameter

/-- The non-polar tubular region. -/
def canonicalLatitudeCauchyJetTubularRegion :
    Set (EffectiveQuotient period hPeriod) :=
  {point |
    canonicalLatitudeQuotientNormalSquare period hPeriod point < 1}

/-- The outer polar region on which every Cauchy profile has vanished. -/
def canonicalLatitudeCauchyJetPolarZeroRegion :
    Set (EffectiveQuotient period hPeriod) :=
  {point |
    1 < canonicalLatitudeQuotientNormalAbsAngle period hPeriod point}

/-- The tubular region is open. -/
theorem canonicalLatitudeCauchyJetTubularRegion_isOpen :
    IsOpen (canonicalLatitudeCauchyJetTubularRegion period hPeriod) := by
  unfold canonicalLatitudeCauchyJetTubularRegion
  exact isOpen_lt
    ((canonicalLatitudeQuotientNormalSquare period hPeriod)
      |>.contMDiff_toFun.continuous) continuous_const

/-- The polar zero region is open. -/
theorem canonicalLatitudeCauchyJetPolarZeroRegion_isOpen :
    IsOpen (canonicalLatitudeCauchyJetPolarZeroRegion period hPeriod) := by
  unfold canonicalLatitudeCauchyJetPolarZeroRegion
  exact isOpen_lt continuous_const
    (canonicalLatitudeQuotientNormalAbsAngle_continuous period hPeriod)

/-- At a pole the absolute latitude angle is `pi/2`. -/
theorem canonicalLatitudeQuotientNormalAbsAngle_eq_pi_div_two_of_square_eq_one
    (point : EffectiveQuotient period hPeriod)
    (hPoint : canonicalLatitudeQuotientNormalSquare period hPeriod point = 1) :
    canonicalLatitudeQuotientNormalAbsAngle period hPeriod point =
      Real.pi / 2 := by
  unfold canonicalLatitudeQuotientNormalAbsAngle
  rw [hPoint, Real.sqrt_one, Real.arcsin_one]

/-- The tubular and polar regions cover the physical bulk. -/
theorem canonicalLatitudeCauchyJet_tubular_union_polar :
    canonicalLatitudeCauchyJetTubularRegion period hPeriod ∪
        canonicalLatitudeCauchyJetPolarZeroRegion period hPeriod =
      Set.univ := by
  ext point
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hTubular :
      canonicalLatitudeQuotientNormalSquare period hPeriod point < 1
  · exact Or.inl hTubular
  · right
    have hSquare :
        canonicalLatitudeQuotientNormalSquare period hPeriod point = 1 :=
      le_antisymm
        (canonicalLatitudeQuotientNormalSquare_le_one period hPeriod point)
        (not_lt.mp hTubular)
    rw [canonicalLatitudeQuotientNormalAbsAngle_eq_pi_div_two_of_square_eq_one
      period hPeriod point hSquare]
    nlinarith [Real.pi_gt_three]

namespace CanonicalLatitudeDeckCauchyData

/-- The descended tubular field vanishes once the absolute tubular normal is at
least one. -/
theorem tubularDescend_eq_zero_of_one_le_absAngle
    (data : CanonicalLatitudeDeckCauchyData period)
    (point : CanonicalLatitudeTubularCollarQuotient period)
    (hPoint : 1 ≤ canonicalLatitudeTubularNormalAbsAngle
      period hPeriod point) :
    data.tubularDescend period point = 0 := by
  refine Quotient.inductionOn point ?_ hPoint
  intro parameter hParameter
  rw [canonicalLatitudeTubularNormalAbsAngle_mk] at hParameter
  exact canonicalLatitudeLocalCauchyExtension_eq_zero_of_one_le_abs
    (data.value, data.normal) (parameter.1, parameter.2.1) hParameter

/-- Every explicit global Cauchy candidate vanishes on the canonical polar
region. -/
theorem globalCandidate_eq_zero_on_polar
    (data : CanonicalLatitudeDeckCauchyData period) :
    Set.EqOn
      (canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data)
      (fun _ => 0)
      (canonicalLatitudeCauchyJetPolarZeroRegion period hPeriod) := by
  intro point hPolar
  unfold canonicalLatitudeCauchyJetGlobalCandidate
  split_ifs with hTubular
  · let boundaryPoint : canonicalLatitudeTubularBulkSet period hPeriod :=
      ⟨point, hTubular⟩
    let collarPoint : CanonicalLatitudeTubularCollarQuotient period :=
      (canonicalLatitudeTubularCollarEquivBulkSet period hPeriod).symm
        boundaryPoint
    have hBulk : canonicalLatitudeTubularCollarToBulk period hPeriod collarPoint =
        point := by
      have hApply := (canonicalLatitudeTubularCollarEquivBulkSet
        period hPeriod).apply_symm_apply boundaryPoint
      exact congrArg Subtype.val hApply
    have hAngle : 1 < canonicalLatitudeTubularNormalAbsAngle
        period hPeriod collarPoint := by
      unfold canonicalLatitudeTubularNormalAbsAngle
      rw [hBulk]
      exact hPolar
    unfold CanonicalLatitudeDeckCauchyData.tubularBulkField
    change data.tubularDescend period collarPoint = 0
    exact data.tubularDescend_eq_zero_of_one_le_absAngle
      period hPeriod collarPoint hAngle.le
  · rfl

end CanonicalLatitudeDeckCauchyData

/-- Boundary-core data for which only tubular pointwise smoothness remains to be
proved. -/
structure CanonicalPhysicalScalarCauchyJetTubularSmoothnessData
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  core : CanonicalPhysicalScalarCauchyJetBoundaryCoreData
    period ValueCore NormalCore
  tubular_smoothAt : ∀ (data : ValueCore × NormalCore)
    (point : EffectiveQuotient period hPeriod),
    point ∈ canonicalLatitudeCauchyJetTubularRegion period hPeriod →
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (core.candidate hPeriod data) point

namespace CanonicalPhysicalScalarCauchyJetTubularSmoothnessData

/-- The canonical tubular--polar regions instantiate the generic open-cover
smoothness criterion. -/
def toOpenCoverData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (tubular : CanonicalPhysicalScalarCauchyJetTubularSmoothnessData
      period hPeriod ValueCore NormalCore) :
    CanonicalPhysicalScalarCauchyJetOpenCoverData
      period hPeriod ValueCore NormalCore where
  core := tubular.core
  tubularRegion := canonicalLatitudeCauchyJetTubularRegion period hPeriod
  zeroRegion := canonicalLatitudeCauchyJetPolarZeroRegion period hPeriod
  zeroRegion_open := canonicalLatitudeCauchyJetPolarZeroRegion_isOpen
    period hPeriod
  cover := canonicalLatitudeCauchyJet_tubular_union_polar period hPeriod
  tubular_smoothAt := tubular.tubular_smoothAt
  zero_on := by
    intro data
    exact (tubular.core.deckData data).globalCandidate_eq_zero_on_polar
      period hPeriod

/-- Install the complete globally smooth candidate extension from the sole
remaining tubular smoothness theorem. -/
def toCandidateExtensionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (tubular : CanonicalPhysicalScalarCauchyJetTubularSmoothnessData
      period hPeriod ValueCore NormalCore) :=
  tubular.toOpenCoverData.toCandidateExtensionData

/-- Tubular-smoothness certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (tubular : CanonicalPhysicalScalarCauchyJetTubularSmoothnessData
      period hPeriod ValueCore NormalCore) :
    (∀ data : ValueCore × NormalCore,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (tubular.core.candidate hPeriod data)) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) :=
  tubular.toOpenCoverData.certificate

end CanonicalPhysicalScalarCauchyJetTubularSmoothnessData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPolarOpenCover4D
end JanusFormal
