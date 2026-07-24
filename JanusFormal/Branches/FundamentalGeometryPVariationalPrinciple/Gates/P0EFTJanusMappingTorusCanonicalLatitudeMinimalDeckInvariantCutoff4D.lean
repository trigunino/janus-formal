import Mathlib.Analysis.Calculus.FDeriv.Congr
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffProfile4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D

/-!
# Global deck-invariant shrinking latitude cutoffs

The reflected-sphere monodromy reverses the first sphere coordinate.  The local
shrinking profile is even, so its composition with this signed coordinate is
invariant under every deck transformation.  It therefore descends to a smooth
scalar cutoff on the mapping torus.

The descended cutoff is locally identically zero along the canonical throat,
not merely zero at the throat point.  Multiplication by it consequently kills
both the value and normal Cauchy traces.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffProfile4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Signed normal coordinate on the algebraic unit three-sphere. -/
def canonicalLatitudeSphereSignedNormal (point : UnitThreeSphere) : Real :=
  point.1 0

/-- The signed sphere coordinate is smooth for the transported sphere atlas. -/
theorem canonicalLatitudeSphereSignedNormal_contMDiff :
    ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ canonicalLatitudeSphereSignedNormal := by
  letI : Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩
  have hTo := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  have hAmbient : ContMDiff (𝓡 3) 𝓘(Real, R4Point) ∞
      (fun point : StandardSphere3 =>
        (EuclideanSpace.equiv (Fin 4) Real point.1)) := by
    exact (EuclideanSpace.equiv (Fin 4) Real).contDiff.contMDiff.comp
      contMDiff_coe_sphere
  have hCoordinate : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞
      (fun point : StandardSphere3 =>
        (EuclideanSpace.equiv (Fin 4) Real point.1) 0) :=
    (contDiff_apply Real Real (0 : Fin 4)).contMDiff.comp hAmbient
  exact (hCoordinate.comp hTo).congr fun point => rfl

/-- Reflection reverses the signed normal coordinate. -/
theorem canonicalLatitudeSphereSignedNormal_reflection
    (point : UnitThreeSphere) :
    canonicalLatitudeSphereSignedNormal (sphereReflection point) =
      -canonicalLatitudeSphereSignedNormal point := by
  simp [canonicalLatitudeSphereSignedNormal, sphereReflection, reflectPoint]

/-- The shrinking profile is even. -/
theorem canonicalLatitudeMinimalCutoffProfile_neg
    (index : Nat) (normal : Real) :
    canonicalLatitudeMinimalCutoffProfile index (-normal) =
      canonicalLatitudeMinimalCutoffProfile index normal := by
  unfold canonicalLatitudeMinimalCutoffProfile
  rw [mul_neg, ContDiffBump.neg canonicalLatitudeCollarCutoff]

/-- Every monodromy iterate preserves the even shrinking profile. -/
theorem canonicalLatitudeMinimalCutoffProfile_zpow_reflection
    (index : Nat) (winding : Int) :
    ∀ point : UnitThreeSphere,
      canonicalLatitudeMinimalCutoffProfile index
          (canonicalLatitudeSphereSignedNormal
            ((sphereReflection ^ winding) point)) =
        canonicalLatitudeMinimalCutoffProfile index
          (canonicalLatitudeSphereSignedNormal point) := by
  induction winding using Int.induction_on with
  | zero =>
      intro point
      simp
  | succ winding ih =>
      intro point
      rw [zpow_add_one]
      change canonicalLatitudeMinimalCutoffProfile index
          (canonicalLatitudeSphereSignedNormal
            ((sphereReflection ^ (winding : Int)) (sphereReflection point))) = _
      rw [ih (sphereReflection point),
        canonicalLatitudeSphereSignedNormal_reflection,
        canonicalLatitudeMinimalCutoffProfile_neg]
  | pred winding ih =>
      intro point
      rw [zpow_sub_one]
      change canonicalLatitudeMinimalCutoffProfile index
          (canonicalLatitudeSphereSignedNormal
            ((sphereReflection ^ (-(winding : Int)))
              (sphereReflection.symm point))) = _
      rw [ih (sphereReflection.symm point)]
      have hInverse : sphereReflection.symm point = sphereReflection point := rfl
      rw [hInverse, canonicalLatitudeSphereSignedNormal_reflection,
        canonicalLatitudeMinimalCutoffProfile_neg]

/-- Signed normal coordinate on the reflected-sphere cover. -/
def canonicalLatitudeCoverSignedNormal
    (point : EffectiveCover period hPeriod) : Real :=
  canonicalLatitudeSphereSignedNormal point.fiber

/-- Smoothness of the signed cover coordinate. -/
theorem canonicalLatitudeCoverSignedNormal_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (canonicalLatitudeCoverSignedNormal period hPeriod) := by
  have hTo := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞
    (coverHomeomorphProd (sphereData period hPeriod))
  have hProduct : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : UnitThreeSphere × Real =>
        canonicalLatitudeSphereSignedNormal point.1) :=
    canonicalLatitudeSphereSignedNormal_contMDiff.comp contMDiff_fst
  exact (hProduct.comp hTo).congr fun point => rfl

/-- Cover-level shrinking cutoff. -/
def canonicalLatitudeMinimalCoverCutoff
    (index : Nat) (point : EffectiveCover period hPeriod) : Real :=
  canonicalLatitudeMinimalCutoffProfile index
    (canonicalLatitudeCoverSignedNormal period hPeriod point)

/-- Smoothness of the cover cutoff. -/
theorem canonicalLatitudeMinimalCoverCutoff_contMDiff
    (index : Nat) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (canonicalLatitudeMinimalCoverCutoff period hPeriod index) :=
  (canonicalLatitudeMinimalCutoffProfile_contDiff index).contMDiff.comp
    (canonicalLatitudeCoverSignedNormal_contMDiff period hPeriod)

/-- Deck invariance of every cover cutoff. -/
theorem canonicalLatitudeMinimalCoverCutoff_deck
    (index : Nat) (winding : Int)
    (point : EffectiveCover period hPeriod) :
    canonicalLatitudeMinimalCoverCutoff period hPeriod index
        (winding +ᵥ point) =
      canonicalLatitudeMinimalCoverCutoff period hPeriod index point := by
  unfold canonicalLatitudeMinimalCoverCutoff canonicalLatitudeCoverSignedNormal
  rw [vadd_fiber]
  change canonicalLatitudeMinimalCutoffProfile index
      (canonicalLatitudeSphereSignedNormal
        ((sphereReflection ^ winding) point.fiber)) = _
  exact canonicalLatitudeMinimalCutoffProfile_zpow_reflection
    index winding point.fiber

/-- Deck-invariant smooth cutoff field on the cover. -/
def canonicalLatitudeMinimalDeckInvariantCutoff
    (index : Nat) : SmoothDeckInvariantField period hPeriod Real where
  toFun := canonicalLatitudeMinimalCoverCutoff period hPeriod index
  contMDiff_toFun :=
    canonicalLatitudeMinimalCoverCutoff_contMDiff period hPeriod index
  deck_invariant := canonicalLatitudeMinimalCoverCutoff_deck
    period hPeriod index

/-- Global smooth cutoff descended to the mapping torus. -/
def canonicalLatitudeMinimalQuotientCutoff
    (index : Nat) : SmoothQuotientField period hPeriod Real :=
  descendSmooth period hPeriod Real
    (canonicalLatitudeMinimalDeckInvariantCutoff period hPeriod index)

/-- Evaluation of the descended cutoff on a cover representative. -/
@[simp] theorem canonicalLatitudeMinimalQuotientCutoff_mk
    (index : Nat) (point : EffectiveCover period hPeriod) :
    canonicalLatitudeMinimalQuotientCutoff period hPeriod index
        (mappingTorusMk (sphereData period hPeriod) point) =
      canonicalLatitudeMinimalCoverCutoff period hPeriod index point :=
  descend_mk period hPeriod Real
    (canonicalLatitudeMinimalDeckInvariantCutoff period hPeriod index) point

/-- The global cutoff takes values in `[0,1]`. -/
theorem canonicalLatitudeMinimalQuotientCutoff_nonnegative
    (index : Nat) (point : EffectiveQuotient period hPeriod) :
    0 ≤ canonicalLatitudeMinimalQuotientCutoff period hPeriod index point := by
  refine Quotient.inductionOn point ?_
  intro representative
  rw [canonicalLatitudeMinimalQuotientCutoff_mk]
  exact canonicalLatitudeMinimalCutoffProfile_nonnegative _ _

/-- Upper bound for the global cutoff. -/
theorem canonicalLatitudeMinimalQuotientCutoff_le_one
    (index : Nat) (point : EffectiveQuotient period hPeriod) :
    canonicalLatitudeMinimalQuotientCutoff period hPeriod index point ≤ 1 := by
  refine Quotient.inductionOn point ?_
  intro representative
  rw [canonicalLatitudeMinimalQuotientCutoff_mk]
  exact canonicalLatitudeMinimalCutoffProfile_le_one _ _

/-- The quotient cutoff along a canonical latitude is exactly the one-dimensional
profile evaluated at `sin normal`. -/
theorem canonicalLatitudeMinimalQuotientCutoff_latitude
    (index : Nat) (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeMinimalQuotientCutoff period hPeriod index
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal) =
      canonicalLatitudeMinimalCutoffProfile index (Real.sin normal) := by
  unfold quotientNormalLatitude
  rw [canonicalLatitudeMinimalQuotientCutoff_mk]
  rfl

/-- Pointwise multiplication by the global cutoff. -/
def canonicalLatitudeMinimalCutoffLinearMap
    (index : Nat) :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      SmoothQuotientField period hPeriod Real where
  toFun field :=
    { toFun := fun point =>
        canonicalLatitudeMinimalQuotientCutoff period hPeriod index point *
          field point
      contMDiff_toFun :=
        (canonicalLatitudeMinimalQuotientCutoff period hPeriod index)
          |>.contMDiff_toFun.mul field.contMDiff_toFun }
  map_add' first second := by
    ext point
    change
      canonicalLatitudeMinimalQuotientCutoff period hPeriod index point *
          (first point + second point) =
        canonicalLatitudeMinimalQuotientCutoff period hPeriod index point * first point +
          canonicalLatitudeMinimalQuotientCutoff period hPeriod index point * second point
    ring
  map_smul' scalar field := by
    ext point
    change
      canonicalLatitudeMinimalQuotientCutoff period hPeriod index point *
          (scalar * field point) =
        scalar *
          (canonicalLatitudeMinimalQuotientCutoff period hPeriod index point * field point)
    ring

@[simp] theorem canonicalLatitudeMinimalCutoffLinearMap_apply
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field point =
      canonicalLatitudeMinimalQuotientCutoff period hPeriod index point *
        field point :=
  rfl

/-- The cutoff multiplier has zero canonical latitude value at the throat. -/
theorem canonicalLatitudeValue_minimalCutoff_zero
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeValue period hPeriod
        (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field)
        base 0 = 0 := by
  unfold canonicalLatitudeValue canonicalNormalSlice
  rw [canonicalLatitudeMinimalCutoffLinearMap_apply,
    canonicalLatitudeMinimalQuotientCutoff_latitude,
    Real.sin_zero,
    canonicalLatitudeMinimalCutoffProfile_zero,
    zero_mul]

/-- Along every canonical normal curve, the cut field is locally identically
zero near the throat. -/
theorem canonicalLatitudeValue_minimalCutoff_eventuallyEq_zero
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeValue period hPeriod
        (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field)
        base =ᶠ[𝓝 0]
      fun _ : Real => 0 := by
  have hSin : Tendsto Real.sin (𝓝 (0 : Real)) (𝓝 (0 : Real)) := by
    simpa only [Real.sin_zero] using Real.continuous_sin.tendsto (0 : Real)
  have hProfile :=
    (canonicalLatitudeMinimalCutoffProfile_eventuallyEq_zero index).comp_tendsto
      hSin
  filter_upwards [hProfile] with normal hNormal
  have hNormal' :
      canonicalLatitudeMinimalCutoffProfile index (Real.sin normal) = 0 := by
    simpa [Function.comp_def] using hNormal
  unfold canonicalLatitudeValue canonicalNormalSlice
  rw [canonicalLatitudeMinimalCutoffLinearMap_apply,
    canonicalLatitudeMinimalQuotientCutoff_latitude, hNormal', zero_mul]

/-- The normal derivative of the cut field vanishes at the throat. -/
theorem canonicalLatitudeDerivative_minimalCutoff_zero
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeDerivative period hPeriod
        (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field)
        base 0 = 0 := by
  unfold canonicalLatitudeDerivative
  have hDerivative : HasDerivAt
      (canonicalLatitudeValue period hPeriod
        (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field)
        base) 0 0 :=
    (hasDerivAt_const (x := (0 : Real)) (c := (0 : Real)))
      |>.congr_of_eventuallyEq
        (canonicalLatitudeValue_minimalCutoff_eventuallyEq_zero
          period hPeriod index field base)
  exact hDerivative.deriv

/-- First-sheet value trace of every cut field is zero. -/
theorem smoothFirstSheetValueL2_minimalCutoff_eq_zero
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real) :
    smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod
        (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field) = 0 := by
  rw [Lp.ext_iff]
  filter_upwards
    [smoothCanonicalPhysicalScalarFirstSheetValueL2_ae period hPeriod
      (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field),
     Lp.coeFn_zero Real 2 (canonicalLatitudeBaseMeasure period)]
    with base hValue hZero
  rw [hValue, hZero]
  exact canonicalLatitudeValue_minimalCutoff_zero
    period hPeriod index field base

/-- First-sheet normal trace of every cut field is zero. -/
theorem smoothFirstSheetNormalL2_minimalCutoff_eq_zero
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real) :
    smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod
        (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field) = 0 := by
  rw [Lp.ext_iff]
  filter_upwards
    [smoothCanonicalPhysicalScalarFirstSheetNormalL2_ae period hPeriod
      (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field),
     Lp.coeFn_zero Real 2 (canonicalLatitudeBaseMeasure period)]
    with base hNormal hZero
  rw [hNormal, hZero]
  exact canonicalLatitudeDerivative_minimalCutoff_zero
    period hPeriod index field base

/-- The paired first-sheet Cauchy trace of every cut field is zero. -/
theorem smoothFirstSheetCauchyTrace_minimalCutoff_eq_zero
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real) :
    smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
        (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field) = 0 := by
  apply Prod.ext
  · exact smoothFirstSheetValueL2_minimalCutoff_eq_zero
      period hPeriod index field
  · exact smoothFirstSheetNormalL2_minimalCutoff_eq_zero
      period hPeriod index field

/-- Square of the signed normal coordinate; unlike the signed coordinate itself,
this descends globally and cuts out the throat exactly. -/
def canonicalLatitudeCoverNormalSquare
    (point : EffectiveCover period hPeriod) : Real :=
  canonicalLatitudeCoverSignedNormal period hPeriod point ^ 2

/-- Every deck iterate preserves the squared signed normal. -/
theorem canonicalLatitudeSphereSignedNormal_sq_zpow_reflection
    (winding : Int) :
    ∀ point : UnitThreeSphere,
      canonicalLatitudeSphereSignedNormal ((sphereReflection ^ winding) point) ^ 2 =
        canonicalLatitudeSphereSignedNormal point ^ 2 := by
  induction winding using Int.induction_on with
  | zero =>
      intro point
      simp
  | succ winding ih =>
      intro point
      rw [zpow_add_one]
      change canonicalLatitudeSphereSignedNormal
          ((sphereReflection ^ (winding : Int)) (sphereReflection point)) ^ 2 = _
      rw [ih (sphereReflection point),
        canonicalLatitudeSphereSignedNormal_reflection]
      ring
  | pred winding ih =>
      intro point
      rw [zpow_sub_one]
      change canonicalLatitudeSphereSignedNormal
          ((sphereReflection ^ (-(winding : Int)))
            (sphereReflection.symm point)) ^ 2 = _
      rw [ih (sphereReflection.symm point)]
      have hInverse : sphereReflection.symm point = sphereReflection point := rfl
      rw [hInverse, canonicalLatitudeSphereSignedNormal_reflection]
      ring

/-- Globally descended squared normal coordinate. -/
def canonicalLatitudeNormalSquareDeckInvariantField :
    SmoothDeckInvariantField period hPeriod Real where
  toFun := canonicalLatitudeCoverNormalSquare period hPeriod
  contMDiff_toFun :=
    (canonicalLatitudeCoverSignedNormal_contMDiff period hPeriod).pow 2
  deck_invariant := by
    intro winding point
    unfold canonicalLatitudeCoverNormalSquare canonicalLatitudeCoverSignedNormal
    rw [vadd_fiber]
    change canonicalLatitudeSphereSignedNormal
        ((sphereReflection ^ winding) point.fiber) ^ 2 = _
    exact canonicalLatitudeSphereSignedNormal_sq_zpow_reflection
      winding point.fiber

/-- Smooth squared normal coordinate on the quotient. -/
def canonicalLatitudeQuotientNormalSquare :
    SmoothQuotientField period hPeriod Real :=
  descendSmooth period hPeriod Real
    (canonicalLatitudeNormalSquareDeckInvariantField period hPeriod)

@[simp] theorem canonicalLatitudeQuotientNormalSquare_mk
    (point : EffectiveCover period hPeriod) :
    canonicalLatitudeQuotientNormalSquare period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point) =
      canonicalLatitudeCoverSignedNormal period hPeriod point ^ 2 :=
  descend_mk period hPeriod Real
    (canonicalLatitudeNormalSquareDeckInvariantField period hPeriod) point

/-- The exact global throat set. -/
def canonicalLatitudeGlobalThroatSet : Set (EffectiveQuotient period hPeriod) :=
  {point | canonicalLatitudeQuotientNormalSquare period hPeriod point = 0}

/-- The global throat set is closed and measurable. -/
theorem canonicalLatitudeGlobalThroatSet_isClosed :
    IsClosed (canonicalLatitudeGlobalThroatSet period hPeriod) := by
  unfold canonicalLatitudeGlobalThroatSet
  exact isClosed_eq
    (canonicalLatitudeQuotientNormalSquare period hPeriod).contMDiff_toFun.continuous
    continuous_const

/-- Off the throat, the global cutoffs converge pointwise to one. -/
theorem canonicalLatitudeMinimalQuotientCutoff_tendsto_one
    (point : EffectiveQuotient period hPeriod)
    (hPoint : point ∉ canonicalLatitudeGlobalThroatSet period hPeriod) :
    Tendsto
      (fun index : Nat =>
        canonicalLatitudeMinimalQuotientCutoff period hPeriod index point)
      atTop (𝓝 1) := by
  refine Quotient.inductionOn point ?_ hPoint
  intro representative hRepresentative
  rw [canonicalLatitudeGlobalThroatSet] at hRepresentative
  have hNormal :
      canonicalLatitudeCoverSignedNormal period hPeriod representative ≠ 0 := by
    intro hZero
    apply hRepresentative
    change canonicalLatitudeQuotientNormalSquare period hPeriod
      (mappingTorusMk (sphereData period hPeriod) representative) = 0
    rw [canonicalLatitudeQuotientNormalSquare_mk, hZero]
    norm_num
  simpa only [canonicalLatitudeMinimalQuotientCutoff_mk,
    canonicalLatitudeMinimalCoverCutoff] using
    canonicalLatitudeMinimalCutoffProfile_tendsto_one
      (canonicalLatitudeCoverSignedNormal period hPeriod representative) hNormal

/-- Global deck-invariant cutoff certificate. -/
theorem canonicalLatitudeMinimalDeckInvariantCutoff_certificate
    (index : Nat) :
    (∀ (winding : Int) (point : EffectiveCover period hPeriod),
      canonicalLatitudeMinimalCoverCutoff period hPeriod index
          (winding +ᵥ point) =
        canonicalLatitudeMinimalCoverCutoff period hPeriod index point) ∧
      (∀ point,
        0 ≤ canonicalLatitudeMinimalQuotientCutoff period hPeriod index point ∧
          canonicalLatitudeMinimalQuotientCutoff period hPeriod index point ≤ 1) ∧
      (∀ field,
        smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
            (canonicalLatitudeMinimalCutoffLinearMap
              period hPeriod index field) = 0) :=
  ⟨canonicalLatitudeMinimalCoverCutoff_deck period hPeriod index,
    fun point =>
      ⟨canonicalLatitudeMinimalQuotientCutoff_nonnegative
          period hPeriod index point,
        canonicalLatitudeMinimalQuotientCutoff_le_one
          period hPeriod index point⟩,
    smoothFirstSheetCauchyTrace_minimalCutoff_eq_zero period hPeriod index⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D
end JanusFormal
