import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D

/-!
# Canonical smooth periodic and antiperiodic boundary cores

The physical Cauchy extension previously accepted arbitrary value and normal
core types together with representatives, periodicity proofs, `L²` embeddings
and almost-everywhere agreement data.

This file defines the canonical core types themselves:

* smooth, square-integrable value representatives satisfying the period law;
* smooth, square-integrable normal representatives satisfying the sign-twisted
  antiperiod law.

Their pointwise vector-space structures, deck laws, smoothness and canonical
`L²` embeddings are built into the types.  The only remaining boundary-core
input is density of these two canonical embeddings.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetOpenCoverSmoothness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D

variable (period : Real)

local instance canonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Canonical smooth value core: smooth, square-integrable and periodic. -/
structure CanonicalLatitudeSmoothPeriodicValueCore where
  toFun : CanonicalLatitudeBase → Real
  contMDiff_toFun : ContMDiff canonicalLatitudeBaseModelWithCorners
    𝓘(Real, Real) ∞ toFun
  deck_periodic : CanonicalLatitudeValueDeckPeriodic period toFun
  memLp_toFun : MemLp toFun (2 : ENNReal)
    (canonicalLatitudeBaseMeasure period)

/-- Canonical smooth normal core: smooth, square-integrable and
antiperiodic. -/
structure CanonicalLatitudeSmoothAntiperiodicNormalCore where
  toFun : CanonicalLatitudeBase → Real
  contMDiff_toFun : ContMDiff canonicalLatitudeBaseModelWithCorners
    𝓘(Real, Real) ∞ toFun
  deck_antiperiodic : CanonicalLatitudeNormalDeckAntiperiodic period toFun
  memLp_toFun : MemLp toFun (2 : ENNReal)
    (canonicalLatitudeBaseMeasure period)

instance : CoeFun (CanonicalLatitudeSmoothPeriodicValueCore period)
    (fun _ => CanonicalLatitudeBase → Real) :=
  ⟨CanonicalLatitudeSmoothPeriodicValueCore.toFun⟩

instance : CoeFun (CanonicalLatitudeSmoothAntiperiodicNormalCore period)
    (fun _ => CanonicalLatitudeBase → Real) :=
  ⟨CanonicalLatitudeSmoothAntiperiodicNormalCore.toFun⟩

@[ext] theorem CanonicalLatitudeSmoothPeriodicValueCore.ext
    {first second : CanonicalLatitudeSmoothPeriodicValueCore period}
    (hEqual : ∀ base, first base = second base) : first = second := by
  cases first
  cases second
  simp only [mk.injEq]
  exact funext hEqual

@[ext] theorem CanonicalLatitudeSmoothAntiperiodicNormalCore.ext
    {first second : CanonicalLatitudeSmoothAntiperiodicNormalCore period}
    (hEqual : ∀ base, first base = second base) : first = second := by
  cases first
  cases second
  simp only [mk.injEq]
  exact funext hEqual

instance : Zero (CanonicalLatitudeSmoothPeriodicValueCore period) where
  zero :=
    { toFun := fun _ => 0
      contMDiff_toFun := contMDiff_const
      deck_periodic := by
        intro base
        rfl
      memLp_toFun := MemLp.zero }

instance : Add (CanonicalLatitudeSmoothPeriodicValueCore period) where
  add first second :=
    { toFun := fun base => first base + second base
      contMDiff_toFun := first.contMDiff_toFun.add second.contMDiff_toFun
      deck_periodic := by
        intro base
        change first (canonicalLatitudeBaseDeck period base) +
          second (canonicalLatitudeBaseDeck period base) =
            first base + second base
        rw [first.deck_periodic base, second.deck_periodic base]
      memLp_toFun := first.memLp_toFun.add second.memLp_toFun }

instance : Neg (CanonicalLatitudeSmoothPeriodicValueCore period) where
  neg value :=
    { toFun := fun base => -value base
      contMDiff_toFun := value.contMDiff_toFun.neg
      deck_periodic := by
        intro base
        change -value (canonicalLatitudeBaseDeck period base) = -value base
        rw [value.deck_periodic base]
      memLp_toFun := value.memLp_toFun.neg }

instance : AddCommGroup (CanonicalLatitudeSmoothPeriodicValueCore period) where
  add_assoc := by intro first second third; ext base; exact add_assoc _ _ _
  zero_add := by intro value; ext base; exact zero_add _
  add_zero := by intro value; ext base; exact add_zero _
  nsmul := nsmulRec
  add_comm := by intro first second; ext base; exact add_comm _ _
  neg_add_cancel := by intro value; ext base; exact neg_add_cancel _
  sub_eq_add_neg := by intro first second; ext base; exact sub_eq_add_neg _ _
  zsmul := zsmulRec

instance : SMul Real (CanonicalLatitudeSmoothPeriodicValueCore period) where
  smul scalar value :=
    { toFun := fun base => scalar * value base
      contMDiff_toFun := contMDiff_const.mul value.contMDiff_toFun
      deck_periodic := by
        intro base
        change scalar * value (canonicalLatitudeBaseDeck period base) =
          scalar * value base
        rw [value.deck_periodic base]
      memLp_toFun := value.memLp_toFun.const_smul scalar }

instance : Module Real (CanonicalLatitudeSmoothPeriodicValueCore period) where
  one_smul := by intro value; ext base; exact one_mul _
  mul_smul := by intro first second value; ext base; exact mul_assoc _ _ _
  smul_add := by intro scalar first second; ext base; exact mul_add _ _ _
  smul_zero := by intro scalar; ext base; exact mul_zero _
  add_smul := by intro first second value; ext base; exact add_mul _ _ _
  zero_smul := by intro value; ext base; exact zero_mul _

instance : Zero (CanonicalLatitudeSmoothAntiperiodicNormalCore period) where
  zero :=
    { toFun := fun _ => 0
      contMDiff_toFun := contMDiff_const
      deck_antiperiodic := by
        intro base
        simp
      memLp_toFun := MemLp.zero }

instance : Add (CanonicalLatitudeSmoothAntiperiodicNormalCore period) where
  add first second :=
    { toFun := fun base => first base + second base
      contMDiff_toFun := first.contMDiff_toFun.add second.contMDiff_toFun
      deck_antiperiodic := by
        intro base
        change first (canonicalLatitudeBaseDeck period base) +
          second (canonicalLatitudeBaseDeck period base) =
            -(first base + second base)
        rw [first.deck_antiperiodic base,
          second.deck_antiperiodic base]
        ring
      memLp_toFun := first.memLp_toFun.add second.memLp_toFun }

instance : Neg (CanonicalLatitudeSmoothAntiperiodicNormalCore period) where
  neg normal :=
    { toFun := fun base => -normal base
      contMDiff_toFun := normal.contMDiff_toFun.neg
      deck_antiperiodic := by
        intro base
        change -normal (canonicalLatitudeBaseDeck period base) =
          -(-normal base)
        rw [normal.deck_antiperiodic base]
      memLp_toFun := normal.memLp_toFun.neg }

instance : AddCommGroup (CanonicalLatitudeSmoothAntiperiodicNormalCore period) where
  add_assoc := by intro first second third; ext base; exact add_assoc _ _ _
  zero_add := by intro value; ext base; exact zero_add _
  add_zero := by intro value; ext base; exact add_zero _
  nsmul := nsmulRec
  add_comm := by intro first second; ext base; exact add_comm _ _
  neg_add_cancel := by intro value; ext base; exact neg_add_cancel _
  sub_eq_add_neg := by intro first second; ext base; exact sub_eq_add_neg _ _
  zsmul := zsmulRec

instance : SMul Real (CanonicalLatitudeSmoothAntiperiodicNormalCore period) where
  smul scalar normal :=
    { toFun := fun base => scalar * normal base
      contMDiff_toFun := contMDiff_const.mul normal.contMDiff_toFun
      deck_antiperiodic := by
        intro base
        change scalar * normal (canonicalLatitudeBaseDeck period base) =
          -(scalar * normal base)
        rw [normal.deck_antiperiodic base]
        ring
      memLp_toFun := normal.memLp_toFun.const_smul scalar }

instance : Module Real (CanonicalLatitudeSmoothAntiperiodicNormalCore period) where
  one_smul := by intro value; ext base; exact one_mul _
  mul_smul := by intro first second value; ext base; exact mul_assoc _ _ _
  smul_add := by intro scalar first second; ext base; exact mul_add _ _ _
  smul_zero := by intro scalar; ext base; exact mul_zero _
  add_smul := by intro first second value; ext base; exact add_mul _ _ _
  zero_smul := by intro value; ext base; exact zero_mul _

/-- Canonical `L²` embedding of the periodic value core. -/
def canonicalLatitudeSmoothPeriodicValueEmbedding :
    CanonicalLatitudeSmoothPeriodicValueCore period →ₗ[Real]
      BoundaryL2 period where
  toFun value := value.memLp_toFun.toLp value.toFun
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [(first + second).memLp_toFun.coeFn_toLp,
       first.memLp_toFun.coeFn_toLp,
       second.memLp_toFun.coeFn_toLp,
       Lp.coeFn_add
        (first.memLp_toFun.toLp first.toFun)
        (second.memLp_toFun.toLp second.toFun)]
      with base hSum hFirst hSecond hAdd
    simp only [Pi.add_apply] at hAdd
    rw [hSum, hAdd, hFirst, hSecond]
    rfl
  map_smul' scalar value := by
    apply Lp.ext
    filter_upwards
      [(scalar • value).memLp_toFun.coeFn_toLp,
       value.memLp_toFun.coeFn_toLp,
       Lp.coeFn_smul scalar (value.memLp_toFun.toLp value.toFun)]
      with base hScaled hValue hSmul
    simp only [Pi.smul_apply, smul_eq_mul] at hSmul
    rw [hScaled]
    simp only [RingHom.id_apply]
    rw [hSmul, hValue]
    rfl

/-- Canonical `L²` embedding of the antiperiodic normal core. -/
def canonicalLatitudeSmoothAntiperiodicNormalEmbedding :
    CanonicalLatitudeSmoothAntiperiodicNormalCore period →ₗ[Real]
      BoundaryL2 period where
  toFun normal := normal.memLp_toFun.toLp normal.toFun
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [(first + second).memLp_toFun.coeFn_toLp,
       first.memLp_toFun.coeFn_toLp,
       second.memLp_toFun.coeFn_toLp,
       Lp.coeFn_add
        (first.memLp_toFun.toLp first.toFun)
        (second.memLp_toFun.toLp second.toFun)]
      with base hSum hFirst hSecond hAdd
    simp only [Pi.add_apply] at hAdd
    rw [hSum, hAdd, hFirst, hSecond]
    rfl
  map_smul' scalar normal := by
    apply Lp.ext
    filter_upwards
      [(scalar • normal).memLp_toFun.coeFn_toLp,
       normal.memLp_toFun.coeFn_toLp,
       Lp.coeFn_smul scalar (normal.memLp_toFun.toLp normal.toFun)]
      with base hScaled hNormal hSmul
    simp only [Pi.smul_apply, smul_eq_mul] at hSmul
    rw [hScaled]
    simp only [RingHom.id_apply]
    rw [hSmul, hNormal]
    rfl

/-- Almost-everywhere realization of the value embedding. -/
theorem canonicalLatitudeSmoothPeriodicValueEmbedding_ae
    (value : CanonicalLatitudeSmoothPeriodicValueCore period) :
    (canonicalLatitudeSmoothPeriodicValueEmbedding period value :
        CanonicalLatitudeBase → Real) =ᵐ[canonicalLatitudeBaseMeasure period]
      value.toFun :=
  value.memLp_toFun.coeFn_toLp

/-- Almost-everywhere realization of the normal embedding. -/
theorem canonicalLatitudeSmoothAntiperiodicNormalEmbedding_ae
    (normal : CanonicalLatitudeSmoothAntiperiodicNormalCore period) :
    (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period normal :
        CanonicalLatitudeBase → Real) =ᵐ[canonicalLatitudeBaseMeasure period]
      normal.toFun :=
  normal.memLp_toFun.coeFn_toLp

/-- The sole density input for the canonical smooth boundary cores. -/
structure CanonicalLatitudeSmoothBoundaryCoreDensityData where
  valueDense : DenseRange
    (canonicalLatitudeSmoothPeriodicValueEmbedding period)
  normalDense : DenseRange
    (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)

namespace CanonicalLatitudeSmoothBoundaryCoreDensityData

/-- Install the smooth Cauchy boundary-core package used by the explicit global
jet construction. -/
def toSmoothCauchyJetBoundaryCoreData
    (density : CanonicalLatitudeSmoothBoundaryCoreDensityData period) :
    CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period
      (CanonicalLatitudeSmoothPeriodicValueCore period)
      (CanonicalLatitudeSmoothAntiperiodicNormalCore period) where
  toCanonicalPhysicalScalarCauchyJetBoundaryCoreData :=
    { valueRepresentative :=
        { toFun := fun value => value.toFun
          map_add' := by intro first second; rfl
          map_smul' := by intro scalar value; rfl }
      normalRepresentative :=
        { toFun := fun normal => normal.toFun
          map_add' := by intro first second; rfl
          map_smul' := by intro scalar normal; rfl }
      valuePeriodic := fun value => value.deck_periodic
      normalAntiperiodic := fun normal => normal.deck_antiperiodic
      valueEmbedding := canonicalLatitudeSmoothPeriodicValueEmbedding period
      normalEmbedding := canonicalLatitudeSmoothAntiperiodicNormalEmbedding period
      valueDense := density.valueDense
      normalDense := density.normalDense
      valueEmbedding_ae :=
        canonicalLatitudeSmoothPeriodicValueEmbedding_ae period
      normalEmbedding_ae :=
        canonicalLatitudeSmoothAntiperiodicNormalEmbedding_ae period }
  value_contMDiff := fun value => value.contMDiff_toFun
  normal_contMDiff := fun normal => normal.contMDiff_toFun

/-- Canonical boundary-core certificate. -/
theorem certificate
    (density : CanonicalLatitudeSmoothBoundaryCoreDensityData period) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) ∧
      (∀ value : CanonicalLatitudeSmoothPeriodicValueCore period,
        CanonicalLatitudeValueDeckPeriodic period value) ∧
      (∀ normal : CanonicalLatitudeSmoothAntiperiodicNormalCore period,
        CanonicalLatitudeNormalDeckAntiperiodic period normal) :=
  ⟨density.valueDense, density.normalDense,
    fun value => value.deck_periodic,
    fun normal => normal.deck_antiperiodic⟩

end CanonicalLatitudeSmoothBoundaryCoreDensityData

end
end P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
end JanusFormal
