import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanGlobalSpinCJetRealization

namespace JanusFormal
namespace P0EFTJanusCechAbelianConnectionDescent

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff InnerProductSpace Topology
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusRieszShapeOperatorSmoothReducedJetBase
open P0EFTJanusEuclideanGlobalSpinCJetRealization

universe u v

/-- Conditional multi-chart descent data for an abelian connection on a
Euclidean model.  The gauge shifts are supplied one-forms; no logarithm of a
determinant-line transition function is asserted here. -/
structure CechAbelianConnectionDescentData
    (Tangent : Type u) (Index : Type v)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent] where
  domain : Index → Set Tangent
  domain_isOpen : ∀ index, IsOpen (domain index)
  cover : ∀ base, ∃ index, base ∈ domain index
  potential : Index → Tangent → ContinuousConnectionValue Tangent
  potential_contDiffOn :
    ∀ index, ContDiffOn ℝ ∞ (potential index) (domain index)
  gaugeShift :
    Index → Index → Tangent → ContinuousConnectionValue Tangent
  gaugeShift_contDiffOn : ∀ first second,
    ContDiffOn ℝ ∞ (gaugeShift first second)
      (domain first ∩ domain second)
  gaugeShift_self : ∀ index base, base ∈ domain index →
    gaugeShift index index base = 0
  gaugeShift_inverse : ∀ first second base,
    base ∈ domain first → base ∈ domain second →
      gaugeShift first second base + gaugeShift second first base = 0
  gaugeShift_cocycle : ∀ first second third base,
    base ∈ domain first → base ∈ domain second →
      base ∈ domain third →
        gaugeShift first second base + gaugeShift second third base =
          gaugeShift first third base
  affine_compatible : ∀ first second base,
    base ∈ domain first → base ∈ domain second →
      potential second base =
        potential first base + gaugeShift first second base

variable {Tangent : Type u} {Index : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]

/-- Fréchet derivative of a local connection potential. -/
def CechAbelianConnectionDescentData.localPotentialDerivative
    (data : CechAbelianConnectionDescentData Tangent Index)
    (index : Index) (base : Tangent) :
    ContinuousConnectionDerivative Tangent :=
  fderiv ℝ (data.potential index) base

/-- Fréchet derivative of an overlap gauge-shift one-form. -/
def CechAbelianConnectionDescentData.gaugeShiftDerivative
    (data : CechAbelianConnectionDescentData Tangent Index)
    (first second : Index) (base : Tangent) :
    ContinuousConnectionDerivative Tangent :=
  fderiv ℝ (data.gaugeShift first second) base

/-- Local abelian curvature, obtained by antisymmetrizing the derivative of
the local potential. -/
def CechAbelianConnectionDescentData.localCurvature
    (data : CechAbelianConnectionDescentData Tangent Index)
    (index : Index) (base : Tangent) :
    ContinuousGaugeCurvature (Tangent := Tangent) :=
  continuousCurvatureFromDerivative
    (data.localPotentialDerivative index base)

/-- The derivative of a smooth local potential is smooth on its open chart
domain. -/
theorem CechAbelianConnectionDescentData.localPotentialDerivative_contDiffOn
    (data : CechAbelianConnectionDescentData Tangent Index)
    (index : Index) :
    ContDiffOn ℝ ∞ (data.localPotentialDerivative index)
      (data.domain index) := by
  change ContDiffOn ℝ ∞
    (fderiv ℝ (data.potential index)) (data.domain index)
  exact (data.potential_contDiffOn index).fderiv_of_isOpen
    (data.domain_isOpen index) (m := ∞) (by simp)

/-- Antisymmetrizing the smoothly varying derivative preserves local
smoothness of the curvature coefficient. -/
theorem CechAbelianConnectionDescentData.localCurvature_contDiffOn
    (data : CechAbelianConnectionDescentData Tangent Index)
    (index : Index) :
    ContDiffOn ℝ ∞ (data.localCurvature index) (data.domain index) := by
  have hAntisymmetrization :
      ContDiff ℝ ∞
        (continuousCurvatureFromDerivative (Tangent := Tangent)) := by
    change ContDiff ℝ ∞
      (fun derivative : ContinuousConnectionDerivative Tangent ↦
        derivative - continuousDerivativeFlip (Tangent := Tangent) derivative)
    fun_prop
  change ContDiffOn ℝ ∞
    (continuousCurvatureFromDerivative (Tangent := Tangent) ∘
      data.localPotentialDerivative index) (data.domain index)
  exact hAntisymmetrization.comp_contDiffOn
    (data.localPotentialDerivative_contDiffOn index)

/-- Curvature contribution of an overlap gauge shift. -/
def CechAbelianConnectionDescentData.gaugeShiftCurvature
    (data : CechAbelianConnectionDescentData Tangent Index)
    (first second : Index) (base : Tangent) :
    ContinuousGaugeCurvature (Tangent := Tangent) :=
  continuousCurvatureFromDerivative
    (data.gaugeShiftDerivative first second base)

/-- Pointwise symmetry of the derivative of an overlap gauge shift. -/
def CechAbelianConnectionDescentData.GaugeShiftDerivativeSymmetric
    (data : CechAbelianConnectionDescentData Tangent Index)
    (first second : Index) (base : Tangent) : Prop :=
  ∀ x y,
    data.gaugeShiftDerivative first second base x y =
      data.gaugeShiftDerivative first second base y x

/-- Equivalent curvature-flat formulation of the overlap condition. -/
def CechAbelianConnectionDescentData.GaugeShiftCurvatureFlat
    (data : CechAbelianConnectionDescentData Tangent Index)
    (first second : Index) (base : Tangent) : Prop :=
  data.gaugeShiftCurvature first second base = 0

theorem continuousCurvatureFromDerivative_add
    (first second : ContinuousConnectionDerivative Tangent) :
    continuousCurvatureFromDerivative (first + second) =
      continuousCurvatureFromDerivative first +
        continuousCurvatureFromDerivative second := by
  ext x y
  change (first x y + second x y) - (first y x + second y x) =
    (first x y - first y x) + (second x y - second y x)
  abel

/-- Differentiating affine compatibility on an open overlap gives the affine
law for the corresponding first jets. -/
theorem CechAbelianConnectionDescentData.localPotentialDerivative_affine
    (data : CechAbelianConnectionDescentData Tangent Index)
    (first second : Index) (base : Tangent)
    (hFirst : base ∈ data.domain first)
    (hSecond : base ∈ data.domain second) :
    data.localPotentialDerivative second base =
      data.localPotentialDerivative first base +
        data.gaugeShiftDerivative first second base := by
  have hOverlapOpen : IsOpen (data.domain first ∩ data.domain second) :=
    (data.domain_isOpen first).inter (data.domain_isOpen second)
  have hOverlap : base ∈ data.domain first ∩ data.domain second :=
    ⟨hFirst, hSecond⟩
  have hEventually :
      data.potential second =ᶠ[nhds base]
        (fun point ↦ data.potential first point +
          data.gaugeShift first second point) := by
    filter_upwards [hOverlapOpen.mem_nhds hOverlap] with point hPoint
    exact data.affine_compatible first second point hPoint.1 hPoint.2
  have hPotentialDifferentiable :
      DifferentiableAt ℝ (data.potential first) base :=
    ((data.potential_contDiffOn first).contDiffAt
      ((data.domain_isOpen first).mem_nhds hFirst)).differentiableAt (by simp)
  have hShiftDifferentiable :
      DifferentiableAt ℝ (data.gaugeShift first second) base :=
    ((data.gaugeShift_contDiffOn first second).contDiffAt
      (hOverlapOpen.mem_nhds hOverlap)).differentiableAt (by simp)
  calc
    data.localPotentialDerivative second base =
        fderiv ℝ
          (fun point ↦ data.potential first point +
            data.gaugeShift first second point) base := by
      exact hEventually.fderiv_eq
    _ = data.localPotentialDerivative first base +
          data.gaugeShiftDerivative first second base := by
      simpa [CechAbelianConnectionDescentData.localPotentialDerivative,
        CechAbelianConnectionDescentData.gaugeShiftDerivative] using
        (fderiv_fun_add hPotentialDifferentiable hShiftDifferentiable)

/-- Symmetric derivative and curvature-flatness are the same pointwise
condition for an additive abelian gauge shift. -/
theorem CechAbelianConnectionDescentData.gaugeShiftDerivativeSymmetric_iff_flat
    (data : CechAbelianConnectionDescentData Tangent Index)
    (first second : Index) (base : Tangent) :
    data.GaugeShiftDerivativeSymmetric first second base ↔
      data.GaugeShiftCurvatureFlat first second base := by
  constructor
  · intro hSymmetric
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    change data.gaugeShiftDerivative first second base x y -
        data.gaugeShiftDerivative first second base y x = 0
    rw [hSymmetric x y, sub_self]
  · intro hFlat x y
    change data.gaugeShiftCurvature first second base = 0 at hFlat
    have hAt := congrArg
      (fun curvature : ContinuousGaugeCurvature (Tangent := Tangent) ↦
        curvature x y) hFlat
    change data.gaugeShiftDerivative first second base x y -
        data.gaugeShiftDerivative first second base y x = 0 at hAt
    exact sub_eq_zero.mp hAt

/-- Curvature descends across an overlap whenever the supplied additive gauge
shift is curvature-flat. -/
theorem CechAbelianConnectionDescentData.localCurvature_eq_of_gaugeShiftFlat
    (data : CechAbelianConnectionDescentData Tangent Index)
    (first second : Index) (base : Tangent)
    (hFirst : base ∈ data.domain first)
    (hSecond : base ∈ data.domain second)
    (hFlat : data.GaugeShiftCurvatureFlat first second base) :
    data.localCurvature first base = data.localCurvature second base := by
  symm
  rw [CechAbelianConnectionDescentData.localCurvature,
    data.localPotentialDerivative_affine first second base hFirst hSecond,
    continuousCurvatureFromDerivative_add]
  change data.localCurvature first base +
      data.gaugeShiftCurvature first second base = data.localCurvature first base
  rw [hFlat]
  exact add_zero (data.localCurvature first base)

/-- In particular, a symmetric gauge-shift derivative makes the local
curvature two-forms agree on the overlap. -/
theorem CechAbelianConnectionDescentData.localCurvature_eq_of_gaugeShiftDerivative_symmetric
    (data : CechAbelianConnectionDescentData Tangent Index)
    (first second : Index) (base : Tangent)
    (hFirst : base ∈ data.domain first)
    (hSecond : base ∈ data.domain second)
    (hSymmetric : data.GaugeShiftDerivativeSymmetric first second base) :
    data.localCurvature first base = data.localCurvature second base :=
  data.localCurvature_eq_of_gaugeShiftFlat first second base hFirst hSecond
    ((data.gaugeShiftDerivativeSymmetric_iff_flat first second base).1 hSymmetric)

/-- Conditional hypothesis that every gauge shift is curvature-flat wherever
both of its charts are defined. -/
def CechAbelianConnectionDescentData.AllOverlapGaugeShiftsCurvatureFlat
    (data : CechAbelianConnectionDescentData Tangent Index) : Prop :=
  ∀ first second base,
    base ∈ data.domain first → base ∈ data.domain second →
      data.GaugeShiftCurvatureFlat first second base

/-- A representative chart selected from the supplied cover.  This is only a
Classical choice of representative; no regularity of the selection is
asserted. -/
def CechAbelianConnectionDescentData.selectedCurvatureChart
    (data : CechAbelianConnectionDescentData Tangent Index)
    (base : Tangent) : Index :=
  Classical.choose (data.cover base)

theorem CechAbelianConnectionDescentData.selectedCurvatureChart_mem
    (data : CechAbelianConnectionDescentData Tangent Index)
    (base : Tangent) :
    base ∈ data.domain (data.selectedCurvatureChart base) :=
  Classical.choose_spec (data.cover base)

/-- Pointwise descended curvature, represented using an arbitrary chart from
the cover.  The flat-overlap hypothesis makes its value independent of this
Classical representative.  This definition does not assert a smooth global
two-form. -/
def CechAbelianConnectionDescentData.descendedCurvature
    (data : CechAbelianConnectionDescentData Tangent Index)
    (_hFlat : data.AllOverlapGaugeShiftsCurvatureFlat)
    (base : Tangent) : ContinuousGaugeCurvature (Tangent := Tangent) :=
  data.localCurvature (data.selectedCurvatureChart base) base

/-- The selected descended value agrees with every local curvature whose
chart contains the base point. -/
theorem CechAbelianConnectionDescentData.descendedCurvature_eq_local
    (data : CechAbelianConnectionDescentData Tangent Index)
    (hFlat : data.AllOverlapGaugeShiftsCurvatureFlat)
    (index : Index) (base : Tangent)
    (hIndex : base ∈ data.domain index) :
    data.descendedCurvature hFlat base = data.localCurvature index base := by
  apply data.localCurvature_eq_of_gaugeShiftFlat
    (data.selectedCurvatureChart base) index base
    (data.selectedCurvatureChart_mem base) hIndex
  exact hFlat (data.selectedCurvatureChart base) index base
    (data.selectedCurvatureChart_mem base) hIndex

/-- Hence any two valid chart representatives give the same curvature. -/
theorem CechAbelianConnectionDescentData.localCurvature_chart_independent
    (data : CechAbelianConnectionDescentData Tangent Index)
    (hFlat : data.AllOverlapGaugeShiftsCurvatureFlat)
    (first second : Index) (base : Tangent)
    (hFirst : base ∈ data.domain first)
    (hSecond : base ∈ data.domain second) :
    data.localCurvature first base = data.localCurvature second base :=
  data.localCurvature_eq_of_gaugeShiftFlat first second base hFirst hSecond
    (hFlat first second base hFirst hSecond)

/-- The descended curvature is the unique pointwise function agreeing with
all local curvatures on their chart domains. -/
theorem CechAbelianConnectionDescentData.descendedCurvature_unique
    (data : CechAbelianConnectionDescentData Tangent Index)
    (hFlat : data.AllOverlapGaugeShiftsCurvatureFlat)
    (candidate : Tangent → ContinuousGaugeCurvature (Tangent := Tangent))
    (hCandidate : ∀ index base, base ∈ data.domain index →
      candidate base = data.localCurvature index base) :
    candidate = data.descendedCurvature hFlat := by
  funext base
  let index := data.selectedCurvatureChart base
  exact (hCandidate index base (data.selectedCurvatureChart_mem base)).trans
    (data.descendedCurvature_eq_local hFlat index base
      (data.selectedCurvatureChart_mem base)).symm

/-- Flat overlap shifts glue the chartwise smooth curvature coefficients to a
globally smooth curvature function.  Regularity follows locally from any
chart in the open cover, so no regularity of the selected chart is needed. -/
theorem CechAbelianConnectionDescentData.descendedCurvature_contDiff
    (data : CechAbelianConnectionDescentData Tangent Index)
    (hFlat : data.AllOverlapGaugeShiftsCurvatureFlat) :
    ContDiff ℝ ∞ (data.descendedCurvature hFlat) := by
  rw [contDiff_iff_contDiffAt]
  intro base
  let index := data.selectedCurvatureChart base
  have hIndex : base ∈ data.domain index :=
    data.selectedCurvatureChart_mem base
  have hLocalAt : ContDiffAt ℝ ∞ (data.localCurvature index) base :=
    (data.localCurvature_contDiffOn index).contDiffAt
      ((data.domain_isOpen index).mem_nhds hIndex)
  have hEventuallyEq :
      data.descendedCurvature hFlat =ᶠ[nhds base]
        data.localCurvature index := by
    filter_upwards [(data.domain_isOpen index).mem_nhds hIndex] with point hPoint
    exact data.descendedCurvature_eq_local hFlat index point hPoint
  exact hLocalAt.congr_of_eventuallyEq hEventuallyEq

/-- The former equality-only model embeds as the zero-shift special case on
the full-overlap cover. -/
def equalityOnlyConnectionDescent
    [Nonempty Index]
    (data : CechAbelianConnectionData Tangent Tangent Index) :
    CechAbelianConnectionDescentData Tangent Index where
  domain := fun _ ↦ Set.univ
  domain_isOpen := fun _ ↦ isOpen_univ
  cover := fun base ↦ ⟨Classical.choice inferInstance, Set.mem_univ base⟩
  potential := data.potential
  potential_contDiffOn := fun index ↦ (data.potential_contDiff index).contDiffOn
  gaugeShift := fun _ _ _ ↦ 0
  gaugeShift_contDiffOn := by fun_prop
  gaugeShift_self := by simp
  gaugeShift_inverse := by simp
  gaugeShift_cocycle := by simp
  affine_compatible := by
    intro first second base _ _
    simpa using (data.compatible second first base)

end

end P0EFTJanusCechAbelianConnectionDescent
end JanusFormal
