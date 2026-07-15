import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanStructuredJetOverlapGroupoid

namespace JanusFormal
namespace P0EFTJanusEuclideanStructuredJetOverlapDescent

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff InnerProductSpace Topology
open P0EFTJanusStructuredJetActionGroupoid
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusRieszShapeOperatorSmoothReducedJetBase
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusProjectedSeedSmoothCoefficientTransport
open P0EFTJanusEuclideanImmersionConnectionJetExtraction
open P0EFTJanusEuclideanMetricKoszulConnection
open P0EFTJanusEuclideanStructuredJetActionGroupoidRealization
open P0EFTJanusEuclideanStructuredJetOverlapGroupoid

universe u v w y z

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type w}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]
variable {ι κ : Type y} [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Projected-seed chart centers whose chart is valid at one fixed base point.
This is only the low-order Euclidean point-centered atlas. -/
def EuclideanLowOrderValidChartCenterAt
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base : Tangent) : Type u :=
  {center : Tangent //
    projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) center base}

/-- A valid center at a fixed base, repackaged as the certified chart point
used by the concrete low-order jet extractor. -/
def euclideanLowOrderValidChartPointAt
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base : Tangent)
    (center : EuclideanLowOrderValidChartCenterAt data base) :
    EuclideanValidChartPoint data where
  center := center.1
  base := base
  valid := center.2

/-- The actual reduced low-order jet extracted in a valid chart at a fixed
base point. -/
def euclideanLowOrderValidChartJetAt
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base : Tangent)
    (center : EuclideanLowOrderValidChartCenterAt data base) :
    LowOrderReducedData Tangent Normal :=
  euclideanLowOrderStructuredJetAt data
    (euclideanLowOrderValidChartPointAt data base center)

/-- The point-centered chart gives a canonical valid center at every base. -/
def euclideanLowOrderCanonicalCenterAt
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base : Tangent) : EuclideanLowOrderValidChartCenterAt data base :=
  ⟨base, pointwiseNormalSeedChart_valid_at_center data.basisData base⟩

/-- Canonical overlap arrow from the jet in `second` to the jet in `first`. -/
def euclideanLowOrderValidChartOverlapArrowAt
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base : Tangent)
    (first second : EuclideanLowOrderValidChartCenterAt data base) :
    ActionArrow (Symmetry := LowOrderSpinCFrame Tangent Normal)
      (euclideanLowOrderValidChartJetAt data base second)
      (euclideanLowOrderValidChartJetAt data base first) :=
  euclideanLowOrderSpinCOverlapArrow data first.1 second.1 base
    first.2 second.2

@[simp]
theorem euclideanLowOrderValidChartOverlapArrowAt_self
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base : Tangent)
    (center : EuclideanLowOrderValidChartCenterAt data base) :
    euclideanLowOrderValidChartOverlapArrowAt data base center center =
      idArrow (euclideanLowOrderValidChartJetAt data base center) := by
  exact euclideanLowOrderSpinCOverlapArrow_self data center.1 base center.2

/-- Canonical overlap arrows obey the Cech composition law. -/
theorem euclideanLowOrderValidChartOverlapArrowAt_comp
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base : Tangent)
    (first second third : EuclideanLowOrderValidChartCenterAt data base) :
    comp
        (euclideanLowOrderValidChartOverlapArrowAt data base first second)
        (euclideanLowOrderValidChartOverlapArrowAt data base second third) =
      euclideanLowOrderValidChartOverlapArrowAt data base first third := by
  exact euclideanLowOrderSpinCOverlapArrow_comp data
    first.1 second.1 third.1 base first.2 second.2 third.2

/-- At a fixed base, every pair of actual low-order chart jets lies in one
residual SpinC-frame orbit. -/
theorem euclideanLowOrderValidChartJets_sameOrbit
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base : Tangent)
    (first second : EuclideanLowOrderValidChartCenterAt data base) :
    SameOrbit (Symmetry := LowOrderSpinCFrame Tangent Normal)
      (euclideanLowOrderValidChartJetAt data base first)
      (euclideanLowOrderValidChartJetAt data base second) :=
  ⟨euclideanLowOrderValidChartOverlapArrowAt data base second first⟩

/-- Invariance of a low-order observable under every residual orthogonal and
SpinC frame action. -/
def IsEuclideanLowOrderSpinCInvariant
    {Target : Type z}
    (observable : LowOrderReducedData Tangent Normal → Target) : Prop :=
  ∀ (symmetry : LowOrderSpinCFrame Tangent Normal)
    (jet : LowOrderReducedData Tangent Normal),
      observable (symmetry • jet) = observable jet

/-- Values of an invariant observable agree in all valid charts at a fixed
base point. -/
theorem euclideanLowOrderInvariantObservable_chart_independent
    {Target : Type z}
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (observable : LowOrderReducedData Tangent Normal → Target)
    (hInvariant : IsEuclideanLowOrderSpinCInvariant observable)
    (base : Tangent)
    (first second : EuclideanLowOrderValidChartCenterAt data base) :
    observable (euclideanLowOrderValidChartJetAt data base first) =
      observable (euclideanLowOrderValidChartJetAt data base second) := by
  let arrow := euclideanLowOrderValidChartOverlapArrowAt data base first second
  calc
    observable (euclideanLowOrderValidChartJetAt data base first) =
        observable
          (arrow.element • euclideanLowOrderValidChartJetAt data base second) := by
      exact congrArg observable arrow.maps_source.symm
    _ = observable (euclideanLowOrderValidChartJetAt data base second) :=
      hInvariant arrow.element
        (euclideanLowOrderValidChartJetAt data base second)

/-- Descended value chosen in the canonical chart centered at the base. -/
def euclideanLowOrderDescendedObservableAt
    {Target : Type z}
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (observable : LowOrderReducedData Tangent Normal → Target)
    (base : Tangent) : Target :=
  observable (euclideanLowOrderValidChartJetAt data base
    (euclideanLowOrderCanonicalCenterAt data base))

/-- A smooth realization of an observable on the normed space of continuous
reduced coefficients.  Agreement is required on every actual local jet, so
this is a structural regularity condition on the observable rather than an
assumption about the descended composite. -/
structure SmoothEuclideanLowOrderObservableRealization
    {Target : Type z}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (observable : LowOrderReducedData Tangent Normal → Target) where
  continuousObservable :
    SmoothLowOrderReducedJet (Tangent := Tangent) (Normal := Normal) → Target
  continuousObservable_contDiff : ContDiff ℝ ∞ continuousObservable
  agrees_on_actual_jets :
    ∀ jet : ActualJanusLocalJetData
        (Tangent := Tangent) (Normal := Normal),
      observable (actualJetToLowOrderReducedData jet) =
        continuousObservable jet.toReducedJet

/-- On a fixed projected-seed chart, the continuous reduced coefficient pair
underlying the concrete Euclidean low-order jet. -/
def euclideanLowOrderContinuousChartJet
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (center base : Tangent) :
    SmoothLowOrderReducedJet (Tangent := Tangent) (Normal := Normal) :=
  let globalData := data.coefficients.toEuclideanImmersionConnectionJetData
    |>.toProjectedSeedGlobalAmbientJetData
  let chartData := globalData.toChartData data.tangentBasis
    data.tangentBasis_orthonormal data.normalBasis
    data.normalBasis_orthonormal data.basisData center
  chartData.reducedJet base

/-- The fixed-center continuous representative is smooth on its valid chart
domain, directly from projected-seed coefficient transport. -/
theorem euclideanLowOrderContinuousChartJet_contDiffOn
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (center : Tangent) :
    ContDiffOn ℝ ∞ (euclideanLowOrderContinuousChartJet data center)
      (projectedSeedCoefficientDomain data.basisData center) := by
  exact
    (data.coefficients.toEuclideanImmersionConnectionJetData
      |>.toProjectedSeedGlobalAmbientJetData
      |>.toChartData data.tangentBasis data.tangentBasis_orthonormal
        data.normalBasis data.normalBasis_orthonormal data.basisData center)
      |>.reducedJet_contDiffOn

/-- At every valid point, the proof-carrying groupoid jet and the continuous
coefficient representative give the same value to a smoothly realized
observable. -/
theorem euclideanLowOrderSmoothObservable_validChart_eq_continuous
    {Target : Type z}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (observable : LowOrderReducedData Tangent Normal → Target)
    (realization : SmoothEuclideanLowOrderObservableRealization observable)
    (base : Tangent)
    (center : EuclideanLowOrderValidChartCenterAt data base) :
    observable (euclideanLowOrderValidChartJetAt data base center) =
      realization.continuousObservable
        (euclideanLowOrderContinuousChartJet data center.1 base) := by
  exact realization.agrees_on_actual_jets _

/-- A smoothly realized observable is smooth on every fixed-center valid
chart. -/
theorem euclideanLowOrderSmoothObservable_fixedChart_contDiffOn
    {Target : Type z}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (observable : LowOrderReducedData Tangent Normal → Target)
    (realization : SmoothEuclideanLowOrderObservableRealization observable)
    (center : Tangent) :
    ContDiffOn ℝ ∞
      (fun base => realization.continuousObservable
        (euclideanLowOrderContinuousChartJet data center base))
      (projectedSeedCoefficientDomain data.basisData center) := by
  exact realization.continuousObservable_contDiff.comp_contDiffOn
    (euclideanLowOrderContinuousChartJet_contDiffOn data center)

/-- Every valid-chart evaluation equals the canonical descended value. -/
theorem euclideanLowOrderInvariantObservable_eq_descended
    {Target : Type z}
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (observable : LowOrderReducedData Tangent Normal → Target)
    (hInvariant : IsEuclideanLowOrderSpinCInvariant observable)
    (base : Tangent)
    (center : EuclideanLowOrderValidChartCenterAt data base) :
    observable (euclideanLowOrderValidChartJetAt data base center) =
      euclideanLowOrderDescendedObservableAt data observable base := by
  exact euclideanLowOrderInvariantObservable_chart_independent data observable
    hInvariant base center (euclideanLowOrderCanonicalCenterAt data base)

/-- The descended observable is globally smooth.  Around each point the proof
keeps that point as a fixed chart center; invariance identifies the moving
canonical representative with this smooth fixed-chart representative.  Thus
no unproved joint smoothness of the point-centered seed chart is assumed. -/
theorem euclideanLowOrderDescendedObservable_contDiff
    {Target : Type z}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (observable : LowOrderReducedData Tangent Normal → Target)
    (hInvariant : IsEuclideanLowOrderSpinCInvariant observable)
    (realization : SmoothEuclideanLowOrderObservableRealization observable) :
    ContDiff ℝ ∞
      (euclideanLowOrderDescendedObservableAt data observable) := by
  rw [contDiff_iff_contDiffAt]
  intro base
  have hDomainNhds :
      projectedSeedCoefficientDomain data.basisData base ∈ nhds base := by
    change ∀ᶠ nearby in nhds base,
      projectedSeedChartValid data.basisData.tangentFrame
        (pointwiseNormalSeedCharts data.basisData) base nearby
    exact pointwiseNormalSeedChart_eventually_valid data.basisData base
  have hLocalAt : ContDiffAt ℝ ∞
      (fun nearby => realization.continuousObservable
        (euclideanLowOrderContinuousChartJet data base nearby)) base :=
    (euclideanLowOrderSmoothObservable_fixedChart_contDiffOn
      data observable realization base).contDiffAt hDomainNhds
  have hEventuallyEq :
      euclideanLowOrderDescendedObservableAt data observable =ᶠ[nhds base]
        fun nearby => realization.continuousObservable
          (euclideanLowOrderContinuousChartJet data base nearby) := by
    filter_upwards [hDomainNhds] with nearby hNearby
    let center : EuclideanLowOrderValidChartCenterAt data nearby :=
      ⟨base, hNearby⟩
    calc
      euclideanLowOrderDescendedObservableAt data observable nearby =
          observable (euclideanLowOrderValidChartJetAt data nearby center) :=
        (euclideanLowOrderInvariantObservable_eq_descended data observable
          hInvariant nearby center).symm
      _ = realization.continuousObservable
          (euclideanLowOrderContinuousChartJet data base nearby) :=
        euclideanLowOrderSmoothObservable_validChart_eq_continuous
          data observable realization nearby center
  exact hLocalAt.congr_of_eventuallyEq hEventuallyEq

/-- The descended value exists uniquely because the point-centered chart is
always valid. This is fixed-base, low-order Euclidean descent, not a claim of
full smooth effective descent for the global Janus structured-jet groupoid. -/
theorem euclideanLowOrderInvariantObservable_existsUnique_descended
    {Target : Type z}
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (observable : LowOrderReducedData Tangent Normal → Target)
    (hInvariant : IsEuclideanLowOrderSpinCInvariant observable)
    (base : Tangent) :
    ∃! value : Target,
      ∀ center : EuclideanLowOrderValidChartCenterAt data base,
        observable (euclideanLowOrderValidChartJetAt data base center) = value := by
  refine ⟨euclideanLowOrderDescendedObservableAt data observable base, ?_, ?_⟩
  · intro center
    exact euclideanLowOrderInvariantObservable_eq_descended data observable
      hInvariant base center
  · intro value hValue
    exact (hValue (euclideanLowOrderCanonicalCenterAt data base)).symm

end

end P0EFTJanusEuclideanStructuredJetOverlapDescent
end JanusFormal
