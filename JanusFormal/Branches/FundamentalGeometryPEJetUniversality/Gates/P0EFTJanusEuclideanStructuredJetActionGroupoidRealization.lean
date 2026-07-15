import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusStructuredJetActionGroupoid
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanGlobalSpinCJetRealization

namespace JanusFormal
namespace P0EFTJanusEuclideanStructuredJetActionGroupoidRealization

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusStructuredJetActionGroupoid
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusRieszShapeOperatorEquivariance
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusProjectedSeedSmoothCoefficientTransport
open P0EFTJanusProjectedSeedAmbientJetDescent
open P0EFTJanusEuclideanImmersionConnectionJetExtraction
open P0EFTJanusEuclideanMetricKoszulConnection
open P0EFTJanusEuclideanGlobalSpinCJetRealization
open P0EFTJanusCliffordSpin2DoubleCover

universe u v w y

private instance orthogonalFrameMulAction
    {Model : Type*}
    [NormedAddCommGroup Model] [InnerProductSpace ℝ Model] :
    MulAction (Model ≃ₗᵢ[ℝ] Model) Model where
  smul frame value := frame value
  one_smul := by intro value; rfl
  mul_smul := by
    intro first second value
    rfl

/-- Residual tangent/normal frames together with the rank-two SpinC group. -/
abbrev LowOrderSpinCFrame
    (Tangent Normal : Type*)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] :=
  ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal) ×
    CliffordSpinC2

/-- SpinC acts trivially on the gauge-invariant reduced curvature jet, while
the residual orthogonal frame acts by the already proved tensor laws. -/
instance lowOrderSpinCFrameAction
    {Tangent Normal : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] :
    MulAction (LowOrderSpinCFrame Tangent Normal)
      (LowOrderReducedData Tangent Normal) where
  smul symmetry jet := actOnReducedData symmetry.1 jet
  one_smul := by
    intro jet
    exact actOnReducedData_one jet
  mul_smul := by
    intro first second jet
    exact actOnReducedData_mul first.1 second.1 jet

/-- Forget the continuous bundling while retaining the exact reduced tensor
and curvature identities. -/
def actualJetToLowOrderReducedData
    {Tangent Normal : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    LowOrderReducedData Tangent Normal where
  secondFundamental := fun first second => data.toReducedJet.1 first second
  gaugeCurvature := fun first second => data.toReducedJet.2 first second
  gaugeCurvature_alternating := data.toReducedJet_isGeometric.2

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type w}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]
variable {ι κ : Type y} [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- A certified point of one projected-seed chart. -/
structure EuclideanValidChartPoint
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) where
  center : Tangent
  base : Tangent
  valid : projectedSeedChartValid data.basisData.tangentFrame
    (pointwiseNormalSeedCharts data.basisData) center base

/-- Concrete reduced structured jet extracted from actual Euclidean
immersion, metric-Koszul and gauge-potential derivatives. -/
def euclideanLowOrderStructuredJetAt
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (point : EuclideanValidChartPoint data) :
    LowOrderReducedData Tangent Normal := by
  let globalData := data.coefficients.toEuclideanImmersionConnectionJetData
    |>.toProjectedSeedGlobalAmbientJetData
  let chartData := globalData.toChartData data.tangentBasis
    data.tangentBasis_orthonormal data.normalBasis
    data.normalBasis_orthonormal data.basisData point.center
  exact actualJetToLowOrderReducedData (chartData.localJet point.base)

/-- Every residual-SpinC symmetry determines an arrow of the instantiated
low-order action groupoid. -/
def euclideanLowOrderSpinCArrowAt
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (point : EuclideanValidChartPoint data)
    (symmetry : LowOrderSpinCFrame Tangent Normal) :
    ActionArrow (Symmetry := LowOrderSpinCFrame Tangent Normal)
      (euclideanLowOrderStructuredJetAt data point)
      (symmetry • euclideanLowOrderStructuredJetAt data point) where
  element := symmetry
  maps_source := rfl

/-- Data-bearing realization of the valid-chart low-order action groupoid and
its one-chart rank-two SpinC bundle/connection. -/
theorem euclidean_lowOrder_spinC_groupoid_realized
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (point : EuclideanValidChartPoint data)
    (symmetry : LowOrderSpinCFrame Tangent Normal) :
    Nonempty (ActionArrow (Symmetry := LowOrderSpinCFrame Tangent Normal)
      (euclideanLowOrderStructuredJetAt data point)
      (symmetry • euclideanLowOrderStructuredJetAt data point)) ∧
    Nonempty (CechPrincipalBundleData Tangent Unit CliffordSpinC2) ∧
    Nonempty (CechAbelianConnectionData Tangent Tangent Unit) := by
  exact ⟨⟨euclideanLowOrderSpinCArrowAt data point symmetry⟩,
    ⟨EuclideanMetricProjectedSeedImmersionData.spinCBundle data⟩,
    ⟨EuclideanMetricProjectedSeedImmersionData.spinCConnection data⟩⟩

end

end P0EFTJanusEuclideanStructuredJetActionGroupoidRealization
end JanusFormal
