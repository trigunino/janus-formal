import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorVariableOverlap
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorStructuredJetInstantiation

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorVariableOverlapInstantiation

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorMovingFrame
open P0EFTJanusRieszShapeOperatorVariableOverlap
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorStructuredJetInstantiation

universe u v w x

variable {JetBase : Type w} {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup JetBase] [NormedSpace ℝ JetBase]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]

/-- A reference trivialization and a family of variable overlap gauges indexed
by chart centers. This is the exact situation already handled by the variable
overlap invariance theorem. -/
structure VariableOverlapRieszCharts (Chart : Type x) where
  referenceTangentFrame : SmoothOrthogonalFrameFamily JetBase Tangent
  referenceNormalFrame : SmoothOrthogonalFrameFamily JetBase Normal
  transition : Chart → SmoothResidualOrthogonalFrameFamily JetBase Tangent Normal
  form : JetBase → ContinuousSecondFundamentalForm
    (Tangent := Tangent) (Normal := Normal)
  physicalNormal : JetBase → Normal
  form_contDiff : ContDiff ℝ ∞ form
  physicalNormal_contDiff : ContDiff ℝ ∞ physicalNormal

variable {Chart : Type x}

/-- Coordinate-free physical Riesz family in the reference trivialization. -/
def VariableOverlapRieszCharts.physicalRiesz
    (charts : VariableOverlapRieszCharts
      (JetBase := JetBase) (Tangent := Tangent) (Normal := Normal) Chart) :
    JetBase → Tangent →L[ℝ] Tangent :=
  geometricRieszShapeFamily charts.referenceTangentFrame
    charts.referenceNormalFrame charts.form charts.physicalNormal

/-- Local Riesz expression in the chart obtained by the selected variable
orthogonal reparametrization. -/
def VariableOverlapRieszCharts.localRiesz
    (charts : VariableOverlapRieszCharts
      (JetBase := JetBase) (Tangent := Tangent) (Normal := Normal) Chart)
    (chart : Chart) : JetBase → Tangent →L[ℝ] Tangent :=
  geometricRieszShapeFamily
    (reparametrizeSmoothOrthogonalFrameFamilyVariable
      charts.referenceTangentFrame (charts.transition chart).tangent)
    (reparametrizeSmoothOrthogonalFrameFamilyVariable
      charts.referenceNormalFrame (charts.transition chart).normal)
    (transformContinuousIIOnOverlap (charts.transition chart) charts.form)
    charts.physicalNormal

/-- Every local chart expression realizes the same physical Riesz family. -/
theorem VariableOverlapRieszCharts.localRiesz_eq_physicalRiesz
    (charts : VariableOverlapRieszCharts
      (JetBase := JetBase) (Tangent := Tangent) (Normal := Normal) Chart)
    (chart : Chart) :
    charts.localRiesz chart = charts.physicalRiesz := by
  exact geometricRieszShapeFamily_variable_coordinate_invariant
    charts.referenceTangentFrame charts.referenceNormalFrame
    (charts.transition chart) charts.form charts.physicalNormal

/-- Each local chart expression is smooth. -/
theorem VariableOverlapRieszCharts.localRiesz_contDiff
    (charts : VariableOverlapRieszCharts
      (JetBase := JetBase) (Tangent := Tangent) (Normal := Normal) Chart)
    (chart : Chart) :
    ContDiff ℝ ∞ (charts.localRiesz chart) := by
  exact geometricRieszShapeFamily_variable_overlap_contDiff
    charts.referenceTangentFrame charts.referenceNormalFrame
    (charts.transition chart) charts.form charts.physicalNormal
    charts.form_contDiff charts.physicalNormal_contDiff

/-- The physical Riesz family itself is smooth. -/
theorem VariableOverlapRieszCharts.physicalRiesz_contDiff
    (charts : VariableOverlapRieszCharts
      (JetBase := JetBase) (Tangent := Tangent) (Normal := Normal) Chart) :
    ContDiff ℝ ∞ charts.physicalRiesz := by
  exact geometricRieszShapeFamily_contDiff
    charts.referenceTangentFrame charts.referenceNormalFrame
    charts.form charts.physicalNormal
    charts.form_contDiff charts.physicalNormal_contDiff

/-- Convert the variable-overlap construction into the two final theorem
obligations expected by `StructuredJetRieszData`. -/
theorem variableOverlap_closes_final_obligations
    (charts : VariableOverlapRieszCharts
      (JetBase := JetBase) (Tangent := Tangent) (Normal := Normal) Chart) :
    (∀ chart, charts.localRiesz chart = charts.physicalRiesz) ∧
    (∀ chart, ContDiff ℝ ∞ (charts.localRiesz chart)) := by
  exact ⟨charts.localRiesz_eq_physicalRiesz,
    charts.localRiesz_contDiff⟩

/-- Exact status after discharging the realization and local-smoothness proofs
from variable overlap invariance. -/
structure VariableOverlapInstantiationStatus where
  referenceFramesSupplied : Prop
  smoothTransitionFamiliesSupplied : Prop
  secondFundamentalFormSmooth : Prop
  physicalNormalFieldSmooth : Prop
  realizationIdentityDerived : Prop
  localSmoothnessDerived : Prop
  pointwiseNormalBasisCoverConnected : Prop
  structuredJetDataConstructed : Prop

/-- Closure of the variable-overlap instantiation stage. -/
def variableOverlapInstantiationClosed
    (s : VariableOverlapInstantiationStatus) : Prop :=
  s.referenceFramesSupplied ∧
  s.smoothTransitionFamiliesSupplied ∧
  s.secondFundamentalFormSmooth ∧
  s.physicalNormalFieldSmooth ∧
  s.realizationIdentityDerived ∧
  s.localSmoothnessDerived ∧
  s.pointwiseNormalBasisCoverConnected ∧
  s.structuredJetDataConstructed

/-- After the two analytic obligations are derived, the remaining step is only
connecting the actual pointwise normal-basis cover to these overlap charts. -/
theorem missing_cover_connection_blocks_structured_instantiation
    (s : VariableOverlapInstantiationStatus)
    (hMissing : Not s.pointwiseNormalBasisCoverConnected) :
    Not (variableOverlapInstantiationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorVariableOverlapInstantiation
end JanusFormal
