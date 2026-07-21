import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D

/-!
# Smooth inverse musical map on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothInverseMusical4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped Manifold ContDiff Topology
open Bundle ContinuousLinearMap Filter
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackSmooth4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance cutBulkIsManifold :
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobal_isManifold period hPeriod

private abbrev CutBulkCotangentFiber
    (point : PositiveHemisphereCutBulk period hPeriod) :=
  CutBulkTangentFiber period hPeriod point →L[Real] Real

private abbrev ModelTangent := CutCollarCoordinates
private abbrev ModelCotangent := ModelTangent →L[Real] Real

/-- Genuine smooth tangent-vector fields on the cut bulk. -/
abbrev CutBulkSmoothVectorField :=
  ContMDiffSection cutCollarModelWithCorners ModelTangent ∞
    (CutBulkTangentFiber period hPeriod)

/-- Genuine smooth covector fields on the cut bulk. -/
abbrev CutBulkSmoothCovectorField :=
  ContMDiffSection cutCollarModelWithCorners ModelCotangent ∞
    (CutBulkCotangentFiber period hPeriod)

local instance cutBulkTangentFiniteDimensional
    (point : PositiveHemisphereCutBulk period hPeriod) :
    FiniteDimensional Real (CutBulkTangentFiber period hPeriod point) := by
  change FiniteDimensional Real CutCollarCoordinates
  infer_instance

/-- Pointwise raising of a cut-bulk covector. -/
def cutBulkInverseMetricSharp
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (covector : CutBulkCotangentFiber period hPeriod point) :
    CutBulkTangentFiber period hPeriod point :=
  (metric.musical point).symm covector

private def metricCoordinates
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (anchor current : PositiveHemisphereCutBulk period hPeriod) :
    ModelTangent →L[Real] ModelCotangent :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (CutBulkTangentFiber period hPeriod) ModelCotangent
    (CutBulkCotangentFiber period hPeriod)
    anchor current anchor current (metric.tensor.tensor current)

private def covectorCoordinates
    (covector : CutBulkSmoothCovectorField period hPeriod)
    (anchor current : PositiveHemisphereCutBulk period hPeriod) :
    ModelCotangent :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (CutBulkTangentFiber period hPeriod) Real
    (fun _ : PositiveHemisphereCutBulk period hPeriod => Real)
    anchor current anchor current (covector current)

private theorem metricCoordinates_contMDiffAt
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (anchor : PositiveHemisphereCutBulk period hPeriod) :
    ContMDiffAt cutCollarModelWithCorners
      𝓘(Real, ModelTangent →L[Real] ModelCotangent) ∞
      (metricCoordinates period hPeriod metric anchor) anchor := by
  have hMetric := metric.tensor.tensor.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hMetric
  exact hMetric.2

private theorem covectorCoordinates_contMDiffAt
    (covector : CutBulkSmoothCovectorField period hPeriod)
    (anchor : PositiveHemisphereCutBulk period hPeriod) :
    ContMDiffAt cutCollarModelWithCorners 𝓘(Real, ModelCotangent) ∞
      (covectorCoordinates period hPeriod covector anchor) anchor := by
  have hCovector := covector.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hCovector
  exact hCovector.2

private theorem metricCoordinates_isInvertible
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (anchor : PositiveHemisphereCutBulk period hPeriod) :
    (metricCoordinates period hPeriod metric anchor anchor).IsInvertible := by
  have hTangent : anchor ∈
      (trivializationAt ModelTangent
        (CutBulkTangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelTangent
      (CutBulkTangentFiber period hPeriod) anchor
  have hCotangent : anchor ∈
      (trivializationAt ModelCotangent
        (CutBulkCotangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelCotangent
      (CutBulkCotangentFiber period hPeriod) anchor
  unfold metricCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ← metric.musical_eq_tensor anchor]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

private theorem inverseMetricCoordinates_apply_eq
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (covector : CutBulkSmoothCovectorField period hPeriod)
    (anchor current : PositiveHemisphereCutBulk period hPeriod)
    (hTangent : current ∈
      (trivializationAt ModelTangent
        (CutBulkTangentFiber period hPeriod) anchor).baseSet)
    (hCotangent : current ∈
      (trivializationAt ModelCotangent
        (CutBulkCotangentFiber period hPeriod) anchor).baseSet) :
    (metricCoordinates period hPeriod metric anchor current).inverse
        (covectorCoordinates period hPeriod covector anchor current) =
      ((trivializationAt ModelTangent
        (CutBulkTangentFiber period hPeriod) anchor)
        ⟨current, cutBulkInverseMetricSharp period hPeriod metric current
          (covector current)⟩).2 := by
  have hCovectorCoordinates :
      covectorCoordinates period hPeriod covector anchor current =
        (trivializationAt ModelCotangent
          (CutBulkCotangentFiber period hPeriod) anchor
          |>.continuousLinearEquivAt Real current hCotangent)
            (covector current) := by
    rfl
  have hVectorCoordinates :
      ((trivializationAt ModelTangent
        (CutBulkTangentFiber period hPeriod) anchor)
        ⟨current, cutBulkInverseMetricSharp period hPeriod metric current
          (covector current)⟩).2 =
        (trivializationAt ModelTangent
          (CutBulkTangentFiber period hPeriod) anchor
          |>.continuousLinearEquivAt Real current hTangent)
            (cutBulkInverseMetricSharp period hPeriod metric current
              (covector current)) := by
    rfl
  unfold metricCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ← metric.musical_eq_tensor current, hCovectorCoordinates,
    hVectorCoordinates]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.inverse_equiv,
    cutBulkInverseMetricSharp, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_symm]

/-- Raising a smooth cut-bulk one-form gives a smooth tangent-vector field. -/
def cutBulkSmoothInverseMusical
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (covector : CutBulkSmoothCovectorField period hPeriod) :
    CutBulkSmoothVectorField period hPeriod where
  toFun := fun point => cutBulkInverseMetricSharp period hPeriod metric point
    (covector point)
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_section]
    have hMetric := metricCoordinates_contMDiffAt period hPeriod metric anchor
    have hInverse :=
      (metricCoordinates_isInvertible period hPeriod metric anchor
        |>.contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt hMetric
    have hCovector := covectorCoordinates_contMDiffAt period hPeriod
      covector anchor
    have hFormula := hInverse.clm_apply hCovector
    apply hFormula.congr_of_eventuallyEq
    have hTangent : ∀ᶠ current in 𝓝 anchor, current ∈
        (trivializationAt ModelTangent
          (CutBulkTangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelTangent
        (CutBulkTangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelTangent
            (CutBulkTangentFiber period hPeriod) anchor)
    have hCotangent : ∀ᶠ current in 𝓝 anchor, current ∈
        (trivializationAt ModelCotangent
          (CutBulkCotangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelCotangent
        (CutBulkCotangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelCotangent
            (CutBulkCotangentFiber period hPeriod) anchor)
    filter_upwards [hTangent, hCotangent] with current hTangent' hCotangent'
    exact (inverseMetricCoordinates_apply_eq period hPeriod metric covector
      anchor current hTangent' hCotangent').symm

@[simp]
theorem cutBulkSmoothInverseMusical_apply
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (covector : CutBulkSmoothCovectorField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    cutBulkSmoothInverseMusical period hPeriod metric covector point =
      cutBulkInverseMetricSharp period hPeriod metric point (covector point) :=
  rfl

theorem cutBulkSmoothInverseMusical_flat
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (covector : CutBulkSmoothCovectorField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    metric.musical point
        (cutBulkSmoothInverseMusical period hPeriod metric covector point) =
      covector point :=
  (metric.musical point).apply_symm_apply (covector point)

end
end P0EFTJanusMappingTorusCutBulkSmoothInverseMusical4D
end JanusFormal
