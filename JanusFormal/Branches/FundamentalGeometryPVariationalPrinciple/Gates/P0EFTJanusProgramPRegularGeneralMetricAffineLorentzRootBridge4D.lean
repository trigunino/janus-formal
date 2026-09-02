import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusSmoothGeneralLorentzMetricOfTensor4D

/-!
# Affine Lorentz metric from an intrinsic relative root

An invertible relative endomorphism alone does not determine its inertia.  This
gate instead uses the exact Candidate-A mechanism: a base-metric self-adjoint
root whose square is the affine relative endomorphism.  The root gives an
explicit congruence from `g + h` to `g`, hence preserves Lorentz signature.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricAffineLorentzRootBridge4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusSmoothGeneralLorentzMetricOfTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

/-- Intrinsic root data sufficient to turn the affine nondegenerate tensor into
a tensor explicitly congruent to the base Lorentz metric. -/
structure RegularGeneralMetricAffineRootData
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) where
  root : ∀ point : EffectiveQuotient period hPeriod,
    TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point
  square : ∀ point,
    (root point).comp (root point) =
      regularGeneralMetricAffineRelativeEndomorphismAt
        period hPeriod metric tensor point
  selfAdjoint : ∀ point first second,
    metric.metric.musical point (root point first) second =
      metric.metric.musical point first (root point second)

/-- Nondegeneracy of the affine relative endomorphism forces any exact square
root to be injective. -/
theorem RegularGeneralMetricAffineRootData.root_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod) :
    Function.Injective (data.root point) := by
  intro first second hEqual
  apply regularGeneralMetricAffineRelativeEndomorphismAt_injective
    period hPeriod metric tensor hDomain point
  have hFirst := DFunLike.congr_fun (data.square point) first
  have hSecond := DFunLike.congr_fun (data.square point) second
  change data.root point (data.root point first) =
    regularGeneralMetricAffineRelativeEndomorphismAt
      period hPeriod metric tensor point first at hFirst
  change data.root point (data.root point second) =
    regularGeneralMetricAffineRelativeEndomorphismAt
      period hPeriod metric tensor point second at hSecond
  rw [← hFirst, ← hSecond, hEqual]

/-- Root transported to the regular four-frame. -/
def regularGeneralMetricAffineRootCoordinateAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (point : EffectiveQuotient period hPeriod) :
    (Fin 4 → Real) →L[Real] (Fin 4 → Real) :=
  (metric.frameEquiv point).symm.toContinuousLinearMap.comp
    ((data.root point).comp
      (metric.frameEquiv point).toContinuousLinearMap)

theorem regularGeneralMetricAffineRootCoordinateAt_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod) :
    Function.Injective
      (regularGeneralMetricAffineRootCoordinateAt
        period hPeriod metric tensor data point) := by
  intro first second hEqual
  apply (metric.frameEquiv point).injective
  apply RegularGeneralMetricAffineRootData.root_injective
    period hPeriod metric tensor data hDomain point
  apply (metric.frameEquiv point).symm.injective
  simpa [regularGeneralMetricAffineRootCoordinateAt] using hEqual

/-- The exact root as a pointwise continuous linear equivalence. -/
def regularGeneralMetricAffineRootEquivAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      TangentFiber period hPeriod point :=
  (metric.frameEquiv point).symm.trans
    ((LinearEquiv.ofInjectiveEndo
      (regularGeneralMetricAffineRootCoordinateAt
        period hPeriod metric tensor data point).toLinearMap
      (regularGeneralMetricAffineRootCoordinateAt_injective
        period hPeriod metric tensor data hDomain point)).toContinuousLinearEquiv.trans
          (metric.frameEquiv point))

@[simp]
theorem regularGeneralMetricAffineRootEquivAt_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    regularGeneralMetricAffineRootEquivAt
        period hPeriod metric tensor data hDomain point vector =
      data.root point vector := by
  simp [regularGeneralMetricAffineRootEquivAt,
    regularGeneralMetricAffineRootCoordinateAt]

/-- Exact affine congruence supplied by the self-adjoint square root. -/
theorem regularGeneralMetricAffineRootData_congruence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    (metric.metric.tensor + tensor).tensor point first second =
      metric.metric.tensor.tensor point
        (regularGeneralMetricAffineRootEquivAt
          period hPeriod metric tensor data hDomain point first)
        (regularGeneralMetricAffineRootEquivAt
          period hPeriod metric tensor data hDomain point second) := by
  have hPacket :=
    (regularGeneralMetricAffineNondegenerateMetric
      period hPeriod metric tensor hDomain).musical_eq_tensor point
  have hPacketFirst := DFunLike.congr_fun hPacket first
  have hPacketSecond := DFunLike.congr_fun hPacketFirst second
  have hSquare := DFunLike.congr_fun (data.square point) first
  change data.root point (data.root point first) =
    regularGeneralMetricAffineRelativeEndomorphismAt
      period hPeriod metric tensor point first at hSquare
  calc
    (metric.metric.tensor + tensor).tensor point first second =
        regularGeneralMetricAffineMusical
          period hPeriod metric tensor hDomain point first second := by
      exact hPacketSecond.symm
    _ = metric.metric.musical point
        (regularGeneralMetricAffineRelativeEndomorphismAt
          period hPeriod metric tensor point first) second := by
      rw [regularGeneralMetricAffineMusical_apply]
    _ = metric.metric.musical point
        (data.root point (data.root point first)) second := by rw [hSquare]
    _ = metric.metric.musical point
        (data.root point first) (data.root point second) :=
      data.selfAdjoint point (data.root point first) second
    _ = metric.metric.tensor.tensor point
        (regularGeneralMetricAffineRootEquivAt
          period hPeriod metric tensor data hDomain point first)
        (regularGeneralMetricAffineRootEquivAt
          period hPeriod metric tensor data hDomain point second) := by
      rw [regularGeneralMetricAffineRootEquivAt_apply,
        regularGeneralMetricAffineRootEquivAt_apply]
      have hMetric := DFunLike.congr_fun
        (metric.metric.musical_eq_tensor point) (data.root point first)
      exact DFunLike.congr_fun hMetric (data.root point second)

/-- The affine tensor is Lorentzian because it is explicitly congruent to the
base Lorentz metric. -/
theorem regularGeneralMetricAffineRootData_lorentzian
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    IsEverywhereLorentzian period hPeriod
      (metric.metric.tensor + tensor) := by
  intro point
  rcases metric.metric.lorentzian point with ⟨frame, hFrame⟩
  refine ⟨(regularGeneralMetricAffineRootEquivAt
    period hPeriod metric tensor data hDomain point).trans frame, ?_⟩
  intro first second
  rw [regularGeneralMetricAffineRootData_congruence
    period hPeriod metric tensor data hDomain point first second]
  rw [hFrame]
  rfl

/-- Genuine affine Lorentz metric obtained from the exact root data. -/
def regularGeneralMetricAffineLorentzMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    SmoothGeneralLorentzMetric period hPeriod :=
  smoothGeneralLorentzMetricOfTensor period hPeriod
    (metric.metric.tensor + tensor)
    (regularGeneralMetricAffineRootData_lorentzian
      period hPeriod metric tensor data hDomain)

@[simp]
theorem regularGeneralMetricAffineLorentzMetric_tensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    (regularGeneralMetricAffineLorentzMetric
      period hPeriod metric tensor data hDomain).tensor =
        metric.metric.tensor + tensor :=
  rfl

/-- Gate marker: exact self-adjoint root data turns the affine nondegenerate
tensor into a genuine Lorentz metric with no inertia axiom. -/
theorem regular_general_metric_affine_lorentz_root_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (data : RegularGeneralMetricAffineRootData
      period hPeriod metric tensor)
    (hDomain : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (RegularFrame period hPeriod metric) metric.metric) :
    ∃ varied : SmoothGeneralLorentzMetric period hPeriod,
      varied.tensor = metric.metric.tensor + tensor :=
  ⟨regularGeneralMetricAffineLorentzMetric
    period hPeriod metric tensor data hDomain, rfl⟩

end

end P0EFTJanusProgramPRegularGeneralMetricAffineLorentzRootBridge4D
end JanusFormal
