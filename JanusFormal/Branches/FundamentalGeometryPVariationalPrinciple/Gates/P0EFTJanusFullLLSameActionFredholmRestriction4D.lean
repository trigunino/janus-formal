import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLVariationalAPI4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D

/-!
# Exact same-action Fredholm restriction of the full LL Hessian

The true LL action has the three independent direction slots `llAuxMetric`,
`llMeasure`, and `llField`.  The largest slice supported by the existing
Fredholm realization keeps every smooth `llField` direction and imposes
exactly

`llAuxMetric = 0`, `llMeasure = 0`.

On this slice the full action Hessian is the pairing of the completed LL
Jacobi operator, which is self-adjoint Fredholm of index zero.  The two
omitted slots are not declared inactive: their genuine diagonal and mixed
terms remain in `globalPTFullLLHessianForm`.  No Hilbert completion,
closed-range theorem, or Fredholm operator for those residual terms is
currently available, so this gate does not extend the identity operator to
them.
-/

namespace JanusFormal
namespace P0EFTJanusFullLLSameActionFredholmRestriction4D

set_option autoImplicit false
noncomputable section

open Set
open MeasureTheory
open scoped Manifold ContDiff Topology InnerProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The three smooth LL slots, with the field tagged by the positive Jacobi
energy data used for its completion. -/
structure FullLLSmoothPacket
    (data : PositiveLLH1Data period hPeriod) where
  llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber
  llMeasure : SmoothThroatField period hPeriod Real
  llField : LLH1Smooth period hPeriod data

/-- Faithful inclusion of all three LL slots in the already established full
direction packet, with the non-LL active slots set to zero. -/
def fullLLSmoothPacketDirection
    {data : PositiveLLH1Data period hPeriod}
    (packet : FullLLSmoothPacket period hPeriod data) :
    FullMatterRobinLLDirections period hPeriod :=
  { fullRobinLLDirection period hPeriod 0 packet.llField.toTest with
    llAuxMetric := packet.llAuxMetric
    llMeasure := packet.llMeasure }

/-- The exact field-only slice on which the existing LL Fredholm operator is
defined. -/
def fullLLFieldPacket
    (data : PositiveLLH1Data period hPeriod)
    (field : LLH1Smooth period hPeriod data) :
    FullLLSmoothPacket period hPeriod data where
  llAuxMetric := 0
  llMeasure := 0
  llField := field

/-- Predicate recording only the two restrictions required by the existing
Fredholm realization. -/
def OnLLFredholmSlice
    {data : PositiveLLH1Data period hPeriod}
    (packet : FullLLSmoothPacket period hPeriod data) : Prop :=
  packet.llAuxMetric = 0 ∧ packet.llMeasure = 0

/-- Exact characterization of the supported slice: no restriction is placed
on the smooth LL field direction. -/
theorem onLLFredholmSlice_iff_exists_field
    {data : PositiveLLH1Data period hPeriod}
    (packet : FullLLSmoothPacket period hPeriod data) :
    OnLLFredholmSlice period hPeriod packet ↔
      ∃ field : LLH1Smooth period hPeriod data,
        packet = fullLLFieldPacket period hPeriod data field := by
  constructor
  · rintro ⟨hAux, hMeasure⟩
    refine ⟨packet.llField, ?_⟩
    cases packet with
    | mk llAuxMetric llMeasure llField =>
        dsimp at hAux hMeasure ⊢
        subst llAuxMetric
        subst llMeasure
        rfl
  · rintro ⟨field, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Full-action direction associated with a smooth point of the Fredholm
core. -/
def fullLLFredholmDirection
    (data : PositiveLLH1Data period hPeriod)
    (field : LLH1Smooth period hPeriod data) :
    FullMatterRobinLLDirections period hPeriod :=
  fullRobinLLDirection period hPeriod 0 field.toTest

@[simp]
theorem fullLLSmoothPacketDirection_fieldPacket
    (data : PositiveLLH1Data period hPeriod)
    (field : LLH1Smooth period hPeriod data) :
    fullLLSmoothPacketDirection period hPeriod
        (fullLLFieldPacket period hPeriod data field) =
      fullLLFredholmDirection period hPeriod data field :=
  rfl

/-- On the exact supported slice, the true full three-slot LL Hessian is the
pairing of the completed Jacobi operator. -/
theorem fullLLHessian_fredholmSlice_eq_operator_pairing
    (data : PositiveLLH1Data period hPeriod)
    (first second : LLH1Smooth period hPeriod data) :
    fullLLHessian period hPeriod data.frame data.fields
        (fullLLFredholmDirection period hPeriod data first)
        (fullLLFredholmDirection period hPeriod data second) data.mu =
      inner Real
        (completedLLJacobiOperator period hPeriod data
          (llH1SmoothEmbedding period hPeriod data first))
        (llH1SmoothEmbedding period hPeriod data second) := by
  letI : IsFiniteMeasure data.mu := data.finiteMeasure
  unfold fullLLHessian fullLLFredholmDirection
  rw [fullLLHessian_zeroAuxMeasure_eq_fluxHessian]
  exact
    (completedLLJacobiOperator_smooth_pairing
      period hPeriod data first second).symm

/-- Differentiating the true LL Euler functional along the same exact slice
gives the Fredholm pairing, so the operator is tied to the unchanged action. -/
theorem fullLLEulerAlong_fredholmSlice_hasDerivAt
    (data : PositiveLLH1Data period hPeriod)
    (first second : LLH1Smooth period hPeriod data) :
    HasDerivAt
      (fullLLEulerAlong period hPeriod data.frame data.fields
        (fullLLFredholmDirection period hPeriod data first)
        (fullLLFredholmDirection period hPeriod data second) data.mu)
      (inner Real
        (completedLLJacobiOperator period hPeriod data
          (llH1SmoothEmbedding period hPeriod data first))
        (llH1SmoothEmbedding period hPeriod data second)) 0 := by
  letI : IsFiniteMeasure data.mu := data.finiteMeasure
  rw [← fullLLHessian_fredholmSlice_eq_operator_pairing
    period hPeriod data first second]
  exact fullLLEuler_second_direction_hasDerivAt period hPeriod data.frame
    data.fields (fullLLFredholmDirection period hPeriod data first)
    (fullLLFredholmDirection period hPeriod data second) data.mu

/-- Closed range and finite-dimensional kernel and cokernel on the exact
completed field slice. -/
theorem fullLLFredholmSlice_fredholm_criterion
    (data : PositiveLLH1Data period hPeriod) :
    IsClosed
        (LinearMap.range
          (completedLLJacobiOperator period hPeriod data).toLinearMap :
            Set (LLH1Space period hPeriod data)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (completedLLJacobiOperator period hPeriod data).toLinearMap) ∧
      FiniteDimensional Real
        (CompletedLLJacobiCokernel period hPeriod data) :=
  completedLLJacobiOperator_fredholm_criterion period hPeriod data

/-- Self-adjoint, closed-range, index-zero closure of the same-action
Fredholm slice. -/
theorem fullLLFredholmSlice_closure
    (data : PositiveLLH1Data period hPeriod) :
    IsSelfAdjoint (completedLLJacobiOperator period hPeriod data) ∧
      IsClosed
        (LinearMap.range
          (completedLLJacobiOperator period hPeriod data).toLinearMap :
            Set (LLH1Space period hPeriod data)) ∧
      completedLLJacobiIndex period hPeriod data = 0 :=
  completed_ll_jacobi_fredholm_closure period hPeriod data

end
end P0EFTJanusFullLLSameActionFredholmRestriction4D
end JanusFormal
