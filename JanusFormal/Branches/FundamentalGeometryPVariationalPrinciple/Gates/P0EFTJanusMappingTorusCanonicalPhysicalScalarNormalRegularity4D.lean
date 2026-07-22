import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSquaredGraphEstimates4D

/-!
# Higher regularity and the physical scalar normal trace

A normal derivative trace is naturally bounded on a space with one more degree
of regularity than the value trace.  This file isolates that standard
factorization.

A smooth regularity realization is controlled by the Euler graph norm, and a
bounded normal-trace map acts on the regularity space.  Their composition gives
the first-sheet normal graph estimate.  The regularity realization extends to
the completed maximal graph, and its normal trace agrees there with the normal
component of the completed Cauchy trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSquaredGraphEstimates4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe z

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type z}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- Higher-regularity realization with bounded normal trace. -/
structure NormalRegularityData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  smoothRegularity : SmoothQuotientField period hPeriod Real →ₗ[Real] Regularity
  normalTrace : Regularity →L[Real] BoundaryL2 period
  normal_agrees : ∀ field : SmoothQuotientField period hPeriod Real,
    normalTrace (smoothRegularity field) =
      smoothCanonicalPhysicalScalarFirstSheetNormalL2
        period hPeriod field
  constant : Real
  nonnegative : 0 ≤ constant
  regularity_bound_sq : ∀ field : SmoothQuotientField period hPeriod Real,
    ‖smoothRegularity field‖ ^ 2 ≤
      constant ^ 2 *
        ‖canonicalScalarGreenCoreToGraph green.core field‖ ^ 2

namespace NormalRegularityData

/-- Linear higher-regularity graph estimate. -/
theorem regularity_norm_le_graph
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity))
    (field : SmoothQuotientField period hPeriod Real) :
    ‖regularity.smoothRegularity field‖ ≤
      regularity.constant *
        ‖canonicalScalarGreenCoreToGraph green.core field‖ := by
  have hSquare := regularity.regularity_bound_sq field
  have hLeft := norm_nonneg (regularity.smoothRegularity field)
  have hRight :
      0 ≤ regularity.constant *
        ‖canonicalScalarGreenCoreToGraph green.core field‖ :=
    mul_nonneg regularity.nonnegative (norm_nonneg _)
  nlinarith

/-- Combined normal-trace graph constant. -/
def normalGraphConstant
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity)) : Real :=
  ‖regularity.normalTrace‖ * regularity.constant

/-- The combined constant is nonnegative. -/
theorem normalGraphConstant_nonnegative
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity)) :
    0 ≤ regularity.normalGraphConstant green :=
  mul_nonneg (norm_nonneg _) regularity.nonnegative

/-- Higher regularity gives the linear normal graph estimate. -/
def toNormalGraphEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity)) :
    green.NormalGraphEstimate period hPeriod where
  constant := regularity.normalGraphConstant green
  nonnegative := regularity.normalGraphConstant_nonnegative green
  bound := by
    intro field
    rw [← regularity.normal_agrees field]
    calc
      ‖regularity.normalTrace (regularity.smoothRegularity field)‖ ≤
          ‖regularity.normalTrace‖ *
            ‖regularity.smoothRegularity field‖ :=
        regularity.normalTrace.le_opNorm _
      _ ≤ ‖regularity.normalTrace‖ *
          (regularity.constant *
            ‖canonicalScalarGreenCoreToGraph green.core field‖) :=
        mul_le_mul_of_nonneg_left
          (regularity.regularity_norm_le_graph green field) (norm_nonneg _)
      _ = regularity.normalGraphConstant green *
          ‖canonicalScalarGreenCoreToGraph green.core field‖ := by
        unfold normalGraphConstant
        ring

/-- Higher regularity also gives the squared normal graph estimate. -/
def toSquaredNormalGraphEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity)) :
    green.SquaredNormalGraphEstimate period hPeriod where
  constant := regularity.normalGraphConstant green
  nonnegative := regularity.normalGraphConstant_nonnegative green
  bound_sq := by
    intro field
    have hLinear := (regularity.toNormalGraphEstimate green).bound field
    have hLeft := norm_nonneg
      (smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field)
    have hRight :
        0 ≤ regularity.normalGraphConstant green *
          ‖canonicalScalarGreenCoreToGraph green.core field‖ :=
      mul_nonneg (regularity.normalGraphConstant_nonnegative green) (norm_nonneg _)
    have hSquare :
        ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2
            period hPeriod field‖ ^ 2 ≤
          (regularity.normalGraphConstant green *
            ‖canonicalScalarGreenCoreToGraph green.core field‖) ^ 2 := by
      nlinarith
    simpa [mul_pow] using hSquare

/-- Continuous higher-regularity extension to the completed maximal graph. -/
def completedRegularity
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity)) :
    CanonicalScalarGreenCoreGraphSpace green.core →L[Real] Regularity :=
  regularity.smoothRegularity.extendOfNorm
    (canonicalScalarGreenCoreToGraph green.core)

/-- Agreement of completed higher regularity on smooth core vectors. -/
theorem completedRegularity_smooth
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity))
    (field : SmoothQuotientField period hPeriod Real) :
    regularity.completedRegularity green
        (canonicalScalarGreenCoreToGraph green.core field) =
      regularity.smoothRegularity field :=
  LinearMap.extendOfNorm_eq
    (canonicalScalarGreenCoreToGraph_denseRange green.core)
    ⟨regularity.constant, regularity.regularity_norm_le_graph green⟩ field

/-- Norm estimate for completed higher regularity. -/
theorem completedRegularity_norm_le
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity))
    (field : CanonicalScalarGreenCoreGraphSpace green.core) :
    ‖regularity.completedRegularity green field‖ ≤
      regularity.constant * ‖field‖ :=
  LinearMap.norm_extendOfNorm_apply_le
    (canonicalScalarGreenCoreToGraph_denseRange green.core)
    regularity.constant (regularity.regularity_norm_le_graph green) field

/-- Normal component of a completed Cauchy trace. -/
def completedBoundaryNormalTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound
      green.core) :
    CanonicalScalarGreenCoreGraphSpace green.core →L[Real] BoundaryL2 period :=
  (ContinuousLinearMap.snd Real (BoundaryL2 period) (BoundaryL2 period)).comp
    (canonicalScalarGreenCoreCompletedBoundaryTrace green.core traceBound)

/-- The regularity normal trace agrees with the normal component of the completed
Cauchy trace. -/
theorem normalTrace_completedRegularity_eq_completedBoundaryNormalTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity))
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound
      green.core)
    (field : CanonicalScalarGreenCoreGraphSpace green.core) :
    regularity.normalTrace (regularity.completedRegularity green field) =
      regularity.completedBoundaryNormalTrace green traceBound field := by
  let good : Set (CanonicalScalarGreenCoreGraphSpace green.core) :=
    {candidate |
      regularity.normalTrace
          (regularity.completedRegularity green candidate) =
        regularity.completedBoundaryNormalTrace green traceBound candidate}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range
      (canonicalScalarGreenCoreToGraph green.core) ⊆ good := by
    rintro candidate ⟨smoothField, rfl⟩
    rw [regularity.completedRegularity_smooth,
      regularity.normal_agrees]
    unfold completedBoundaryNormalTrace
    rw [canonicalScalarGreenCoreCompletedBoundaryTrace_smooth]
    rfl
  have hClosure : closure (Set.range
      (canonicalScalarGreenCoreToGraph green.core)) = Set.univ :=
    (canonicalScalarGreenCoreToGraph_denseRange green.core).closure_range
  have hField : field ∈ closure (Set.range
      (canonicalScalarGreenCoreToGraph green.core)) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hRange hGoodClosed) hField

/-- Normal-regularity certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (regularity : green.NormalRegularityData
      period hPeriod (Regularity := Regularity)) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2
          period hPeriod field‖ ≤
        regularity.normalGraphConstant green *
          ‖canonicalScalarGreenCoreToGraph green.core field‖) ∧
      (∀ field : CanonicalScalarGreenCoreGraphSpace green.core,
        ‖regularity.completedRegularity green field‖ ≤
          regularity.constant * ‖field‖) :=
  ⟨(regularity.toNormalGraphEstimate green).bound,
    regularity.completedRegularity_norm_le green⟩

end NormalRegularityData

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
end JanusFormal
