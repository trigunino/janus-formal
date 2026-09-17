import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiLowerBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiClosure4D

/-! The smooth LL Jacobi lower bound persists on its closed L² realization. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLStrongJacobiClosedLowerBound4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLStrongJacobiLowerBound4D

/-- A quadratic lower bound on a closable real-Hilbert partial operator
extends unchanged to its graph closure. -/
theorem linearPMap_closure_quadratic_lower_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H]
    (T : H →ₗ.[Real] H) (hClosable : T.IsClosable) (constant : Real)
    (hLower : ∀ x : T.domain,
      -(constant * ‖(x : H)‖ ^ 2) ≤ inner Real (T x) (x : H))
    (x : T.closure.domain) :
    -(constant * ‖(x : H)‖ ^ 2) ≤
      inner Real (T.closure x) (x : H) := by
  let S : Set (H × H) :=
    {pair | -(constant * ‖pair.1‖ ^ 2) ≤ inner Real pair.2 pair.1}
  have hClosed : IsClosed S :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hSubset : (T.graph : Set (H × H)) ⊆ S := by
    intro pair hPair
    obtain ⟨value, hInput, hOutput⟩ := T.mem_graph_iff.mp hPair
    change -(constant * ‖pair.1‖ ^ 2) ≤ inner Real pair.2 pair.1
    rw [← hInput, ← hOutput]
    exact hLower value
  have hGraph : T.graph.topologicalClosure = T.closure.graph :=
    hClosable.graph_closure_eq_closure_graph
  have hPair : (((x : H), T.closure x) : H × H) ∈
      closure (T.graph : Set (H × H)) := by
    rw [← Submodule.topologicalClosure_coe, hGraph]
    exact T.closure.mem_graph x
  exact (closure_minimal hSubset hClosed) hPair

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

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The closed field-only Jacobi operator retains its smooth-core L² bound. -/
theorem llJacobiClosedPMap_l2_lower_bound
    (fields : IndependentFields period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ x : (llJacobiClosedPMap period hPeriod fields).domain,
        -(constant * ‖(x : Lp LLFieldFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ ^ 2) ≤
          inner Real (llJacobiClosedPMap period hPeriod fields x)
            (x : Lp LLFieldFiber (2 : ENNReal)
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
  obtain ⟨constant, hNonnegative, hSmooth⟩ :=
    llStrongJacobi_smooth_l2_lower_bound period hPeriod fields
  let T := llJacobiSmoothPMap period hPeriod fields
  have hCore (x : T.domain) :
      -(constant * ‖(x : Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ ^ 2) ≤
        inner Real (T x)
          (x : Lp LLFieldFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
    obtain ⟨direction, hDirection⟩ := x.property
    let e : LLWeakTestSpace period hPeriod ≃ₗ[Real]
        llJacobiSmoothDomain period hPeriod :=
      LinearEquiv.ofInjective (llSmoothToL2LinearMap period hPeriod)
        (llSmoothToL2LinearMap_injective period hPeriod)
    have hInput : (x : Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        llSmoothToL2 period hPeriod direction := hDirection.symm
    have hApply : T x = llStrongJacobiToL2 period hPeriod fields direction := by
      have hEq : x =
          ⟨llSmoothToL2 period hPeriod direction,
            LinearMap.mem_range_self (llSmoothToL2LinearMap period hPeriod)
              direction⟩ := Subtype.ext hDirection.symm
      rw [hEq]
      change llStrongJacobiLinearMap period hPeriod fields
        (e.symm (e direction)) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hInput, hApply]
    exact hSmooth direction
  refine ⟨constant, hNonnegative, ?_⟩
  intro x
  exact linearPMap_closure_quadratic_lower_bound T
    (llJacobiSmoothPMap_isClosable period hPeriod fields) constant hCore x

end
end P0EFTJanusProgramPT12LLStrongJacobiClosedLowerBound4D
end JanusFormal
