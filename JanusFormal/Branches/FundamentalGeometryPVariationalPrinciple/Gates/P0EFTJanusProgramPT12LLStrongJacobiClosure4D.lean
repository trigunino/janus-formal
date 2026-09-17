import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLSmoothL2Density4D

/-!
# Closure of the smooth LL Jacobi operator

The same-action smooth LL Jacobi residual is a densely defined symmetric
operator on the canonical LL L² space. Its graph therefore has a canonical
closed operator extension. No Fredholm or self-adjoint claim is made here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLStrongJacobiClosure4D

set_option autoImplicit false
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
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D

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

private abbrev LLFieldL2 :=
  Lp LLFieldFiber (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

private theorem llSmoothToL2_ae
    (field : LLWeakTestSpace period hPeriod) :
    (llSmoothToL2 period hPeriod field :
      EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod] field.toFun :=
  (smoothThroatField_memLp period hPeriod LLFieldFiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) field).coeFn_toLp

private theorem llSmoothToL2_add
    (first second : LLWeakTestSpace period hPeriod) :
    llSmoothToL2 period hPeriod (first + second) =
      llSmoothToL2 period hPeriod first + llSmoothToL2 period hPeriod second := by
  apply Lp.ext
  filter_upwards
    [llSmoothToL2_ae period hPeriod (first + second),
      llSmoothToL2_ae period hPeriod first,
      llSmoothToL2_ae period hPeriod second,
      Lp.coeFn_add (llSmoothToL2 period hPeriod first)
        (llSmoothToL2 period hPeriod second)]
    with point hSum hFirst hSecond hAdd
  simp only [Pi.add_apply] at hAdd
  rw [hSum, hAdd, hFirst, hSecond]
  rfl

private theorem llSmoothToL2_smul
    (scalar : Real) (field : LLWeakTestSpace period hPeriod) :
    llSmoothToL2 period hPeriod (scalar • field) =
      scalar • llSmoothToL2 period hPeriod field := by
  apply Lp.ext
  filter_upwards
    [llSmoothToL2_ae period hPeriod (scalar • field),
      llSmoothToL2_ae period hPeriod field,
      Lp.coeFn_smul scalar (llSmoothToL2 period hPeriod field)]
    with point hScaled hField hSmul
  simp only [Pi.smul_apply] at hSmul
  rw [hScaled, hSmul, hField]
  rfl

/-- Linear inclusion of smooth LL tests into their actual L² classes. -/
def llSmoothToL2LinearMap :
    LLWeakTestSpace period hPeriod →ₗ[Real] LLFieldL2 period hPeriod where
  toFun := llSmoothToL2 period hPeriod
  map_add' := llSmoothToL2_add period hPeriod
  map_smul' := llSmoothToL2_smul period hPeriod

/-- Open positivity makes the L² class faithful on smooth LL fields. -/
theorem llSmoothToL2LinearMap_injective :
    Function.Injective (llSmoothToL2LinearMap period hPeriod) := by
  intro first second hEqual
  letI : (intrinsicCanonicalThroatVolumeMeasure period hPeriod).IsOpenPosMeasure :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  have hSame :
      (llSmoothToL2 period hPeriod first :
        EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      (llSmoothToL2 period hPeriod second :
        EffectiveThroat period hPeriod → LLFieldFiber) := by
    rw [show llSmoothToL2 period hPeriod first =
      llSmoothToL2 period hPeriod second from hEqual]
  have hAE : first.toFun =ᵐ[
      intrinsicCanonicalThroatVolumeMeasure period hPeriod] second.toFun :=
    (llSmoothToL2_ae period hPeriod first).symm.trans
      (hSame.trans (llSmoothToL2_ae period hPeriod second))
  apply SmoothThroatField.ext
  intro point
  exact congrFun (Measure.eq_of_ae_eq hAE
    first.contMDiff_toFun.continuous second.contMDiff_toFun.continuous) point

/-- The dense smooth L² domain of the Jacobi operator. -/
def llJacobiSmoothDomain : Submodule Real (LLFieldL2 period hPeriod) :=
  LinearMap.range (llSmoothToL2LinearMap period hPeriod)

private def llSmoothEquivDomain :
    LLWeakTestSpace period hPeriod ≃ₗ[Real]
      llJacobiSmoothDomain period hPeriod :=
  LinearEquiv.ofInjective (llSmoothToL2LinearMap period hPeriod)
    (llSmoothToL2LinearMap_injective period hPeriod)

/-- The same-action Jacobi residual as a partial L² operator. -/
def llJacobiSmoothPMap
    (fields : IndependentFields period hPeriod) :
    LLFieldL2 period hPeriod →ₗ.[Real] LLFieldL2 period hPeriod where
  domain := llJacobiSmoothDomain period hPeriod
  toFun := (llStrongJacobiLinearMap period hPeriod fields).comp
    (llSmoothEquivDomain period hPeriod).symm.toLinearMap

theorem llJacobiSmoothPMap_denseDomain
    (fields : IndependentFields period hPeriod) :
    Dense ((llJacobiSmoothPMap period hPeriod fields).domain :
      Set (LLFieldL2 period hPeriod)) := by
  change Dense (llJacobiSmoothDomain period hPeriod : Set (LLFieldL2 period hPeriod))
  rw [dense_iff_closure_eq]
  change closure (Set.range (llSmoothToL2 period hPeriod)) = Set.univ
  exact (llSmoothToL2_denseRange period hPeriod).closure_range

private theorem llJacobiSmooth_pairing_symmetric
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod) :
    inner Real (llStrongJacobiToL2 period hPeriod fields first)
        (llSmoothToL2 period hPeriod second) =
      inner Real (llSmoothToL2 period hPeriod first)
        (llStrongJacobiToL2 period hPeriod fields second) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  calc
    inner Real (llStrongJacobiToL2 period hPeriod fields first)
        (llSmoothToL2 period hPeriod second) =
        ∫ point, inner Real
          (llStrongJacobiToL2 period hPeriod fields first point)
          (llSmoothToL2 period hPeriod second point) ∂mu :=
      L2.inner_def _ _
    _ = ∫ point, inner Real
          (llStrongJacobiToL2 period hPeriod fields first point)
          (second point) ∂mu := by
      apply integral_congr_ae
      filter_upwards [llSmoothToL2_ae period hPeriod second] with point hPoint
      rw [hPoint]
    _ = weakLLJacobiOperator period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields mu first second :=
      (weakLLJacobiOperator_eq_llStrongJacobiToL2_pairing
        period hPeriod fields first second).symm
    _ = weakLLJacobiOperator period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields mu second first :=
      weakLLJacobiOperator_symmetric period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields first second mu
    _ = ∫ point, inner Real
          (llStrongJacobiToL2 period hPeriod fields second point)
          (first point) ∂mu :=
      weakLLJacobiOperator_eq_llStrongJacobiToL2_pairing
        period hPeriod fields second first
    _ = ∫ point, inner Real
          (llSmoothToL2 period hPeriod first point)
          (llStrongJacobiToL2 period hPeriod fields second point) ∂mu := by
      apply integral_congr_ae
      filter_upwards [llSmoothToL2_ae period hPeriod first] with point hPoint
      rw [hPoint]
      exact real_inner_comm _ _
    _ = inner Real (llSmoothToL2 period hPeriod first)
          (llStrongJacobiToL2 period hPeriod fields second) :=
      (L2.inner_def _ _).symm

/-- Symmetry of the actual same-action smooth-core Jacobi operator. -/
theorem llJacobiSmoothPMap_symmetric
    (fields : IndependentFields period hPeriod) :
    (llJacobiSmoothPMap period hPeriod fields).IsFormalAdjoint
      (llJacobiSmoothPMap period hPeriod fields) := by
  intro first second
  let firstSmooth := (llSmoothEquivDomain period hPeriod).symm first
  let secondSmooth := (llSmoothEquivDomain period hPeriod).symm second
  have hFirst : (first : LLFieldL2 period hPeriod) =
      llSmoothToL2 period hPeriod firstSmooth := by
    exact (congrArg Subtype.val
      ((llSmoothEquivDomain period hPeriod).apply_symm_apply first)).symm
  have hSecond : (second : LLFieldL2 period hPeriod) =
      llSmoothToL2 period hPeriod secondSmooth := by
    exact (congrArg Subtype.val
      ((llSmoothEquivDomain period hPeriod).apply_symm_apply second)).symm
  change inner Real (llStrongJacobiToL2 period hPeriod fields firstSmooth)
      (second : LLFieldL2 period hPeriod) =
    inner Real (first : LLFieldL2 period hPeriod)
      (llStrongJacobiToL2 period hPeriod fields secondSmooth)
  rw [hFirst, hSecond]
  exact llJacobiSmooth_pairing_symmetric period hPeriod fields firstSmooth secondSmooth

/-- A densely defined symmetric LL Jacobi operator has a graph closure. -/
theorem llJacobiSmoothPMap_isClosable
    (fields : IndependentFields period hPeriod) :
    (llJacobiSmoothPMap period hPeriod fields).IsClosable := by
  have hDense := llJacobiSmoothPMap_denseDomain period hPeriod fields
  have hSymmetric := llJacobiSmoothPMap_symmetric period hPeriod fields
  exact (LinearPMap.adjoint_isClosed hDense).isClosable.leIsClosable
    (hSymmetric.le_adjoint hDense)

/-- The canonical closed realization generated by the same-action smooth core. -/
def llJacobiClosedPMap
    (fields : IndependentFields period hPeriod) :
    LLFieldL2 period hPeriod →ₗ.[Real] LLFieldL2 period hPeriod :=
  (llJacobiSmoothPMap period hPeriod fields).closure

theorem llJacobiClosedPMap_isClosed
    (fields : IndependentFields period hPeriod) :
    (llJacobiClosedPMap period hPeriod fields).IsClosed :=
  (llJacobiSmoothPMap_isClosable period hPeriod fields).closure_isClosed

theorem llJacobiSmoothPMap_le_closed
    (fields : IndependentFields period hPeriod) :
    llJacobiSmoothPMap period hPeriod fields ≤
      llJacobiClosedPMap period hPeriod fields :=
  (llJacobiSmoothPMap period hPeriod fields).le_closure

/-- Closing the graph preserves the LL Jacobi symmetry identity. -/
theorem llJacobiClosedPMap_symmetric
    (fields : IndependentFields period hPeriod) :
    (llJacobiClosedPMap period hPeriod fields).IsFormalAdjoint
      (llJacobiClosedPMap period hPeriod fields) := by
  let T := llJacobiSmoothPMap period hPeriod fields
  let C := llJacobiClosedPMap period hPeriod fields
  have hGraph : T.graph.topologicalClosure = C.graph :=
    (llJacobiSmoothPMap_isClosable period hPeriod fields).graph_closure_eq_closure_graph
  have hSym : T.IsFormalAdjoint T :=
    llJacobiSmoothPMap_symmetric period hPeriod fields
  have hFirst (x : C.domain) (y : T.domain) :
      inner Real (C x) (y : LLFieldL2 period hPeriod) =
        inner Real (x : LLFieldL2 period hPeriod) (T y) := by
    have hSubset : (T.graph : Set ((LLFieldL2 period hPeriod) ×
        LLFieldL2 period hPeriod)) ⊆
        {p | inner Real p.2 (y : LLFieldL2 period hPeriod) =
          inner Real p.1 (T y)} := by
      intro p hp
      obtain ⟨z, hz₁, hz₂⟩ := T.mem_graph_iff.mp hp
      change inner Real p.2 (y : LLFieldL2 period hPeriod) =
        inner Real p.1 (T y)
      rw [← hz₁, ← hz₂]
      exact hSym z y
    have hClosed : IsClosed
        {p : (LLFieldL2 period hPeriod) × LLFieldL2 period hPeriod |
          inner Real p.2 (y : LLFieldL2 period hPeriod) =
            inner Real p.1 (T y)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hx : ((x : LLFieldL2 period hPeriod), C x) ∈
        closure (T.graph : Set ((LLFieldL2 period hPeriod) ×
          LLFieldL2 period hPeriod)) := by
      rw [← Submodule.topologicalClosure_coe, hGraph]
      exact C.mem_graph x
    exact (closure_minimal hSubset hClosed) hx
  intro x y
  have hSubset : (T.graph : Set ((LLFieldL2 period hPeriod) ×
      LLFieldL2 period hPeriod)) ⊆
      {p | inner Real (C x) p.1 =
        inner Real (x : LLFieldL2 period hPeriod) p.2} := by
    intro p hp
    obtain ⟨z, hz₁, hz₂⟩ := T.mem_graph_iff.mp hp
    change inner Real (C x) p.1 =
      inner Real (x : LLFieldL2 period hPeriod) p.2
    rw [← hz₁, ← hz₂]
    exact hFirst x z
  have hClosed : IsClosed
      {p : (LLFieldL2 period hPeriod) × LLFieldL2 period hPeriod |
        inner Real (C x) p.1 =
          inner Real (x : LLFieldL2 period hPeriod) p.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hy : ((y : LLFieldL2 period hPeriod), C y) ∈
      closure (T.graph : Set ((LLFieldL2 period hPeriod) ×
        LLFieldL2 period hPeriod)) := by
    rw [← Submodule.topologicalClosure_coe, hGraph]
    exact C.mem_graph y
  exact (closure_minimal hSubset hClosed) hy

end
end P0EFTJanusProgramPT12LLStrongJacobiClosure4D
end JanusFormal
