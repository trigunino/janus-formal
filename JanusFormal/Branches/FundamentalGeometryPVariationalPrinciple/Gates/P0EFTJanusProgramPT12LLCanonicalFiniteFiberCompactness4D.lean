import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Finite-fiber reduction of canonical LL Rellich compactness -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalFiniteFiberCompactness4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal BigOperators
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

/-- Scalar `L²` over the same measure as the four-component LL flux. -/
abbrev LLScalarL2 (data : PositiveLLH1Data period hPeriod) :=
  Lp Real (2 : ENNReal) data.mu

private def llFieldCoordinate (coordinate : Fin 4) :
    LLFieldFiber →L[Real] Real :=
  PiLp.proj (2 : ENNReal) (fun _ : Fin 4 => Real) coordinate

private def llFieldCoordinateSingle (coordinate : Fin 4) :
    Real →L[Real] LLFieldFiber :=
  (PiLp.continuousLinearEquiv (2 : ENNReal) Real
      (fun _ : Fin 4 => Real)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single Real (fun _ : Fin 4 => Real) coordinate)

/-- Pointwise projection of an LL `L²` field onto one of its four real coordinates. -/
def llFluxL2Coordinate
    (data : PositiveLLH1Data period hPeriod) (coordinate : Fin 4) :
    LLFluxL2 period hPeriod data →L[Real] LLScalarL2 period hPeriod data :=
  (llFieldCoordinate coordinate).compLpL (2 : ENNReal) data.mu

private def llFluxL2CoordinateSingle
    (data : PositiveLLH1Data period hPeriod) (coordinate : Fin 4) :
    LLScalarL2 period hPeriod data →L[Real] LLFluxL2 period hPeriod data :=
  (llFieldCoordinateSingle coordinate).compLpL (2 : ENNReal) data.mu

private theorem llField_coordinate_reconstruction :
    (∑ coordinate : Fin 4,
      (llFieldCoordinateSingle coordinate).comp
        (llFieldCoordinate coordinate)) =
      ContinuousLinearMap.id Real LLFieldFiber := by
  classical
  ext field coordinate
  simp [llFieldCoordinateSingle, llFieldCoordinate]

private theorem compLpL_comp
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    {X : Type*} [MeasurableSpace X] (measure : Measure X)
    (outer : F →L[Real] G) (inner : E →L[Real] F) :
    (outer.compLpL (2 : ENNReal) measure).comp
        (inner.compLpL (2 : ENNReal) measure) =
      (outer.comp inner).compLpL (2 : ENNReal) measure := by
  ext field
  filter_upwards
    [outer.coeFn_compLpL
      (inner.compLpL (2 : ENNReal) measure field),
     inner.coeFn_compLpL field,
     (outer.comp inner).coeFn_compLpL field]
    with point hOuter hInner hComp
  change
    (outer.compLpL (2 : ENNReal) measure
      (inner.compLpL (2 : ENNReal) measure field)) point = _
  rw [hOuter, hInner, hComp]
  rfl

private theorem compLpL_sum
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {X : Type*} [MeasurableSpace X] (measure : Measure X)
    {Index : Type*} [Fintype Index]
    (maps : Index → E →L[Real] F) :
    (∑ index, maps index).compLpL (2 : ENNReal) measure =
      ∑ index, (maps index).compLpL (2 : ENNReal) measure := by
  classical
  have hSum (indices : Finset Index) :
      (∑ index ∈ indices, maps index).compLpL (2 : ENNReal) measure =
        ∑ index ∈ indices,
          (maps index).compLpL (2 : ENNReal) measure := by
    induction indices using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        ext field
        filter_upwards
          [(0 : E →L[Real] F).coeFn_compLpL field,
           Lp.coeFn_zero F (2 : ENNReal) measure]
          with point hPoint hZero
        rw [hPoint]
        change (0 : F) = ((0 : Lp F (2 : ENNReal) measure) : X → F) point
        exact hZero.symm
    | @insert index indices hIndex inductionHypothesis =>
        rw [Finset.sum_insert hIndex, Finset.sum_insert hIndex,
          ContinuousLinearMap.add_compLpL, inductionHypothesis]
  simpa using hSum Finset.univ

private theorem compLpL_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {X : Type*} [MeasurableSpace X] (measure : Measure X) :
    (ContinuousLinearMap.id Real E).compLpL
        (2 : ENNReal) measure =
      ContinuousLinearMap.id Real
        (Lp E (2 : ENNReal) measure) := by
  ext field
  filter_upwards
    [(ContinuousLinearMap.id Real E).coeFn_compLpL field]
    with point hPoint
  simpa using hPoint

private theorem llFluxL2_coordinate_reconstruction
    (data : PositiveLLH1Data period hPeriod) :
    (∑ coordinate : Fin 4,
      (llFluxL2CoordinateSingle period hPeriod data coordinate).comp
        (llFluxL2Coordinate period hPeriod data coordinate)) =
      ContinuousLinearMap.id Real (LLFluxL2 period hPeriod data) := by
  classical
  calc
    _ = ∑ coordinate : Fin 4,
        (((llFieldCoordinateSingle coordinate).comp
          (llFieldCoordinate coordinate)).compLpL
            (2 : ENNReal) data.mu) := by
          apply Finset.sum_congr rfl
          intro coordinate _
          exact compLpL_comp data.mu
            (llFieldCoordinateSingle coordinate)
            (llFieldCoordinate coordinate)
    _ = ((∑ coordinate : Fin 4,
          (llFieldCoordinateSingle coordinate).comp
            (llFieldCoordinate coordinate)).compLpL
              (2 : ENNReal) data.mu) := by
          rw [← compLpL_sum data.mu]
    _ = (ContinuousLinearMap.id Real LLFieldFiber).compLpL
          (2 : ENNReal) data.mu := by
          rw [llField_coordinate_reconstruction]
    _ = _ := compLpL_id data.mu

/-- The vector-valued LL embedding is compact exactly when its four scalar
coordinate embeddings are compact. -/
theorem canonicalLLH1ToFluxL2_isCompact_iff_coordinate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsCompactOperator (canonicalLLH1ToFluxL2 period hPeriod analysis) ↔
      ∀ coordinate : Fin 4,
        IsCompactOperator
          ((llFluxL2Coordinate period hPeriod
              (analysis.llH1Data period hPeriod) coordinate).comp
            (canonicalLLH1ToFluxL2 period hPeriod analysis)) := by
  classical
  constructor
  · intro compact coordinate
    exact compact.clm_comp
      (llFluxL2Coordinate period hPeriod
        (analysis.llH1Data period hPeriod) coordinate)
  · intro coordinateCompact
    let embedding := canonicalLLH1ToFluxL2 period hPeriod analysis
    have hReconstruction :
        embedding =
          ∑ coordinate : Fin 4,
            (llFluxL2CoordinateSingle period hPeriod
                (analysis.llH1Data period hPeriod) coordinate).comp
              ((llFluxL2Coordinate period hPeriod
                  (analysis.llH1Data period hPeriod) coordinate).comp embedding) := by
      apply ContinuousLinearMap.ext
      intro field
      have h := congrArg
        (fun operator => operator (embedding field))
        (llFluxL2_coordinate_reconstruction period hPeriod
          (analysis.llH1Data period hPeriod))
      simpa only [ContinuousLinearMap.id_apply, sum_apply,
        ContinuousLinearMap.comp_apply] using h.symm
    change IsCompactOperator embedding
    rw [hReconstruction]
    change
      (∑ coordinate : Fin 4,
        (llFluxL2CoordinateSingle period hPeriod
            (analysis.llH1Data period hPeriod) coordinate).comp
          ((llFluxL2Coordinate period hPeriod
              (analysis.llH1Data period hPeriod) coordinate).comp embedding)) ∈
        compactOperator (RingHom.id Real)
          (LLH1Space period hPeriod (analysis.llH1Data period hPeriod))
          (LLFluxL2 period hPeriod (analysis.llH1Data period hPeriod))
    exact Submodule.sum_mem _ fun coordinate _ =>
      (coordinateCompact coordinate).clm_comp
        (llFluxL2CoordinateSingle period hPeriod
          (analysis.llH1Data period hPeriod) coordinate)

end
end P0EFTJanusProgramPT12LLCanonicalFiniteFiberCompactness4D
end JanusFormal
