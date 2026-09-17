import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullSmoothL2Density4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiLinearMap4D

/-! The three-slot same-action LL Jacobi operator on its dense smooth L² core. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiClosure4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
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
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullJacobiLinearMap4D
open P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D

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

variable (Fiber : Type*) [NormedAddCommGroup Fiber]
  [NormedSpace Real Fiber] [CompleteSpace Fiber]

private theorem smoothToL2_ae
    (field : SmoothThroatField period hPeriod Fiber) :
    (smoothThroatToL2 period hPeriod Fiber field :
      EffectiveThroat period hPeriod → Fiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod] field.toFun :=
  (smoothThroatField_memLp period hPeriod Fiber
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) field).coeFn_toLp

private theorem smoothToL2_add
    (first second : SmoothThroatField period hPeriod Fiber) :
    smoothThroatToL2 period hPeriod Fiber (first + second) =
      smoothThroatToL2 period hPeriod Fiber first +
        smoothThroatToL2 period hPeriod Fiber second := by
  apply Lp.ext
  filter_upwards
    [smoothToL2_ae period hPeriod Fiber (first + second),
      smoothToL2_ae period hPeriod Fiber first,
      smoothToL2_ae period hPeriod Fiber second,
      Lp.coeFn_add (smoothThroatToL2 period hPeriod Fiber first)
        (smoothThroatToL2 period hPeriod Fiber second)]
    with point hSum hFirst hSecond hAdd
  simp only [Pi.add_apply] at hAdd
  rw [hSum, hAdd, hFirst, hSecond]
  rfl

private theorem smoothToL2_smul
    (scalar : Real) (field : SmoothThroatField period hPeriod Fiber) :
    smoothThroatToL2 period hPeriod Fiber (scalar • field) =
      scalar • smoothThroatToL2 period hPeriod Fiber field := by
  apply Lp.ext
  filter_upwards
    [smoothToL2_ae period hPeriod Fiber (scalar • field),
      smoothToL2_ae period hPeriod Fiber field,
      Lp.coeFn_smul scalar (smoothThroatToL2 period hPeriod Fiber field)]
    with point hScaled hField hSmul
  simp only [Pi.smul_apply] at hSmul
  rw [hScaled, hSmul, hField]
  rfl

private theorem smoothToL2_injective :
    Function.Injective (smoothThroatToL2 period hPeriod Fiber) := by
  intro first second hEqual
  letI : (intrinsicCanonicalThroatVolumeMeasure period hPeriod).IsOpenPosMeasure :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  have hSame :
      (smoothThroatToL2 period hPeriod Fiber first :
        EffectiveThroat period hPeriod → Fiber) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      (smoothThroatToL2 period hPeriod Fiber second :
        EffectiveThroat period hPeriod → Fiber) := by
    rw [hEqual]
  have hAE : first.toFun =ᵐ[
      intrinsicCanonicalThroatVolumeMeasure period hPeriod] second.toFun :=
    (smoothToL2_ae period hPeriod Fiber first).symm.trans
      (hSame.trans (smoothToL2_ae period hPeriod Fiber second))
  apply SmoothThroatField.ext
  intro point
  exact congrFun (Measure.eq_of_ae_eq hAE
    first.contMDiff_toFun.continuous second.contMDiff_toFun.continuous) point

/-- The smooth three-slot inclusion as a real-linear map. -/
def fullLLSmoothToL2LinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      FullLLL2 period hPeriod where
  toFun := fullLLSmoothToL2 period hPeriod analysis
  map_add' first second := by
    apply Prod.ext
    · apply Prod.ext
      · exact smoothToL2_add period hPeriod LLMetricFiber first.1.1 second.1.1
      · exact smoothToL2_add period hPeriod Real first.1.2 second.1.2
    · change smoothThroatToL2 period hPeriod LLFieldFiber
        (first.2.toTest + second.2.toTest) =
        smoothThroatToL2 period hPeriod LLFieldFiber first.2.toTest +
          smoothThroatToL2 period hPeriod LLFieldFiber second.2.toTest
      exact smoothToL2_add period hPeriod LLFieldFiber first.2.toTest second.2.toTest
  map_smul' scalar direction := by
    apply Prod.ext
    · apply Prod.ext
      · exact smoothToL2_smul period hPeriod LLMetricFiber scalar direction.1.1
      · exact smoothToL2_smul period hPeriod Real scalar direction.1.2
    · change smoothThroatToL2 period hPeriod LLFieldFiber
        (scalar • direction.2.toTest) =
        scalar • smoothThroatToL2 period hPeriod LLFieldFiber direction.2.toTest
      exact smoothToL2_smul period hPeriod LLFieldFiber scalar direction.2.toTest

/-- Open positivity makes each smooth component faithful in L². -/
theorem fullLLSmoothToL2LinearMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective (fullLLSmoothToL2LinearMap period hPeriod analysis) := by
  intro first second hEqual
  have hAux := congrArg (fun value : FullLLL2 period hPeriod => value.1.1) hEqual
  have hMeasure := congrArg (fun value : FullLLL2 period hPeriod => value.1.2) hEqual
  have hField := congrArg (fun value : FullLLL2 period hPeriod => value.2) hEqual
  have hAux' : first.1.1 = second.1.1 :=
    smoothToL2_injective period hPeriod LLMetricFiber hAux
  have hMeasure' : first.1.2 = second.1.2 :=
    smoothToL2_injective period hPeriod Real hMeasure
  have hField' : first.2.toTest = second.2.toTest :=
    smoothToL2_injective period hPeriod LLFieldFiber hField
  apply Prod.ext
  · exact Prod.ext hAux' hMeasure'
  · exact LLH1Smooth.ext period hPeriod hField'

/-- The same three L² slots with the Hilbert sum norm. -/
abbrev FullLLHilbert :=
  WithLp 2
    (WithLp 2
      (Lp LLMetricFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
       Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ×
     Lp LLFieldFiber (2 : ENNReal)
       (intrinsicCanonicalThroatVolumeMeasure period hPeriod))

/-- Linear identification of the raw product with its Hilbert L² product. -/
def fullLLL2HilbertEquiv :
    FullLLL2 period hPeriod ≃ₗ[Real] FullLLHilbert period hPeriod where
  toFun value := WithLp.toLp 2 (WithLp.toLp 2 value.1, value.2)
  invFun value := ((WithLp.ofLp (WithLp.ofLp value).1),
    (WithLp.ofLp value).2)
  left_inv value := rfl
  right_inv value := by
    cases value with
    | toLp value =>
      cases value.1 with
      | toLp inner => rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def fullLLHilbertHomeomorph :
    FullLLHilbert period hPeriod ≃ₜ FullLLL2 period hPeriod :=
  (WithLp.homeomorphProd 2
    (WithLp 2
      (Lp LLMetricFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
       Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)))
    (Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))).trans
    ((WithLp.homeomorphProd 2
      (Lp LLMetricFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))).prodCongr
      (Homeomorph.refl _))

/-- Dense graph domain of the full LL Jacobi residual. -/
def fullLLSmoothToHilbertLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      FullLLHilbert period hPeriod :=
  (fullLLL2HilbertEquiv period hPeriod).toLinearMap.comp
    (fullLLSmoothToL2LinearMap period hPeriod analysis)

/-- Dense graph domain of the full LL Jacobi residual. -/
def fullLLJacobiSmoothDomain
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Submodule Real (FullLLHilbert period hPeriod) :=
  LinearMap.range (fullLLSmoothToHilbertLinearMap period hPeriod analysis)

private def fullLLSmoothEquivDomain
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis ≃ₗ[Real]
      fullLLJacobiSmoothDomain period hPeriod analysis :=
  LinearEquiv.ofInjective (fullLLSmoothToHilbertLinearMap period hPeriod analysis)
    ((fullLLL2HilbertEquiv period hPeriod).injective.comp
      (fullLLSmoothToL2LinearMap_injective period hPeriod analysis))

/-- The same-action three-slot Jacobi residual as an L² partial operator. -/
def fullLLJacobiSmoothPMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    FullLLHilbert period hPeriod →ₗ.[Real] FullLLHilbert period hPeriod where
  domain := fullLLJacobiSmoothDomain period hPeriod analysis
  toFun := ((fullLLL2HilbertEquiv period hPeriod).toLinearMap.comp
    (llFullJacobiLinearMap period hPeriod data analysis)).comp
      (fullLLSmoothEquivDomain period hPeriod analysis).symm.toLinearMap

theorem fullLLJacobiSmoothPMap_denseDomain
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Dense ((fullLLJacobiSmoothPMap period hPeriod data analysis).domain :
      Set (FullLLHilbert period hPeriod)) := by
  change Dense (fullLLJacobiSmoothDomain period hPeriod analysis :
    Set (FullLLHilbert period hPeriod))
  rw [dense_iff_closure_eq]
  change closure (Set.range (fun direction =>
    (fullLLHilbertHomeomorph period hPeriod).symm
      (fullLLSmoothToL2 period hPeriod analysis direction))) = Set.univ
  exact (((fullLLHilbertHomeomorph period hPeriod).symm.surjective.denseRange).comp
    (fullLLSmoothToL2_denseRange period hPeriod analysis)
    (fullLLHilbertHomeomorph period hPeriod).symm.continuous).closure_range

private theorem fullLLJacobiSmooth_pairing_symmetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    inner Real (fullLLL2HilbertEquiv period hPeriod
        (llFullJacobiLinearMap period hPeriod data analysis first))
        (fullLLL2HilbertEquiv period hPeriod
          (fullLLSmoothToL2 period hPeriod analysis second)) =
      inner Real (fullLLL2HilbertEquiv period hPeriod
          (fullLLSmoothToL2 period hPeriod analysis first))
        (fullLLL2HilbertEquiv period hPeriod
          (llFullJacobiLinearMap period hPeriod data analysis second)) := by
  have hFirst := llFullJacobiLinearMap_pairing_eq_sameActionHessian
    period hPeriod data analysis first second
  have hSecond := llFullJacobiLinearMap_pairing_eq_sameActionHessian
    period hPeriod data analysis second first
  have hSym : globalCandidateAFullLLSameActionHessian period hPeriod data
      first second = globalCandidateAFullLLSameActionHessian period hPeriod data
        second first := by
    unfold globalCandidateAFullLLSameActionHessian
    exact fullLLHessian_symmetric period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (data.boundary.llFields period hPeriod)
      (globalCandidateAFullLLDirection period hPeriod first)
      (globalCandidateAFullLLDirection period hPeriod second)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  change
    (inner Real ((llFullJacobiLinearMap period hPeriod data analysis first).1.1)
        (smoothThroatToL2 period hPeriod LLMetricFiber second.1.1) +
      inner Real ((llFullJacobiLinearMap period hPeriod data analysis first).1.2)
        (smoothThroatToL2 period hPeriod Real second.1.2)) +
      inner Real ((llFullJacobiLinearMap period hPeriod data analysis first).2)
        (llSmoothToL2 period hPeriod second.2.toTest) =
    (inner Real (smoothThroatToL2 period hPeriod LLMetricFiber first.1.1)
        ((llFullJacobiLinearMap period hPeriod data analysis second).1.1) +
      inner Real (smoothThroatToL2 period hPeriod Real first.1.2)
        ((llFullJacobiLinearMap period hPeriod data analysis second).1.2)) +
      inner Real (llSmoothToL2 period hPeriod first.2.toTest)
        ((llFullJacobiLinearMap period hPeriod data analysis second).2)
  rw [real_inner_comm
      ((llFullJacobiLinearMap period hPeriod data analysis second).1.1)
      (smoothThroatToL2 period hPeriod LLMetricFiber first.1.1),
    real_inner_comm
      ((llFullJacobiLinearMap period hPeriod data analysis second).1.2)
      (smoothThroatToL2 period hPeriod Real first.1.2),
    real_inner_comm
      ((llFullJacobiLinearMap period hPeriod data analysis second).2)
      (llSmoothToL2 period hPeriod first.2.toTest)]
  rw [show smoothThroatToL2 period hPeriod LLMetricFiber second.1.1 =
      llAuxTestToL2 period hPeriod second.1.1 from rfl,
    show smoothThroatToL2 period hPeriod Real second.1.2 =
      llMeasureTestToL2 period hPeriod second.1.2 from rfl,
    show llSmoothToL2 period hPeriod second.2.toTest =
      llFieldTestToL2 period hPeriod second.2 from rfl,
    show smoothThroatToL2 period hPeriod LLMetricFiber first.1.1 =
      llAuxTestToL2 period hPeriod first.1.1 from rfl,
    show smoothThroatToL2 period hPeriod Real first.1.2 =
      llMeasureTestToL2 period hPeriod first.1.2 from rfl,
    show llSmoothToL2 period hPeriod first.2.toTest =
      llFieldTestToL2 period hPeriod first.2 from rfl]
  calc
    _ = globalCandidateAFullLLSameActionHessian period hPeriod data first second := by
      simpa only [add_assoc] using hFirst
    _ = globalCandidateAFullLLSameActionHessian period hPeriod data second first := hSym
    _ = _ := by simpa only [add_assoc] using hSecond.symm

/-- The three-slot smooth-core operator is symmetric. -/
theorem fullLLJacobiSmoothPMap_symmetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (fullLLJacobiSmoothPMap period hPeriod data analysis).IsFormalAdjoint
      (fullLLJacobiSmoothPMap period hPeriod data analysis) := by
  intro first second
  let firstSmooth := (fullLLSmoothEquivDomain period hPeriod analysis).symm first
  let secondSmooth := (fullLLSmoothEquivDomain period hPeriod analysis).symm second
  have hFirst : (first : FullLLHilbert period hPeriod) =
      fullLLL2HilbertEquiv period hPeriod
        (fullLLSmoothToL2 period hPeriod analysis firstSmooth) := by
    exact (congrArg Subtype.val
      ((fullLLSmoothEquivDomain period hPeriod analysis).apply_symm_apply first)).symm
  have hSecond : (second : FullLLHilbert period hPeriod) =
      fullLLL2HilbertEquiv period hPeriod
        (fullLLSmoothToL2 period hPeriod analysis secondSmooth) := by
    exact (congrArg Subtype.val
      ((fullLLSmoothEquivDomain period hPeriod analysis).apply_symm_apply second)).symm
  change inner Real (fullLLL2HilbertEquiv period hPeriod
      (llFullJacobiLinearMap period hPeriod data analysis firstSmooth))
      (second : FullLLHilbert period hPeriod) =
    inner Real (first : FullLLHilbert period hPeriod)
      (fullLLL2HilbertEquiv period hPeriod
        (llFullJacobiLinearMap period hPeriod data analysis secondSmooth))
  rw [hFirst, hSecond]
  exact fullLLJacobiSmooth_pairing_symmetric period hPeriod data analysis
    firstSmooth secondSmooth

/-- Dense symmetry gives closability of the three-slot graph. -/
theorem fullLLJacobiSmoothPMap_isClosable
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (fullLLJacobiSmoothPMap period hPeriod data analysis).IsClosable := by
  have hDense := fullLLJacobiSmoothPMap_denseDomain period hPeriod data analysis
  have hSymmetric := fullLLJacobiSmoothPMap_symmetric period hPeriod data analysis
  exact (LinearPMap.adjoint_isClosed hDense).isClosable.leIsClosable
    (hSymmetric.le_adjoint hDense)

/-- Canonical closed realization of the three-slot smooth Jacobi operator. -/
def fullLLJacobiClosedPMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    FullLLHilbert period hPeriod →ₗ.[Real] FullLLHilbert period hPeriod :=
  (fullLLJacobiSmoothPMap period hPeriod data analysis).closure

theorem fullLLJacobiClosedPMap_isClosed
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (fullLLJacobiClosedPMap period hPeriod data analysis).IsClosed :=
  (fullLLJacobiSmoothPMap_isClosable period hPeriod data analysis).closure_isClosed

theorem fullLLJacobiSmoothPMap_le_closed
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    fullLLJacobiSmoothPMap period hPeriod data analysis ≤
      fullLLJacobiClosedPMap period hPeriod data analysis :=
  (fullLLJacobiSmoothPMap period hPeriod data analysis).le_closure

end
end P0EFTJanusProgramPT12LLFullJacobiClosure4D
end JanusFormal
