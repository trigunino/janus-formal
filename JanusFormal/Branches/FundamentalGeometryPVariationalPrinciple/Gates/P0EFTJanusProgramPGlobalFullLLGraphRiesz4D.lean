import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedSelfAdjointFredholmReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLSameActionFredholmRestriction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLHessianExplicitPolarization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D

/-!
# Full three-slot LL graph Riesz realization

The smooth core retains `llAuxMetric`, `llMeasure`, and `llField`.  Its
completion contains the already constructed auxiliary/measure graph Hilbert
space and the positive LL energy completion.  A further finite graph feature
records exactly the two genuine cross blocks.  Thus no measure direction is
silently quotiented and no coercivity or nonvanishing weight is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open Set
open MeasureTheory
open scoped Manifold ContDiff Topology ENNReal InnerProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLHessianExplicitPolarization4D
open P0EFTJanusFullLLSameActionFredholmRestriction4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPSpinorialCompleteVariation4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLLAuxMeasureSameActionHessian4D
open P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D

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

local instance :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

/-- Faithful smooth core of all three LL slots. -/
abbrev GlobalFullLLSmooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalLLAuxMeasureSmooth period hPeriod ×
    LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)

/-- Four direct/PT scalar features for one side of the two cross blocks. -/
abbrev GlobalFullLLCrossFiber :=
  WithLp 2 (WithLp 2 (Real × Real) × WithLp 2 (Real × Real))

/-- Both sides of the symmetric cross pairing. -/
abbrev GlobalFullLLCrossGraphFiber :=
  WithLp 2 (GlobalFullLLCrossFiber × GlobalFullLLCrossFiber)

/-- Auxiliary/measure side of the exact cross Hessian. -/
def globalCandidateAFullLLCrossU
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (point : EffectiveThroat period hPeriod) :
    GlobalFullLLCrossFiber :=
  WithLp.toLp 2
    (WithLp.toLp 2
      (inner Real
          ((data.boundary.llFields period hPeriod).llAuxMetric point)
          (direction.1.1 point),
        inner Real
          ((throatPTPullback period hPeriod LLMetricFiber
            (data.boundary.llFields period hPeriod).llAuxMetric) point)
          ((differentialLLAuxMetricDirectionPT period hPeriod
            direction.1.1) point)),
      WithLp.toLp 2
        (direction.1.2 point,
          (throatPTPullback period hPeriod Real direction.1.2) point))

/-- LL-field side of the exact cross Hessian. -/
def globalCandidateAFullLLCrossV
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (point : EffectiveThroat period hPeriod) :
    GlobalFullLLCrossFiber :=
  WithLp.toLp 2
    (WithLp.toLp 2
      (throatDerivativePairing period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (data.boundary.llFields period hPeriod).llField
          direction.2.toTest point,
        throatDerivativePairing period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (throatPTPullback period hPeriod LLFieldFiber
            (data.boundary.llFields period hPeriod).llField)
          (differentialLLFluxDirectionPT period hPeriod
            direction.2.toTest) point),
      WithLp.toLp 2
        (inner Real
            ((data.boundary.llFields period hPeriod).llField point)
            (direction.2.toTest point),
          inner Real
            ((throatPTPullback period hPeriod LLFieldFiber
              (data.boundary.llFields period hPeriod).llField) point)
            ((differentialLLFluxDirectionPT period hPeriod
              direction.2.toTest) point)))

/-- The finite graph feature carrying both cross-factor maps. -/
def globalCandidateAFullLLCrossGraphFeature
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis)
    (point : EffectiveThroat period hPeriod) :
    GlobalFullLLCrossGraphFiber :=
  WithLp.toLp 2
    (globalCandidateAFullLLCrossU period hPeriod data direction point,
      globalCandidateAFullLLCrossV period hPeriod data direction point)

theorem globalCandidateAFullLLCrossGraphFeature_continuous
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    Continuous
      (globalCandidateAFullLLCrossGraphFeature period hPeriod data direction) := by
  have hU₁ : Continuous (fun point =>
      inner Real
        ((data.boundary.llFields period hPeriod).llAuxMetric point)
        (direction.1.1 point)) :=
    (data.boundary.llFields period hPeriod).llAuxMetric.contMDiff_toFun.continuous.inner
      direction.1.1.contMDiff_toFun.continuous
  have hU₂ : Continuous (fun point =>
      inner Real
        ((throatPTPullback period hPeriod LLMetricFiber
          (data.boundary.llFields period hPeriod).llAuxMetric) point)
        ((differentialLLAuxMetricDirectionPT period hPeriod
          direction.1.1) point)) :=
    (throatPTPullback period hPeriod LLMetricFiber
      (data.boundary.llFields period hPeriod).llAuxMetric
      ).contMDiff_toFun.continuous.inner
        (differentialLLAuxMetricDirectionPT period hPeriod
          direction.1.1).contMDiff_toFun.continuous
  have hU₃ : Continuous direction.1.2.toFun :=
    direction.1.2.contMDiff_toFun.continuous
  have hU₄ : Continuous
      (throatPTPullback period hPeriod Real direction.1.2).toFun :=
    (throatPTPullback period hPeriod Real
      direction.1.2).contMDiff_toFun.continuous
  have hV₁ := throatDerivativePairing_continuous period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod).llField direction.2.toTest
  have hV₂ := throatDerivativePairing_continuous period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (throatPTPullback period hPeriod LLFieldFiber
      (data.boundary.llFields period hPeriod).llField)
    (differentialLLFluxDirectionPT period hPeriod direction.2.toTest)
  have hV₃ : Continuous (fun point =>
      inner Real
        ((data.boundary.llFields period hPeriod).llField point)
        (direction.2.toTest point)) :=
    (data.boundary.llFields period hPeriod).llField.contMDiff_toFun.continuous.inner
      direction.2.toTest.contMDiff_toFun.continuous
  have hV₄ : Continuous (fun point =>
      inner Real
        ((throatPTPullback period hPeriod LLFieldFiber
          (data.boundary.llFields period hPeriod).llField) point)
        ((differentialLLFluxDirectionPT period hPeriod
          direction.2.toTest) point)) :=
    (throatPTPullback period hPeriod LLFieldFiber
      (data.boundary.llFields period hPeriod).llField
      ).contMDiff_toFun.continuous.inner
        (differentialLLFluxDirectionPT period hPeriod
          direction.2.toTest).contMDiff_toFun.continuous
  have hU : Continuous
      (globalCandidateAFullLLCrossU period hPeriod data direction) := by
    exact
      (WithLp.prodContinuousLinearEquiv 2 Real
        (WithLp 2 (Real × Real)) (WithLp 2 (Real × Real))).symm.continuous.comp
        (((WithLp.prodContinuousLinearEquiv 2 Real Real Real).symm.continuous.comp
          (hU₁.prodMk hU₂)).prodMk
        ((WithLp.prodContinuousLinearEquiv 2 Real Real Real).symm.continuous.comp
          (hU₃.prodMk hU₄)))
  have hV : Continuous
      (globalCandidateAFullLLCrossV period hPeriod data direction) := by
    exact
      (WithLp.prodContinuousLinearEquiv 2 Real
        (WithLp 2 (Real × Real)) (WithLp 2 (Real × Real))).symm.continuous.comp
        (((WithLp.prodContinuousLinearEquiv 2 Real Real Real).symm.continuous.comp
          (hV₁.prodMk hV₂)).prodMk
        ((WithLp.prodContinuousLinearEquiv 2 Real Real Real).symm.continuous.comp
          (hV₃.prodMk hV₄)))
  exact
    (WithLp.prodContinuousLinearEquiv 2 Real
      GlobalFullLLCrossFiber GlobalFullLLCrossFiber).symm.continuous.comp
      (hU.prodMk hV)

theorem globalCandidateAFullLLCrossGraphFeature_memLp
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    MemLp (globalCandidateAFullLLCrossGraphFeature period hPeriod data direction)
      2 (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (globalCandidateAFullLLCrossGraphFeature_continuous period hPeriod
    data direction).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The cross graph feature as an actual `L2` vector. -/
def globalCandidateAFullLLCrossGraphToL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    Lp GlobalFullLLCrossGraphFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (globalCandidateAFullLLCrossGraphFeature_memLp period hPeriod
    data direction).toLp
      (globalCandidateAFullLLCrossGraphFeature period hPeriod data direction)

theorem globalCandidateAFullLLCrossGraphToL2_ae
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    (globalCandidateAFullLLCrossGraphToL2 period hPeriod data direction :
      EffectiveThroat period hPeriod → GlobalFullLLCrossGraphFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      globalCandidateAFullLLCrossGraphFeature period hPeriod data direction :=
  (globalCandidateAFullLLCrossGraphFeature_memLp period hPeriod
    data direction).coeFn_toLp

theorem globalCandidateAFullLLCrossGraphFeature_add
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLCrossGraphFeature period hPeriod data
        (first + second) =
      globalCandidateAFullLLCrossGraphFeature period hPeriod data first +
        globalCandidateAFullLLCrossGraphFeature period hPeriod data second := by
  funext point
  have hAux :
      (first + second).1.1 point = first.1.1 point + second.1.1 point := rfl
  have hAuxPT :
      differentialLLAuxMetricDirectionPT period hPeriod
          (first + second).1.1 point =
        differentialLLAuxMetricDirectionPT period hPeriod first.1.1 point +
          differentialLLAuxMetricDirectionPT period hPeriod second.1.1 point :=
    rfl
  have hMeasure :
      (first + second).1.2 point = first.1.2 point + second.1.2 point := rfl
  have hMeasurePT :
      throatPTPullback period hPeriod Real (first + second).1.2 point =
        throatPTPullback period hPeriod Real first.1.2 point +
          throatPTPullback period hPeriod Real second.1.2 point := rfl
  have hField :
      (first + second).2.toTest =
        first.2.toTest + second.2.toTest := rfl
  have hFieldPT :
      differentialLLFluxDirectionPT period hPeriod
          (first + second).2.toTest =
        differentialLLFluxDirectionPT period hPeriod first.2.toTest +
          differentialLLFluxDirectionPT period hPeriod second.2.toTest := by
    rw [hField]
    exact differentialLLFluxDirectionPT_add period hPeriod _ _
  have hFieldAt :
      (first.2.toTest + second.2.toTest) point =
        first.2.toTest point + second.2.toTest point := rfl
  have hFieldPTAt :
      (differentialLLFluxDirectionPT period hPeriod first.2.toTest +
          differentialLLFluxDirectionPT period hPeriod second.2.toTest) point =
        differentialLLFluxDirectionPT period hPeriod first.2.toTest point +
          differentialLLFluxDirectionPT period hPeriod second.2.toTest point := rfl
  have hDerivative
      (base : SmoothThroatField period hPeriod LLFieldFiber)
      (firstField secondField : SmoothThroatField period hPeriod LLFieldFiber) :
      throatDerivativePairing period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          base (firstField + secondField) point =
        throatDerivativePairing period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            base firstField point +
          throatDerivativePairing period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            base secondField point := by
    unfold throatDerivativePairing
    rw [throatFrameDerivative_add]
    simp only [Pi.add_apply, inner_add_right, Finset.sum_add_distrib]
  unfold globalCandidateAFullLLCrossGraphFeature
    globalCandidateAFullLLCrossU globalCandidateAFullLLCrossV
  rw [hAux, hAuxPT, hMeasure, hMeasurePT, hField]
  rw [differentialLLFluxDirectionPT_add]
  rw [hFieldAt, hFieldPTAt]
  rw [inner_add_right, inner_add_right, inner_add_right, inner_add_right]
  rw [hDerivative, hDerivative]
  rfl

theorem globalCandidateAFullLLCrossGraphFeature_smul
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (scalar : Real)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLCrossGraphFeature period hPeriod data
        (scalar • direction) =
      scalar •
        globalCandidateAFullLLCrossGraphFeature period hPeriod data direction := by
  funext point
  have hAux :
      (scalar • direction).1.1 point = scalar • direction.1.1 point := rfl
  have hAuxPT :
      differentialLLAuxMetricDirectionPT period hPeriod
          (scalar • direction).1.1 point =
        scalar • differentialLLAuxMetricDirectionPT period hPeriod
          direction.1.1 point := rfl
  have hMeasure :
      (scalar • direction).1.2 point = scalar * direction.1.2 point := rfl
  have hMeasurePT :
      throatPTPullback period hPeriod Real (scalar • direction).1.2 point =
        scalar * throatPTPullback period hPeriod Real direction.1.2 point := rfl
  have hField :
      (scalar • direction).2.toTest = scalar • direction.2.toTest := rfl
  have hFieldPT :
      differentialLLFluxDirectionPT period hPeriod
          (scalar • direction).2.toTest =
        scalar • differentialLLFluxDirectionPT period hPeriod
          direction.2.toTest := by
    rw [hField]
    exact differentialLLFluxDirectionPT_smul period hPeriod _ _
  have hFieldAt :
      (scalar • direction.2.toTest) point =
        scalar • direction.2.toTest point := rfl
  have hFieldPTAt :
      (scalar • differentialLLFluxDirectionPT period hPeriod
          direction.2.toTest) point =
        scalar • differentialLLFluxDirectionPT period hPeriod
          direction.2.toTest point := rfl
  have hDerivative
      (base : SmoothThroatField period hPeriod LLFieldFiber)
      (field : SmoothThroatField period hPeriod LLFieldFiber) :
      throatDerivativePairing period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          base (scalar • field) point =
        scalar * throatDerivativePairing period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          base field point := by
    unfold throatDerivativePairing
    rw [throatFrameDerivative_smul]
    simp only [Pi.smul_apply, real_inner_smul_right, Finset.mul_sum]
  unfold globalCandidateAFullLLCrossGraphFeature
    globalCandidateAFullLLCrossU globalCandidateAFullLLCrossV
  rw [hAux, hAuxPT, hMeasure, hMeasurePT, hField]
  rw [differentialLLFluxDirectionPT_smul]
  rw [hFieldAt, hFieldPTAt]
  rw [real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right]
  rw [hDerivative, hDerivative]
  rfl

/-- Linear cross-feature map into its ambient `L2` space. -/
def globalCandidateAFullLLCrossGraphL2LinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      Lp GlobalFullLLCrossGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  toFun := globalCandidateAFullLLCrossGraphToL2 period hPeriod data
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [globalCandidateAFullLLCrossGraphToL2_ae period hPeriod data
        (first + second),
       globalCandidateAFullLLCrossGraphToL2_ae period hPeriod data first,
       globalCandidateAFullLLCrossGraphToL2_ae period hPeriod data second,
       Lp.coeFn_add
        (globalCandidateAFullLLCrossGraphToL2 period hPeriod data first)
        (globalCandidateAFullLLCrossGraphToL2 period hPeriod data second)]
      with point hAdd hFirst hSecond hLpAdd
    rw [hAdd, hLpAdd]
    simp only [Pi.add_apply]
    rw [hFirst, hSecond]
    exact congrFun
      (globalCandidateAFullLLCrossGraphFeature_add period hPeriod
        data first second) point
  map_smul' scalar direction := by
    apply Lp.ext
    filter_upwards
      [globalCandidateAFullLLCrossGraphToL2_ae period hPeriod data
        (scalar • direction),
       globalCandidateAFullLLCrossGraphToL2_ae period hPeriod data direction,
       Lp.coeFn_smul scalar
        (globalCandidateAFullLLCrossGraphToL2 period hPeriod data direction)]
      with point hSmul hDirection hLpSmul
    rw [hSmul]
    simp only [RingHom.id_apply]
    rw [hLpSmul]
    simp only [Pi.smul_apply]
    rw [hDirection]
    exact congrFun
      (globalCandidateAFullLLCrossGraphFeature_smul period hPeriod
        data scalar direction) point

/-- Existing two block completions, with the Hilbert product norm. -/
abbrev GlobalFullLLBaseHilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (GlobalLLAuxMeasureGraphHilbert period hPeriod data ×
      LLH1Space period hPeriod (analysis.llH1Data period hPeriod))

/-- Ambient Hilbert space adding only the exact finite cross graph. -/
abbrev GlobalFullLLGraphAmbient
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (GlobalFullLLBaseHilbert period hPeriod data analysis ×
      Lp GlobalFullLLCrossGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))

/-- Linear inclusion of the three smooth slots into the full graph ambient
space. -/
def globalCandidateAFullLLGraphAmbientLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      GlobalFullLLGraphAmbient period hPeriod data analysis where
  toFun direction :=
    WithLp.toLp 2
      (WithLp.toLp 2
        (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
            data direction.1,
          llH1SmoothEmbedding period hPeriod
            (analysis.llH1Data period hPeriod) direction.2),
        globalCandidateAFullLLCrossGraphToL2 period hPeriod data direction)
  map_add' first second := by
    change WithLp.toLp 2
        (WithLp.toLp 2
          (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data
              (first.1 + second.1),
            llH1SmoothEmbedding period hPeriod
              (analysis.llH1Data period hPeriod) (first.2 + second.2)),
          globalCandidateAFullLLCrossGraphL2LinearMap period hPeriod
            data analysis (first + second)) = _
    rw [(globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
      data).map_add]
    rw [(llH1SmoothEmbedding period hPeriod
      (analysis.llH1Data period hPeriod)).map_add]
    rw [(globalCandidateAFullLLCrossGraphL2LinearMap period hPeriod
      data analysis).map_add]
    rfl
  map_smul' scalar direction := by
    change WithLp.toLp 2
        (WithLp.toLp 2
          (globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data
              (scalar • direction.1),
            llH1SmoothEmbedding period hPeriod
              (analysis.llH1Data period hPeriod) (scalar • direction.2)),
          globalCandidateAFullLLCrossGraphL2LinearMap period hPeriod
            data analysis (scalar • direction)) = _
    rw [(globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
      data).map_smul]
    rw [(llH1SmoothEmbedding period hPeriod
      (analysis.llH1Data period hPeriod)).map_smul]
    rw [(globalCandidateAFullLLCrossGraphL2LinearMap period hPeriod
      data analysis).map_smul]
    rfl

/-- Closed full graph generated by the genuine smooth three-slot packet. -/
def globalCandidateAFullLLGraphSubmodule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Submodule Real (GlobalFullLLGraphAmbient period hPeriod data analysis) :=
  (LinearMap.range
    (globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
      data analysis)).topologicalClosure

/-- Natural Hilbert completion of all three LL slots. -/
abbrev GlobalFullLLGraphHilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  globalCandidateAFullLLGraphSubmodule period hPeriod data analysis

noncomputable local instance globalFullLLGraphAmbientInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphAmbient period hPeriod data analysis) := by
  infer_instance

noncomputable local instance globalFullLLGraphInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  Submodule.innerProductSpace
    (globalCandidateAFullLLGraphSubmodule period hPeriod data analysis)

/-- Canonical smooth inclusion into the full graph completion. -/
def globalCandidateAFullLLSmoothEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis where
  toFun direction :=
    ⟨globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
        data analysis direction,
      (LinearMap.range
        (globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
          data analysis)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
            data analysis) direction)⟩
  map_add' first second := Subtype.ext
    ((globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
      data analysis).map_add first second)
  map_smul' scalar direction := Subtype.ext
    ((globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
      data analysis).map_smul scalar direction)

theorem globalCandidateAFullLLSmoothEmbedding_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let graph :=
    globalCandidateAFullLLGraphAmbientLinearMap period hPeriod data analysis
  have hRange :
      Subtype.val '' Set.range
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis) =
        (LinearMap.range graph :
          Set (GlobalFullLLGraphAmbient period hPeriod data analysis)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨direction, rfl⟩, rfl⟩
      exact ⟨direction, rfl⟩
    · rintro ⟨direction, rfl⟩
      exact
        ⟨globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis direction,
          ⟨direction, rfl⟩, rfl⟩
  change closure (LinearMap.range graph :
      Set (GlobalFullLLGraphAmbient period hPeriod data analysis)) ⊆
    closure (Subtype.val '' Set.range
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis))
  rw [hRange]

theorem globalCandidateAFullLLSmoothEmbedding_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis) := by
  intro first second hEqual
  have hAmbient :
      globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
          data analysis first =
        globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
          data analysis second :=
    congrArg Subtype.val hEqual
  have hBase :
      (globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
          data analysis first).fst =
        (globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
          data analysis second).fst :=
    congrArg (fun value : GlobalFullLLGraphAmbient period hPeriod data analysis =>
      value.fst) hAmbient
  have hAux :
      globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod data first.1 =
        globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
          data second.1 :=
    congrArg
      (fun value : GlobalFullLLBaseHilbert period hPeriod data analysis =>
        value.fst) hBase
  have hField :
      llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) first.2 =
        llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) second.2 :=
    congrArg
      (fun value : GlobalFullLLBaseHilbert period hPeriod data analysis =>
        value.snd) hBase
  apply Prod.ext
  · exact globalCandidateALLAuxMeasureSmoothEmbedding_injective
      period hPeriod data hAux
  · exact llH1SmoothEmbedding_injective period hPeriod
      (analysis.llH1Data period hPeriod) hField

@[implicit_reducible]
def globalCandidateAFullLLGraphCompleteSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CompleteSpace (GlobalFullLLGraphHilbert period hPeriod data analysis) := by
  letI : CompleteSpace
      (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  unfold GlobalFullLLGraphHilbert globalCandidateAFullLLGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalCandidateAFullLLGraphAmbientLinearMap period hPeriod
        data analysis))

noncomputable local instance globalFullLLGraphCompleteSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CompleteSpace (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis

/-- Projection to the existing auxiliary/measure graph factor. -/
def globalCandidateAFullLLAuxProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalLLAuxMeasureGraphHilbert period hPeriod data :=
  (WithLp.fstL 2 Real
      (GlobalLLAuxMeasureGraphHilbert period hPeriod data)
      (LLH1Space period hPeriod (analysis.llH1Data period hPeriod))).comp
    ((WithLp.fstL 2 Real
      (GlobalFullLLBaseHilbert period hPeriod data analysis)
      (Lp GlobalFullLLCrossGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))).comp
      (globalCandidateAFullLLGraphSubmodule period hPeriod
        data analysis).subtypeL)

/-- Projection to the existing positive LL energy completion. -/
def globalCandidateAFullLLFieldProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      LLH1Space period hPeriod (analysis.llH1Data period hPeriod) :=
  (WithLp.sndL 2 Real
      (GlobalLLAuxMeasureGraphHilbert period hPeriod data)
      (LLH1Space period hPeriod (analysis.llH1Data period hPeriod))).comp
    ((WithLp.fstL 2 Real
      (GlobalFullLLBaseHilbert period hPeriod data analysis)
      (Lp GlobalFullLLCrossGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))).comp
      (globalCandidateAFullLLGraphSubmodule period hPeriod
        data analysis).subtypeL)

/-- Projection to the auxiliary/measure side `U` of the cross graph. -/
def globalCandidateAFullLLCrossUProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  ((WithLp.fstL 2 Real GlobalFullLLCrossFiber GlobalFullLLCrossFiber).compLpL
      (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).comp
    ((WithLp.sndL 2 Real
      (GlobalFullLLBaseHilbert period hPeriod data analysis)
      (Lp GlobalFullLLCrossGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))).comp
      (globalCandidateAFullLLGraphSubmodule period hPeriod
        data analysis).subtypeL)

/-- Projection to the LL-field side `V` of the cross graph. -/
def globalCandidateAFullLLCrossVProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  ((WithLp.sndL 2 Real GlobalFullLLCrossFiber GlobalFullLLCrossFiber).compLpL
      (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).comp
    ((WithLp.sndL 2 Real
      (GlobalFullLLBaseHilbert period hPeriod data analysis)
      (Lp GlobalFullLLCrossGraphFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))).comp
      (globalCandidateAFullLLGraphSubmodule period hPeriod
        data analysis).subtypeL)

/-- Continuous full LL Hessian form on the completed graph. -/
def globalCandidateAFullLLContinuousHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    Real :=
  inner Real
      (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
        (globalCandidateAFullLLAuxProjection period hPeriod
          data analysis first))
      (globalCandidateAFullLLAuxProjection period hPeriod data analysis second) +
    inner Real
      (globalCandidateAFullLLFieldProjection period hPeriod data analysis first)
      (globalCandidateAFullLLFieldProjection period hPeriod data analysis second) +
    inner Real
      (globalCandidateAFullLLCrossUProjection period hPeriod data analysis first)
      (globalCandidateAFullLLCrossVProjection period hPeriod data analysis second) +
    inner Real
      (globalCandidateAFullLLCrossVProjection period hPeriod data analysis first)
      (globalCandidateAFullLLCrossUProjection period hPeriod data analysis second)

private def globalCandidateAFullLLAuxPart
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis := by
  letI : CompleteSpace
      (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  exact
    (ContinuousLinearMap.adjoint
      (𝕜 := Real)
      (E := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (F := GlobalLLAuxMeasureGraphHilbert period hPeriod data)
      (globalCandidateAFullLLAuxProjection period hPeriod data analysis)).comp
        ((globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data).comp
          (globalCandidateAFullLLAuxProjection period hPeriod data analysis))

private def globalCandidateAFullLLFieldPart
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis := by
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  exact
    (ContinuousLinearMap.adjoint
      (𝕜 := Real)
      (E := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (F := LLH1Space period hPeriod (analysis.llH1Data period hPeriod))
      (globalCandidateAFullLLFieldProjection period hPeriod data analysis)).comp
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis)

private def globalCandidateAFullLLCrossUVPart
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis := by
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  exact
    (ContinuousLinearMap.adjoint
      (𝕜 := Real)
      (E := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (F := Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (globalCandidateAFullLLCrossVProjection period hPeriod data analysis)).comp
        (globalCandidateAFullLLCrossUProjection period hPeriod data analysis)

private def globalCandidateAFullLLCrossVUPart
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis := by
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  exact
    (ContinuousLinearMap.adjoint
      (𝕜 := Real)
      (E := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (F := Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (globalCandidateAFullLLCrossUProjection period hPeriod data analysis)).comp
        (globalCandidateAFullLLCrossVProjection period hPeriod data analysis)

/-- Bounded Riesz representative of the complete three-slot graph form. -/
def globalCandidateAFullLLGraphRieszOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  globalCandidateAFullLLAuxPart period hPeriod data analysis +
    globalCandidateAFullLLFieldPart period hPeriod data analysis +
    globalCandidateAFullLLCrossUVPart period hPeriod data analysis +
    globalCandidateAFullLLCrossVUPart period hPeriod data analysis

private theorem globalCandidateAFullLLAuxPart_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    inner Real
        (globalCandidateAFullLLAuxPart period hPeriod data analysis first)
        second =
      inner Real
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
          (globalCandidateAFullLLAuxProjection period hPeriod data analysis
            first))
        (globalCandidateAFullLLAuxProjection period hPeriod data analysis
          second) := by
  letI : CompleteSpace
      (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  unfold globalCandidateAFullLLAuxPart
  change inner Real
      ((ContinuousLinearMap.adjoint
        (𝕜 := Real)
        (globalCandidateAFullLLAuxProjection period hPeriod data analysis))
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
          (globalCandidateAFullLLAuxProjection period hPeriod data analysis
            first)))
      second = _
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

private theorem globalCandidateAFullLLFieldPart_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    inner Real
        (globalCandidateAFullLLFieldPart period hPeriod data analysis first)
        second =
      inner Real
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis
          first)
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis
          second) := by
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  unfold globalCandidateAFullLLFieldPart
  rw [ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

private theorem globalCandidateAFullLLCrossUVPart_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    inner Real
        (globalCandidateAFullLLCrossUVPart period hPeriod data analysis first)
        second =
      inner Real
        (globalCandidateAFullLLCrossUProjection period hPeriod data analysis
          first)
        (globalCandidateAFullLLCrossVProjection period hPeriod data analysis
          second) := by
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  unfold globalCandidateAFullLLCrossUVPart
  rw [ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

private theorem globalCandidateAFullLLCrossVUPart_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    inner Real
        (globalCandidateAFullLLCrossVUPart period hPeriod data analysis first)
        second =
      inner Real
        (globalCandidateAFullLLCrossVProjection period hPeriod data analysis
          first)
        (globalCandidateAFullLLCrossUProjection period hPeriod data analysis
          second) := by
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  unfold globalCandidateAFullLLCrossVUPart
  rw [ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem globalCandidateAFullLLGraphRieszOperator_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    inner Real
        (globalCandidateAFullLLGraphRieszOperator period hPeriod
          data analysis first) second =
      globalCandidateAFullLLContinuousHessian period hPeriod
        data analysis first second := by
  letI : CompleteSpace
      (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  unfold globalCandidateAFullLLGraphRieszOperator
    globalCandidateAFullLLContinuousHessian
  change inner Real
      (((globalCandidateAFullLLAuxPart period hPeriod data analysis first +
          globalCandidateAFullLLFieldPart period hPeriod data analysis first) +
        globalCandidateAFullLLCrossUVPart period hPeriod data analysis first) +
        globalCandidateAFullLLCrossVUPart period hPeriod data analysis first)
      second = _
  have hFour
      (a b c d : GlobalFullLLGraphHilbert period hPeriod data analysis) :
      inner Real (((a + b) + c) + d) second =
        inner Real a second + inner Real b second +
          inner Real c second + inner Real d second := by
    calc
      _ = inner Real ((a + b) + c) second + inner Real d second :=
        @InnerProductSpace.add_left Real
          (GlobalFullLLGraphHilbert period hPeriod data analysis) _ _
          (globalFullLLGraphInnerProductSpace period hPeriod data analysis)
          ((a + b) + c) d second
      _ = (inner Real (a + b) second + inner Real c second) +
          inner Real d second :=
        congrArg (fun value : Real => value + inner Real d second)
          (@InnerProductSpace.add_left Real
            (GlobalFullLLGraphHilbert period hPeriod data analysis) _ _
            (globalFullLLGraphInnerProductSpace period hPeriod data analysis)
            (a + b) c second)
      _ = _ :=
        congrArg
          (fun value : Real =>
            (value + inner Real c second) + inner Real d second)
          (@InnerProductSpace.add_left Real
            (GlobalFullLLGraphHilbert period hPeriod data analysis) _ _
            (globalFullLLGraphInnerProductSpace period hPeriod data analysis)
            a b second)
  calc
    _ = inner Real
          (globalCandidateAFullLLAuxPart period hPeriod data analysis first)
          second +
        inner Real
          (globalCandidateAFullLLFieldPart period hPeriod data analysis first)
          second +
        inner Real
          (globalCandidateAFullLLCrossUVPart period hPeriod data analysis first)
          second +
        inner Real
          (globalCandidateAFullLLCrossVUPart period hPeriod data analysis first)
          second := hFour _ _ _ _
    _ = _ := by
      let auxPair := inner Real
        (globalCandidateAFullLLAuxPart period hPeriod data analysis first)
        second
      let fieldPair := inner Real
        (globalCandidateAFullLLFieldPart period hPeriod data analysis first)
        second
      let crossUVPair := inner Real
        (globalCandidateAFullLLCrossUVPart period hPeriod data analysis first)
        second
      let crossVUPair := inner Real
        (globalCandidateAFullLLCrossVUPart period hPeriod data analysis first)
        second
      let auxTarget := inner Real
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
          (globalCandidateAFullLLAuxProjection period hPeriod data analysis
            first))
        (globalCandidateAFullLLAuxProjection period hPeriod data analysis
          second)
      let fieldTarget := inner Real
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis
          first)
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis
          second)
      let crossUVTarget := inner Real
        (globalCandidateAFullLLCrossUProjection period hPeriod data analysis
          first)
        (globalCandidateAFullLLCrossVProjection period hPeriod data analysis
          second)
      let crossVUTarget := inner Real
        (globalCandidateAFullLLCrossVProjection period hPeriod data analysis
          first)
        (globalCandidateAFullLLCrossUProjection period hPeriod data analysis
          second)
      change auxPair + fieldPair + crossUVPair + crossVUPair =
        auxTarget + fieldTarget + crossUVTarget + crossVUTarget
      have hAux : auxPair = auxTarget := by
        simpa only [auxPair, auxTarget] using
          globalCandidateAFullLLAuxPart_pairing period hPeriod data analysis
            first second
      have hField : fieldPair = fieldTarget := by
        simpa only [fieldPair, fieldTarget] using
          globalCandidateAFullLLFieldPart_pairing period hPeriod data analysis
            first second
      have hCrossUV : crossUVPair = crossUVTarget := by
        simpa only [crossUVPair, crossUVTarget] using
          globalCandidateAFullLLCrossUVPart_pairing period hPeriod data analysis
            first second
      have hCrossVU : crossVUPair = crossVUTarget := by
        simpa only [crossVUPair, crossVUTarget] using
          globalCandidateAFullLLCrossVUPart_pairing period hPeriod data analysis
            first second
      rw [hAux, hField, hCrossUV, hCrossVU]

theorem globalCandidateAFullLLGraphRieszOperator_symmetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLContinuousHessian period hPeriod
        data analysis first second =
      globalCandidateAFullLLContinuousHessian period hPeriod
        data analysis second first := by
  let auxFirst :=
    globalCandidateAFullLLAuxProjection period hPeriod data analysis first
  let auxSecond :=
    globalCandidateAFullLLAuxProjection period hPeriod data analysis second
  let fieldFirst :=
    globalCandidateAFullLLFieldProjection period hPeriod data analysis first
  let fieldSecond :=
    globalCandidateAFullLLFieldProjection period hPeriod data analysis second
  let crossUFirst :=
    globalCandidateAFullLLCrossUProjection period hPeriod data analysis first
  let crossUSecond :=
    globalCandidateAFullLLCrossUProjection period hPeriod data analysis second
  let crossVFirst :=
    globalCandidateAFullLLCrossVProjection period hPeriod data analysis first
  let crossVSecond :=
    globalCandidateAFullLLCrossVProjection period hPeriod data analysis second
  change
    inner Real
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
          auxFirst) auxSecond +
      inner Real fieldFirst fieldSecond +
      inner Real crossUFirst crossVSecond +
      inner Real crossVFirst crossUSecond =
    inner Real
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
          auxSecond) auxFirst +
      inner Real fieldSecond fieldFirst +
      inner Real crossUSecond crossVFirst +
      inner Real crossVSecond crossUFirst
  rw [globalCandidateALLAuxMeasureGraphRieszOperator_symmetric
      period hPeriod data auxFirst auxSecond,
    real_inner_comm fieldSecond fieldFirst,
    real_inner_comm crossVSecond crossUFirst,
    real_inner_comm crossUSecond crossVFirst]
  rw [real_inner_comm
    (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
      auxSecond) auxFirst]
  ring

/-- Exact radical characterization of the completed full LL kernel. -/
theorem globalCandidateAFullLLGraphRieszOperator_mem_ker_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    direction ∈ LinearMap.ker
        (globalCandidateAFullLLGraphRieszOperator period hPeriod
          data analysis).toLinearMap ↔
      ∀ test,
        globalCandidateAFullLLContinuousHessian period hPeriod
          data analysis direction test = 0 := by
  constructor
  · intro hKernel test
    have hZero := LinearMap.mem_ker.mp hKernel
    change globalCandidateAFullLLGraphRieszOperator period hPeriod
      data analysis direction = 0 at hZero
    rw [← globalCandidateAFullLLGraphRieszOperator_pairing
      period hPeriod data analysis]
    rw [hZero]
    exact inner_zero_left test
  · intro hRadical
    apply LinearMap.mem_ker.mpr
    have hInner :
        inner Real
            (globalCandidateAFullLLGraphRieszOperator period hPeriod
              data analysis direction)
            (globalCandidateAFullLLGraphRieszOperator period hPeriod
              data analysis direction) = 0 := by
      rw [globalCandidateAFullLLGraphRieszOperator_pairing
        period hPeriod data analysis]
      exact hRadical
        (globalCandidateAFullLLGraphRieszOperator period hPeriod
          data analysis direction)
    exact (@inner_self_eq_zero Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) _ _).mp hInner

/-- Faithful insertion of the three smooth LL slots in the unchanged full
direction packet. -/
def globalCandidateAFullLLDirection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    FullMatterRobinLLDirections period hPeriod :=
  addDirection period hPeriod
    (globalCandidateALLAuxMeasureDirection period hPeriod
      direction.1.1 direction.1.2)
    (fullLLFredholmDirection period hPeriod
      (analysis.llH1Data period hPeriod) direction.2)

@[simp]
theorem globalCandidateAFullLLDirection_llAuxMetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    (globalCandidateAFullLLDirection period hPeriod direction).llAuxMetric =
      direction.1.1 := by
  simp [globalCandidateAFullLLDirection, addDirection,
    globalCandidateALLAuxMeasureDirection, fullLLFredholmDirection,
    fullRobinLLDirection, commonRobinLLDirection]

@[simp]
theorem globalCandidateAFullLLDirection_llMeasure
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    (globalCandidateAFullLLDirection period hPeriod direction).llMeasure =
      direction.1.2 := by
  simp [globalCandidateAFullLLDirection, addDirection,
    globalCandidateALLAuxMeasureDirection, fullLLFredholmDirection,
    fullRobinLLDirection, commonRobinLLDirection]

@[simp]
theorem globalCandidateAFullLLDirection_llField
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    (globalCandidateAFullLLDirection period hPeriod direction).common.ll =
      direction.2.toTest := by
  simp [globalCandidateAFullLLDirection, addDirection,
    globalCandidateALLAuxMeasureDirection, fullLLFredholmDirection,
    fullRobinLLDirection, commonRobinLLDirection]

theorem globalCandidateAFullLLDirection_eq_addDirection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLDirection period hPeriod direction =
      addDirection period hPeriod
        (globalCandidateALLAuxMeasureDirection period hPeriod
          direction.1.1 direction.1.2)
        (fullLLFredholmDirection period hPeriod
          (analysis.llH1Data period hPeriod) direction.2) :=
  rfl

/-! ## Faithful smooth-core attachment to the typed physical tangent -/

/-- The three LL smooth slots inserted in the existing independent variation
record, with every non-LL direction held at zero. -/
def fullLLSmoothIndependentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      IndependentFieldVariation period hPeriod where
  toFun := fun direction =>
    { metrics := zeroSmoothDiagonalMetricVariation period hPeriod
      matter := 0
      gauge := 0
      ghosts := 0
      auxiliaries := 0
      llAuxMetric := direction.1.1
      llMeasure := direction.1.2
      llField := direction.2.toTest }
  map_add' first second := by
    apply IndependentFieldVariation.ext
    case hMetrics =>
      change zeroSmoothDiagonalMetricVariation period hPeriod =
        zeroSmoothDiagonalMetricVariation period hPeriod +
          zeroSmoothDiagonalMetricVariation period hPeriod
      have hZero :
          zeroSmoothDiagonalMetricVariation period hPeriod =
            (0 : SmoothDiagonalMetricVariation period hPeriod) := by
        apply SmoothDiagonalMetricVariation.ext <;> rfl
      rw [hZero]
      exact (add_zero 0).symm
    case hMatter =>
      change (0 : _) = 0 + 0
      exact (zero_add 0).symm
    case hGauge =>
      change (0 : _) = 0 + 0
      exact (zero_add 0).symm
    case hGhosts =>
      change (0 : _) = 0 + 0
      exact (zero_add 0).symm
    case hAuxiliaries =>
      change (0 : _) = 0 + 0
      exact (zero_add 0).symm
    case hLLAuxMetric =>
      change first.1.1 + second.1.1 = first.1.1 + second.1.1
      rfl
    case hLLMeasure =>
      change first.1.2 + second.1.2 = first.1.2 + second.1.2
      rfl
    case hLLField =>
      change first.2.toTest + second.2.toTest =
        first.2.toTest + second.2.toTest
      rfl
  map_smul' scalar direction := by
    apply IndependentFieldVariation.ext
    case hMetrics =>
      change zeroSmoothDiagonalMetricVariation period hPeriod =
        scalar • zeroSmoothDiagonalMetricVariation period hPeriod
      have hZero :
          zeroSmoothDiagonalMetricVariation period hPeriod =
            (0 : SmoothDiagonalMetricVariation period hPeriod) := by
        apply SmoothDiagonalMetricVariation.ext <;> rfl
      rw [hZero]
      exact (smul_zero scalar).symm
    case hMatter =>
      change (0 : _) = scalar • 0
      exact (smul_zero scalar).symm
    case hGauge =>
      change (0 : _) = scalar • 0
      exact (smul_zero scalar).symm
    case hGhosts =>
      change (0 : _) = scalar • 0
      exact (smul_zero scalar).symm
    case hAuxiliaries =>
      change (0 : _) = scalar • 0
      exact (smul_zero scalar).symm
    case hLLAuxMetric =>
      change scalar • direction.1.1 = scalar • direction.1.1
      rfl
    case hLLMeasure =>
      change scalar • direction.1.2 = scalar • direction.1.2
      rfl
    case hLLField =>
      change scalar • direction.2.toTest = scalar • direction.2.toTest
      rfl

def fullLLSmoothCompleteLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      ProgramPCompleteVariation4D period hPeriod :=
  (independentCompleteVariationLinearMap period hPeriod).comp
    (fullLLSmoothIndependentLinearMap period hPeriod analysis)

def fullLLSmoothMatterFreeLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      MatterFreeCompleteVariation period hPeriod where
  toFun := fun direction =>
    ⟨fullLLSmoothCompleteLinearMap period hPeriod analysis direction, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (fullLLSmoothCompleteLinearMap
      period hPeriod analysis).map_add first second
  map_smul' scalar direction := by
    apply Subtype.ext
    exact (fullLLSmoothCompleteLinearMap
      period hPeriod analysis).map_smul scalar direction

def fullLLSmoothGeneralMetricLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      GeneralMetricMatterFreeVariation period hPeriod where
  toFun := fun direction =>
    ⟨fullLLSmoothMatterFreeLinearMap period hPeriod analysis direction, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (fullLLSmoothMatterFreeLinearMap
      period hPeriod analysis).map_add first second
  map_smul' scalar direction := by
    apply Subtype.ext
    exact (fullLLSmoothMatterFreeLinearMap
      period hPeriod analysis).map_smul scalar direction

/-- Honest attachment of the full LL smooth core to the D10-free physical
tangent.  This deliberately does not extend to arbitrary graph-completion
vectors. -/
def fullLLSmoothPhysicalTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration :=
  (LinearMap.inl Real
      (GeneralMetricMatterFreeVariation period hPeriod)
      (Sector →
        D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter)).comp
    (fullLLSmoothGeneralMetricLinearMap period hPeriod analysis)

theorem fullLLSmoothPhysicalTangentLinearMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (fullLLSmoothPhysicalTangentLinearMap period hPeriod analysis) := by
  intro first second hEqual
  have hAux := congrArg
    (fun tangent : GlobalPhysicalFieldTangent period hPeriod configuration =>
      tangent.completeVariation.independent.llAuxMetric) hEqual
  have hMeasure := congrArg
    (fun tangent : GlobalPhysicalFieldTangent period hPeriod configuration =>
      tangent.completeVariation.independent.llMeasure) hEqual
  have hField := congrArg
    (fun tangent : GlobalPhysicalFieldTangent period hPeriod configuration =>
      tangent.completeVariation.independent.llField) hEqual
  change first.1.1 = second.1.1 at hAux
  change first.1.2 = second.1.2 at hMeasure
  change first.2.toTest = second.2.toTest at hField
  exact Prod.ext (Prod.ext hAux hMeasure)
    (LLH1Smooth.ext period hPeriod hField)

@[simp]
theorem globalCandidateAFullLLAuxProjection_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLAuxProjection period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis direction) =
      globalCandidateALLAuxMeasureSmoothEmbedding period hPeriod
        data direction.1 :=
  rfl

@[simp]
theorem globalCandidateAFullLLFieldProjection_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLFieldProjection period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis direction) =
      llH1SmoothEmbedding period hPeriod
        (analysis.llH1Data period hPeriod) direction.2 :=
  rfl

theorem globalCandidateAFullLLCrossUProjection_smooth_ae
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    ((globalCandidateAFullLLCrossUProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis direction) :
        Lp GlobalFullLLCrossFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
      EffectiveThroat period hPeriod → GlobalFullLLCrossFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      globalCandidateAFullLLCrossU period hPeriod data direction := by
  have hProjection :=
    (WithLp.fstL 2 Real
      GlobalFullLLCrossFiber GlobalFullLLCrossFiber).coeFn_compLpL
        (p := (2 : ENNReal))
        (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (globalCandidateAFullLLCrossGraphToL2 period hPeriod data direction)
  have hGraph :=
    globalCandidateAFullLLCrossGraphToL2_ae period hPeriod data direction
  filter_upwards [hProjection, hGraph] with point hProjection hGraph
  change
    (((WithLp.fstL 2 Real
        GlobalFullLLCrossFiber GlobalFullLLCrossFiber).compLpL
        (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (globalCandidateAFullLLCrossGraphToL2 period hPeriod data direction) :
      Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
      EffectiveThroat period hPeriod → GlobalFullLLCrossFiber) point = _
  rw [hProjection, hGraph]
  rfl

theorem globalCandidateAFullLLCrossVProjection_smooth_ae
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    ((globalCandidateAFullLLCrossVProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis direction) :
        Lp GlobalFullLLCrossFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
      EffectiveThroat period hPeriod → GlobalFullLLCrossFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      globalCandidateAFullLLCrossV period hPeriod data direction := by
  have hProjection :=
    (WithLp.sndL 2 Real
      GlobalFullLLCrossFiber GlobalFullLLCrossFiber).coeFn_compLpL
        (p := (2 : ENNReal))
        (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (globalCandidateAFullLLCrossGraphToL2 period hPeriod data direction)
  have hGraph :=
    globalCandidateAFullLLCrossGraphToL2_ae period hPeriod data direction
  filter_upwards [hProjection, hGraph] with point hProjection hGraph
  change
    (((WithLp.sndL 2 Real
        GlobalFullLLCrossFiber GlobalFullLLCrossFiber).compLpL
        (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (globalCandidateAFullLLCrossGraphToL2 period hPeriod data direction) :
      Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
      EffectiveThroat period hPeriod → GlobalFullLLCrossFiber) point = _
  rw [hProjection, hGraph]
  rfl

/-- The cross graph records exactly the one-sided auxiliary/measure--field
mixed density of the unchanged LL Hessian. -/
theorem globalCandidateAFullLLCrossFiber_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (auxDirection fieldDirection :
      GlobalFullLLSmooth period hPeriod analysis)
    (point : EffectiveThroat period hPeriod) :
    inner Real
        (globalCandidateAFullLLCrossU period hPeriod
          data auxDirection point)
        (globalCandidateAFullLLCrossV period hPeriod
          data fieldDirection point) =
      ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (data.boundary.llFields period hPeriod).llAuxMetric
          (data.boundary.llFields period hPeriod).llField
          auxDirection.1.1 0 0 fieldDirection.2.toTest point +
        ptLLWorldvolumeHessianDensity period hPeriod
          (data.boundary.llFields period hPeriod)
          (fullDirectionLLVariation period hPeriod
            (globalCandidateALLAuxMeasureDirection period hPeriod
              auxDirection.1.1 auxDirection.1.2))
          (fullDirectionLLVariation period hPeriod
            (fullLLFredholmDirection period hPeriod
              (analysis.llH1Data period hPeriod) fieldDirection.2)) point := by
  have zeroLL_apply (x : EffectiveThroat period hPeriod) :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod LLFieldFiber) x = 0 := rfl
  have zeroMetric_apply (x : EffectiveThroat period hPeriod) :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod LLMetricFiber) x = 0 := rfl
  have zeroReal_apply (x : EffectiveThroat period hPeriod) :
      SmoothThroatField.toFun
        (0 : SmoothThroatField period hPeriod Real) x = 0 := rfl
  simp only [globalCandidateAFullLLCrossU,
    globalCandidateAFullLLCrossV, WithLp.prod_inner_apply,
    WithLp.toLp_fst, WithLp.toLp_snd]
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
    differentialLLKineticMixedHessianDensity
    ptLLWorldvolumeHessianDensity ptAverage
    llWorldvolumeHessianDensity fullDirectionLLVariation
    globalCandidateALLAuxMeasureDirection fullLLFredholmDirection
    fullRobinLLDirection commonRobinLLDirection
  simp [throatDerivativePairing, differentialLLFluxDirectionPT,
    differentialLLAuxMetricDirectionPT,
    P0EFTJanusThroatLinearOperationsZero4D.throatPTPullback_zero,
    zeroLL_apply, zeroMetric_apply, zeroReal_apply]
  ring

/-- One cross `L2` pairing is the exact one-sided mixed block of the same
unchanged LL action. -/
theorem globalCandidateAFullLLCrossU_smooth_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (auxDirection fieldDirection :
      GlobalFullLLSmooth period hPeriod analysis) :
    inner Real
        (globalCandidateAFullLLCrossUProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis auxDirection))
        (globalCandidateAFullLLCrossVProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis fieldDirection)) =
      fullLLHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod)
        (globalCandidateALLAuxMeasureDirection period hPeriod
          auxDirection.1.1 auxDirection.1.2)
        (fullLLFredholmDirection period hPeriod
          (analysis.llH1Data period hPeriod) fieldDirection.2)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hKinetic :
      Integrable
        (ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (data.boundary.llFields period hPeriod).llAuxMetric
          (data.boundary.llFields period hPeriod).llField
          auxDirection.1.1 0 0 fieldDirection.2.toTest)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
    unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
    exact
      ((differentialLLKineticMixedHessianDensity_integrable period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod).llAuxMetric
        (data.boundary.llFields period hPeriod).llField
        auxDirection.1.1 0 0 fieldDirection.2.toTest
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).add
        (differentialLLKineticMixedHessianDensity_integrable period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (throatPTPullback period hPeriod LLMetricFiber
            (data.boundary.llFields period hPeriod).llAuxMetric)
          (throatPTPullback period hPeriod LLFieldFiber
            (data.boundary.llFields period hPeriod).llField)
          (differentialLLAuxMetricDirectionPT period hPeriod
            auxDirection.1.1)
          (differentialLLAuxMetricDirectionPT period hPeriod 0)
          (differentialLLFluxDirectionPT period hPeriod 0)
          (differentialLLFluxDirectionPT period hPeriod
            fieldDirection.2.toTest)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))).const_mul
        (1 / 2 : Real)
  have hWorldvolume :
      Integrable
        (ptLLWorldvolumeHessianDensity period hPeriod
          (data.boundary.llFields period hPeriod)
          (fullDirectionLLVariation period hPeriod
            (globalCandidateALLAuxMeasureDirection period hPeriod
              auxDirection.1.1 auxDirection.1.2))
          (fullDirectionLLVariation period hPeriod
            (fullLLFredholmDirection period hPeriod
              (analysis.llH1Data period hPeriod) fieldDirection.2)))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    ptLLWorldvolumeHessianDensity_integrable period hPeriod
      (data.boundary.llFields period hPeriod)
      (fullDirectionLLVariation period hPeriod
        (globalCandidateALLAuxMeasureDirection period hPeriod
          auxDirection.1.1 auxDirection.1.2))
      (fullDirectionLLVariation period hPeriod
        (fullLLFredholmDirection period hPeriod
          (analysis.llH1Data period hPeriod) fieldDirection.2))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  rw [L2.inner_def]
  unfold fullLLHessian globalPTFullLLHessianForm
    globalPTDifferentialLLKineticMixedHessian
    globalPTLLWorldvolumeHessian
  change
    (∫ point, inner Real
      ((globalCandidateAFullLLCrossUProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis auxDirection) :
        Lp GlobalFullLLCrossFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) point)
      ((globalCandidateAFullLLCrossVProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis fieldDirection) :
        Lp GlobalFullLLCrossFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) point)
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
    (∫ point,
      ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod).llAuxMetric
        (data.boundary.llFields period hPeriod).llField
        auxDirection.1.1 0 0 fieldDirection.2.toTest point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
    ∫ point,
      ptLLWorldvolumeHessianDensity period hPeriod
        (data.boundary.llFields period hPeriod)
        (fullDirectionLLVariation period hPeriod
          (globalCandidateALLAuxMeasureDirection period hPeriod
            auxDirection.1.1 auxDirection.1.2))
        (fullDirectionLLVariation period hPeriod
          (fullLLFredholmDirection period hPeriod
            (analysis.llH1Data period hPeriod) fieldDirection.2)) point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod
  rw [← integral_add hKinetic hWorldvolume]
  apply integral_congr_ae
  filter_upwards
    [globalCandidateAFullLLCrossUProjection_smooth_ae period hPeriod
      data analysis auxDirection,
     globalCandidateAFullLLCrossVProjection_smooth_ae period hPeriod
      data analysis fieldDirection]
    with point hAux hField
  rw [hAux, hField]
  exact globalCandidateAFullLLCrossFiber_inner period hPeriod
    data auxDirection fieldDirection point

/-- Auxiliary/measure diagonal block on the smooth core. -/
theorem globalCandidateAFullLLAux_smooth_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    inner Real
        (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
          (globalCandidateAFullLLAuxProjection period hPeriod data analysis
            (globalCandidateAFullLLSmoothEmbedding period hPeriod
              data analysis first)))
        (globalCandidateAFullLLAuxProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis second)) =
      fullLLHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod)
        (globalCandidateALLAuxMeasureDirection period hPeriod
          first.1.1 first.1.2)
        (globalCandidateALLAuxMeasureDirection period hPeriod
          second.1.1 second.1.2)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  simpa only [globalCandidateAFullLLAuxProjection_smooth,
    globalCandidateALLAuxMeasureHessian] using
    globalCandidateALLAuxMeasureGraphRieszOperator_smooth_pairing
      period hPeriod data first.1 second.1

/-- LL-field diagonal block on the smooth core. -/
theorem globalCandidateAFullLLField_smooth_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    inner Real
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis first))
        (globalCandidateAFullLLFieldProjection period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis second)) =
      fullLLHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod)
        (fullLLFredholmDirection period hPeriod
          (analysis.llH1Data period hPeriod) first.2)
        (fullLLFredholmDirection period hPeriod
          (analysis.llH1Data period hPeriod) second.2)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [globalCandidateAFullLLFieldProjection_smooth period hPeriod
      data analysis first,
    globalCandidateAFullLLFieldProjection_smooth period hPeriod
      data analysis second]
  change inner Real
      (completedLLJacobiOperator period hPeriod
        (analysis.llH1Data period hPeriod)
        (llH1SmoothEmbedding period hPeriod
          (analysis.llH1Data period hPeriod) first.2))
      (llH1SmoothEmbedding period hPeriod
        (analysis.llH1Data period hPeriod) second.2) = _
  simpa only [
    GlobalAnalysisData.llH1Data,
    GlobalBoundaryVariationData.llFields] using
    (fullLLHessian_fredholmSlice_eq_operator_pairing period hPeriod
      (analysis.llH1Data period hPeriod) first.2 second.2).symm

/-- The unchanged full three-slot LL Hessian selected by the actual
Candidate-A background. -/
def globalCandidateAFullLLSameActionHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (first second : GlobalFullLLSmooth period hPeriod analysis) : Real :=
  fullLLHessian period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateAFullLLDirection period hPeriod first)
    (globalCandidateAFullLLDirection period hPeriod second)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- On the injective dense smooth core, the graph form is exactly the
unchanged full three-slot LL action Hessian. -/
theorem globalCandidateAFullLLContinuousHessian_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLContinuousHessian period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis first)
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis second) =
      globalCandidateAFullLLSameActionHessian period hPeriod
        data first second := by
  unfold globalCandidateAFullLLContinuousHessian
    globalCandidateAFullLLSameActionHessian
  rw [globalCandidateAFullLLAux_smooth_inner period hPeriod data analysis,
    globalCandidateAFullLLField_smooth_inner period hPeriod data analysis,
    globalCandidateAFullLLCrossU_smooth_inner period hPeriod data analysis]
  rw [real_inner_comm
    (globalCandidateAFullLLCrossUProjection period hPeriod data analysis
      (globalCandidateAFullLLSmoothEmbedding period hPeriod
        data analysis second))
    (globalCandidateAFullLLCrossVProjection period hPeriod data analysis
      (globalCandidateAFullLLSmoothEmbedding period hPeriod
        data analysis first))]
  rw [globalCandidateAFullLLCrossU_smooth_inner period hPeriod
    data analysis second first]
  rw [fullLLHessian_symmetric period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateALLAuxMeasureDirection period hPeriod
      second.1.1 second.1.2)
    (fullLLFredholmDirection period hPeriod
      (analysis.llH1Data period hPeriod) first.2)]
  rw [globalCandidateAFullLLDirection_eq_addDirection period hPeriod first,
    globalCandidateAFullLLDirection_eq_addDirection period hPeriod second,
    fullLLHessian_add_first, fullLLHessian_add_second,
    fullLLHessian_add_second]
  ring

/-- The bounded graph Riesz operator represents the exact same-action full
LL Hessian on the injective dense smooth core. -/
theorem globalCandidateAFullLLGraphRieszOperator_smooth_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    inner Real
        (globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod
            data analysis first))
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis second) =
      globalCandidateAFullLLSameActionHessian period hPeriod
        data first second := by
  rw [globalCandidateAFullLLGraphRieszOperator_pairing period hPeriod
    data analysis]
  exact globalCandidateAFullLLContinuousHessian_smooth period hPeriod
    data analysis first second

/-- The same-action identity also linearizes the true Euler functional along
the second full three-slot direction. -/
theorem globalCandidateAFullLLEulerAlong_hasDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    HasDerivAt
      (fullLLEulerAlong period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod)
        (globalCandidateAFullLLDirection period hPeriod first)
        (globalCandidateAFullLLDirection period hPeriod second)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (globalCandidateAFullLLSameActionHessian period hPeriod
        data first second) 0 := by
  exact fullLLEuler_second_direction_hasDerivAt period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateAFullLLDirection period hPeriod first)
    (globalCandidateAFullLLDirection period hPeriod second)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Symmetry of the completed full graph Riesz representative. Since it is
bounded on a Hilbert space, this is its self-adjointness criterion. -/
theorem globalCandidateAFullLLGraphRieszOperator_isSymmetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    inner Real
        (globalCandidateAFullLLGraphRieszOperator period hPeriod
          data analysis first) second =
      inner Real first
        (globalCandidateAFullLLGraphRieszOperator period hPeriod
          data analysis second) := by
  letI : CompleteSpace
      (GlobalLLAuxMeasureGraphHilbert period hPeriod data) :=
    globalCandidateALLAuxMeasureGraphCompleteSpace period hPeriod data
  letI : CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis
  rw [globalCandidateAFullLLGraphRieszOperator_pairing period hPeriod
    data analysis]
  rw [real_inner_comm
    (globalCandidateAFullLLGraphRieszOperator period hPeriod
      data analysis second) first]
  rw [globalCandidateAFullLLGraphRieszOperator_pairing period hPeriod
    data analysis]
  exact globalCandidateAFullLLGraphRieszOperator_symmetric period hPeriod
    data analysis first second

/-- The complete off-shell three-slot LL Hessian is a bounded self-adjoint
operator on its genuine graph Hilbert completion. -/
theorem globalCandidateAFullLLGraphRieszOperator_isSelfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    @IsSelfAdjoint
      (GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
        GlobalFullLLGraphHilbert period hPeriod data analysis)
      (@ContinuousLinearMap.instStarId
        Real
        (GlobalFullLLGraphHilbert period hPeriod data analysis)
        inferInstance inferInstance
        (globalFullLLGraphInnerProductSpace period hPeriod data analysis)
        (globalCandidateAFullLLGraphCompleteSpace period hPeriod
          data analysis))
      (globalCandidateAFullLLGraphRieszOperator period hPeriod
        data analysis) := by
  apply (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
    Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    inferInstance inferInstance
    (globalFullLLGraphInnerProductSpace period hPeriod data analysis)
    (globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis)
    (globalCandidateAFullLLGraphRieszOperator period hPeriod
      data analysis)).2
  exact globalCandidateAFullLLGraphRieszOperator_isSymmetric
    period hPeriod data analysis

/-- For the full off-shell LL block, self-adjointness reduces the remaining
Fredholm proof to closed range and finite-dimensional radical. -/
theorem globalCandidateAFullLLGraphRieszOperator_fredholm_of_closedRange_finiteKernel
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hClosed : IsClosed
      ((globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis).range :
        Set (GlobalFullLLGraphHilbert period hPeriod data analysis)))
    (hKernel : FiniteDimensional Real
      (globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis).ker) :
    IsClosed
        ((globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis).range :
          Set (GlobalFullLLGraphHilbert period hPeriod data analysis)) ∧
      FiniteDimensional Real
        (globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis).ker ∧
      FiniteDimensional Real
        (GlobalFullLLGraphHilbert period hPeriod data analysis ⧸
          (globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis).range) := by
  exact
    @_root_.JanusFormal.P0EFTJanusBoundedSelfAdjointFredholmReduction4D.boundedSelfAdjoint_fredholm_of_closedRange_finiteKernel
        (GlobalFullLLGraphHilbert period hPeriod data analysis)
        inferInstance
        (globalFullLLGraphInnerProductSpace period hPeriod data analysis)
        (globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis)
        (globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis)
        (globalCandidateAFullLLGraphRieszOperator_isSelfAdjoint
          period hPeriod data analysis)
        hClosed hKernel

/-! ## Genuine quadratic action on the complete LL graph -/

local instance globalFullLLC2GraphNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (globalFullLLGraphInnerProductSpace period hPeriod data analysis).toNormedSpace

local instance (priority := 10000) globalFullLLC2GraphModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (globalFullLLC2GraphNormedSpace period hPeriod data analysis).toModule

local instance globalFullLLC2GraphDualNormedAddCommGroup
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedAddCommGroup
      (GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedAddCommGroup
    Real Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (globalFullLLC2GraphNormedSpace period hPeriod data analysis)
    inferInstance
    (RingHom.id Real) inferInstance

local instance globalFullLLC2GraphDualNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedSpace
    Real Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (globalFullLLC2GraphNormedSpace period hPeriod data analysis)
    inferInstance
    (RingHom.id Real) inferInstance
    Real inferInstance inferInstance inferInstance

private def globalCandidateAFullLLAuxFormProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalLLAuxMeasureGraphHilbert period hPeriod data where
  toFun := globalCandidateAFullLLAuxProjection
    period hPeriod data analysis
  map_add' first second :=
    (globalCandidateAFullLLAuxProjection
      period hPeriod data analysis).map_add first second
  map_smul' scalar state :=
    (globalCandidateAFullLLAuxProjection
      period hPeriod data analysis).map_smul scalar state
  cont := (globalCandidateAFullLLAuxProjection
    period hPeriod data analysis).continuous

private def globalCandidateAFullLLFieldFormProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      LLH1Space period hPeriod (analysis.llH1Data period hPeriod) where
  toFun := globalCandidateAFullLLFieldProjection
    period hPeriod data analysis
  map_add' first second :=
    (globalCandidateAFullLLFieldProjection
      period hPeriod data analysis).map_add first second
  map_smul' scalar state :=
    (globalCandidateAFullLLFieldProjection
      period hPeriod data analysis).map_smul scalar state
  cont := (globalCandidateAFullLLFieldProjection
    period hPeriod data analysis).continuous

private def globalCandidateAFullLLAuxGraphForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real] Real :=
  (innerSL Real :
      Lp GlobalLLAuxMeasureFeatureFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →L[Real]
        Lp GlobalLLAuxMeasureFeatureFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →L[Real]
          Real).bilinearComp
      (E' := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (F' := GlobalFullLLGraphHilbert period hPeriod data analysis)
      ((globalCandidateALLAuxMeasureFeatureProjection
        period hPeriod data).comp
          (globalCandidateAFullLLAuxFormProjection
            period hPeriod data analysis))
      ((globalCandidateALLAuxMeasureFeatureProjection
        period hPeriod data).comp
          (globalCandidateAFullLLAuxFormProjection
            period hPeriod data analysis))

private def globalCandidateAFullLLFieldGraphForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real] Real :=
  (innerSL Real :
      LLH1Space period hPeriod
          (analysis.llH1Data period hPeriod) →L[Real]
        LLH1Space period hPeriod
            (analysis.llH1Data period hPeriod) →L[Real] Real).bilinearComp
      (E' := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (F' := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (globalCandidateAFullLLFieldFormProjection
        period hPeriod data analysis)
      (globalCandidateAFullLLFieldFormProjection
        period hPeriod data analysis)

section CrossGraphForms

local instance (priority := 10000) globalFullLLCrossL2Module :
    Module Real
      (Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :=
  (inferInstance : InnerProductSpace Real
    (Lp GlobalFullLLCrossFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    ).toNormedSpace.toModule

private def globalCandidateAFullLLCrossUFormProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  toFun := globalCandidateAFullLLCrossUProjection
    period hPeriod data analysis
  map_add' first second :=
    (globalCandidateAFullLLCrossUProjection
      period hPeriod data analysis).map_add first second
  map_smul' scalar state :=
    (globalCandidateAFullLLCrossUProjection
      period hPeriod data analysis).map_smul scalar state
  cont := (globalCandidateAFullLLCrossUProjection
    period hPeriod data analysis).continuous

private def globalCandidateAFullLLCrossVFormProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      Lp GlobalFullLLCrossFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  toFun := globalCandidateAFullLLCrossVProjection
    period hPeriod data analysis
  map_add' first second :=
    (globalCandidateAFullLLCrossVProjection
      period hPeriod data analysis).map_add first second
  map_smul' scalar state :=
    (globalCandidateAFullLLCrossVProjection
      period hPeriod data analysis).map_smul scalar state
  cont := (globalCandidateAFullLLCrossVProjection
    period hPeriod data analysis).continuous

private def globalCandidateAFullLLCrossUVGraphForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real] Real :=
  (innerSL Real :
      Lp GlobalFullLLCrossFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →L[Real]
        Lp GlobalFullLLCrossFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →L[Real]
          Real).bilinearComp
      (E' := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (F' := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (globalCandidateAFullLLCrossUFormProjection
        period hPeriod data analysis)
      (globalCandidateAFullLLCrossVFormProjection
        period hPeriod data analysis)

private def globalCandidateAFullLLCrossVUGraphForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real] Real :=
  (innerSL Real :
      Lp GlobalFullLLCrossFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →L[Real]
        Lp GlobalFullLLCrossFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →L[Real]
          Real).bilinearComp
      (E' := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (F' := GlobalFullLLGraphHilbert period hPeriod data analysis)
      (globalCandidateAFullLLCrossVFormProjection
        period hPeriod data analysis)
      (globalCandidateAFullLLCrossUFormProjection
        period hPeriod data analysis)

end CrossGraphForms

/-- Calculus-facing bounded bilinear form represented by the complete LL
graph Riesz operator. -/
def globalCandidateAFullLLGraphForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real] Real :=
  globalCandidateAFullLLAuxGraphForm period hPeriod data analysis +
    globalCandidateAFullLLFieldGraphForm period hPeriod data analysis +
    globalCandidateAFullLLCrossUVGraphForm period hPeriod data analysis +
    globalCandidateAFullLLCrossVUGraphForm period hPeriod data analysis

@[simp]
theorem globalCandidateAFullLLGraphForm_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLGraphForm period hPeriod data analysis first second =
      globalCandidateAFullLLContinuousHessian period hPeriod
        data analysis first second := by
  change
    inner Real
          (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
            (globalCandidateAFullLLAuxProjection period hPeriod
              data analysis first))
          (globalCandidateALLAuxMeasureFeatureProjection period hPeriod data
            (globalCandidateAFullLLAuxProjection period hPeriod
              data analysis second)) +
        inner Real
          (globalCandidateAFullLLFieldProjection period hPeriod
            data analysis first)
          (globalCandidateAFullLLFieldProjection period hPeriod
            data analysis second) +
        inner Real
          (globalCandidateAFullLLCrossUProjection period hPeriod
            data analysis first)
          (globalCandidateAFullLLCrossVProjection period hPeriod
            data analysis second) +
        inner Real
          (globalCandidateAFullLLCrossVProjection period hPeriod
            data analysis first)
          (globalCandidateAFullLLCrossUProjection period hPeriod
            data analysis second) =
      inner Real
          (globalCandidateALLAuxMeasureGraphRieszOperator period hPeriod data
            (globalCandidateAFullLLAuxProjection period hPeriod
              data analysis first))
          (globalCandidateAFullLLAuxProjection period hPeriod
            data analysis second) +
        inner Real
          (globalCandidateAFullLLFieldProjection period hPeriod
            data analysis first)
          (globalCandidateAFullLLFieldProjection period hPeriod
            data analysis second) +
        inner Real
          (globalCandidateAFullLLCrossUProjection period hPeriod
            data analysis first)
          (globalCandidateAFullLLCrossVProjection period hPeriod
            data analysis second) +
        inner Real
          (globalCandidateAFullLLCrossVProjection period hPeriod
            data analysis first)
          (globalCandidateAFullLLCrossUProjection period hPeriod
            data analysis second)
  rw [globalCandidateALLAuxMeasureGraphRieszOperator_pairing
    period hPeriod data
    (globalCandidateAFullLLAuxProjection period hPeriod data analysis first)
    (globalCandidateAFullLLAuxProjection period hPeriod data analysis second)]

theorem globalCandidateAFullLLGraphForm_comm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLGraphForm period hPeriod data analysis first second =
      globalCandidateAFullLLGraphForm
        period hPeriod data analysis second first := by
  rw [globalCandidateAFullLLGraphForm_apply,
    globalCandidateAFullLLGraphForm_apply]
  exact globalCandidateAFullLLGraphRieszOperator_symmetric
    period hPeriod data analysis first second

/-- Pull the complete LL graph form back along a bounded linear chart map.
The complete graph's calculus structures remain internal to this gate. -/
def globalCandidateAFullLLGraphFormPullback
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace E : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [domainGroup : NormedAddCommGroup E]
    [domainNorm : NormedSpace Real E]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (projection : E →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis) :
    E →L[Real] E →L[Real] Real :=
  @ContinuousLinearMap.bilinearComp
    Real Real Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    (GlobalFullLLGraphHilbert period hPeriod data analysis) Real
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (globalFullLLC2GraphNormedSpace period hPeriod data analysis)
    (globalFullLLC2GraphNormedSpace period hPeriod data analysis) inferInstance
    (RingHom.id Real) (RingHom.id Real)
    E E inferInstance inferInstance
    Real Real inferInstance inferInstance inferInstance inferInstance
    (RingHom.id Real) (RingHom.id Real)
    (RingHom.id Real) (RingHom.id Real)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAFullLLGraphForm period hPeriod data analysis)
    projection projection

/-- Genuine quadratic action on the complete three-slot LL graph. -/
def globalCandidateAFullLLGraphAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) : Real :=
  (1 / 2 : Real) *
    globalCandidateAFullLLGraphForm period hPeriod data analysis state state

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second,
      bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

private theorem symmetricQuadratic_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real) :
    ContDiff Real ⊤ (fun state => (1 / 2 : Real) * bilinear state state) :=
  contDiff_const.mul (bilinear.contDiff.clm_apply contDiff_id)

theorem globalCandidateAFullLLGraphAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    HasFDerivAt
      (globalCandidateAFullLLGraphAction period hPeriod data analysis)
      (globalCandidateAFullLLGraphForm period hPeriod data analysis state)
      state := by
  change HasFDerivAt
    (fun point => (1 / 2 : Real) *
      globalCandidateAFullLLGraphForm period hPeriod data analysis point point)
    (globalCandidateAFullLLGraphForm period hPeriod data analysis state)
    state
  exact @symmetricQuadratic_hasFDerivAt
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup
    (globalFullLLC2GraphNormedSpace period hPeriod data analysis)
    (globalCandidateAFullLLGraphForm period hPeriod data analysis)
    (globalCandidateAFullLLGraphForm_comm period hPeriod data analysis)
    state

theorem globalCandidateAFullLLGraphAction_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    fderiv Real
        (globalCandidateAFullLLGraphAction period hPeriod data analysis)
        state =
      globalCandidateAFullLLGraphForm period hPeriod data analysis state :=
  (globalCandidateAFullLLGraphAction_hasFDerivAt
    period hPeriod data analysis state).fderiv

theorem globalCandidateAFullLLGraphAction_second_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (base : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    fderiv Real
        (fun state => fderiv Real
          (globalCandidateAFullLLGraphAction period hPeriod data analysis)
          state)
        base =
      globalCandidateAFullLLGraphForm period hPeriod data analysis := by
  rw [show
      (fun state => fderiv Real
        (globalCandidateAFullLLGraphAction period hPeriod data analysis)
        state) =
      (fun state =>
        globalCandidateAFullLLGraphForm
          period hPeriod data analysis state) from by
    funext state
    exact globalCandidateAFullLLGraphAction_fderiv
      period hPeriod data analysis state]
  exact ContinuousLinearMap.fderiv
    (globalCandidateAFullLLGraphForm period hPeriod data analysis)

theorem globalCandidateAFullLLGraphAction_contDiff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ContDiff Real ⊤
      (globalCandidateAFullLLGraphAction period hPeriod data analysis) := by
  change ContDiff Real ⊤
    (fun state => (1 / 2 : Real) *
      globalCandidateAFullLLGraphForm period hPeriod data analysis state state)
  exact @symmetricQuadratic_contDiff
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup
    (globalFullLLC2GraphNormedSpace period hPeriod data analysis)
    (globalCandidateAFullLLGraphForm period hPeriod data analysis)

theorem globalCandidateAFullLLGraphAction_contDiff_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ContDiff Real 2
      (globalCandidateAFullLLGraphAction period hPeriod data analysis) :=
  (globalCandidateAFullLLGraphAction_contDiff
    period hPeriod data analysis).of_le (by simp)

/-- The graph action has exactly the unchanged full LL Hessian on the dense
smooth core. -/
theorem globalCandidateAFullLLGraphAction_second_fderiv_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (base : GlobalFullLLGraphHilbert period hPeriod data analysis)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    (fderiv Real
        (fun state => fderiv Real
          (globalCandidateAFullLLGraphAction period hPeriod data analysis)
          state)
        base)
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis first)
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis second) =
      globalCandidateAFullLLSameActionHessian period hPeriod
        data first second := by
  rw [globalCandidateAFullLLGraphAction_second_fderiv,
    globalCandidateAFullLLGraphForm_apply]
  exact globalCandidateAFullLLContinuousHessian_smooth
    period hPeriod data analysis first second

end
end P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
end JanusFormal
