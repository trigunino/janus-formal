import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLCanonicalReducedKernelD9Reading4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ActiveQuotientBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLRobinLLExactTaylorReducedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLHigherTaylorZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLPureMetricInactive4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveDiagonalOrderTwo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D
import Mathlib.Order.Closure

/-! The canonical reduced Jacobi kernel has zero Robin--LL active quotient class. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLCanonicalKernelActiveQuotientZero4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusMatterRobinFullLLActiveQuotientReducedFredholmPairing4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ActiveQuotientBridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLRobinLLExactTaylorReducedFredholm4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
open P0EFTJanusIntegratedPTFullLLHigherTaylorZero4D
open P0EFTJanusFullMatterRobinTrueLLPureMetricInactive4D
open P0EFTJanusFullMatterRobinTrueLLInactiveDiagonalOrderTwo4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
open P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalSharedInclusion4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : Measure.IsOpenPosMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

theorem canonical_reducedJacobi_kernel_activeQuotient_eq_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    (⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ : ActiveQuotient period hPeriod) =
      ⟦fullRobinLLDirection period hPeriod 0 0⟧ := by
  have hComponents := reducedJacobi_canonical_shared_inclusion_kernel_components
    period hPeriod scalarData kPlus kMinus hCoupling llData robin ll hKernel
  have hLL : ll = 0 :=
    (P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D.llH1SmoothEmbedding_eq_zero_iff
      period hPeriod llData ll).mp hComponents.2
  rw [hComponents.1, hLL]
  rw [LLH1Smooth.toTest_zero]

theorem canonical_reducedJacobi_kernel_quotientHessian_eq_zeroClass
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (other : ActiveQuotient period hPeriod)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    quotientHessian period hPeriod matterData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        ⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ other =
      quotientHessian period hPeriod matterData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        ⟦fullRobinLLDirection period hPeriod 0 0⟧ other := by
  rw [canonical_reducedJacobi_kernel_activeQuotient_eq_zero period hPeriod
    scalarData kPlus kMinus hCoupling llData robin ll hKernel]

theorem canonical_reducedJacobi_kernel_quotientEuler_eq_zeroClass
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (llData : PositiveLLH1Data period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
        ⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ =
      quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
        ⟦fullRobinLLDirection period hPeriod 0 0⟧ := by
  rw [canonical_reducedJacobi_kernel_activeQuotient_eq_zero period hPeriod
    scalarData kPlus kMinus hCoupling llData robin ll hKernel]

theorem zeroRobinLLClass_quotientHessian_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (other : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        ⟦fullRobinLLDirection period hPeriod 0 0⟧ other = 0 := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  induction other using Quotient.inductionOn with
  | _ direction =>
      rw [quotientHessian_mk]
      apply globalMatterRobinFullLLHessian_inactive_left
      rfl

theorem zeroRobinLLClass_quotientEuler_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (llData : PositiveLLH1Data period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) :
    quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
        ⟦fullRobinLLDirection period hPeriod 0 0⟧ = 0 := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [quotientEuler_mk]
  apply fullMatterRobinTrueLLEuler_eq_zero_of_activeProjection_zero
  rfl

theorem canonical_reducedJacobi_kernel_quotientHessian_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (other : ActiveQuotient period hPeriod)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    quotientHessian period hPeriod matterData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        ⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ other = 0 := by
  rw [canonical_reducedJacobi_kernel_quotientHessian_eq_zeroClass period hPeriod
    matterData scalarData kPlus kMinus hCoupling llData robin ll other hKernel]
  exact zeroRobinLLClass_quotientHessian_eq_zero period hPeriod matterData
    kPlus kMinus llData other

theorem canonical_reducedJacobi_kernel_quotientEuler_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (llData : PositiveLLH1Data period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
        ⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ = 0 := by
  rw [canonical_reducedJacobi_kernel_quotientEuler_eq_zeroClass period hPeriod
    matterData scalarData kPlus kMinus hCoupling bulkPlus bulkMinus llData junction
    robin ll hKernel]
  exact zeroRobinLLClass_quotientEuler_eq_zero period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus llData junction

theorem canonical_reducedJacobi_kernel_enrichedD9ActiveHessian_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (other : GlobalMatterEnrichedD9Projection period hPeriod)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        (globalMatterEnrichedD9Projection period hPeriod llData.fields
          (fullRobinLLDirection period hPeriod robin ll.toTest) sector column point) other = 0 := by
  rw [← quotientHessian_enrichedD9_classes]
  have hClass : enrichedD9ActiveQuotientClass period hPeriod
      (globalMatterEnrichedD9Projection period hPeriod llData.fields
        (fullRobinLLDirection period hPeriod robin ll.toTest) sector column point) =
      (⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ : ActiveQuotient period hPeriod) := by
    apply (P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D.activeQuotientEquiv
      period hPeriod).injective
    simp
  rw [hClass]
  exact canonical_reducedJacobi_kernel_quotientHessian_eq_zero period hPeriod
    matterData scalarData kPlus kMinus hCoupling llData robin ll _ hKernel

theorem canonical_reducedJacobi_kernel_enrichedD9ActiveEuler_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (llData : PositiveLLH1Data period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
        (globalMatterEnrichedD9Projection period hPeriod llData.fields
          (fullRobinLLDirection period hPeriod robin ll.toTest) sector column point) = 0 := by
  rw [← quotientEuler_enrichedD9_class]
  have hClass : enrichedD9ActiveQuotientClass period hPeriod
      (globalMatterEnrichedD9Projection period hPeriod llData.fields
        (fullRobinLLDirection period hPeriod robin ll.toTest) sector column point) =
      (⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ : ActiveQuotient period hPeriod) := by
    apply (P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D.activeQuotientEquiv
      period hPeriod).injective
    simp
  rw [hClass]
  exact canonical_reducedJacobi_kernel_quotientEuler_eq_zero period hPeriod matterData
    scalarData kPlus kMinus hCoupling bulkPlus bulkMinus llData junction robin ll hKernel

theorem canonical_reducedJacobi_kernel_TaylorC1_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (llData : PositiveLLH1Data period hPeriod)
    (junction robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
      (fullRobinLLDirection period hPeriod robin ll.toTest) = 0 := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler]
  have h := canonical_reducedJacobi_kernel_quotientEuler_eq_zero period hPeriod matterData
    scalarData kPlus kMinus hCoupling bulkPlus bulkMinus llData junction robin ll hKernel
  rwa [quotientEuler_mk] at h

theorem canonical_reducedJacobi_kernel_TaylorC2_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
      (fullRobinLLDirection period hPeriod robin ll.toTest) = 0 := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian]
  have h := canonical_reducedJacobi_kernel_quotientHessian_eq_zero period hPeriod
    matterData scalarData kPlus kMinus hCoupling llData robin ll
    (⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ : ActiveQuotient period hPeriod) hKernel
  rw [quotientHessian_mk] at h
  rw [h, mul_zero]

theorem canonical_reducedJacobi_kernel_trueCurve_hasDerivAt_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (llData : PositiveLLH1Data period hPeriod)
    (junction robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    HasDerivAt (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
      (fullRobinLLDirection period hPeriod robin ll.toTest) t) 0 0 := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  have hEuler := canonical_reducedJacobi_kernel_quotientEuler_eq_zero period hPeriod
    matterData scalarData kPlus kMinus hCoupling bulkPlus bulkMinus llData junction
    robin ll hKernel
  rw [quotientEuler_mk] at hEuler
  simpa only [P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D.fullMatterRobinTrueLLCurve,
    hEuler] using fullMatterRobinTrueLLAction_hasDerivAt period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
    (fullRobinLLDirection period hPeriod robin ll.toTest)

theorem canonical_reducedJacobi_kernel_trueCurve_second_iteratedDeriv_eq_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (llData : PositiveLLH1Data period hPeriod)
    (junction robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    iteratedDeriv 2 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
      (fullRobinLLDirection period hPeriod robin ll.toTest) t) 0 = 0 := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [fullMatterRobinTrueLLCurve_robinLL_second_iteratedDeriv period hPeriod matterData
    scalarData kPlus kMinus bulkPlus bulkMinus
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData junction robin ll]
  have h := canonical_reducedJacobi_kernel_quotientHessian_eq_zero period hPeriod
    matterData scalarData kPlus kMinus hCoupling llData robin ll
    (⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ : ActiveQuotient period hPeriod) hKernel
  change quotientHessian period hPeriod matterData kPlus kMinus
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
    (robinLLActiveQuotientDirection period hPeriod robin ll.toTest)
    (robinLLActiveQuotientDirection period hPeriod robin ll.toTest) = 0 at h
  rw [quotientHessian_robinLL_eq_reducedJacobi_pairing] at h
  exact h

theorem canonical_reducedJacobi_kernel_higherLL_and_curve_constant
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (llData : PositiveLLH1Data period hPeriod)
    (junction robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData)
    (hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    globalPTFullLLTaylorCubic period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
        (fullRobinLLDirection period hPeriod robin ll.toTest).llAuxMetric
        (fullDirectionLLVariation period hPeriod
          (fullRobinLLDirection period hPeriod robin ll.toTest)) llData.mu = 0 ∧
      globalPTFullLLTaylorQuartic period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
        (fullRobinLLDirection period hPeriod robin ll.toTest).llAuxMetric
        (fullDirectionLLVariation period hPeriod
          (fullRobinLLDirection period hPeriod robin ll.toTest)) llData.mu = 0 ∧
      iteratedDeriv 3 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
        (fullRobinLLDirection period hPeriod robin ll.toTest) t) 0 = 0 ∧
      iteratedDeriv 4 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
        (fullRobinLLDirection period hPeriod robin ll.toTest) t) 0 = 0 ∧
      ∀ t : Real, fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction
        (fullRobinLLDirection period hPeriod robin ll.toTest) t =
          fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
            (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields junction := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  have hComponents := reducedJacobi_canonical_shared_inclusion_kernel_components
    period hPeriod scalarData kPlus kMinus hCoupling llData robin ll hKernel
  have hLL : ll = 0 :=
    (P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D.llH1SmoothEmbedding_eq_zero_iff
      period hPeriod llData ll).mp hComponents.2
  rw [hComponents.1, hLL]
  rw [LLH1Smooth.toTest_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change globalPTFullLLTaylorCubic period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
      (zeroLLVariation period hPeriod) llData.mu = 0
    exact globalPTFullLLTaylorCubic_zero period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields llData.mu
  · change globalPTFullLLTaylorQuartic period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
      (zeroLLVariation period hPeriod) llData.mu = 0
    exact globalPTFullLLTaylorQuartic_zero period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields llData.mu
  · rw [fullMatterRobinTrueLLCurve_third_iteratedDeriv]
    change 6 * globalPTFullLLTaylorCubic period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
      (zeroLLVariation period hPeriod) llData.mu = 0
    rw [globalPTFullLLTaylorCubic_zero, mul_zero]
  · rw [fullMatterRobinTrueLLCurve_fourth_iteratedDeriv]
    change 24 * globalPTFullLLTaylorQuartic period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields 0
      (zeroLLVariation period hPeriod) llData.mu = 0
    rw [globalPTFullLLTaylorQuartic_zero, mul_zero]
  · intro t
    apply fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero
    rfl

theorem canonical_reducedJacobi_robinLL_kernel_iff
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData) :
    reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
        (reducedRobinLLInclusion period hPeriod scalarData
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0 ↔
      robin = 0 ∧ ll = 0 := by
  constructor
  · intro hKernel
    have hComponents := reducedJacobi_canonical_shared_inclusion_kernel_components
      period hPeriod scalarData kPlus kMinus hCoupling llData robin ll hKernel
    exact ⟨hComponents.1,
      (P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D.llH1SmoothEmbedding_eq_zero_iff
        period hPeriod llData ll).mp hComponents.2⟩
  · rintro ⟨rfl, rfl⟩
    have hRobinEmbedding : smoothThroatFieldToL2 period hPeriod
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (0 : SmoothThroatField period hPeriod Real) = 0 := by
      apply Lp.ext
      filter_upwards [smoothThroatFieldToL2_ae period hPeriod
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (0 : SmoothThroatField period hPeriod Real),
        Lp.coeFn_zero Real 2 (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
        with point hPoint hZero
      rw [hPoint, hZero]
      rfl
    have hInclusion : reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData 0 0 = 0 := by
      ext <;> simp [reducedRobinLLInclusion, hRobinEmbedding]
    rw [hInclusion]
    exact map_zero _

theorem canonical_robinLL_activeQuotient_eq_zero_iff
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData) :
    (⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ : ActiveQuotient period hPeriod) =
        ⟦fullRobinLLDirection period hPeriod 0 0⟧ ↔
      robin = 0 ∧ ll = 0 := by
  constructor
  · intro hClass
    have hActive := congrArg
      (P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D.activeQuotientEquiv period hPeriod)
      hClass
    have hRobin := congrArg ActiveDirection.robin hActive
    have hLLTest := congrArg ActiveDirection.llField hActive
    change robin = 0 at hRobin
    change ll.toTest = 0 at hLLTest
    have hLL : ll = 0 := by
      apply LLH1Smooth.ext
      simpa using hLLTest
    exact ⟨hRobin, hLL⟩
  · rintro ⟨rfl, rfl⟩
    rw [LLH1Smooth.toTest_zero]

theorem canonical_reducedJacobi_robinLL_kernel_iff_activeQuotient_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData) :
    reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
        (reducedRobinLLInclusion period hPeriod scalarData
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0 ↔
      (⟦fullRobinLLDirection period hPeriod robin ll.toTest⟧ : ActiveQuotient period hPeriod) =
        ⟦fullRobinLLDirection period hPeriod 0 0⟧ := by
  rw [canonical_reducedJacobi_robinLL_kernel_iff period hPeriod scalarData
    kPlus kMinus hCoupling llData robin ll,
    canonical_robinLL_activeQuotient_eq_zero_iff period hPeriod llData robin ll]

def canonicalSmoothRobinLLInclusionLinear
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (llData : PositiveLLH1Data period hPeriod) :
    (SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) →ₗ[Real]
      ReducedBosonicJacobiSpace period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData where
  toFun direction := reducedRobinLLInclusion period hPeriod scalarData
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData direction.1 direction.2
  map_add' first second := by
    apply Prod.ext
    · simp [reducedRobinLLInclusion]
    · apply Prod.ext
      · change smoothThroatFieldToL2 period hPeriod
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) (first.1 + second.1) =
            smoothThroatFieldToL2 period hPeriod
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first.1 +
            smoothThroatFieldToL2 period hPeriod
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) second.1
        apply Lp.ext
        filter_upwards [smoothThroatFieldToL2_ae period hPeriod
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) (first.1 + second.1),
          smoothThroatFieldToL2_ae period hPeriod
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first.1,
          smoothThroatFieldToL2_ae period hPeriod
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) second.1,
          Lp.coeFn_add
            (smoothThroatFieldToL2 period hPeriod
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first.1)
            (smoothThroatFieldToL2 period hPeriod
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) second.1)]
          with point hSum hFirst hSecond hAdd
        rw [hSum, hAdd]
        have hSmoothAdd : (first.1 + second.1).toFun point =
            first.1.toFun point + second.1.toFun point := rfl
        rw [hSmoothAdd]
        simpa only [Pi.add_apply] using congrArg₂ (fun a b : Real => a + b)
          hFirst.symm hSecond.symm
      · exact map_add _ _ _
  map_smul' scalar direction := by
    apply Prod.ext
    · simp [reducedRobinLLInclusion]
    · apply Prod.ext
      · change smoothThroatFieldToL2 period hPeriod
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) (scalar • direction.1) =
            scalar • smoothThroatFieldToL2 period hPeriod
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1
        apply Lp.ext
        filter_upwards [smoothThroatFieldToL2_ae period hPeriod
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) (scalar • direction.1),
          smoothThroatFieldToL2_ae period hPeriod
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1,
          Lp.coeFn_smul scalar
            (smoothThroatFieldToL2 period hPeriod
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1)]
          with point hSmul hDirection hLpSmul
        rw [hSmul, hLpSmul]
        have hSmoothSmul : (scalar • direction.1).toFun point =
            scalar * direction.1.toFun point := rfl
        rw [hSmoothSmul]
        simpa only [Pi.smul_apply, smul_eq_mul] using
          congrArg (fun value : Real => scalar * value) hDirection.symm
      · exact map_smul _ _ _

def canonicalSmoothRobinLLJacobiLinear
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    (SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) →ₗ[Real]
      ReducedBosonicJacobiSpace period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData :=
  (reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData).toLinearMap.comp
      (canonicalSmoothRobinLLInclusionLinear period hPeriod scalarData llData)

theorem canonicalSmoothRobinLLJacobiLinear_injective
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod) :
    Function.Injective
      (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData) := by
  intro first second hEq
  have hZero : canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus
      llData (first - second) = 0 := by
    rw [map_sub, hEq, sub_self]
  have hKernel : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
          (first - second).1 (first - second).2) = 0 := hZero
  have hComponents := (canonical_reducedJacobi_robinLL_kernel_iff period hPeriod
    scalarData kPlus kMinus hCoupling llData (first - second).1 (first - second).2).mp hKernel
  apply sub_eq_zero.mp
  exact Prod.ext hComponents.1 hComponents.2

theorem canonicalSmoothRobinLLJacobiLinear_ker_eq_bot
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod) :
    LinearMap.ker (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData
      kPlus kMinus llData) = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr
    (canonicalSmoothRobinLLJacobiLinear_injective period hPeriod scalarData
      kPlus kMinus hCoupling llData)

def canonicalSmoothRobinLLJacobiRangeEquiv
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod) :
    (SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) ≃ₗ[Real]
      LinearMap.range
        (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData) :=
  LinearEquiv.ofInjective
    (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData)
    (canonicalSmoothRobinLLJacobiLinear_injective period hPeriod scalarData
      kPlus kMinus hCoupling llData)

@[simp] theorem canonicalSmoothRobinLLJacobiRangeEquiv_apply_coe
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (direction : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    ((canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
      hCoupling llData direction : LinearMap.range
        (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData)) :
      ReducedBosonicJacobiSpace period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData) =
      canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus
        llData direction := by
  rfl

theorem canonicalSmoothRobinLLJacobiRangeEquiv_surjective
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod) :
    Function.Surjective
      (canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
        hCoupling llData) :=
  (canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
    hCoupling llData).surjective

theorem canonicalSmoothRobinLLJacobiRangeEquiv_inverse_exact
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod) :
    Function.LeftInverse
        (canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
          hCoupling llData).symm
        (canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
          hCoupling llData) ∧
      Function.RightInverse
        (canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
          hCoupling llData).symm
        (canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
          hCoupling llData) := by
  constructor
  · intro direction
    exact (canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData
      kPlus kMinus hCoupling llData).symm_apply_apply direction
  · intro value
    exact (canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData
      kPlus kMinus hCoupling llData).apply_symm_apply value

/-! This certificate concerns only the assembled matter--Robin--LL sector.
Einstein--Hilbert and Candidate A metric terms are deliberately absent. -/
theorem pureMetric_sectorial_active_class_and_D9_zero
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    (⟦pureMetricFullDirection period hPeriod metric⟧ : ActiveQuotient period hPeriod) =
        ⟦fullRobinLLDirection period hPeriod 0 0⟧ ∧
      toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields
          (pureMetricFullDirection period hPeriod metric) sector column point) =
        P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D.zeroActiveDirection
          period hPeriod := by
  constructor
  · apply Quotient.sound
    exact (pureMetricFullDirection_activeProjection_zero period hPeriod metric).trans rfl
  · simp [toActiveDirection_projection, pureMetricFullDirection,
      activeProjection,
      P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D.zeroActiveDirection]

theorem pureMetric_sectorial_C1_C2_C3_C4_and_derivatives_zero
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction
        (pureMetricFullDirection period hPeriod metric) = 0 ∧
      fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields (pureMetricFullDirection period hPeriod metric) = 0 ∧
      globalPTFullLLTaylorCubic period hPeriod frame fields
        (pureMetricFullDirection period hPeriod metric).llAuxMetric
        (fullDirectionLLVariation period hPeriod
          (pureMetricFullDirection period hPeriod metric)) llMeasure = 0 ∧
      globalPTFullLLTaylorQuartic period hPeriod frame fields
        (pureMetricFullDirection period hPeriod metric).llAuxMetric
        (fullDirectionLLVariation period hPeriod
          (pureMetricFullDirection period hPeriod metric)) llMeasure = 0 ∧
      HasDerivAt (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (pureMetricFullDirection period hPeriod metric) t) 0 0 ∧
      iteratedDeriv 2 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (pureMetricFullDirection period hPeriod metric) t) 0 = 0 ∧
      iteratedDeriv 3 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (pureMetricFullDirection period hPeriod metric) t) 0 = 0 ∧
      iteratedDeriv 4 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (pureMetricFullDirection period hPeriod metric) t) 0 = 0 := by
  have hInactive := pureMetricFullDirection_activeProjection_zero period hPeriod metric
  have hEuler := pureMetricFullDirection_sectorial_Euler_zero period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction metric
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler]
    exact hEuler
  · exact fullMatterRobinTrueLLTaylorC2_eq_zero_of_inactive period hPeriod matterData
      kPlus kMinus robinMeasure frame llMeasure fields _ hInactive
  · change globalPTFullLLTaylorCubic period hPeriod frame fields 0
      (zeroLLVariation period hPeriod) llMeasure = 0
    exact globalPTFullLLTaylorCubic_zero period hPeriod frame fields llMeasure
  · change globalPTFullLLTaylorQuartic period hPeriod frame fields 0
      (zeroLLVariation period hPeriod) llMeasure = 0
    exact globalPTFullLLTaylorQuartic_zero period hPeriod frame fields llMeasure
  · simpa only [P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D.fullMatterRobinTrueLLCurve,
      hEuler] using fullMatterRobinTrueLLAction_hasDerivAt period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (pureMetricFullDirection period hPeriod metric)
  · exact fullMatterRobinTrueLLCurve_second_iteratedDeriv_eq_zero_of_inactive
      period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
      llMeasure fields junction _ hInactive
  · rw [fullMatterRobinTrueLLCurve_third_iteratedDeriv]
    change 6 * globalPTFullLLTaylorCubic period hPeriod frame fields 0
      (zeroLLVariation period hPeriod) llMeasure = 0
    rw [globalPTFullLLTaylorCubic_zero, mul_zero]
  · rw [fullMatterRobinTrueLLCurve_fourth_iteratedDeriv]
    change 24 * globalPTFullLLTaylorQuartic period hPeriod frame fields 0
      (zeroLLVariation period hPeriod) llMeasure = 0
    rw [globalPTFullLLTaylorQuartic_zero, mul_zero]

def addPureMetric (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    FullMatterRobinLLDirections period hPeriod :=
  addDirection period hPeriod direction (pureMetricFullDirection period hPeriod metric)

theorem addPureMetric_activeProjection
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    activeProjection period hPeriod (addPureMetric period hPeriod direction metric) =
      activeProjection period hPeriod direction := by
  simp [addPureMetric, addDirection, pureMetricFullDirection, activeProjection]

theorem addPureMetric_activeQuotientClass
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    (⟦addPureMetric period hPeriod direction metric⟧ : ActiveQuotient period hPeriod) =
      ⟦direction⟧ := by
  apply (P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D.activeQuotientEquiv
    period hPeriod).injective
  simpa using addPureMetric_activeProjection period hPeriod direction metric

theorem addPureMetric_enrichedD9_activeReading
    (fields : IndependentFields period hPeriod) (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      (addPureMetric period hPeriod direction metric) sector column point) =
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      direction sector column point) := by
  simpa using addPureMetric_activeProjection period hPeriod direction metric

/-! Equality for the assembled matter--Robin--LL sector only; Einstein--Hilbert
is absent from this certificate. -/
theorem addPureMetric_sectorial_curve
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction (addPureMetric period hPeriod direction metric) t =
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction direction t := by
  simp [fullMatterRobinTrueLLCurve, addPureMetric, addDirection, pureMetricFullDirection,
    differentialLLFullCurve]

theorem addPureMetric_TaylorC1
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction (addPureMetric period hPeriod direction metric) =
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction direction := by
  rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler,
    fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler, trueEuler_factors_active,
    trueEuler_factors_active, addPureMetric_activeProjection]

theorem addPureMetric_TaylorC2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields (addPureMetric period hPeriod direction metric) =
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields direction := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullHessian_factors_active, fullHessian_factors_active,
    addPureMetric_activeProjection]

theorem addPureMetric_TaylorC3_C4
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    globalPTFullLLTaylorCubic period hPeriod frame fields
        (addPureMetric period hPeriod direction metric).llAuxMetric
        (fullDirectionLLVariation period hPeriod
          (addPureMetric period hPeriod direction metric)) llMeasure =
      globalPTFullLLTaylorCubic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure ∧
    globalPTFullLLTaylorQuartic period hPeriod frame fields
        (addPureMetric period hPeriod direction metric).llAuxMetric
        (fullDirectionLLVariation period hPeriod
          (addPureMetric period hPeriod direction metric)) llMeasure =
      globalPTFullLLTaylorQuartic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure := by
  constructor <;>
    simp [addPureMetric, addDirection, pureMetricFullDirection, fullDirectionLLVariation]

/-! Equality of iterated derivatives follows from equality of the entire
assembled sectorial curves. Einstein--Hilbert remains absent. -/
theorem addPureMetric_iteratedDeriv
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) (order : Nat) :
    iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      (addPureMetric period hPeriod direction metric) t) 0 =
    iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 := by
  have hCurves : (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      (addPureMetric period hPeriod direction metric) t) =
      (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) := by
    funext t
    exact addPureMetric_sectorial_curve period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction direction metric t
  rw [hCurves]

theorem addPureMetric_iteratedDeriv_orders_one_to_four
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    (∀ order ∈ ({1, 2, 3, 4} : Finset Nat),
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (addPureMetric period hPeriod direction metric) t) 0 =
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0) := by
  intro order _
  exact addPureMetric_iteratedDeriv period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction metric order

theorem addPureMetric_mixedTaylorCoefficient_and_Hessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields (addPureMetric period hPeriod first metric) second =
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second ∧
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first (addPureMetric period hPeriod second metric) =
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second ∧
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields (addPureMetric period hPeriod first metric) second =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second ∧
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first (addPureMetric period hPeriod second metric) =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second := by
  have hFirst := addPureMetric_activeProjection period hPeriod first metric
  have hSecond := addPureMetric_activeProjection period hPeriod second metric
  constructor
  · rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
      fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
      fullHessian_factors_active, fullHessian_factors_active, hFirst]
  constructor
  · rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
      fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
      fullHessian_factors_active, fullHessian_factors_active, hSecond]
  constructor
  · rw [fullHessian_factors_active, fullHessian_factors_active, hFirst]
  · rw [fullHessian_factors_active, fullHessian_factors_active, hSecond]

/-! Mixed Euler derivatives for the assembled sector only; Einstein--Hilbert
is absent. -/
theorem addPureMetric_mixedEulerDerivatives
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure matter junction fields
      (addPureMetric period hPeriod first metric) second)
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 ∧
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure matter junction fields
      first (addPureMetric period hPeriod second metric))
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 := by
  have hMixed := addPureMetric_mixedTaylorCoefficient_and_Hessian period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure fields first second metric
  constructor
  · simpa [hMixed.1] using
      representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields
        (addPureMetric period hPeriod first metric) second
  · simpa [hMixed.2.1] using
      representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields
        first (addPureMetric period hPeriod second metric)

theorem addPureMetric_quotientHessian_slots
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (firstMetric secondMetric : SmoothDiagonalMetricVariation period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦addPureMetric period hPeriod first firstMetric⟧ ⟦second⟧ =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦second⟧ ∧
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦addPureMetric period hPeriod second secondMetric⟧ =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦second⟧ ∧
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦addPureMetric period hPeriod first firstMetric⟧
        ⟦addPureMetric period hPeriod second secondMetric⟧ =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦second⟧ := by
  rw [addPureMetric_activeQuotientClass period hPeriod first firstMetric,
    addPureMetric_activeQuotientClass period hPeriod second secondMetric]
  exact ⟨rfl, rfl, rfl⟩

/-! D9 Hessian invariance in the assembled active sector; Einstein--Hilbert
is absent. -/
theorem addPureMetric_enrichedD9ActiveHessian_slots
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (firstMetric secondMetric : SmoothDiagonalMetricVariation period hPeriod) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields
          (addPureMetric period hPeriod first firstMetric) sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) ∧
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields
          (addPureMetric period hPeriod second secondMetric) sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) ∧
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields
          (addPureMetric period hPeriod first firstMetric) sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields
          (addPureMetric period hPeriod second secondMetric) sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := by
  have hMixedFirst := (addPureMetric_mixedTaylorCoefficient_and_Hessian period hPeriod
    matterData kPlus kMinus robinMeasure frame llMeasure fields first second firstMetric).2.2.1
  have hMixedSecond := (addPureMetric_mixedTaylorCoefficient_and_Hessian period hPeriod
    matterData kPlus kMinus robinMeasure frame llMeasure fields first second secondMetric).2.2.2
  constructor
  · rw [← fullHessian_eq_enrichedD9ActiveHessian,
      ← fullHessian_eq_enrichedD9ActiveHessian]
    exact hMixedFirst
  constructor
  · rw [← fullHessian_eq_enrichedD9ActiveHessian,
      ← fullHessian_eq_enrichedD9ActiveHessian]
    exact hMixedSecond
  · rw [← fullHessian_eq_enrichedD9ActiveHessian,
      ← fullHessian_eq_enrichedD9ActiveHessian,
      fullHessian_factors_active, fullHessian_factors_active,
      addPureMetric_activeProjection, addPureMetric_activeProjection]

theorem canonicalSmoothRobinLL_quotientHessian_eq_operatorPairing
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    quotientHessian period hPeriod matterData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
        ⟦fullRobinLLDirection period hPeriod first.1 first.2.toTest⟧
        ⟦fullRobinLLDirection period hPeriod second.1 second.2.toTest⟧ =
      reducedBosonicJacobiOperatorBlockPairing period hPeriod scalarData kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
        (canonicalSmoothRobinLLInclusionLinear period hPeriod scalarData llData first)
        (canonicalSmoothRobinLLInclusionLinear period hPeriod scalarData llData second) := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  change quotientHessian period hPeriod matterData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu llData.fields
      (robinLLActiveQuotientDirection period hPeriod first.1 first.2.toTest)
      (robinLLActiveQuotientDirection period hPeriod second.1 second.2.toTest) = _
  rw [quotientHessian_robinLL_eq_reducedJacobi_pairing]
  unfold canonicalSmoothRobinLLInclusionLinear reducedBosonicJacobiOperatorBlockPairing
    reducedBosonicNaturalHessian
  rfl

def canonicalSmoothRobinLLJacobiRangePullbackForm
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) : Real :=
  let firstImage := canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData
    kPlus kMinus llData first
  let secondImage := canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData
    kPlus kMinus llData second
  inner Real firstImage.1 secondImage.1 + inner Real firstImage.2.1 secondImage.2.1 +
    inner Real firstImage.2.2 secondImage.2.2

theorem canonicalSmoothRobinLLJacobiRangePullbackForm_eq_range_inner
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (first second : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData kPlus kMinus
        llData first second =
      let firstImage := ((canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
          hCoupling llData first : LinearMap.range
            (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData)) :
          ReducedBosonicJacobiSpace period hPeriod scalarData
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData)
      let secondImage := ((canonicalSmoothRobinLLJacobiRangeEquiv period hPeriod scalarData kPlus kMinus
          hCoupling llData second : LinearMap.range
            (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData)) :
          ReducedBosonicJacobiSpace period hPeriod scalarData
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData)
      inner Real firstImage.1 secondImage.1 + inner Real firstImage.2.1 secondImage.2.1 +
        inner Real firstImage.2.2 secondImage.2.2 := by
  rfl

theorem canonicalSmoothRobinLLJacobiRangePullbackForm_kernel_iff
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (first : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    (∀ second, canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData
        kPlus kMinus llData first second = 0) ↔ first = 0 := by
  constructor
  · intro hZero
    have hSelf := hZero first
    have hMapZero : canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData
        kPlus kMinus llData first = 0 := by
      unfold canonicalSmoothRobinLLJacobiRangePullbackForm at hSelf
      let image := canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData
        kPlus kMinus llData first
      have h₁ : inner Real image.1 image.1 = 0 := by
        have hnon₁ : 0 ≤ inner Real image.1 image.1 := real_inner_self_nonneg
        have hnon₂ : 0 ≤ inner Real image.2.1 image.2.1 := real_inner_self_nonneg
        have hnon₃ : 0 ≤ inner Real image.2.2 image.2.2 := real_inner_self_nonneg
        change inner Real image.1 image.1 + inner Real image.2.1 image.2.1 +
          inner Real image.2.2 image.2.2 = 0 at hSelf
        linarith
      have h₂ : inner Real image.2.1 image.2.1 = 0 := by
        have hnon₁ : 0 ≤ inner Real image.1 image.1 := real_inner_self_nonneg
        have hnon₂ : 0 ≤ inner Real image.2.1 image.2.1 := real_inner_self_nonneg
        have hnon₃ : 0 ≤ inner Real image.2.2 image.2.2 := real_inner_self_nonneg
        change inner Real image.1 image.1 + inner Real image.2.1 image.2.1 +
          inner Real image.2.2 image.2.2 = 0 at hSelf
        linarith
      have h₃ : inner Real image.2.2 image.2.2 = 0 := by
        have hnon₁ : 0 ≤ inner Real image.1 image.1 := real_inner_self_nonneg
        have hnon₂ : 0 ≤ inner Real image.2.1 image.2.1 := real_inner_self_nonneg
        have hnon₃ : 0 ≤ inner Real image.2.2 image.2.2 := real_inner_self_nonneg
        change inner Real image.1 image.1 + inner Real image.2.1 image.2.1 +
          inner Real image.2.2 image.2.2 = 0 at hSelf
        linarith
      apply Prod.ext
      · exact inner_self_eq_zero.mp h₁
      · apply Prod.ext
        · exact inner_self_eq_zero.mp h₂
        · exact inner_self_eq_zero.mp h₃
    apply (canonicalSmoothRobinLLJacobiLinear_injective period hPeriod scalarData
      kPlus kMinus hCoupling llData)
    simpa using hMapZero
  · rintro rfl
    intro second
    simp [canonicalSmoothRobinLLJacobiRangePullbackForm]

theorem canonicalSmoothRobinLLJacobiRangePullbackForm_symmetric
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData kPlus kMinus
        llData first second =
      canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData kPlus kMinus
        llData second first := by
  let firstImage := canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData
    kPlus kMinus llData first
  let secondImage := canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData
    kPlus kMinus llData second
  change inner Real firstImage.1 secondImage.1 + inner Real firstImage.2.1 secondImage.2.1 +
      inner Real firstImage.2.2 secondImage.2.2 =
    inner Real secondImage.1 firstImage.1 + inner Real secondImage.2.1 firstImage.2.1 +
      inner Real secondImage.2.2 firstImage.2.2
  rw [real_inner_comm firstImage.1, real_inner_comm firstImage.2.1,
    real_inner_comm firstImage.2.2]

theorem canonicalSmoothRobinLLJacobiRangePullbackForm_nonneg
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    0 ≤ canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData
      kPlus kMinus llData direction direction := by
  unfold canonicalSmoothRobinLLJacobiRangePullbackForm
  have h₁ : 0 ≤ inner Real
      (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData direction).1
      (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData direction).1 :=
    real_inner_self_nonneg
  have h₂ : 0 ≤ inner Real
      (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData direction).2.1
      (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData direction).2.1 :=
    real_inner_self_nonneg
  have h₃ : 0 ≤ inner Real
      (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData direction).2.2
      (canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData kPlus kMinus llData direction).2.2 :=
    real_inner_self_nonneg
  linarith

theorem canonicalSmoothRobinLLJacobiRangePullbackForm_posDef
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (direction : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData kPlus kMinus
      llData direction direction = 0 ↔ direction = 0 := by
  constructor
  · intro hSelf
    let image := canonicalSmoothRobinLLJacobiLinear period hPeriod scalarData
      kPlus kMinus llData direction
    have h₁ : inner Real image.1 image.1 = 0 := by
      have hnon₁ : 0 ≤ inner Real image.1 image.1 := real_inner_self_nonneg
      have hnon₂ : 0 ≤ inner Real image.2.1 image.2.1 := real_inner_self_nonneg
      have hnon₃ : 0 ≤ inner Real image.2.2 image.2.2 := real_inner_self_nonneg
      change inner Real image.1 image.1 + inner Real image.2.1 image.2.1 +
        inner Real image.2.2 image.2.2 = 0 at hSelf
      linarith
    have h₂ : inner Real image.2.1 image.2.1 = 0 := by
      have hnon₁ : 0 ≤ inner Real image.1 image.1 := real_inner_self_nonneg
      have hnon₂ : 0 ≤ inner Real image.2.1 image.2.1 := real_inner_self_nonneg
      have hnon₃ : 0 ≤ inner Real image.2.2 image.2.2 := real_inner_self_nonneg
      change inner Real image.1 image.1 + inner Real image.2.1 image.2.1 +
        inner Real image.2.2 image.2.2 = 0 at hSelf
      linarith
    have h₃ : inner Real image.2.2 image.2.2 = 0 := by
      have hnon₁ : 0 ≤ inner Real image.1 image.1 := real_inner_self_nonneg
      have hnon₂ : 0 ≤ inner Real image.2.1 image.2.1 := real_inner_self_nonneg
      have hnon₃ : 0 ≤ inner Real image.2.2 image.2.2 := real_inner_self_nonneg
      change inner Real image.1 image.1 + inner Real image.2.1 image.2.1 +
        inner Real image.2.2 image.2.2 = 0 at hSelf
      linarith
    have hImage : image = 0 := by
      apply Prod.ext
      · exact inner_self_eq_zero.mp h₁
      · exact Prod.ext (inner_self_eq_zero.mp h₂) (inner_self_eq_zero.mp h₃)
    apply (canonicalSmoothRobinLLJacobiLinear_injective period hPeriod scalarData
      kPlus kMinus hCoupling llData)
    simpa using hImage
  · rintro rfl
    simp [canonicalSmoothRobinLLJacobiRangePullbackForm]

theorem canonicalSmoothRobinLLJacobiRangePullbackForm_nondegenerate_bilateral
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (direction : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    ((∀ other, canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData
        kPlus kMinus llData direction other = 0) ↔ direction = 0) ∧
    ((∀ other, canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData
        kPlus kMinus llData other direction = 0) ↔ direction = 0) := by
  constructor
  · exact canonicalSmoothRobinLLJacobiRangePullbackForm_kernel_iff period hPeriod
      scalarData kPlus kMinus hCoupling llData direction
  · constructor
    · intro hRight
      apply (canonicalSmoothRobinLLJacobiRangePullbackForm_kernel_iff period hPeriod
        scalarData kPlus kMinus hCoupling llData direction).mp
      intro other
      rw [canonicalSmoothRobinLLJacobiRangePullbackForm_symmetric]
      exact hRight other
    · rintro rfl
      intro other
      simp [canonicalSmoothRobinLLJacobiRangePullbackForm]

theorem canonicalSmoothRobinLLJacobiRangePullbackForm_exact_blocks
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData kPlus kMinus
        llData first second =
      inner Real
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
          (smoothThroatFieldToL2 period hPeriod
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first.1))
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
          (smoothThroatFieldToL2 period hPeriod
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) second.1)) +
      inner Real (llH1SmoothEmbedding period hPeriod llData first.2)
        (llH1SmoothEmbedding period hPeriod llData second.2) := by
  unfold canonicalSmoothRobinLLJacobiRangePullbackForm
    canonicalSmoothRobinLLJacobiLinear canonicalSmoothRobinLLInclusionLinear
  simp [reducedRobinLLInclusion, reducedBosonicJacobiOperator_apply]

theorem canonicalSmoothRobinLLJacobiRangePullbackForm_diagonal_graphNorm
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : SmoothThroatField period hPeriod Real × LLH1Smooth period hPeriod llData) :
    canonicalSmoothRobinLLJacobiRangePullbackForm period hPeriod scalarData kPlus kMinus
        llData direction direction =
      ‖robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
          (smoothThroatFieldToL2 period hPeriod
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1)‖ ^ 2 +
        ‖direction.2‖ ^ 2 := by
  rw [canonicalSmoothRobinLLJacobiRangePullbackForm_exact_blocks]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  congr 1
  exact congrArg (fun value : Real => value ^ 2)
    (UniformSpace.Completion.norm_coe direction.2)

theorem completedRobinLLJacobi_blocks_bounded
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (robin : ThroatScalarL2 period hPeriod
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    (ll : LLH1Space period hPeriod llData) :
    ‖robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) robin‖ ≤
      ‖robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ * ‖robin‖ ∧
    ‖P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D.completedLLJacobiOperator
        period hPeriod llData ll‖ = ‖ll‖ := by
  constructor
  · exact ContinuousLinearMap.le_opNorm _ _
  · rfl

theorem completedRobinLLJacobi_pairing_bound
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (firstRobin secondRobin : ThroatScalarL2 period hPeriod
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    (firstLL secondLL : LLH1Space period hPeriod llData) :
    |inner Real
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) firstRobin)
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) secondRobin) +
      inner Real firstLL secondLL| ≤
      (‖robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ ^ 2) *
          (‖firstRobin‖ * ‖secondRobin‖) + ‖firstLL‖ * ‖secondLL‖ := by
  have hTriangle := abs_add_le (inner Real
    (robinL2HessianOperator period hPeriod kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) firstRobin)
    (robinL2HessianOperator period hPeriod kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) secondRobin))
    (inner Real firstLL secondLL)
  have hRobinInner : |inner Real
      (robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) firstRobin)
      (robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) secondRobin)| ≤
      (‖robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ * ‖firstRobin‖) *
      (‖robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ * ‖secondRobin‖) := by
    calc
      _ ≤ ‖robinL2HessianOperator period hPeriod kPlus kMinus
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) firstRobin‖ *
          ‖robinL2HessianOperator period hPeriod kPlus kMinus
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) secondRobin‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul
        (ContinuousLinearMap.le_opNorm _ _)
        (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) (by positivity)
  have hLLInner : |inner Real firstLL secondLL| ≤ ‖firstLL‖ * ‖secondLL‖ :=
    abs_real_inner_le_norm _ _
  calc
    _ ≤ |inner Real
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) firstRobin)
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) secondRobin)| +
        |inner Real firstLL secondLL| := hTriangle
    _ ≤ (‖robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ * ‖firstRobin‖) *
        (‖robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ * ‖secondRobin‖) +
        ‖firstLL‖ * ‖secondLL‖ := add_le_add hRobinInner hLLInner
    _ = _ := by ring

private abbrev CompletedRobinLLSpace
    (llData : PositiveLLH1Data period hPeriod) :=
  ThroatScalarL2 period hPeriod (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
    LLH1Space period hPeriod llData

def completedRobinLLJacobiPairingBilinear
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    CompletedRobinLLSpace period hPeriod llData →ₗ[Real]
      CompletedRobinLLSpace period hPeriod llData →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun first second => inner Real
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first.1)
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) second.1) +
      inner Real first.2 second.2)
    (by intros; simp [inner_add_left, add_assoc, add_left_comm, add_comm])
    (by intros; simp [real_inner_smul_left, mul_add])
    (by intros; simp [inner_add_right, add_assoc, add_left_comm, add_comm])
    (by intros; simp [real_inner_smul_right, mul_add])

def completedRobinLLJacobiPairingContinuous
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    CompletedRobinLLSpace period hPeriod llData →L[Real]
      CompletedRobinLLSpace period hPeriod llData →L[Real] Real :=
  LinearMap.mkContinuous₂
    (completedRobinLLJacobiPairingBilinear period hPeriod kPlus kMinus llData)
    (‖robinL2HessianOperator period hPeriod kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ ^ 2 + 1) (by
      intro first second
      have hBase := completedRobinLLJacobi_pairing_bound period hPeriod kPlus kMinus
        llData first.1 second.1 first.2 second.2
      have hR : ‖first.1‖ * ‖second.1‖ ≤ ‖first‖ * ‖second‖ :=
        mul_le_mul (norm_fst_le first) (norm_fst_le second) (norm_nonneg _) (norm_nonneg _)
      have hLL : ‖first.2‖ * ‖second.2‖ ≤ ‖first‖ * ‖second‖ :=
        mul_le_mul (norm_snd_le first) (norm_snd_le second) (norm_nonneg _) (norm_nonneg _)
      change |inner Real
          (robinL2HessianOperator period hPeriod kPlus kMinus
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first.1)
          (robinL2HessianOperator period hPeriod kPlus kMinus
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) second.1) +
        inner Real first.2 second.2| ≤ _
      calc
        _ ≤ ‖robinL2HessianOperator period hPeriod kPlus kMinus
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ ^ 2 *
              (‖first.1‖ * ‖second.1‖) + ‖first.2‖ * ‖second.2‖ := hBase
        _ ≤ ‖robinL2HessianOperator period hPeriod kPlus kMinus
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ ^ 2 *
              (‖first‖ * ‖second‖) + ‖first‖ * ‖second‖ := by
          gcongr
        _ = (‖robinL2HessianOperator period hPeriod kPlus kMinus
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ ^ 2 + 1) *
              ‖first‖ * ‖second‖ := by ring)

@[simp] theorem completedRobinLLJacobiPairingContinuous_apply
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData) :
    completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData first second =
      inner Real
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first.1)
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) second.1) +
      inner Real first.2 second.2 := by
  rfl

theorem completedRobinLLJacobiPairingContinuous_bound
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData) :
    ‖completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
        first second‖ ≤
      (‖robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ ^ 2 + 1) *
        ‖first‖ * ‖second‖ := by
  rw [completedRobinLLJacobiPairingContinuous_apply, Real.norm_eq_abs]
  have hBase := completedRobinLLJacobi_pairing_bound period hPeriod kPlus kMinus llData
    first.1 second.1 first.2 second.2
  have hR : ‖first.1‖ * ‖second.1‖ ≤ ‖first‖ * ‖second‖ :=
    mul_le_mul (norm_fst_le first) (norm_fst_le second) (norm_nonneg _) (norm_nonneg _)
  have hLL : ‖first.2‖ * ‖second.2‖ ≤ ‖first‖ * ‖second‖ :=
    mul_le_mul (norm_snd_le first) (norm_snd_le second) (norm_nonneg _) (norm_nonneg _)
  calc
    _ ≤ ‖robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ ^ 2 *
          (‖first.1‖ * ‖second.1‖) + ‖first.2‖ * ‖second.2‖ := hBase
    _ ≤ ‖robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)‖ ^ 2 *
          (‖first‖ * ‖second‖) + ‖first‖ * ‖second‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_left hR (sq_nonneg _)) hLL
    _ = _ := by ring

theorem completedRobinLLJacobiPairingContinuous_symmetric
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData) :
    completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData first second =
      completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData second first := by
  rw [completedRobinLLJacobiPairingContinuous_apply,
    completedRobinLLJacobiPairingContinuous_apply]
  rw [real_inner_comm
      (robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first.1),
    real_inner_comm first.2]

theorem completedRobinLLJacobiPairingContinuous_nonneg
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData) :
    0 ≤ completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
      direction direction := by
  rw [completedRobinLLJacobiPairingContinuous_apply]
  exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg

theorem completedRobinLLJacobiPairingContinuous_diagonal_graphNorm
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData) :
    completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
        direction direction =
      ‖robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1‖ ^ 2 +
        ‖direction.2‖ ^ 2 := by
  rw [completedRobinLLJacobiPairingContinuous_apply,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem completedRobinLLJacobiPairingContinuous_diagonal_zero_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData) :
    completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
        direction direction = 0 ↔
      robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1 = 0 ∧
        direction.2 = 0 := by
  rw [completedRobinLLJacobiPairingContinuous_diagonal_graphNorm]
  constructor
  · intro hZero
    have hRobinNorm : ‖robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1‖ = 0 := by
      nlinarith [sq_nonneg ‖direction.2‖]
    have hLLNorm : ‖direction.2‖ = 0 := by
      nlinarith [sq_nonneg ‖robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1‖]
    exact ⟨norm_eq_zero.mp hRobinNorm, norm_eq_zero.mp hLLNorm⟩
  · rintro ⟨hRobin, hLL⟩
    simp [hRobin, hLL]

theorem completedRobinLLJacobiPairingContinuous_radical_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData) :
    (∀ other, completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
        direction other = 0) ↔
      robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1 = 0 ∧
        direction.2 = 0 := by
  constructor
  · intro hRadical
    exact (completedRobinLLJacobiPairingContinuous_diagonal_zero_iff period hPeriod
      kPlus kMinus llData direction).mp (hRadical direction)
  · rintro ⟨hRobin, hLL⟩ other
    rw [completedRobinLLJacobiPairingContinuous_apply]
    simp [hRobin, hLL]

theorem completedRobinLLJacobiPairingContinuous_rightRadical_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData) :
    (∀ other, completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
        other direction = 0) ↔
      robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1 = 0 ∧
        direction.2 = 0 := by
  constructor
  · intro hRight
    apply (completedRobinLLJacobiPairingContinuous_radical_iff period hPeriod
      kPlus kMinus llData direction).mp
    intro other
    rw [completedRobinLLJacobiPairingContinuous_symmetric]
    exact hRight other
  · intro hKernel other
    rw [completedRobinLLJacobiPairingContinuous_symmetric]
    exact (completedRobinLLJacobiPairingContinuous_radical_iff period hPeriod
      kPlus kMinus llData direction).mpr hKernel other

theorem completedRobinLLJacobiPairingContinuous_bilateralRadical_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData) :
    ((∀ other, completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
          direction other = 0) ∧
      (∀ other, completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
          other direction = 0)) ↔
      robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1 = 0 ∧
        direction.2 = 0 := by
  constructor
  · intro hBilateral
    exact (completedRobinLLJacobiPairingContinuous_radical_iff period hPeriod
      kPlus kMinus llData direction).mp hBilateral.1
  · intro hKernel
    exact ⟨
      (completedRobinLLJacobiPairingContinuous_radical_iff period hPeriod
        kPlus kMinus llData direction).mpr hKernel,
      (completedRobinLLJacobiPairingContinuous_rightRadical_iff period hPeriod
        kPlus kMinus llData direction).mpr hKernel⟩

def completedRobinLLJacobiBlockLinear
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    CompletedRobinLLSpace period hPeriod llData →ₗ[Real]
      CompletedRobinLLSpace period hPeriod llData where
  toFun direction :=
    (robinL2HessianOperator period hPeriod kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1, direction.2)
  map_add' first second := by ext <;> simp
  map_smul' scalar direction := by ext <;> simp

@[simp] theorem completedRobinLLJacobiBlockLinear_apply
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData) :
    completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData direction =
      (robinL2HessianOperator period hPeriod kPlus kMinus
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) direction.1, direction.2) := by
  rfl

def completedRobinLLJacobiRadical
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    Submodule Real (CompletedRobinLLSpace period hPeriod llData) :=
  LinearMap.ker (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData)

theorem mem_completedRobinLLJacobiRadical_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData) :
    direction ∈ completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData ↔
      ∀ other, completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
        direction other = 0 := by
  rw [completedRobinLLJacobiPairingContinuous_radical_iff]
  simp [completedRobinLLJacobiRadical, LinearMap.mem_ker]

noncomputable def completedRobinLLJacobiQuotientEquivRange
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    (CompletedRobinLLSpace period hPeriod llData ⧸
        completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) ≃ₗ[Real]
      LinearMap.range
        (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData) :=
  LinearMap.quotKerEquivRange
    (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData)

theorem mem_completedRobinLLJacobiBlockLinear_range_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (target : CompletedRobinLLSpace period hPeriod llData) :
    target ∈ LinearMap.range
        (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData) ↔
      target.1 ∈ LinearMap.range
        (robinL2HessianOperator period hPeriod kPlus kMinus
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).toLinearMap := by
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨source.1, rfl⟩
  · rintro ⟨sourceRobin, hSourceRobin⟩
    exact ⟨(sourceRobin, target.2), Prod.ext hSourceRobin rfl⟩

noncomputable def completedRobinLLJacobiQuotientPairing
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) : Real :=
  let equivalence := completedRobinLLJacobiQuotientEquivRange period hPeriod
    kPlus kMinus llData
  inner Real (equivalence first : CompletedRobinLLSpace period hPeriod llData).1
      (equivalence second : CompletedRobinLLSpace period hPeriod llData).1 +
    inner Real (equivalence first : CompletedRobinLLSpace period hPeriod llData).2
      (equivalence second : CompletedRobinLLSpace period hPeriod llData).2

@[simp] theorem completedRobinLLJacobiQuotientPairing_mk
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        (Submodule.Quotient.mk first) (Submodule.Quotient.mk second) =
      completedRobinLLJacobiPairingContinuous period hPeriod kPlus kMinus llData
        first second := by
  rfl

theorem completedRobinLLJacobiQuotientPairing_symmetric
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first second =
      completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData second first := by
  simp only [completedRobinLLJacobiQuotientPairing]
  rw [real_inner_comm
      ((completedRobinLLJacobiQuotientEquivRange period hPeriod kPlus kMinus llData first :
        LinearMap.range (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData)) :
          CompletedRobinLLSpace period hPeriod llData).1,
    real_inner_comm
      ((completedRobinLLJacobiQuotientEquivRange period hPeriod kPlus kMinus llData first :
        LinearMap.range (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData)) :
          CompletedRobinLLSpace period hPeriod llData).2]

theorem completedRobinLLJacobiQuotientPairing_nondegenerate
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    (∀ other, completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        direction other = 0) ↔ direction = 0 := by
  constructor
  · intro hRadical
    have hSelf := hRadical direction
    let image := completedRobinLLJacobiQuotientEquivRange period hPeriod
      kPlus kMinus llData direction
    have hNormSum : ‖(image : CompletedRobinLLSpace period hPeriod llData).1‖ ^ 2 +
        ‖(image : CompletedRobinLLSpace period hPeriod llData).2‖ ^ 2 = 0 := by
      simpa [completedRobinLLJacobiQuotientPairing, image,
        real_inner_self_eq_norm_sq] using hSelf
    have hFirst : ‖(image : CompletedRobinLLSpace period hPeriod llData).1‖ = 0 := by
      nlinarith [sq_nonneg ‖(image : CompletedRobinLLSpace period hPeriod llData).2‖]
    have hSecond : ‖(image : CompletedRobinLLSpace period hPeriod llData).2‖ = 0 := by
      nlinarith [sq_nonneg ‖(image : CompletedRobinLLSpace period hPeriod llData).1‖]
    have hImage : image = 0 := by
      apply Subtype.ext
      exact Prod.ext (norm_eq_zero.mp hFirst) (norm_eq_zero.mp hSecond)
    exact (completedRobinLLJacobiQuotientEquivRange period hPeriod
      kPlus kMinus llData).injective (by simpa [image] using hImage)
  · rintro rfl
    intro other
    simp [completedRobinLLJacobiQuotientPairing]

theorem completedRobinLLJacobiQuotientPairing_diagonal_rangeGraphNorm
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        direction direction =
      ‖((completedRobinLLJacobiQuotientEquivRange period hPeriod kPlus kMinus llData
          direction : LinearMap.range
            (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData)) :
          CompletedRobinLLSpace period hPeriod llData).1‖ ^ 2 +
        ‖((completedRobinLLJacobiQuotientEquivRange period hPeriod kPlus kMinus llData
          direction : LinearMap.range
            (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData)) :
          CompletedRobinLLSpace period hPeriod llData).2‖ ^ 2 := by
  simp [completedRobinLLJacobiQuotientPairing]

theorem completedRobinLLJacobiQuotientPairing_nonneg
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    0 ≤ completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      direction direction := by
  rw [completedRobinLLJacobiQuotientPairing_diagonal_rangeGraphNorm]
  positivity

theorem completedRobinLLJacobiQuotientPairing_diagonal_zero_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      direction direction = 0 ↔ direction = 0 := by
  constructor
  · intro hZero
    let image := completedRobinLLJacobiQuotientEquivRange period hPeriod
      kPlus kMinus llData direction
    have hNormSum : ‖(image : CompletedRobinLLSpace period hPeriod llData).1‖ ^ 2 +
        ‖(image : CompletedRobinLLSpace period hPeriod llData).2‖ ^ 2 = 0 := by
      simpa [image] using
        (completedRobinLLJacobiQuotientPairing_diagonal_rangeGraphNorm period hPeriod
          kPlus kMinus llData direction).symm.trans hZero
    have hFirst : (image : CompletedRobinLLSpace period hPeriod llData).1 = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(image : CompletedRobinLLSpace period hPeriod llData).2‖]
    have hSecond : (image : CompletedRobinLLSpace period hPeriod llData).2 = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(image : CompletedRobinLLSpace period hPeriod llData).1‖]
    have hImage : image = 0 := by
      apply Subtype.ext
      exact Prod.ext hFirst hSecond
    exact (completedRobinLLJacobiQuotientEquivRange period hPeriod
      kPlus kMinus llData).injective (by simpa [image] using hImage)
  · rintro rfl
    simp [completedRobinLLJacobiQuotientPairing]

noncomputable def completedRobinLLJacobiQuotientGraphNorm
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) : Real :=
  Real.sqrt (completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
    direction direction)

theorem completedRobinLLJacobiQuotientPairing_cauchySchwarz
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    |completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first second| ≤
      completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData first *
        completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData second := by
  let firstImage := completedRobinLLJacobiQuotientEquivRange period hPeriod
    kPlus kMinus llData first
  let secondImage := completedRobinLLJacobiQuotientEquivRange period hPeriod
    kPlus kMinus llData second
  let a := ‖(firstImage : CompletedRobinLLSpace period hPeriod llData).1‖
  let b := ‖(firstImage : CompletedRobinLLSpace period hPeriod llData).2‖
  let c := ‖(secondImage : CompletedRobinLLSpace period hPeriod llData).1‖
  let d := ‖(secondImage : CompletedRobinLLSpace period hPeriod llData).2‖
  have hPair : |completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      first second| ≤ a * c + b * d := by
    change |inner Real (firstImage : CompletedRobinLLSpace period hPeriod llData).1
        (secondImage : CompletedRobinLLSpace period hPeriod llData).1 +
      inner Real (firstImage : CompletedRobinLLSpace period hPeriod llData).2
        (secondImage : CompletedRobinLLSpace period hPeriod llData).2| ≤ _
    exact (abs_add_le _ _).trans (add_le_add
      (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
  have hab : 0 ≤ a * c + b * d := by positivity
  have hx : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hy : 0 ≤ c ^ 2 + d ^ 2 := by positivity
  have hsx : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 :=
    Real.sq_sqrt hx
  have hsy : Real.sqrt (c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 :=
    Real.sq_sqrt hy
  have hcs : a * c + b * d ≤
      Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
    have hsquare := sq_nonneg (a * d - b * c)
    have hsqrt : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  apply hPair.trans
  simpa [completedRobinLLJacobiQuotientGraphNorm,
    completedRobinLLJacobiQuotientPairing_diagonal_rangeGraphNorm,
    firstImage, secondImage, a, b, c, d] using hcs

theorem completedRobinLLJacobiQuotientGraphNorm_nonneg
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    0 ≤ completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
      direction := by
  exact Real.sqrt_nonneg _

theorem completedRobinLLJacobiQuotientGraphNorm_sq
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
        direction ^ 2 =
      completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        direction direction := by
  exact Real.sq_sqrt (completedRobinLLJacobiQuotientPairing_nonneg period hPeriod
    kPlus kMinus llData direction)

theorem completedRobinLLJacobiQuotientGraphNorm_eq_zero_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
      direction = 0 ↔ direction = 0 := by
  rw [completedRobinLLJacobiQuotientGraphNorm, Real.sqrt_eq_zero
    (completedRobinLLJacobiQuotientPairing_nonneg period hPeriod
      kPlus kMinus llData direction)]
  exact completedRobinLLJacobiQuotientPairing_diagonal_zero_iff period hPeriod
    kPlus kMinus llData direction

theorem completedRobinLLJacobiQuotientPairing_smul_smul
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (scalar : Real)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        (scalar • first) (scalar • second) =
      scalar ^ 2 * completedRobinLLJacobiQuotientPairing period hPeriod
        kPlus kMinus llData first second := by
  simp [completedRobinLLJacobiQuotientPairing, real_inner_smul_left,
    real_inner_smul_right, pow_two, mul_add, mul_assoc]

theorem completedRobinLLJacobiQuotientGraphNorm_smul
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (scalar : Real)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
        (scalar • direction) =
      |scalar| * completedRobinLLJacobiQuotientGraphNorm period hPeriod
        kPlus kMinus llData direction := by
  unfold completedRobinLLJacobiQuotientGraphNorm
  rw [completedRobinLLJacobiQuotientPairing_smul_smul]
  rw [Real.sqrt_mul (sq_nonneg scalar), Real.sqrt_sq_eq_abs]

theorem completedRobinLLJacobiQuotientPairing_add_diagonal
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        (first + second) (first + second) =
      completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first first +
        2 * completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
          first second +
        completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData second second := by
  unfold completedRobinLLJacobiQuotientPairing
  simp only [map_add, Submodule.coe_add, Prod.fst_add, Prod.snd_add,
    inner_add_left, inner_add_right]
  rw [real_inner_comm
      ((completedRobinLLJacobiQuotientEquivRange period hPeriod kPlus kMinus llData second :
        LinearMap.range (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData)) :
          CompletedRobinLLSpace period hPeriod llData).1,
    real_inner_comm
      ((completedRobinLLJacobiQuotientEquivRange period hPeriod kPlus kMinus llData second :
        LinearMap.range (completedRobinLLJacobiBlockLinear period hPeriod kPlus kMinus llData)) :
          CompletedRobinLLSpace period hPeriod llData).2]
  ring

theorem completedRobinLLJacobiQuotientGraphNorm_add_le
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
        (first + second) ≤
      completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData first +
        completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData second := by
  let nx := completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData first
  let ny := completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData second
  let nxy := completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
    (first + second)
  have hx0 : 0 ≤ nx := completedRobinLLJacobiQuotientGraphNorm_nonneg period hPeriod
    kPlus kMinus llData first
  have hy0 : 0 ≤ ny := completedRobinLLJacobiQuotientGraphNorm_nonneg period hPeriod
    kPlus kMinus llData second
  have hxy0 : 0 ≤ nxy := completedRobinLLJacobiQuotientGraphNorm_nonneg period hPeriod
    kPlus kMinus llData (first + second)
  have hCross := completedRobinLLJacobiQuotientPairing_cauchySchwarz period hPeriod
    kPlus kMinus llData first second
  have hCrossUpper : completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      first second ≤ nx * ny := by
    exact (le_abs_self _).trans hCross
  have hxSq := completedRobinLLJacobiQuotientGraphNorm_sq period hPeriod
    kPlus kMinus llData first
  have hySq := completedRobinLLJacobiQuotientGraphNorm_sq period hPeriod
    kPlus kMinus llData second
  have hxySq := completedRobinLLJacobiQuotientGraphNorm_sq period hPeriod
    kPlus kMinus llData (first + second)
  have hExpand := completedRobinLLJacobiQuotientPairing_add_diagonal period hPeriod
    kPlus kMinus llData first second
  change nxy ≤ nx + ny
  change nx ^ 2 = _ at hxSq
  change ny ^ 2 = _ at hySq
  change nxy ^ 2 = _ at hxySq
  nlinarith

noncomputable def completedRobinLLJacobiQuotientGraphSeminorm
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    Seminorm Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :=
  Seminorm.ofSMulLE
    (completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData)
    ((completedRobinLLJacobiQuotientGraphNorm_eq_zero_iff period hPeriod
      kPlus kMinus llData 0).mpr rfl)
    (completedRobinLLJacobiQuotientGraphNorm_add_le period hPeriod kPlus kMinus llData)
    (by
      intro scalar direction
      rw [completedRobinLLJacobiQuotientGraphNorm_smul, Real.norm_eq_abs])

@[simp] theorem completedRobinLLJacobiQuotientGraphSeminorm_apply
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientGraphSeminorm period hPeriod kPlus kMinus llData direction =
      completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData direction := by
  rfl

theorem completedRobinLLJacobiQuotientGraphSeminorm_eq_zero_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientGraphSeminorm period hPeriod kPlus kMinus llData direction = 0 ↔
      direction = 0 := by
  rw [completedRobinLLJacobiQuotientGraphSeminorm_apply]
  exact completedRobinLLJacobiQuotientGraphNorm_eq_zero_iff period hPeriod
    kPlus kMinus llData direction

abbrev CompletedRobinLLJacobiGraphNormedQuotient
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :=
  CompletedRobinLLSpace period hPeriod llData ⧸
    completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData

noncomputable def completedRobinLLJacobiQuotientGraphAddGroupNorm
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    AddGroupNorm (CompletedRobinLLJacobiGraphNormedQuotient period hPeriod
      kPlus kMinus llData) where
  toAddGroupSeminorm :=
    (completedRobinLLJacobiQuotientGraphSeminorm period hPeriod
      kPlus kMinus llData).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' direction hZero :=
    (completedRobinLLJacobiQuotientGraphSeminorm_eq_zero_iff period hPeriod
      kPlus kMinus llData direction).mp hZero

noncomputable abbrev completedRobinLLJacobiQuotientGraphNormedAddCommGroup
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    NormedAddCommGroup (CompletedRobinLLJacobiGraphNormedQuotient period hPeriod
      kPlus kMinus llData) :=
  (completedRobinLLJacobiQuotientGraphAddGroupNorm period hPeriod
    kPlus kMinus llData).toNormedAddCommGroup

theorem completedRobinLLJacobiQuotientGraphNormed_norm_eq
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLJacobiGraphNormedQuotient period hPeriod
      kPlus kMinus llData) :
    letI := completedRobinLLJacobiQuotientGraphNormedAddCommGroup period hPeriod
      kPlus kMinus llData
    ‖direction‖ = completedRobinLLJacobiQuotientGraphNorm period hPeriod
      kPlus kMinus llData direction := by
  rfl

noncomputable def completedRobinLLJacobiGraphNormedPairing
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLJacobiGraphNormedQuotient period hPeriod
      kPlus kMinus llData) : Real :=
  completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first second

theorem completedRobinLLJacobiGraphNormedPairing_bound
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLJacobiGraphNormedQuotient period hPeriod
      kPlus kMinus llData) :
    letI := completedRobinLLJacobiQuotientGraphNormedAddCommGroup period hPeriod
      kPlus kMinus llData
    |completedRobinLLJacobiGraphNormedPairing period hPeriod kPlus kMinus llData
        first second| ≤ ‖first‖ * ‖second‖ := by
  letI := completedRobinLLJacobiQuotientGraphNormedAddCommGroup period hPeriod
    kPlus kMinus llData
  change |completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      first second| ≤
    completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData first *
      completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData second
  exact completedRobinLLJacobiQuotientPairing_cauchySchwarz period hPeriod
    kPlus kMinus llData first second

theorem completedRobinLLJacobiGraphNormedPairing_symmetric
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLJacobiGraphNormedQuotient period hPeriod
      kPlus kMinus llData) :
    completedRobinLLJacobiGraphNormedPairing period hPeriod kPlus kMinus llData first second =
      completedRobinLLJacobiGraphNormedPairing period hPeriod kPlus kMinus llData second first := by
  exact completedRobinLLJacobiQuotientPairing_symmetric period hPeriod
    kPlus kMinus llData first second

theorem completedRobinLLJacobiQuotientPairing_neg_second
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first (-second) =
      -completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first second := by
  simp [completedRobinLLJacobiQuotientPairing]
  ring

theorem completedRobinLLJacobiQuotientPairing_sub_diagonal
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        (first - second) (first - second) =
      completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first first -
        2 * completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
          first second +
        completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData second second := by
  rw [sub_eq_add_neg, completedRobinLLJacobiQuotientPairing_add_diagonal,
    completedRobinLLJacobiQuotientPairing_neg_second]
  have hNeg := completedRobinLLJacobiQuotientPairing_smul_smul period hPeriod
    kPlus kMinus llData (-1) second second
  simp only [neg_one_smul, neg_sq] at hNeg
  rw [hNeg]
  ring

theorem completedRobinLLJacobiQuotientGraphNorm_parallelogram
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
          (first + second) ^ 2 +
        completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
          (first - second) ^ 2 =
      2 * completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData first ^ 2 +
        2 * completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData second ^ 2 := by
  rw [completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientPairing_add_diagonal,
    completedRobinLLJacobiQuotientPairing_sub_diagonal]
  ring

theorem completedRobinLLJacobiQuotientPairing_polarization
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first second =
      (completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
          (first + second) ^ 2 -
        completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
          (first - second) ^ 2) / 4 := by
  rw [completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientPairing_add_diagonal,
    completedRobinLLJacobiQuotientPairing_sub_diagonal]
  ring

def CompletedRobinLLJacobiQuotientOrthogonal
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) : Prop :=
  completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first second = 0

theorem completedRobinLLJacobiQuotientOrthogonal_symmetric
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    CompletedRobinLLJacobiQuotientOrthogonal period hPeriod kPlus kMinus llData first second ↔
      CompletedRobinLLJacobiQuotientOrthogonal period hPeriod kPlus kMinus llData second first := by
  unfold CompletedRobinLLJacobiQuotientOrthogonal
  rw [completedRobinLLJacobiQuotientPairing_symmetric]

theorem completedRobinLLJacobiQuotientGraphNorm_pythagorean_add
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)
    (hOrthogonal : CompletedRobinLLJacobiQuotientOrthogonal period hPeriod
      kPlus kMinus llData first second) :
    completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
        (first + second) ^ 2 =
      completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData first ^ 2 +
        completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData second ^ 2 := by
  rw [completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientPairing_add_diagonal]
  rw [show completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
    first second = 0 from hOrthogonal]
  ring

theorem completedRobinLLJacobiQuotientGraphNorm_pythagorean_sub
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)
    (hOrthogonal : CompletedRobinLLJacobiQuotientOrthogonal period hPeriod
      kPlus kMinus llData first second) :
    completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData
        (first - second) ^ 2 =
      completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData first ^ 2 +
        completedRobinLLJacobiQuotientGraphNorm period hPeriod kPlus kMinus llData second ^ 2 := by
  rw [completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientGraphNorm_sq,
    completedRobinLLJacobiQuotientPairing_sub_diagonal]
  rw [show completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
    first second = 0 from hOrthogonal]
  ring

theorem completedRobinLLJacobiQuotientPairing_add_left
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second other : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        (first + second) other =
      completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData first other +
        completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData second other := by
  unfold completedRobinLLJacobiQuotientPairing
  simp only [map_add, Submodule.coe_add, Prod.fst_add, Prod.snd_add, inner_add_left]
  ring

theorem completedRobinLLJacobiQuotientPairing_smul_left
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (scalar : Real)
    (direction other : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        (scalar • direction) other =
      scalar * completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        direction other := by
  unfold completedRobinLLJacobiQuotientPairing
  simp [real_inner_smul_left, mul_add]

def completedRobinLLJacobiQuotientOrthogonalSubmodule
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) where
  carrier := {other | completedRobinLLJacobiQuotientPairing period hPeriod
    kPlus kMinus llData other direction = 0}
  zero_mem' := by simp [completedRobinLLJacobiQuotientPairing]
  add_mem' := by
    intro first second hFirst hSecond
    change completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      (first + second) direction = 0
    change completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      first direction = 0 at hFirst
    change completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      second direction = 0 at hSecond
    rw [completedRobinLLJacobiQuotientPairing_add_left, hFirst, hSecond, add_zero]
  smul_mem' := by
    intro scalar other hOther
    change completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      (scalar • other) direction = 0
    change completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      other direction = 0 at hOther
    rw [completedRobinLLJacobiQuotientPairing_smul_left, hOther, mul_zero]

@[simp] theorem mem_completedRobinLLJacobiQuotientOrthogonalSubmodule_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction other : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    other ∈ completedRobinLLJacobiQuotientOrthogonalSubmodule period hPeriod
      kPlus kMinus llData direction ↔
      completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        other direction = 0 := by
  rfl

theorem completedRobinLLJacobiQuotient_self_mem_orthogonal_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    direction ∈ completedRobinLLJacobiQuotientOrthogonalSubmodule period hPeriod
      kPlus kMinus llData direction ↔ direction = 0 := by
  rw [mem_completedRobinLLJacobiQuotientOrthogonalSubmodule_iff,
    completedRobinLLJacobiQuotientPairing_diagonal_zero_iff]

theorem completedRobinLLJacobiQuotientOrthogonalSubmodule_zero
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    completedRobinLLJacobiQuotientOrthogonalSubmodule period hPeriod
      kPlus kMinus llData 0 = ⊤ := by
  ext other
  simp [completedRobinLLJacobiQuotientPairing]

def completedRobinLLJacobiQuotientSubmoduleOrthogonal
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) where
  carrier := {other | ∀ direction ∈ source,
    completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
      other direction = 0}
  zero_mem' := by simp [completedRobinLLJacobiQuotientPairing]
  add_mem' := by
    intro first second hFirst hSecond direction hDirection
    rw [completedRobinLLJacobiQuotientPairing_add_left,
      hFirst direction hDirection, hSecond direction hDirection, add_zero]
  smul_mem' := by
    intro scalar other hOther direction hDirection
    rw [completedRobinLLJacobiQuotientPairing_smul_left,
      hOther direction hDirection, mul_zero]

theorem completedRobinLLJacobiQuotientSubmoduleOrthogonal_antitone
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    {smaller larger : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)}
    (hInclusion : smaller ≤ larger) :
    completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod kPlus kMinus llData
        larger ≤
      completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod kPlus kMinus llData
        smaller := by
  intro other hOther direction hDirection
  exact hOther direction (hInclusion hDirection)

theorem iInf_completedRobinLLJacobiQuotientOrthogonalSubmodule_eq_bot
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    (⨅ direction, completedRobinLLJacobiQuotientOrthogonalSubmodule period hPeriod
      kPlus kMinus llData direction) = ⊥ := by
  apply le_antisymm
  · intro direction hAll
    have hSelf : direction ∈ completedRobinLLJacobiQuotientOrthogonalSubmodule period hPeriod
        kPlus kMinus llData direction := by
      exact (iInf_le
        (fun other => completedRobinLLJacobiQuotientOrthogonalSubmodule period hPeriod
          kPlus kMinus llData other) direction) hAll
    have hZero := (completedRobinLLJacobiQuotient_self_mem_orthogonal_iff period hPeriod
      kPlus kMinus llData direction).mp hSelf
    simpa [hZero]
  · exact bot_le

theorem completedRobinLLJacobiQuotientOrthogonalSubmodule_lt_top
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)
    (hDirection : direction ≠ 0) :
    completedRobinLLJacobiQuotientOrthogonalSubmodule period hPeriod
      kPlus kMinus llData direction < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro hTop
  have hSelf : direction ∈ completedRobinLLJacobiQuotientOrthogonalSubmodule period hPeriod
      kPlus kMinus llData direction := by
    rw [hTop]
    exact Submodule.mem_top
  exact hDirection ((completedRobinLLJacobiQuotient_self_mem_orthogonal_iff period hPeriod
    kPlus kMinus llData direction).mp hSelf)

def completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :=
  completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod kPlus kMinus llData
    (completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod kPlus kMinus llData source)

theorem completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    source ≤ completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
      kPlus kMinus llData source := by
  intro direction hDirection other hOther
  rw [completedRobinLLJacobiQuotientPairing_symmetric]
  exact hOther direction hDirection

theorem completedRobinLLJacobiQuotient_span_le_doubleOrthogonal
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (direction : CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :
    Submodule.span Real {direction} ≤
      completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
        kPlus kMinus llData (Submodule.span Real {direction}) :=
  completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal period hPeriod
    kPlus kMinus llData (Submodule.span Real {direction})

theorem completedRobinLLJacobiQuotientSubmoduleOrthogonal_top
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod
      kPlus kMinus llData ⊤ = ⊥ := by
  apply le_antisymm
  · intro direction hOrthogonal
    have hSelf : completedRobinLLJacobiQuotientPairing period hPeriod kPlus kMinus llData
        direction direction = 0 := hOrthogonal direction Submodule.mem_top
    have hZero := (completedRobinLLJacobiQuotientPairing_diagonal_zero_iff period hPeriod
      kPlus kMinus llData direction).mp hSelf
    simpa [hZero]
  · exact bot_le

theorem completedRobinLLJacobiQuotientSubmoduleOrthogonal_galois
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    first ≤ completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod
        kPlus kMinus llData second ↔
      second ≤ completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod
        kPlus kMinus llData first := by
  constructor
  · intro hFirst direction hDirection other hOther
    rw [completedRobinLLJacobiQuotientPairing_symmetric]
    exact (hFirst hOther) direction hDirection
  · intro hSecond direction hDirection other hOther
    rw [completedRobinLLJacobiQuotientPairing_symmetric]
    exact (hSecond hOther) direction hDirection

theorem completedRobinLLJacobiQuotientSubmodule_tripleOrthogonal
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod kPlus kMinus llData
        (completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
          kPlus kMinus llData source) =
      completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod
        kPlus kMinus llData source := by
  apply le_antisymm
  · exact completedRobinLLJacobiQuotientSubmoduleOrthogonal_antitone period hPeriod
      kPlus kMinus llData
      (completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal period hPeriod
        kPlus kMinus llData source)
  · exact completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal period hPeriod
      kPlus kMinus llData
      (completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod
        kPlus kMinus llData source)

theorem completedRobinLLJacobiQuotientSubmodule_doubleOrthogonal_idempotent
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
        kPlus kMinus llData
        (completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
          kPlus kMinus llData source) =
      completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
        kPlus kMinus llData source := by
  unfold completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal
  exact congrArg
    (completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod kPlus kMinus llData)
    (completedRobinLLJacobiQuotientSubmodule_tripleOrthogonal period hPeriod
      kPlus kMinus llData source)

def CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) : Prop :=
  completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
    kPlus kMinus llData source = source

theorem completedRobinLLJacobiQuotient_orthogonal_isOrthogonallyClosed
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData
      (completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod
        kPlus kMinus llData source) := by
  exact completedRobinLLJacobiQuotientSubmodule_tripleOrthogonal period hPeriod
    kPlus kMinus llData source

theorem completedRobinLLJacobiQuotient_doubleOrthogonal_isOrthogonallyClosed
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData
      (completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
        kPlus kMinus llData source) := by
  exact completedRobinLLJacobiQuotientSubmodule_doubleOrthogonal_idempotent period hPeriod
    kPlus kMinus llData source

theorem completedRobinLLJacobiQuotient_doubleOrthogonal_le_of_le_closed
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    {source target : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)}
    (hInclusion : source ≤ target)
    (hClosed : CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData target) :
    completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
      kPlus kMinus llData source ≤ target := by
  have hFirst := completedRobinLLJacobiQuotientSubmoduleOrthogonal_antitone period hPeriod
    kPlus kMinus llData hInclusion
  have hSecond := completedRobinLLJacobiQuotientSubmoduleOrthogonal_antitone period hPeriod
    kPlus kMinus llData hFirst
  change completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
    kPlus kMinus llData target = target at hClosed
  change completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
      kPlus kMinus llData source ≤
    completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
      kPlus kMinus llData target at hSecond
  exact hSecond.trans_eq hClosed

theorem completedRobinLLJacobiQuotientSubmodule_doubleOrthogonal_monotone
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    Monotone (completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
      kPlus kMinus llData) := by
  intro first second hInclusion
  have hFirst := completedRobinLLJacobiQuotientSubmoduleOrthogonal_antitone period hPeriod
    kPlus kMinus llData hInclusion
  exact completedRobinLLJacobiQuotientSubmoduleOrthogonal_antitone period hPeriod
    kPlus kMinus llData hFirst

def completedRobinLLJacobiQuotientOrthogonalClosureOperator
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    ClosureOperator (Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) where
  toFun := completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
    kPlus kMinus llData
  monotone' := completedRobinLLJacobiQuotientSubmodule_doubleOrthogonal_monotone period hPeriod
    kPlus kMinus llData
  le_closure' := completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal period hPeriod
    kPlus kMinus llData
  idempotent' := completedRobinLLJacobiQuotientSubmodule_doubleOrthogonal_idempotent period hPeriod
    kPlus kMinus llData

theorem completedRobinLLJacobiQuotientOrthogonalClosureOperator_isClosed_iff
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (source : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    (completedRobinLLJacobiQuotientOrthogonalClosureOperator period hPeriod
        kPlus kMinus llData).IsClosed source ↔
      CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
        kPlus kMinus llData source := by
  rw [ClosureOperator.isClosed_iff]
  rfl

theorem completedRobinLLJacobiQuotientSubmoduleOrthogonal_bot
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    completedRobinLLJacobiQuotientSubmoduleOrthogonal period hPeriod
      kPlus kMinus llData ⊥ = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro direction _ other hOther
    have hOtherZero : other = 0 := hOther
    subst other
    simp [completedRobinLLJacobiQuotientPairing]

theorem completedRobinLLJacobiQuotientOrthogonalClosureOperator_bot
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    completedRobinLLJacobiQuotientOrthogonalClosureOperator period hPeriod
      kPlus kMinus llData ⊥ = ⊥ := by
  change completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
    kPlus kMinus llData ⊥ = ⊥
  unfold completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal
  rw [completedRobinLLJacobiQuotientSubmoduleOrthogonal_bot,
    completedRobinLLJacobiQuotientSubmoduleOrthogonal_top]

theorem completedRobinLLJacobiQuotientOrthogonalClosureOperator_top
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod) :
    completedRobinLLJacobiQuotientOrthogonalClosureOperator period hPeriod
      kPlus kMinus llData ⊤ = ⊤ := by
  change completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
    kPlus kMinus llData ⊤ = ⊤
  unfold completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal
  rw [completedRobinLLJacobiQuotientSubmoduleOrthogonal_top,
    completedRobinLLJacobiQuotientSubmoduleOrthogonal_bot]

theorem completedRobinLLJacobiQuotient_iInf_isOrthogonallyClosed
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    {index : Sort*}
    (family : index → Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData))
    (hClosed : ∀ i, CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed
      period hPeriod kPlus kMinus llData (family i)) :
    CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData (⨅ i, family i) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    exact completedRobinLLJacobiQuotient_doubleOrthogonal_le_of_le_closed period hPeriod
      kPlus kMinus llData (iInf_le family i) (hClosed i)
  · exact completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal period hPeriod
      kPlus kMinus llData (⨅ i, family i)

def completedRobinLLJacobiQuotientClosedISup
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    {index : Sort*}
    (family : index → Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :=
  completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
    kPlus kMinus llData (⨆ i, family i)

theorem completedRobinLLJacobiQuotientClosedISup_isOrthogonallyClosed
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    {index : Sort*}
    (family : index → Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData
      (completedRobinLLJacobiQuotientClosedISup period hPeriod kPlus kMinus llData family) :=
  completedRobinLLJacobiQuotient_doubleOrthogonal_isOrthogonallyClosed period hPeriod
    kPlus kMinus llData (⨆ i, family i)

theorem completedRobinLLJacobiQuotient_le_closedISup
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    {index : Sort*}
    (family : index → Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData))
    (i : index) :
    family i ≤ completedRobinLLJacobiQuotientClosedISup period hPeriod
      kPlus kMinus llData family := by
  exact (le_iSup family i).trans
    (completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal period hPeriod
      kPlus kMinus llData (⨆ j, family j))

theorem completedRobinLLJacobiQuotientClosedISup_le_of_closed_upperBound
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    {index : Sort*}
    (family : index → Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData))
    (target : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData))
    (hTargetClosed : CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed
      period hPeriod kPlus kMinus llData target)
    (hUpper : ∀ i, family i ≤ target) :
    completedRobinLLJacobiQuotientClosedISup period hPeriod kPlus kMinus llData family ≤
      target := by
  apply completedRobinLLJacobiQuotient_doubleOrthogonal_le_of_le_closed period hPeriod
    kPlus kMinus llData (iSup_le hUpper) hTargetClosed

def completedRobinLLJacobiQuotientClosedSup
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData) :=
  completedRobinLLJacobiQuotientSubmoduleDoubleOrthogonal period hPeriod
    kPlus kMinus llData (first ⊔ second)

theorem completedRobinLLJacobiQuotientClosedSup_comm
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData)) :
    completedRobinLLJacobiQuotientClosedSup period hPeriod kPlus kMinus llData first second =
      completedRobinLLJacobiQuotientClosedSup period hPeriod kPlus kMinus llData second first := by
  unfold completedRobinLLJacobiQuotientClosedSup
  rw [sup_comm]

theorem completedRobinLLJacobiQuotient_inf_isOrthogonallyClosed
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData))
    (hFirst : CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData first)
    (hSecond : CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData second) :
    CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData (first ⊓ second) := by
  apply le_antisymm
  · exact le_inf
      (completedRobinLLJacobiQuotient_doubleOrthogonal_le_of_le_closed period hPeriod
        kPlus kMinus llData inf_le_left hFirst)
      (completedRobinLLJacobiQuotient_doubleOrthogonal_le_of_le_closed period hPeriod
        kPlus kMinus llData inf_le_right hSecond)
  · exact completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal period hPeriod
      kPlus kMinus llData (first ⊓ second)

theorem completedRobinLLJacobiQuotientClosedSup_inf_absorb
    (kPlus kMinus : Real) (llData : PositiveLLH1Data period hPeriod)
    (first second : Submodule Real (CompletedRobinLLSpace period hPeriod llData ⧸
      completedRobinLLJacobiRadical period hPeriod kPlus kMinus llData))
    (hFirst : CompletedRobinLLJacobiQuotientSubmoduleIsOrthogonallyClosed period hPeriod
      kPlus kMinus llData first) :
    completedRobinLLJacobiQuotientClosedSup period hPeriod kPlus kMinus llData
      first (first ⊓ second) = first := by
  apply le_antisymm
  · apply completedRobinLLJacobiQuotient_doubleOrthogonal_le_of_le_closed period hPeriod
      kPlus kMinus llData _ hFirst
    exact sup_le le_rfl inf_le_left
  · exact le_trans le_sup_left
      (completedRobinLLJacobiQuotientSubmodule_le_doubleOrthogonal period hPeriod
        kPlus kMinus llData (first ⊔ first ⊓ second))

end
end P0EFTJanusMatterRobinFullLLCanonicalKernelActiveQuotientZero4D
end JanusFormal
