import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanKoszulConnectionExistence

/-!
# Pointwise throat Koszul candidate from the actual metric jet

At one genuine throat point, sectorwise transversality implies that each
induced Candidate-A metric is nondegenerate.  Its framed value and actual
first derivative are transported through the public throat/`EuclideanR3`
equivalence before applying the Riesz and Koszul constructions.  The metric
slots of the transported derivative are symmetrized explicitly.

The result is only a pointwise Koszul candidate from the symmetrized,
transported actual one-jet, conditional on `HasNoTangentialRadical`.  This
gate proves neither equality of the symmetrized derivative with the raw
transported derivative nor identification of the candidate with a
Levi--Civita connection.  It also proves no chart-overlap law, smooth
dependence on the point, or descent to a global connection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff InnerProductSpace RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusEuclideanMetricKoszulConnection
open P0EFTJanusEuclideanKoszulConnectionExistence

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatMetricTensorNormedAddCommGroup :
    NormedAddCommGroup
      (FramedCovariantTwoTensor ThroatCoverCoordinates) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance throatMetricTensorNormedSpace :
    NormedSpace Real (FramedCovariantTwoTensor ThroatCoverCoordinates) :=
  ContinuousLinearMap.toNormedSpace

local instance euclideanCovectorNormedAddCommGroup :
    NormedAddCommGroup (EuclideanR3 →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanCovectorNormedSpace :
    NormedSpace Real (EuclideanR3 →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

local instance throatMetricDerivativeNormedAddCommGroup :
    NormedAddCommGroup
      (ThroatCoverCoordinates →L[Real]
        FramedCovariantTwoTensor ThroatCoverCoordinates) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance throatMetricDerivativeNormedSpace :
    NormedSpace Real
      (ThroatCoverCoordinates →L[Real]
        FramedCovariantTwoTensor ThroatCoverCoordinates) :=
  ContinuousLinearMap.toNormedSpace

local instance euclideanMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (ContinuousMetricTensor EuclideanR3) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanMetricTensorNormedSpace :
    NormedSpace Real (ContinuousMetricTensor EuclideanR3) :=
  ContinuousLinearMap.toNormedSpace

local instance euclideanMetricDerivativeNormedAddCommGroup :
    NormedAddCommGroup
      (ContinuousMetricDerivativeTensor (Model := EuclideanR3)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanMetricDerivativeNormedSpace :
    NormedSpace Real
      (ContinuousMetricDerivativeTensor (Model := EuclideanR3)) :=
  ContinuousLinearMap.toNormedSpace

local instance euclideanTangentialQuadraticNormedAddCommGroup :
    NormedAddCommGroup (ContinuousTangentialQuadratic EuclideanR3) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanTangentialQuadraticNormedSpace :
    NormedSpace Real (ContinuousTangentialQuadratic EuclideanR3) :=
  ContinuousLinearMap.toNormedSpace

/-! ## Pointwise nondegeneracy -/

/-- Sectorwise transversality is exactly intrinsic nondegeneracy of the
corresponding induced throat metric. -/
theorem globalGaugeFixedInducedMetricBySector_injective_at_of_transverse
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) :
    Function.Injective
      ((globalGaugeFixedInducedMetricBySector
        period hPeriod configuration sector).tensor base) := by
  cases sector with
  | plus =>
      simpa [globalGaugeFixedInducedMetricBySector,
        globalGaugeFixedBulkMetricBySector] using
        (((throatTrace_nondegenerate_iff_no_tangential_radical
          period hPeriod configuration.physical.geometry.plusMetric).2
            (hTransverse .plus)) base)
  | minus =>
      simpa [globalGaugeFixedInducedMetricBySector,
        globalGaugeFixedBulkMetricBySector] using
        (((throatTrace_nondegenerate_iff_no_tangential_radical
          period hPeriod configuration.physical.geometry.minusMetric).2
            (hTransverse .minus)) base)

/-- Assuming transversality, the actual framed metric value is nondegenerate
at the selected point. -/
theorem globalGaugeFixedThroatMetricSecondOrderJetAt_value_injective_of_transverse
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) :
    Function.Injective
      (globalGaugeFixedThroatMetricSecondOrderJetAt
        period hPeriod configuration sector base).value := by
  let hBase : base ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base
  let tangentEquiv :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base).continuousLinearEquivAt
        Real base hBase
  intro first second hEqual
  apply tangentEquiv.symm.injective
  apply globalGaugeFixedInducedMetricBySector_injective_at_of_transverse
    period hPeriod configuration base hTransverse sector
  apply ContinuousLinearMap.ext
  intro tangent
  have hEvaluate := congrArg
    (fun covector => covector (tangentEquiv tangent)) hEqual
  simpa [tangentEquiv, hBase] using hEvaluate

/-! ## Transported metric jet and Riesz inversion -/

/-- Fixed transport of covariant two-tensors, using the same public split as
the actual throat Abelian jets. -/
def throatMetricTensorToEuclideanEquiv :
    FramedCovariantTwoTensor ThroatCoverCoordinates ≃L[Real]
      ContinuousMetricTensor EuclideanR3 :=
  throatToEuclideanEquiv.arrowCongr
    (throatToEuclideanEquiv.arrowCongr
      (ContinuousLinearEquiv.refl Real Real))

/-- Fixed transport of first metric derivatives. -/
def throatMetricDerivativeToEuclideanEquiv :
    (ThroatCoverCoordinates →L[Real]
        FramedCovariantTwoTensor ThroatCoverCoordinates) ≃L[Real]
      ContinuousMetricDerivativeTensor (Model := EuclideanR3) :=
  throatToEuclideanEquiv.arrowCongr throatMetricTensorToEuclideanEquiv

/-- Actual induced metric value in the physical Euclidean frame. -/
def globalGaugeFixedThroatMetricEuclideanValueAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod) (sector : Sector) :
    ContinuousMetricTensor EuclideanR3 :=
  throatMetricTensorToEuclideanEquiv
    (globalGaugeFixedThroatMetricSecondOrderJetAt
      period hPeriod configuration sector base).value

@[simp]
theorem globalGaugeFixedThroatMetricEuclideanValueAt_apply
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod) (sector : Sector)
    (first second : EuclideanR3) :
    globalGaugeFixedThroatMetricEuclideanValueAt
        period hPeriod configuration base sector first second =
      (globalGaugeFixedThroatMetricSecondOrderJetAt
        period hPeriod configuration sector base).value
          (throatRadialReferenceEquiv first)
          (throatRadialReferenceEquiv second) :=
  rfl

/-- Actual first metric derivative in the physical Euclidean frame. -/
def globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod) (sector : Sector) :
    ContinuousMetricDerivativeTensor (Model := EuclideanR3) :=
  throatMetricDerivativeToEuclideanEquiv
    (globalGaugeFixedThroatMetricSecondOrderJetAt
      period hPeriod configuration sector base).firstDerivative

@[simp]
theorem globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt_apply
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod) (sector : Sector)
    (direction first second : EuclideanR3) :
    globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
        period hPeriod configuration base sector direction first second =
      (globalGaugeFixedThroatMetricSecondOrderJetAt
        period hPeriod configuration sector base).firstDerivative
          (throatRadialReferenceEquiv direction)
          (throatRadialReferenceEquiv first)
          (throatRadialReferenceEquiv second) := by
  simp [globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt,
    throatMetricDerivativeToEuclideanEquiv,
    throatMetricTensorToEuclideanEquiv, throatToEuclideanEquiv]

theorem globalGaugeFixedThroatMetricEuclideanValueAt_injective_of_transverse
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) :
    Function.Injective
      (globalGaugeFixedThroatMetricEuclideanValueAt
        period hPeriod configuration base sector) := by
  intro first second hEqual
  apply throatRadialReferenceEquiv.injective
  apply globalGaugeFixedThroatMetricSecondOrderJetAt_value_injective_of_transverse
    period hPeriod configuration base hTransverse sector
  apply ContinuousLinearMap.ext
  intro test
  have hEvaluate := congrArg
    (fun covector => covector (throatToEuclideanEquiv test)) hEqual
  simpa [throatToEuclideanEquiv] using hEvaluate

/-- Riesz operator of the transported actual induced metric. -/
def globalGaugeFixedThroatMetricEuclideanRieszOperatorAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod) (sector : Sector) :
    EuclideanR3 →L[Real] EuclideanR3 :=
  metricRieszOperatorCLM (Model := EuclideanR3)
    (globalGaugeFixedThroatMetricEuclideanValueAt
      period hPeriod configuration base sector)

theorem globalGaugeFixedThroatMetricEuclideanRieszOperatorAt_injective_of_transverse
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) :
    Function.Injective
      (globalGaugeFixedThroatMetricEuclideanRieszOperatorAt
        period hPeriod configuration base sector) := by
  intro first second hEqual
  apply globalGaugeFixedThroatMetricEuclideanValueAt_injective_of_transverse
    period hPeriod configuration base hTransverse sector
  apply ContinuousLinearMap.ext
  intro test
  have hPairing := congrArg (fun vector => ⟪vector, test⟫_ℝ) hEqual
  simpa [globalGaugeFixedThroatMetricEuclideanRieszOperatorAt] using hPairing

/-- Finite-dimensional inverse of the transported metric Riesz operator. -/
def globalGaugeFixedThroatMetricEuclideanRieszEquivAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) : EuclideanR3 ≃L[Real] EuclideanR3 :=
  (LinearEquiv.ofInjectiveEndo
    (globalGaugeFixedThroatMetricEuclideanRieszOperatorAt
      period hPeriod configuration base sector).toLinearMap
    (globalGaugeFixedThroatMetricEuclideanRieszOperatorAt_injective_of_transverse
      period hPeriod configuration base hTransverse sector)).toContinuousLinearEquiv

@[simp]
theorem coe_globalGaugeFixedThroatMetricEuclideanRieszEquivAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) :
    (globalGaugeFixedThroatMetricEuclideanRieszEquivAt
      period hPeriod configuration base hTransverse sector :
        EuclideanR3 →L[Real] EuclideanR3) =
      globalGaugeFixedThroatMetricEuclideanRieszOperatorAt
        period hPeriod configuration base sector := by
  ext vector
  rfl

/-! ## Pointwise Euclidean Koszul connection -/

/-- Explicit symmetrization of the two covariant metric slots. -/
def symmetrizedThroatMetricEuclideanDerivative
    (derivative : ContinuousMetricDerivativeTensor
      (Model := EuclideanR3)) :
    ContinuousMetricDerivativeTensor (Model := EuclideanR3) :=
  (2 : Real)⁻¹ •
    (derivative + swapSecondThirdCLM (Model := EuclideanR3) derivative)

@[simp]
theorem swapSecondThirdCLM_euclidean_apply
    (derivative : ContinuousMetricDerivativeTensor
      (Model := EuclideanR3))
    (direction first second : EuclideanR3) :
    swapSecondThirdCLM (Model := EuclideanR3) derivative
        direction first second =
      derivative direction second first :=
  rfl

theorem symmetrizedThroatMetricEuclideanDerivative_symmetric
    (derivative : ContinuousMetricDerivativeTensor
      (Model := EuclideanR3))
    (direction first second : EuclideanR3) :
    symmetrizedThroatMetricEuclideanDerivative derivative direction first second =
      symmetrizedThroatMetricEuclideanDerivative derivative direction second first := by
  simp only [symmetrizedThroatMetricEuclideanDerivative, smul_apply,
    add_apply, swapSecondThirdCLM_euclidean_apply]
  ring

theorem symmetrizedThroatEuclideanKoszulNumerator_symmetric
    (derivative : ContinuousMetricDerivativeTensor
      (Model := EuclideanR3))
    (first second : EuclideanR3) :
    metricKoszulNumeratorCLM
        (symmetrizedThroatMetricEuclideanDerivative derivative) first second =
      metricKoszulNumeratorCLM
        (symmetrizedThroatMetricEuclideanDerivative derivative) second first := by
  apply ext_inner_right Real
  intro test
  rw [metricKoszulNumeratorCLM_inner,
    metricKoszulNumeratorCLM_inner,
    symmetrizedThroatMetricEuclideanDerivative_symmetric
      derivative test first second]
  ring

/-- Sector-indexed pointwise Koszul candidate from the symmetrized transported
actual metric one-jet, with the exact
`StructuredBackgroundSecondJet EuclideanR3` field type. -/
def globalCandidateAActualThroatTangentialConnectionQuadraticAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector)) :
    Sector → ContinuousTangentialQuadratic EuclideanR3 :=
  fun sector =>
    (2 : Real)⁻¹ •
      postcomposeQuadraticCLM (Model := EuclideanR3)
        (globalGaugeFixedThroatMetricEuclideanRieszEquivAt
          period hPeriod configuration base hTransverse sector).symm.toContinuousLinearMap
        (metricKoszulNumeratorCLM
          (symmetrizedThroatMetricEuclideanDerivative
            (globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
              period hPeriod configuration base sector)))

theorem globalCandidateAActualThroatTangentialConnectionQuadraticAt_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) (first second : EuclideanR3) :
    globalCandidateAActualThroatTangentialConnectionQuadraticAt
        period hPeriod configuration base hTransverse sector first second =
      globalCandidateAActualThroatTangentialConnectionQuadraticAt
        period hPeriod configuration base hTransverse sector second first := by
  simp only [globalCandidateAActualThroatTangentialConnectionQuadraticAt,
    smul_apply, postcomposeQuadraticCLM_apply]
  rw [symmetrizedThroatEuclideanKoszulNumerator_symmetric]

/-- Pointwise Koszul identity relative to the symmetrized transported
derivative; this does not identify the candidate with Levi--Civita. -/
theorem globalCandidateAActualThroatTangentialConnectionQuadraticAt_koszul
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) (first second test : EuclideanR3) :
    let metric := globalGaugeFixedThroatMetricEuclideanValueAt
      period hPeriod configuration base sector
    let derivative := symmetrizedThroatMetricEuclideanDerivative
      (globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
        period hPeriod configuration base sector)
    2 * metric
        (globalCandidateAActualThroatTangentialConnectionQuadraticAt
          period hPeriod configuration base hTransverse sector first second) test =
      derivative first second test + derivative second first test -
        derivative test first second := by
  dsimp only
  have hOperator :
      metricRieszOperatorCLM
          (globalGaugeFixedThroatMetricEuclideanValueAt
            period hPeriod configuration base sector) =
        (globalGaugeFixedThroatMetricEuclideanRieszEquivAt
          period hPeriod configuration base hTransverse sector :
            EuclideanR3 →L[Real] EuclideanR3) := by
    rw [coe_globalGaugeFixedThroatMetricEuclideanRieszEquivAt]
    rfl
  have hApply :
      (globalGaugeFixedThroatMetricEuclideanRieszEquivAt
          period hPeriod configuration base hTransverse sector :
            EuclideanR3 →L[Real] EuclideanR3)
          ((globalGaugeFixedThroatMetricEuclideanRieszEquivAt
            period hPeriod configuration base hTransverse sector).symm.toContinuousLinearMap
              (metricKoszulNumeratorCLM
                (symmetrizedThroatMetricEuclideanDerivative
                  (globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
                    period hPeriod configuration base sector)) first second)) =
        metricKoszulNumeratorCLM
          (symmetrizedThroatMetricEuclideanDerivative
            (globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
              period hPeriod configuration base sector)) first second := by
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  rw [← metricRieszOperatorCLM_inner]
  simp only [globalCandidateAActualThroatTangentialConnectionQuadraticAt,
    smul_apply, postcomposeQuadraticCLM_apply,
    map_smul, inner_smul_left]
  rw [hOperator, hApply, metricKoszulNumeratorCLM_inner]
  simp only [starRingEnd_apply, star_trivial]
  ring

end
end P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D
end JanusFormal
