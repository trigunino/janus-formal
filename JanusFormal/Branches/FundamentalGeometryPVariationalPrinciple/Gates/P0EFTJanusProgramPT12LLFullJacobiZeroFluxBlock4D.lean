import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusThroatLinearOperationsZero4D

/-! The actual smooth L² Jacobi operator is field-only at zero LL flux. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiZeroFluxBlock4D

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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLFullFieldJacobiL2Core4D
open P0EFTJanusProgramPT12LLFullFieldJacobiSameActionPairing4D
open P0EFTJanusProgramPT12LLFullJacobiLinearMap4D
open P0EFTJanusProgramPT12LLFullJacobiClosure4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D
open P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D
open P0EFTJanusThroatLinearOperationsZero4D

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

private theorem auxPlus_zero
    (fields : IndependentFields period hPeriod) :
    auxPlusFields period hPeriod fields 0 = fields := by
  cases fields
  simp [auxPlusFields]

private theorem auxMinus_zero
    (fields : IndependentFields period hPeriod) :
    auxMinusFields period hPeriod fields 0 = fields := by
  cases fields
  simp [auxMinusFields]

private theorem measurePlus_zero
    (fields : IndependentFields period hPeriod) :
    measurePlusFields period hPeriod fields 0 = fields := by
  cases fields
  simp [measurePlusFields]

private theorem fullFieldResidual_pureField
    (fields : IndependentFields period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    llFullFieldJacobiResidual period hPeriod fields 0 0 field =
      llStrongJacobiResidual period hPeriod fields field := by
  rw [llFullFieldJacobiResidual, auxPlus_zero period hPeriod fields,
    auxMinus_zero period hPeriod fields, measurePlus_zero period hPeriod fields]
  simp

/-- The field row of a pure field direction is the earlier strong LL Jacobi row. -/
theorem llFullFieldJacobiToL2_pureField
    (fields : IndependentFields period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    llFullFieldJacobiToL2 period hPeriod fields 0 0 field =
      llStrongJacobiToL2 period hPeriod fields field := by
  apply Lp.ext
  filter_upwards
    [llFullFieldJacobiToL2_ae period hPeriod fields 0 0 field,
      llStrongJacobiToL2_ae period hPeriod fields field]
    with point hFull hStrong
  rw [hFull, hStrong]
  exact congrFun (congrArg SmoothThroatField.toFun
    (fullFieldResidual_pureField period hPeriod fields field)) point

private theorem rawAuxResidual_zeroFlux
    (fields : IndependentFields period hPeriod)
    (hZero : fields.llField = 0)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    rawLLAuxJacobiResidual period hPeriod fields dAux dField = 0 := by
  apply SmoothThroatField.ext
  intro point
  simp [rawLLAuxJacobiResidual, hZero, throatDerivativeEnergy,
    throatDerivativePairing, throatFrameDerivative_zero]

private theorem auxResidual_zeroFlux
    (fields : IndependentFields period hPeriod)
    (hZero : fields.llField = 0)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    llAuxJacobiResidual period hPeriod fields dAux dField = 0 := by
  have hPTZero : (llPTPullback period hPeriod fields).llField = 0 := by
    change throatPTPullback period hPeriod LLFieldFiber fields.llField = 0
    rw [hZero, throatPTPullback_zero]
  rw [llAuxJacobiResidual,
    rawAuxResidual_zeroFlux period hPeriod fields hZero dAux dField,
    rawAuxResidual_zeroFlux period hPeriod
      (llPTPullback period hPeriod fields) hPTZero
      (differentialLLAuxMetricDirectionPT period hPeriod dAux)
      (differentialLLFluxDirectionPT period hPeriod dField)]
  simp

private theorem measureResidual_zeroFlux
    (fields : IndependentFields period hPeriod)
    (hZero : fields.llField = 0)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    llMeasureJacobiResidual period hPeriod fields dField = 0 := by
  apply SmoothThroatField.ext
  intro point
  simp [llMeasureJacobiResidual, hZero]

private theorem auxToL2_zeroFlux
    (fields : IndependentFields period hPeriod)
    (hZero : fields.llField = 0)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    llAuxJacobiToL2 period hPeriod fields dAux dField = 0 := by
  unfold llAuxJacobiToL2
  apply Lp.ext
  filter_upwards
    [((llAuxJacobiResidual period hPeriod fields dAux dField).contMDiff_toFun.continuous.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).coeFn_toLp,
      Lp.coeFn_zero LLMetricFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
    with point hAux hZeroLp
  rw [hAux, hZeroLp]
  exact congrFun (congrArg SmoothThroatField.toFun
    (auxResidual_zeroFlux period hPeriod fields hZero dAux dField)) point

private theorem measureToL2_zeroFlux
    (fields : IndependentFields period hPeriod)
    (hZero : fields.llField = 0)
    (dField : SmoothThroatField period hPeriod LLFieldFiber) :
    llMeasureJacobiToL2 period hPeriod fields dField = 0 := by
  unfold llMeasureJacobiToL2
  apply Lp.ext
  filter_upwards
    [((llMeasureJacobiResidual period hPeriod fields dField).contMDiff_toFun.continuous.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).coeFn_toLp,
      Lp.coeFn_zero Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
    with point hMeasure hZeroLp
  rw [hMeasure, hZeroLp]
  exact congrFun (congrArg SmoothThroatField.toFun
    (measureResidual_zeroFlux period hPeriod fields hZero dField)) point

/-- Exact block diagonalization of the genuine smooth L² Jacobi operator. -/
theorem llFullJacobiLinearMap_zeroFlux_block
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    llFullJacobiLinearMap period hPeriod data analysis direction =
      ((0, 0), llStrongJacobiToL2 period hPeriod
        (data.boundary.llFields period hPeriod) direction.2.toTest) := by
  have hAux := auxToL2_zeroFlux period hPeriod
    (data.boundary.llFields period hPeriod) hZero
    direction.1.1 direction.2.toTest
  have hMeasure := measureToL2_zeroFlux period hPeriod
    (data.boundary.llFields period hPeriod) hZero direction.2.toTest
  have hField : fullFieldToL2 period hPeriod data analysis direction =
      llStrongJacobiToL2 period hPeriod
        (data.boundary.llFields period hPeriod) direction.2.toTest := by
    change llFullFieldJacobiToL2 period hPeriod
        (data.boundary.llFields period hPeriod)
        direction.1.1 direction.1.2 direction.2.toTest = _
    have hDecomp : pureAuxMeasureTest period hPeriod
        direction.1.1 direction.1.2 +
          pureFieldTest period hPeriod direction.2 = direction := by
      rcases direction with ⟨⟨dAux, dMeasure⟩, dField⟩
      simp [pureAuxMeasureTest, pureFieldTest]
    have hMap := (llFullFieldJacobiLinearMap period hPeriod data analysis).map_add
      (pureAuxMeasureTest period hPeriod direction.1.1 direction.1.2)
      (pureFieldTest period hPeriod direction.2)
    rw [hDecomp,
      show llFullFieldJacobiLinearMap period hPeriod data analysis
        (pureAuxMeasureTest period hPeriod direction.1.1 direction.1.2) = 0 from
          congrArg Prod.snd
            (llFullJacobiLinearMap_pureAuxMeasure_zeroFlux period hPeriod
              data analysis hZero direction.1.1 direction.1.2),
      show llFullFieldJacobiLinearMap period hPeriod data analysis
        (pureFieldTest period hPeriod direction.2) =
          llStrongJacobiToL2 period hPeriod
            (data.boundary.llFields period hPeriod) direction.2.toTest from
          llFullFieldJacobiToL2_pureField period hPeriod
            (data.boundary.llFields period hPeriod) direction.2.toTest] at hMap
    change llFullFieldJacobiToL2 period hPeriod
        (data.boundary.llFields period hPeriod)
        direction.1.1 direction.1.2 direction.2.toTest = _ at hMap
    simpa only [zero_add] using hMap
  apply Prod.ext
  · apply Prod.ext
    · exact hAux
    · exact hMeasure
  · exact hField

end
end P0EFTJanusProgramPT12LLFullJacobiZeroFluxBlock4D
end JanusFormal
