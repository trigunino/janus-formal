import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiL2Core4D

/-!
# Full three-slot LL Jacobi field row on the smooth core

Finite differences of the existing strong Euler residual isolate the two
coefficient variations without a new integration-by-parts hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullFieldJacobiL2Core4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D

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

def auxPlusFields
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) :
    IndependentFields period hPeriod :=
  { fields with llAuxMetric := fields.llAuxMetric + dAux }

def auxMinusFields
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber) :
    IndependentFields period hPeriod :=
  { fields with llAuxMetric := fields.llAuxMetric - dAux }

def measurePlusFields
    (fields : IndependentFields period hPeriod)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    IndependentFields period hPeriod :=
  { fields with llMeasure := fields.llMeasure + dMeasure }

/-- Pointwise polarization of the unchanged full LL Hessian against a pure
field test. This also fixes the factors of two in both mixed blocks. -/
theorem raw_field_row_density
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField testField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    differentialLLKineticMixedHessianDensity period hPeriod frame
        fields.llAuxMetric fields.llField dAux 0 dField testField point +
      llWorldvolumeHessianDensity period hPeriod fields
        { measureDirection := dMeasure, fieldDirection := dField }
        { measureDirection := 0, fieldDirection := testField } point =
      differentialLLFluxHessianDensity period hPeriod frame fields
          dField testField point +
        (1 / 2 : Real) *
          (differentialLLFluxFirstVariationDensity period hPeriod frame
              (auxPlusFields period hPeriod fields dAux) testField point -
            differentialLLFluxFirstVariationDensity period hPeriod frame
              (auxMinusFields period hPeriod fields dAux) testField point) +
        (differentialLLFluxFirstVariationDensity period hPeriod frame
            (measurePlusFields period hPeriod fields dMeasure) testField point -
          differentialLLFluxFirstVariationDensity period hPeriod frame
            fields testField point) := by
  simp only [differentialLLKineticMixedHessianDensity,
    llWorldvolumeHessianDensity, differentialLLFluxHessianDensity,
    differentialLLFluxFirstVariationDensity, auxPlusFields, auxMinusFields,
    measurePlusFields, llAuxiliaryKineticWeight]
  simp only [show (fields.llAuxMetric + dAux) point =
      fields.llAuxMetric point + dAux point by rfl,
    show (fields.llAuxMetric - dAux) point =
      fields.llAuxMetric point - dAux point by rfl,
    show (fields.llMeasure + dMeasure) point =
      fields.llMeasure point + dMeasure point by rfl,
    show (0 : SmoothThroatField period hPeriod LLMetricFiber) point = 0 by rfl,
    show (0 : SmoothThroatField period hPeriod Real) point = 0 by rfl]
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [inner_zero_right, mul_zero]
  ring

/-- Integrated raw identity before the PT average. -/
theorem raw_field_row_integral
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField testField : SmoothThroatField period hPeriod LLFieldFiber) :
    (∫ point,
      differentialLLKineticMixedHessianDensity period hPeriod frame
        fields.llAuxMetric fields.llField dAux 0 dField testField point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
      (∫ point,
        llWorldvolumeHessianDensity period hPeriod fields
          { measureDirection := dMeasure, fieldDirection := dField }
          { measureDirection := 0, fieldDirection := testField } point
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalDifferentialLLFluxHessian period hPeriod frame fields
          dField testField (intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
        (1 / 2 : Real) *
          (globalDifferentialLLFluxFirstVariation period hPeriod frame
              (auxPlusFields period hPeriod fields dAux) testField
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod) -
            globalDifferentialLLFluxFirstVariation period hPeriod frame
              (auxMinusFields period hPeriod fields dAux) testField
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        (globalDifferentialLLFluxFirstVariation period hPeriod frame
            (measurePlusFields period hPeriod fields dMeasure) testField
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod) -
          globalDifferentialLLFluxFirstVariation period hPeriod frame
            fields testField
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let kin := differentialLLKineticMixedHessianDensity period hPeriod frame
    fields.llAuxMetric fields.llField dAux 0 dField testField
  let world := llWorldvolumeHessianDensity period hPeriod fields
    { measureDirection := dMeasure, fieldDirection := dField }
    { measureDirection := 0, fieldDirection := testField }
  let hess := differentialLLFluxHessianDensity period hPeriod frame fields
    dField testField
  let plus := differentialLLFluxFirstVariationDensity period hPeriod frame
    (auxPlusFields period hPeriod fields dAux) testField
  let minus := differentialLLFluxFirstVariationDensity period hPeriod frame
    (auxMinusFields period hPeriod fields dAux) testField
  let measurePlus := differentialLLFluxFirstVariationDensity period hPeriod frame
    (measurePlusFields period hPeriod fields dMeasure) testField
  let base := differentialLLFluxFirstVariationDensity period hPeriod frame
    fields testField
  have hKin : Integrable kin mu :=
    differentialLLKineticMixedHessianDensity_integrable period hPeriod frame
      fields.llAuxMetric fields.llField dAux 0 dField testField mu
  have hWorld : Integrable world mu := by
    apply Continuous.integrable_of_hasCompactSupport _
      (HasCompactSupport.of_compactSpace _)
    have hFirst : Continuous (fun point : EffectiveThroat period hPeriod =>
        2 * dMeasure point * inner Real (fields.llField point)
          (testField point)) :=
      ((continuous_const.mul dMeasure.contMDiff_toFun.continuous).mul
        (fields.llField.contMDiff_toFun.continuous.inner
          testField.contMDiff_toFun.continuous))
    have hSecond : Continuous (fun point : EffectiveThroat period hPeriod =>
        2 * fields.llMeasure point * inner Real (dField point)
          (testField point)) :=
      ((continuous_const.mul fields.llMeasure.contMDiff_toFun.continuous).mul
        (dField.contMDiff_toFun.continuous.inner
          testField.contMDiff_toFun.continuous))
    have hWorldEq : world = fun point =>
        2 * dMeasure point * inner Real (fields.llField point)
          (testField point) +
        2 * fields.llMeasure point * inner Real (dField point)
          (testField point) := by
      funext point
      simp [world, llWorldvolumeHessianDensity]
    rw [hWorldEq]
    exact hFirst.add hSecond
  have hHess : Integrable hess mu :=
    (differentialLLFluxHessianDensity_continuous period hPeriod frame fields
      dField testField).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPlus : Integrable plus mu :=
    (differentialLLFluxFirstVariationDensity_continuous period hPeriod frame
      (auxPlusFields period hPeriod fields dAux) testField
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMinus : Integrable minus mu :=
    (differentialLLFluxFirstVariationDensity_continuous period hPeriod frame
      (auxMinusFields period hPeriod fields dAux) testField
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMeasurePlus : Integrable measurePlus mu :=
    (differentialLLFluxFirstVariationDensity_continuous period hPeriod frame
      (measurePlusFields period hPeriod fields dMeasure) testField
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hBase : Integrable base mu :=
    (differentialLLFluxFirstVariationDensity_continuous period hPeriod frame
      fields testField).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change (∫ point, kin point ∂mu) + ∫ point, world point ∂mu =
    (∫ point, hess point ∂mu) +
      (1 / 2 : Real) * ((∫ point, plus point ∂mu) -
        (∫ point, minus point ∂mu)) +
      ((∫ point, measurePlus point ∂mu) -
        (∫ point, base point ∂mu))
  calc
    (∫ point, kin point ∂mu) + ∫ point, world point ∂mu =
        ∫ point, kin point + world point ∂mu :=
      (integral_add hKin hWorld).symm
    _ = ∫ point, hess point + (1 / 2 : Real) *
          (plus point - minus point) +
          (measurePlus point - base point) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact raw_field_row_density period hPeriod frame fields dAux
        dMeasure dField testField point
    _ = (∫ point, hess point ∂mu) +
          (1 / 2 : Real) * ((∫ point, plus point ∂mu) -
            (∫ point, minus point ∂mu)) +
          ((∫ point, measurePlus point ∂mu) -
            (∫ point, base point ∂mu)) := by
      have hAux : Integrable (fun point =>
          (1 / 2 : Real) * (plus point - minus point)) mu :=
        (hPlus.sub hMinus).const_mul _
      have hLeft : Integrable (fun point =>
          hess point + (1 / 2 : Real) * (plus point - minus point)) mu :=
        hHess.add hAux
      calc
        (∫ point, hess point + (1 / 2 : Real) *
            (plus point - minus point) +
            (measurePlus point - base point) ∂mu) =
            (∫ point, hess point + (1 / 2 : Real) *
              (plus point - minus point) ∂mu) +
            (∫ point, measurePlus point - base point ∂mu) :=
          integral_add hLeft (hMeasurePlus.sub hBase)
        _ = (∫ point, hess point ∂mu) +
              (∫ point, (1 / 2 : Real) *
                (plus point - minus point) ∂mu) +
              (∫ point, measurePlus point - base point ∂mu) := by
          rw [integral_add hHess hAux]
        _ = _ := by
          rw [integral_const_mul, integral_sub hPlus hMinus,
            integral_sub hMeasurePlus hBase]

private def strongPT
    (fields : IndependentFields period hPeriod) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  ptSymmetricStrongDifferentialLLEulerField period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (smoothLLStrongRegularity period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) fields

/-- The actual field-output row, including both coefficient variations.
The central difference isolates `2⟨aux,dAux⟩`; the last difference isolates
`2 dMeasure·field`. -/
def llFullFieldJacobiResidual
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField : LLWeakTestSpace period hPeriod) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  llStrongJacobiResidual period hPeriod fields dField +
    (1 / 2 : Real) •
      (strongPT period hPeriod (auxPlusFields period hPeriod fields dAux) -
        strongPT period hPeriod (auxMinusFields period hPeriod fields dAux)) +
    (strongPT period hPeriod (measurePlusFields period hPeriod fields dMeasure) -
      strongPT period hPeriod fields)

/-- On the compact throat the full smooth row has a genuine L² value. -/
def llFullFieldJacobiToL2
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField : LLWeakTestSpace period hPeriod) :
    Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  ((llFullFieldJacobiResidual period hPeriod fields dAux dMeasure dField
    ).contMDiff_toFun.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).toLp
    (llFullFieldJacobiResidual period hPeriod fields dAux dMeasure dField)

theorem llFullFieldJacobiToL2_ae
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (dField : LLWeakTestSpace period hPeriod) :
    (llFullFieldJacobiToL2 period hPeriod fields dAux dMeasure dField :
      EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      llFullFieldJacobiResidual period hPeriod fields dAux dMeasure dField :=
  ((llFullFieldJacobiResidual period hPeriod fields dAux dMeasure dField
    ).contMDiff_toFun.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).coeFn_toLp

end
end P0EFTJanusProgramPT12LLFullFieldJacobiL2Core4D
end JanusFormal
