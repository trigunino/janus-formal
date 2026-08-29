import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricGeneratingFrameSeparation4D

/-!
# Smoothness of finite-frame throat metric energy

The pre-existing bundlewise application theorem makes every reading
`h(vᵢ,vⱼ)` of a smooth throat tensor on the finite smooth generating family a
genuine smooth scalar field.  Finite sums of their squares therefore give a
smooth, hence continuous, separating energy.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricFrameEnergySmooth4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open Bundle
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPThroatMetricGeneratingFrameSeparation4D
open P0EFTJanusProgramPThroatMetricPositiveDualizer4D

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

/-- One genuine smooth scalar frame reading of a smooth symmetric throat
tensor. -/
def throatMetricFrameCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (i j : Fin frame.count) :
    SmoothThroatField period hPeriod Real where
  toFun := fun point =>
    tensor.tensor point (frame.vectorAt point i) (frame.vectorAt point j)
  contMDiff_toFun := by
    have hApplied := tensor.tensor.contMDiff.clm_bundle_apply₂
      (frame.contMDiff_vector i) (frame.contMDiff_vector j)
    intro point
    have hAppliedAt := hApplied point
    rw [contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp]
theorem throatMetricFrameCoefficient_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (i j : Fin frame.count)
    (point : EffectiveThroat period hPeriod) :
    throatMetricFrameCoefficient period hPeriod frame tensor i j point =
      tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j) :=
  rfl

/-- The finite-frame sum of squares as a genuine smooth throat scalar. -/
def throatMetricFrameEnergyField
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    SmoothThroatField period hPeriod Real where
  toFun := throatMetricFrameEnergy period hPeriod frame tensor
  contMDiff_toFun := by
    unfold throatMetricFrameEnergy
    apply ContMDiff.sum
    intro i _
    apply ContMDiff.sum
    intro j _
    exact
      (throatMetricFrameCoefficient
        period hPeriod frame tensor i j).contMDiff_toFun.pow 2

@[simp]
theorem throatMetricFrameEnergyField_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    throatMetricFrameEnergyField period hPeriod frame tensor point =
      throatMetricFrameEnergy period hPeriod frame tensor point :=
  rfl

theorem throatMetricFrameEnergy_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    Continuous (throatMetricFrameEnergy period hPeriod frame tensor) :=
  (throatMetricFrameEnergyField
    period hPeriod frame tensor).contMDiff_toFun.continuous

/-- The two-sector separating energy is itself a genuine smooth scalar. -/
def throatMetricPairFrameEnergyField
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    SmoothThroatField period hPeriod Real where
  toFun := throatMetricPairFrameEnergy period hPeriod frame tensor
  contMDiff_toFun := by
    exact
      (throatMetricFrameEnergyField
        period hPeriod frame tensor.1).contMDiff_toFun.add
      (throatMetricFrameEnergyField
        period hPeriod frame tensor.2).contMDiff_toFun

@[simp]
theorem throatMetricPairFrameEnergyField_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    throatMetricPairFrameEnergyField period hPeriod frame tensor point =
      throatMetricPairFrameEnergy period hPeriod frame tensor point :=
  rfl

theorem throatMetricPairFrameEnergy_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    Continuous (throatMetricPairFrameEnergy period hPeriod frame tensor) :=
  (throatMetricPairFrameEnergyField
    period hPeriod frame tensor).contMDiff_toFun.continuous

/-- Once a smooth tensor-valued dualizer realizes the frame energy,
continuity and pointwise separation are automatic. -/
def throatMetricSmoothPositiveDualizerData_of_frameEnergyPairing
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dualize :
      SmoothThroatGeneralMetricTensorPair period hPeriod →
        SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hPairing :
      ∀ antifield point,
        intrinsicThroatTensorPairPairingAt period hPeriod
            antifield (dualize antifield) point =
          throatMetricPairFrameEnergy
            period hPeriod frame antifield point) :
    ThroatMetricSmoothPositiveDualizerData period hPeriod :=
  throatMetricSmoothPositiveDualizerData_of_frameEnergy
    period hPeriod frame dualize
    (by
      intro antifield
      have hFunctions :
          (fun point =>
            intrinsicThroatTensorPairPairingAt period hPeriod
              antifield (dualize antifield) point) =
            throatMetricPairFrameEnergy
              period hPeriod frame antifield :=
        funext (hPairing antifield)
      rw [hFunctions]
      exact throatMetricPairFrameEnergy_continuous
        period hPeriod frame antifield)
    hPairing

end
end P0EFTJanusProgramPThroatMetricFrameEnergySmooth4D
end JanusFormal
