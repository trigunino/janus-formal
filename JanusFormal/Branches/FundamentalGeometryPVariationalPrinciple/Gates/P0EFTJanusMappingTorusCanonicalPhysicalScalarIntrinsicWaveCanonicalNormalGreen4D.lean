import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalNormalSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D

/-!
# Intrinsic scalar Green data from one normal divergence component

A global intrinsic wave representative supplies all atlas naturality.  A single
normal component of the canonical local Green divergence then determines the
tangential component by subtraction.

The complete Green input is reduced to:

* the intrinsic wave representative;
* one integrable normal density;
* vanishing of the base integral of the induced tangential remainder;
* equality of the normal total integral with the positive half-collar flux.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalNormalSplit4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Smallest current geometric Green input. -/
structure CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
    (massSquared : Real) where
  intrinsicWave : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod
  normalDensity :
    SmoothScalarField period hPeriod →
      SmoothScalarField period hPeriod →
        CanonicalLatitudeCauchyJetProductParameter → Real
  normalDensity_integrable : ∀ field test,
    Integrable (normalDensity field test)
      (canonicalLatitudeCauchyJetProductMeasure period)
  tangential_base_integral_zero :
    ∀ field test normal,
      (∫ base,
        (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test (base, normal) -
          normalDensity field test (base, normal))
        ∂canonicalLatitudeBaseMeasure period) = 0
  normal_integral_eq_halfCollar :
    ∀ field test,
      (∫ parameter,
        normalDensity field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 *
        (∫ base, (∫ normal in (0 : Real)..1,
          cutoffCollarScalarCurrentDensitizedDivergence
            period hPeriod massSquared field test base normal)
          ∂canonicalLatitudeBaseMeasure period)

namespace CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData

/-- Conversion to the canonical one-normal-component split. -/
def toCanonicalNormalSplitData
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared where
  waveNaturality := data.intrinsicWave.toWaveAtlasNaturality
  normalDensity := data.normalDensity
  normalDensity_integrable := data.normalDensity_integrable
  tangential_base_integral_zero := data.tangential_base_integral_zero
  normal_integral_eq_halfCollar := data.normal_integral_eq_halfCollar

/-- Induced tangential remainder. -/
def tangentialDensity
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared) :=
  (data.toCanonicalNormalSplitData period hPeriod).tangentialDensity period hPeriod

/-- Full normal/tangential Green package. -/
def toNormalTangentialGreenData
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D.CanonicalPhysicalScalarIntrinsicWaveNormalTangentialGreenData
      period hPeriod massSquared where
  intrinsicWave := data.intrinsicWave
  normalDensity := data.normalDensity
  tangentialDensity := data.tangentialDensity period hPeriod
  normalDensity_integrable := data.normalDensity_integrable
  tangentialDensity_integrable :=
    (data.toCanonicalNormalSplitData period hPeriod).tangentialDensity_integrable
      period hPeriod
  localDivergence_eq_normal_add_tangential :=
    (data.toCanonicalNormalSplitData period hPeriod).localDivergence_eq_normal_add_tangential
      period hPeriod
  tangential_base_integral_zero := by
    intro field test normal
    simpa [tangentialDensity, toCanonicalNormalSplitData,
      CanonicalPhysicalScalarEulerCanonicalNormalSplitData.tangentialDensity] using
      data.tangential_base_integral_zero field test normal
  normal_integral_eq_halfCollar := data.normal_integral_eq_halfCollar

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared) :=
  (data.toCanonicalNormalSplitData period hPeriod).greenCore period hPeriod

/-- Smallest geometric Green certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ field test,
        Integrable (data.tangentialDensity period hPeriod field test)
          (canonicalLatitudeCauchyJetProductMeasure period)) ∧
      (∀ field test,
        (∫ parameter,
          data.tangentialDensity period hPeriod field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) = 0) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D.cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨data.intrinsicWave.toWaveAtlasNaturality,
    (data.toCanonicalNormalSplitData period hPeriod).tangentialDensity_integrable
      period hPeriod,
    ((data.toCanonicalNormalSplitData period hPeriod).toNormalTangentialSplitData
      period hPeriod).tangential_integral_eq_zero period hPeriod,
    ((data.toCanonicalNormalSplitData period hPeriod).certificate period hPeriod).2.2.2⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
end JanusFormal
