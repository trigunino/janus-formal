import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalTangentialSplit4D

/-!
# Canonical Green divergence from one normal component

The tangential divergence is not independent data.  Once a candidate normal
component is chosen, define

`div_tan := div_local - div_normal`.

The local divergence is integrable by exact coarea and the local Green identity.
Therefore integrability of the normal component automatically implies
integrability of the tangential remainder, while the pointwise decomposition is
an algebraic identity.

The remaining Green input is reduced to:

* one integrable normal density;
* vanishing of the base integral of the induced tangential remainder;
* identification of the normal total integral with the positive half collar.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalNormalSplit4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalTangentialSplit4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Green data determined by one normal component. -/
structure CanonicalPhysicalScalarEulerCanonicalNormalSplitData
    (massSquared : Real) where
  waveNaturality :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod
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

namespace CanonicalPhysicalScalarEulerCanonicalNormalSplitData

/-- Tangential remainder induced by the chosen normal component. -/
def tangentialDensity
    (data : CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  canonicalPhysicalScalarEulerProductLocalDivergenceDensity
      period hPeriod field test parameter -
    data.normalDensity field test parameter

/-- Integrability of the induced tangential remainder. -/
theorem tangentialDensity_integrable
    (data : CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    Integrable (data.tangentialDensity period hPeriod field test)
      (canonicalLatitudeCauchyJetProductMeasure period) := by
  have hLocal :=
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity_integrable
      period hPeriod data.waveNaturality massSquared field test
  exact hLocal.sub (data.normalDensity_integrable field test)

/-- Pointwise normal/tangential decomposition. -/
theorem localDivergence_eq_normal_add_tangential
    (data : CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter =
      data.normalDensity field test parameter +
        data.tangentialDensity period hPeriod field test parameter := by
  unfold tangentialDensity
  ring

/-- Conversion to the full normal/tangential split package. -/
def toNormalTangentialSplitData
    (data : CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerNormalTangentialSplitData
      period hPeriod massSquared where
  waveNaturality := data.waveNaturality
  normalDensity := data.normalDensity
  tangentialDensity := data.tangentialDensity period hPeriod
  normalDensity_integrable := data.normalDensity_integrable
  tangentialDensity_integrable := data.tangentialDensity_integrable period hPeriod
  localDivergence_eq_normal_add_tangential :=
    data.localDivergence_eq_normal_add_tangential period hPeriod
  tangential_base_integral_zero := by
    intro field test normal
    simpa [tangentialDensity] using
      data.tangential_base_integral_zero field test normal
  normal_integral_eq_halfCollar := data.normal_integral_eq_halfCollar

/-- Canonical local-divergence Green package. -/
def toCanonicalLocalDivergenceData
    (data : CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared) :=
  (data.toNormalTangentialSplitData period hPeriod).toCanonicalLocalDivergenceData
    period hPeriod

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared) :=
  (data.toCanonicalLocalDivergenceData period hPeriod).greenCore period hPeriod

/-- Canonical normal-split certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerCanonicalNormalSplitData
      period hPeriod massSquared) :
    (∀ field test,
      Integrable (data.tangentialDensity period hPeriod field test)
        (canonicalLatitudeCauchyJetProductMeasure period)) ∧
      (∀ field test parameter,
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test parameter =
          data.normalDensity field test parameter +
            data.tangentialDensity period hPeriod field test parameter) ∧
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
  ⟨data.tangentialDensity_integrable period hPeriod,
    data.localDivergence_eq_normal_add_tangential period hPeriod,
    (data.toNormalTangentialSplitData period hPeriod).tangential_integral_eq_zero
      period hPeriod,
    ((data.toNormalTangentialSplitData period hPeriod).certificate period hPeriod).2⟩

end CanonicalPhysicalScalarEulerCanonicalNormalSplitData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalNormalSplit4D
end JanusFormal
