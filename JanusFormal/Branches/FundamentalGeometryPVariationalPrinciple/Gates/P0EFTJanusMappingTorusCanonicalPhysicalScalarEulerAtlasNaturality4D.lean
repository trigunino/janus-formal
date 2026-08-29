import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D

/-!
# Physical scalar Euler atlas compatibility from wave naturality

The scalar value representative is intrinsically defined by evaluation at the
quotient point.  Therefore two holonomic coordinates representing the same point
have the same scalar value.  The mass term in `box_g phi - m² phi` is consequently
already overlap compatible.

The sole geometric overlap theorem needed for the Euler residual is naturality
of the covariant scalar wave contraction.  This file isolates that theorem and
shows that it implies compatibility of the complete physical Euler atlas family.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Set Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Scalar chart representatives agree whenever their coordinates represent the
same quotient point. -/
theorem localScalarRepresentative_eq_of_coordinateMap_eq
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (hCoordinate : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localScalarRepresentative period hPeriod field
        firstPatch firstCoordinate =
      localScalarRepresentative period hPeriod field
        secondPatch secondCoordinate := by
  unfold localScalarRepresentative
  rw [hCoordinate]

/-- Exact naturality proposition for the scalar wave contraction. -/
def CanonicalPhysicalScalarWaveAtlasCompatible
    (field : SmoothScalarField period hPeriod) : Prop :=
  ∀ (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4),
    firstPatch.coordinateMap firstCoordinate =
        secondPatch.coordinateMap secondCoordinate →
      covariantScalarJetWave
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            firstPatch firstCoordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            firstPatch field firstCoordinate) =
        covariantScalarJetWave
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            secondPatch secondCoordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            secondPatch field secondCoordinate)

/-- Wave naturality implies compatibility of the full massive Euler residual. -/
theorem canonicalPhysicalScalarEulerAtlasCompatible_of_wave
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (hWave : CanonicalPhysicalScalarWaveAtlasCompatible
      period hPeriod field) :
    CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field := by
  intro firstPatch secondPatch firstCoordinate secondCoordinate hCoordinate
  rw [canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass,
    canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass,
    hWave firstPatch secondPatch firstCoordinate secondCoordinate hCoordinate,
    localScalarRepresentative_eq_of_coordinateMap_eq
      period hPeriod field firstPatch secondPatch
        firstCoordinate secondCoordinate hCoordinate]

/-- Wave naturality for every smooth scalar. -/
def CanonicalPhysicalScalarWaveAtlasNaturality : Prop :=
  ∀ field : SmoothScalarField period hPeriod,
    CanonicalPhysicalScalarWaveAtlasCompatible period hPeriod field

/-- Universal wave naturality supplies universal Euler-atlas compatibility for
every mass parameter. -/
theorem canonicalPhysicalScalarEulerAtlasCompatible_all
    (hWave : CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field :=
  canonicalPhysicalScalarEulerAtlasCompatible_of_wave
    period hPeriod massSquared field (hWave field)

/-- Globalization package after the compatibility theorem is reduced to wave
naturality.  Only continuity of the glued global residual remains analytic. -/
structure CanonicalPhysicalScalarWaveGlobalizationData
    (massSquared : Real) where
  waveNaturality : CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod
  residualContinuous : ∀ field : SmoothScalarField period hPeriod,
    Continuous
      (canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field)
  ae_zero_eq_zero : ∀ field : SmoothScalarField period hPeriod,
    canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field =ᵐ[
          intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0 →
      canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field = 0

namespace CanonicalPhysicalScalarWaveGlobalizationData

/-- Conversion to the reduced Euler-globalization package. -/
def toEulerGlobalizationData
    (globalization : CanonicalPhysicalScalarWaveGlobalizationData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerGlobalizationData
      period hPeriod massSquared where
  compatible := canonicalPhysicalScalarEulerAtlasCompatible_all
    period hPeriod globalization.waveNaturality massSquared
  continuous := globalization.residualContinuous
  ae_zero_eq_zero := globalization.ae_zero_eq_zero

/-- Genuine bulk-L2 Euler operator. -/
def toBulkL2LinearMap
    (globalization : CanonicalPhysicalScalarWaveGlobalizationData
      period hPeriod massSquared) :=
  globalization.toEulerGlobalizationData.toBulkL2LinearMap

/-- Euler-atlas naturality certificate. -/
theorem certificate
    (globalization : CanonicalPhysicalScalarWaveGlobalizationData
      period hPeriod massSquared) :
    (∀ field : SmoothScalarField period hPeriod,
      CanonicalPhysicalScalarEulerAtlasCompatible
        period hPeriod massSquared field) ∧
      (∀ field : SmoothScalarField period hPeriod,
        Continuous
          (canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field)) :=
  ⟨canonicalPhysicalScalarEulerAtlasCompatible_all
      period hPeriod globalization.waveNaturality massSquared,
    globalization.residualContinuous⟩

end CanonicalPhysicalScalarWaveGlobalizationData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
end JanusFormal
