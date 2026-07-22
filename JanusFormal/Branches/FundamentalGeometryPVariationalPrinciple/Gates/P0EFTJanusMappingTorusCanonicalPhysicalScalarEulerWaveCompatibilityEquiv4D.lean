import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D

/-!
# Euler overlap compatibility and scalar-wave naturality

The massive Euler residual is `box_g phi - m² phi`.  Scalar values agree on
chart overlaps because they are evaluations of the same quotient field.
Therefore overlap compatibility of the Euler residual is equivalent to
naturality of the covariant scalar wave contraction, for any fixed mass.

This equivalence lets the compatibility-only Green-core construction reuse the
complete explicit Cauchy-jet globalization and estimate chain originally stated
with wave naturality.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerWaveCompatibilityEquiv4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Set Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Euler compatibility implies naturality of the wave term. -/
theorem waveCompatible_of_eulerCompatible
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (hEuler : CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field) :
    CanonicalPhysicalScalarWaveAtlasCompatible period hPeriod field := by
  intro firstPatch secondPatch firstCoordinate secondCoordinate hCoordinate
  have hEulerOverlap := hEuler firstPatch secondPatch
    firstCoordinate secondCoordinate hCoordinate
  have hValue := localScalarRepresentative_eq_of_coordinateMap_eq
    period hPeriod field firstPatch secondPatch
      firstCoordinate secondCoordinate hCoordinate
  rw [canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass,
    canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass] at hEulerOverlap
  linarith

/-- For a fixed field and mass, wave naturality and Euler compatibility are
logically equivalent. -/
theorem waveCompatible_iff_eulerCompatible
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasCompatible period hPeriod field ↔
      CanonicalPhysicalScalarEulerAtlasCompatible
        period hPeriod massSquared field := by
  constructor
  · exact canonicalPhysicalScalarEulerAtlasCompatible_of_wave
      period hPeriod massSquared field
  · exact waveCompatible_of_eulerCompatible
      period hPeriod massSquared field

/-- A universal Euler compatibility package supplies universal wave naturality. -/
theorem waveNaturality_of_eulerCompatibilityData
    (data : CanonicalPhysicalScalarEulerCompatibilityData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod :=
  fun field => waveCompatible_of_eulerCompatible
    period hPeriod massSquared field (data.compatible field)

namespace CanonicalPhysicalScalarEulerCompatibilityData

/-- Convert compatibility-only Euler data to the earlier wave-globalization
interface.  Its continuity field is filled by the local-diffeomorphism theorem. -/
def toWaveGlobalizationData
    (data : CanonicalPhysicalScalarEulerCompatibilityData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarWaveGlobalizationData
      period hPeriod massSquared where
  waveNaturality := waveNaturality_of_eulerCompatibilityData
    period hPeriod data
  residualContinuous := fun field =>
    canonicalPhysicalScalarEulerGlobalResidual_continuous_of_compatible
      period hPeriod massSquared field (data.compatible field)

/-- Both globalization interfaces construct the same operator data. -/
theorem toWaveGlobalizationData_operatorData_eq
    (data : CanonicalPhysicalScalarEulerCompatibilityData
      period hPeriod massSquared) :
    data.toWaveGlobalizationData.toEulerGlobalizationData.toOperatorData =
      data.toOperatorData := by
  rfl

/-- Compatibility-equivalence certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerCompatibilityData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod ∧
      (∀ field : SmoothScalarField period hPeriod,
        Continuous
          (canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field)) :=
  ⟨waveNaturality_of_eulerCompatibilityData period hPeriod data,
    fun field =>
      canonicalPhysicalScalarEulerGlobalResidual_continuous_of_compatible
        period hPeriod massSquared field (data.compatible field)⟩

end CanonicalPhysicalScalarEulerCompatibilityData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerWaveCompatibilityEquiv4D
end JanusFormal
