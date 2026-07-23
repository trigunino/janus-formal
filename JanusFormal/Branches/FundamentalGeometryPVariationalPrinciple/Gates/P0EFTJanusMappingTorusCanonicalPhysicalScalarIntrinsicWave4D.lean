import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D

/-!
# Scalar-wave naturality from a global intrinsic representative

Overlap naturality is most naturally proved by constructing the intrinsic
scalar d'Alembertian as a global scalar function.  If every holonomic coordinate
formula agrees with that global function at the represented quotient point,
then equality on all overlaps is immediate.

This file replaces the pairwise chart-overlap input by:

* one global wave representative for every smooth scalar;
* one local chart formula identifying the covariant jet contraction with that
  representative.

Massive Euler compatibility then follows automatically because scalar
multiplication by the mass is already intrinsic.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- The local scalar wave contraction, before subtracting the mass term. -/
def canonicalPhysicalScalarWaveAtlasRepresentative
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  covariantScalarJetWave
    (localFixedSignMetric period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch coordinate)
    (localCovariantScalarJet period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch field coordinate)

/-- Intrinsic global realization of the scalar wave operator. -/
structure CanonicalPhysicalScalarIntrinsicWaveData where
  wave : SmoothScalarField period hPeriod →
    EffectiveQuotient period hPeriod → Real
  local_eq :
    ∀ field patch coordinate,
      canonicalPhysicalScalarWaveAtlasRepresentative
          period hPeriod field patch coordinate =
        wave field (patch.coordinateMap coordinate)

namespace CanonicalPhysicalScalarIntrinsicWaveData

/-- A global intrinsic representative gives wave naturality on every overlap. -/
theorem waveAtlasCompatible
    (data : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasCompatible period hPeriod field := by
  intro firstPatch secondPatch firstCoordinate secondCoordinate hCoordinate
  change canonicalPhysicalScalarWaveAtlasRepresentative
      period hPeriod field firstPatch firstCoordinate =
    canonicalPhysicalScalarWaveAtlasRepresentative
      period hPeriod field secondPatch secondCoordinate
  rw [data.local_eq field firstPatch firstCoordinate,
    data.local_eq field secondPatch secondCoordinate,
    hCoordinate]

/-- Universal wave naturality. -/
def toWaveAtlasNaturality
    (data : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod :=
  data.waveAtlasCompatible period hPeriod

/-- Universal massive Euler compatibility. -/
theorem eulerAtlasCompatible
    (data : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field :=
  canonicalPhysicalScalarEulerAtlasCompatible_of_wave
    period hPeriod massSquared field
      (data.waveAtlasCompatible period hPeriod field)

/-- Local Euler residual in terms of the intrinsic wave representative. -/
theorem eulerAtlasResidual_eq_intrinsicWave_sub_mass
    (data : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    canonicalPhysicalScalarEulerAtlasResidual
        period hPeriod massSquared field patch coordinate =
      data.wave field (patch.coordinateMap coordinate) -
        massSquared * field (patch.coordinateMap coordinate) := by
  rw [canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass]
  change canonicalPhysicalScalarWaveAtlasRepresentative
        period hPeriod field patch coordinate -
      massSquared * localScalarRepresentative
        period hPeriod field patch coordinate =
    data.wave field (patch.coordinateMap coordinate) -
      massSquared * field (patch.coordinateMap coordinate)
  rw [data.local_eq field patch coordinate]
  rfl

/-- The global residual selected from the compatible atlas is the intrinsic wave
minus the mass term. -/
theorem eulerGlobalResidual_eq_intrinsicWave_sub_mass
    (data : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field point =
      data.wave field point - massSquared * field point := by
  let witness := canonicalPhysicalScalarEulerChartWitness
    period hPeriod point
  have hGlobal := canonicalPhysicalScalarEulerGlobalResidual_eq_chart
    period hPeriod massSquared field
    (data.eulerAtlasCompatible period hPeriod massSquared field)
    witness.patch witness.coordinate
  rw [witness.coordinate_eq] at hGlobal
  rw [hGlobal]
  have hLocal := data.eulerAtlasResidual_eq_intrinsicWave_sub_mass
    period hPeriod massSquared field witness.patch witness.coordinate
  rw [witness.coordinate_eq] at hLocal
  exact hLocal

/-- Intrinsic-wave compatibility certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod ∧
      (∀ massSquared field patch coordinate,
        canonicalPhysicalScalarEulerAtlasResidual
            period hPeriod massSquared field patch coordinate =
          data.wave field (patch.coordinateMap coordinate) -
            massSquared * field (patch.coordinateMap coordinate)) ∧
      (∀ massSquared field point,
        canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field point =
          data.wave field point - massSquared * field point) :=
  ⟨data.toWaveAtlasNaturality period hPeriod,
    data.eulerAtlasResidual_eq_intrinsicWave_sub_mass period hPeriod,
    data.eulerGlobalResidual_eq_intrinsicWave_sub_mass period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
end JanusFormal
