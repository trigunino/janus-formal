import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

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
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

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

/-- The finite transition-jet obligation that suffices to glue the local wave
representatives. -/
structure CanonicalPhysicalScalarRebasedWaveTransitionData : Prop where
  agreement :
    ∀ field firstPatch secondPatch firstCoordinate secondCoordinate,
      firstPatch.coordinateMap firstCoordinate =
          secondPatch.coordinateMap secondCoordinate →
        RebasedHolonomicTransitionJetAgreement period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
          firstPatch secondPatch firstCoordinate secondCoordinate

/-- Genuine coordinate-transition input for the wave operator.  Metric
congruence is already a theorem, so only covariance of the scalar Hessian
remains in this contract. -/
structure CanonicalPhysicalScalarCovariantWaveTransitionData : Prop where
  hessian_congruence :
    ∀ field firstPatch secondPatch firstCoordinate secondCoordinate
      (samePoint : firstPatch.coordinateMap firstCoordinate =
        secondPatch.coordinateMap secondCoordinate),
      (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          firstPatch field firstCoordinate).hessian =
        (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint).transpose *
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            secondPatch field secondCoordinate).hessian *
          holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint

/-- Field-independent geometric transition datum.  The scalar Hessian and wave
laws are consequences of this one Levi--Civita connection law. -/
structure CanonicalPhysicalScalarLeviCivitaTransitionData : Prop where
  agreement :
    ∀ firstPatch secondPatch firstCoordinate secondCoordinate
      (samePoint : firstPatch.coordinateMap firstCoordinate =
        secondPatch.coordinateMap secondCoordinate),
      HolonomicLeviCivitaTransitionAgreement period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        firstPatch secondPatch firstCoordinate secondCoordinate

namespace CanonicalPhysicalScalarRebasedWaveTransitionData

/-- Rebased metric/scalar jets make the local wave contraction independent of
the chosen holonomic representative. -/
theorem waveAtlasCompatible
    (data : CanonicalPhysicalScalarRebasedWaveTransitionData period hPeriod)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasCompatible period hPeriod field := by
  intro firstPatch secondPatch firstCoordinate secondCoordinate hCoordinate
  let agreement := data.agreement field firstPatch secondPatch
    firstCoordinate secondCoordinate hCoordinate
  unfold covariantScalarJetWave
  simp only [localFixedSignMetric]
  rw [agreement.metricFirstJet.metricMatrix_eq,
    localCovariantScalarJet_eq_of_rebasedTransition period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
      firstPatch secondPatch firstCoordinate secondCoordinate agreement]

/-- The rebased transition contract implies universal wave naturality. -/
def toWaveAtlasNaturality
    (data : CanonicalPhysicalScalarRebasedWaveTransitionData period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod :=
  data.waveAtlasCompatible period hPeriod

end CanonicalPhysicalScalarRebasedWaveTransitionData

namespace CanonicalPhysicalScalarCovariantWaveTransitionData

/-- Genuine Hessian covariance, together with the proved metric congruence,
makes the local wave contraction chart-independent. -/
theorem waveAtlasCompatible
    (data : CanonicalPhysicalScalarCovariantWaveTransitionData period hPeriod)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasCompatible period hPeriod field := by
  intro firstPatch secondPatch firstCoordinate secondCoordinate samePoint
  exact localCovariantScalarWave_eq_of_hessian_congruence period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint
      (data.hessian_congruence field firstPatch secondPatch firstCoordinate
        secondCoordinate samePoint)

/-- The genuine transition contract implies universal wave naturality. -/
def toWaveAtlasNaturality
    (data : CanonicalPhysicalScalarCovariantWaveTransitionData period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod :=
  data.waveAtlasCompatible period hPeriod

end CanonicalPhysicalScalarCovariantWaveTransitionData

namespace CanonicalPhysicalScalarLeviCivitaTransitionData

/-- Canonical Levi--Civita transition data supplied by the proved geometric
naturality theorem. -/
def canonical :
    CanonicalPhysicalScalarLeviCivitaTransitionData period hPeriod where
  agreement := by
    intro firstPatch secondPatch firstCoordinate secondCoordinate samePoint
    exact canonicalHolonomicLeviCivitaTransitionAgreement period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint

/-- Levi--Civita naturality produces covariant Hessian naturality for every
smooth scalar field. -/
def toCovariantWaveTransition
    (data : CanonicalPhysicalScalarLeviCivitaTransitionData period hPeriod) :
    CanonicalPhysicalScalarCovariantWaveTransitionData period hPeriod where
  hessian_congruence := by
    intro field firstPatch secondPatch firstCoordinate secondCoordinate
      samePoint
    exact localCovariantScalarHessian_transition_congruence period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
      firstPatch secondPatch firstCoordinate secondCoordinate
        (data.agreement firstPatch secondPatch firstCoordinate secondCoordinate
          samePoint)

/-- Universal wave naturality from the field-independent connection law. -/
def toWaveAtlasNaturality
    (data : CanonicalPhysicalScalarLeviCivitaTransitionData period hPeriod) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod :=
  data.toCovariantWaveTransition period hPeriod
    |>.toWaveAtlasNaturality period hPeriod

end CanonicalPhysicalScalarLeviCivitaTransitionData

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

/-- Wave naturality glues the chart representatives into a global scalar by
evaluating the canonical total-atlas witness at each quotient point. -/
def ofWaveAtlasNaturality
    (naturality : CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod) :
    CanonicalPhysicalScalarIntrinsicWaveData period hPeriod where
  wave field point :=
    let witness := canonicalPhysicalScalarEulerChartWitness
      period hPeriod point
    canonicalPhysicalScalarWaveAtlasRepresentative
      period hPeriod field witness.patch witness.coordinate
  local_eq := by
    intro field patch coordinate
    let witness := canonicalPhysicalScalarEulerChartWitness
      period hPeriod (patch.coordinateMap coordinate)
    change canonicalPhysicalScalarWaveAtlasRepresentative
        period hPeriod field patch coordinate =
      canonicalPhysicalScalarWaveAtlasRepresentative
        period hPeriod field witness.patch witness.coordinate
    exact naturality field patch witness.patch coordinate witness.coordinate
      witness.coordinate_eq.symm

/-- Build the global intrinsic representative from the concrete rebased
transition-jet contract. -/
def ofRebasedWaveTransition
    (transition :
      CanonicalPhysicalScalarRebasedWaveTransitionData period hPeriod) :
    CanonicalPhysicalScalarIntrinsicWaveData period hPeriod :=
  ofWaveAtlasNaturality period hPeriod
    (transition.toWaveAtlasNaturality period hPeriod)

/-- Build the intrinsic wave directly from genuine covariant transition laws. -/
def ofCovariantWaveTransition
    (transition :
      CanonicalPhysicalScalarCovariantWaveTransitionData period hPeriod) :
    CanonicalPhysicalScalarIntrinsicWaveData period hPeriod :=
  ofWaveAtlasNaturality period hPeriod
    (transition.toWaveAtlasNaturality period hPeriod)

/-- Build the intrinsic wave from the field-independent Levi--Civita
transition law. -/
def ofLeviCivitaTransition
    (transition :
      CanonicalPhysicalScalarLeviCivitaTransitionData period hPeriod) :
    CanonicalPhysicalScalarIntrinsicWaveData period hPeriod :=
  ofWaveAtlasNaturality period hPeriod
    (transition.toWaveAtlasNaturality period hPeriod)

/-- Canonical intrinsic wave operator obtained from the proved atlas
naturality of the Levi--Civita connection. -/
def canonical :
    CanonicalPhysicalScalarIntrinsicWaveData period hPeriod :=
  ofLeviCivitaTransition period hPeriod
    (CanonicalPhysicalScalarLeviCivitaTransitionData.canonical
      period hPeriod)

/-- Constructing a global wave representative is equivalent to proving its
coordinate naturality; the global function itself is not an extra obligation. -/
theorem nonempty_iff_waveAtlasNaturality :
    Nonempty (CanonicalPhysicalScalarIntrinsicWaveData period hPeriod) ↔
      CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod := by
  constructor
  · rintro ⟨data⟩
    exact data.toWaveAtlasNaturality period hPeriod
  · intro naturality
    exact ⟨ofWaveAtlasNaturality period hPeriod naturality⟩

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
