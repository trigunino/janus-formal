import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

/-!
# Global scalar-stress conservation on the actual quotient

The local Levi--Civita gates already prove
`div_g T = E(phi) * grad_g(phi)` for genuine smooth Lorentz metrics and scalar
fields on every supplied holonomic patch.  The canonical transition-jet gate
adds exactly the missing overlap statement after both local jets have been
rebased into a common frame.

This gate chooses one realization from the covering bridge at each point,
defines the global Euler residual, raised gradient and stress divergence, and
proves that each agrees with every other selected local realization.  Hence
vanishing of the local Euler--Lagrange residuals implies global
`div_g T = 0`.

No new regularity contract is introduced.  The sole residual input is the
existing `CanonicalHolonomicAtlasStressConservationBridge`, because the
quotient API still does not construct `SmoothHolonomicFrameChart4` and its
rebased metric/scalar jets from the raw local-section charts.  The resulting
object is a well-defined pointwise rebased divergence; no extra global
smooth-section or integration theorem is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalScalarStressConservation4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One patch selected from the true covering family carried by the residual
rebasing bridge. -/
def globalScalarStressChosenPatch
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (point : EffectiveQuotient period hPeriod) :
    SmoothHolonomicFrameChart4 period hPeriod :=
  (bridge.covers point).choose

theorem globalScalarStressChosenPatch_mem
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (point : EffectiveQuotient period hPeriod) :
    globalScalarStressChosenPatch period hPeriod metric field bridge point ∈
      bridge.atlasPatches :=
  (bridge.covers point).choose_spec.1

/-- A coordinate in the selected patch representing the requested quotient
point. -/
def globalScalarStressChosenCoordinate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (point : EffectiveQuotient period hPeriod) : Vector4 :=
  (bridge.covers point).choose_spec.2.choose

theorem globalScalarStressChosenCoordinate_mapsTo
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (point : EffectiveQuotient period hPeriod) :
    (globalScalarStressChosenPatch period hPeriod metric field bridge point).coordinateMap
        (globalScalarStressChosenCoordinate period hPeriod metric field bridge
          point) = point :=
  (bridge.covers point).choose_spec.2.choose_spec

/-- Global Euler residual represented in any one coherently rebased atlas
patch. -/
def globalSmoothScalarEulerResidual
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  localSmoothScalarEulerResidual period hPeriod metric
    (globalScalarStressChosenPatch period hPeriod metric field bridge point)
    field massSquared source
    (globalScalarStressChosenCoordinate period hPeriod metric field bridge point)

/-- Global raised scalar gradient in the same rebased atlas frame. -/
def globalSmoothScalarRaisedGradient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (point : EffectiveQuotient period hPeriod) : Vector4 :=
  localSmoothScalarRaisedGradient period hPeriod metric
    (globalScalarStressChosenPatch period hPeriod metric field bridge point)
    field
    (globalScalarStressChosenCoordinate period hPeriod metric field bridge point)

/-- Pointwise global covariant scalar-stress divergence, defined through the
coherently rebased covering bridge. -/
def globalSmoothScalarStressDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (point : EffectiveQuotient period hPeriod) : Vector4 :=
  localSmoothScalarStressDivergence period hPeriod metric
    (globalScalarStressChosenPatch period hPeriod metric field bridge point)
    field massSquared source
    (globalScalarStressChosenCoordinate period hPeriod metric field bridge point)

/-- The chosen global Euler representative agrees with every selected local
realization at the same quotient point. -/
theorem globalSmoothScalarEulerResidual_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (point : EffectiveQuotient period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (hPatch : patch ∈ bridge.atlasPatches)
    (coordinate : Vector4)
    (hCoordinate : patch.coordinateMap coordinate = point) :
    globalSmoothScalarEulerResidual period hPeriod metric field bridge
        massSquared source point =
      localSmoothScalarEulerResidual period hPeriod metric patch field
        massSquared source coordinate := by
  apply localSmoothScalarEulerResidual_eq_of_rebasedTransition
  exact bridge.transitionJets.agreement
    (globalScalarStressChosenPatch period hPeriod metric field bridge point)
    patch
    (globalScalarStressChosenPatch_mem period hPeriod metric field bridge point)
    hPatch
    (globalScalarStressChosenCoordinate period hPeriod metric field bridge point)
    coordinate
    ((globalScalarStressChosenCoordinate_mapsTo
      period hPeriod metric field bridge point).trans hCoordinate.symm)

/-- The chosen raised-gradient representative is likewise independent of the
selected patch after rebasing. -/
theorem globalSmoothScalarRaisedGradient_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (point : EffectiveQuotient period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (hPatch : patch ∈ bridge.atlasPatches)
    (coordinate : Vector4)
    (hCoordinate : patch.coordinateMap coordinate = point) :
    globalSmoothScalarRaisedGradient period hPeriod metric field bridge point =
      localSmoothScalarRaisedGradient period hPeriod metric patch field
        coordinate := by
  apply localSmoothScalarRaisedGradient_eq_of_rebasedTransition
  exact bridge.transitionJets.agreement
    (globalScalarStressChosenPatch period hPeriod metric field bridge point)
    patch
    (globalScalarStressChosenPatch_mem period hPeriod metric field bridge point)
    hPatch
    (globalScalarStressChosenCoordinate period hPeriod metric field bridge point)
    coordinate
    ((globalScalarStressChosenCoordinate_mapsTo
      period hPeriod metric field bridge point).trans hCoordinate.symm)

/-- The global divergence agrees with every local realization; this is the
well-definedness statement supplied by the transition-jet bridge. -/
theorem globalSmoothScalarStressDivergence_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (point : EffectiveQuotient period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (hPatch : patch ∈ bridge.atlasPatches)
    (coordinate : Vector4)
    (hCoordinate : patch.coordinateMap coordinate = point) :
    globalSmoothScalarStressDivergence period hPeriod metric field bridge
        massSquared source point =
      localSmoothScalarStressDivergence period hPeriod metric patch field
        massSquared source coordinate := by
  exact CanonicalHolonomicAtlasStressConservationBridge.stressCompatible
    period hPeriod metric field bridge massSquared source
      (globalScalarStressChosenPatch period hPeriod metric field bridge point)
      patch
      (globalScalarStressChosenPatch_mem period hPeriod metric field bridge point)
      hPatch
      (globalScalarStressChosenCoordinate period hPeriod metric field bridge point)
      coordinate
      ((globalScalarStressChosenCoordinate_mapsTo
        period hPeriod metric field bridge point).trans hCoordinate.symm)

/-- Global form of the exact local Noether identity
`div_g T = E(phi) * grad_g(phi)`. -/
theorem globalSmoothScalarStressDivergence_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    globalSmoothScalarStressDivergence period hPeriod metric field bridge
        massSquared source point index =
      globalSmoothScalarEulerResidual period hPeriod metric field bridge
          massSquared source point *
        globalSmoothScalarRaisedGradient period hPeriod metric field bridge
          point index := by
  exact localSmoothScalarStressDivergence_apply period hPeriod metric
    (globalScalarStressChosenPatch period hPeriod metric field bridge point)
    field massSquared source
    (globalScalarStressChosenCoordinate period hPeriod metric field bridge point)
    index

/-- Patchwise Euler--Lagrange equations on the genuine metric and scalar
fields selected by the bridge. -/
def CanonicalAtlasLocalScalarEulerEquations
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real) : Prop :=
  ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod),
    patch ∈ bridge.atlasPatches → ∀ coordinate : Vector4,
      localSmoothScalarEulerResidual period hPeriod metric patch field
        massSquared source coordinate = 0

/-- Pointwise global stress conservation predicate. -/
def GlobalSmoothScalarStressConserved
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real) : Prop :=
  ∀ point : EffectiveQuotient period hPeriod,
    globalSmoothScalarStressDivergence period hPeriod metric field bridge
      massSquared source point = 0

/-- Local Euler equations descend to a zero global Euler residual. -/
theorem globalSmoothScalarEulerResidual_eq_zero_of_localEuler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (hEuler : CanonicalAtlasLocalScalarEulerEquations period hPeriod metric
      field bridge massSquared source) :
    ∀ point : EffectiveQuotient period hPeriod,
      globalSmoothScalarEulerResidual period hPeriod metric field bridge
        massSquared source point = 0 := by
  intro point
  exact hEuler
    (globalScalarStressChosenPatch period hPeriod metric field bridge point)
    (globalScalarStressChosenPatch_mem period hPeriod metric field bridge point)
    (globalScalarStressChosenCoordinate period hPeriod metric field bridge point)

/-- A globally vanishing Euler residual forces the glued covariant stress
divergence to vanish at every quotient point. -/
theorem globalSmoothScalarStressDivergence_eq_zero_of_globalEuler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (hEuler : ∀ point : EffectiveQuotient period hPeriod,
      globalSmoothScalarEulerResidual period hPeriod metric field bridge
        massSquared source point = 0) :
    GlobalSmoothScalarStressConserved period hPeriod metric field bridge
      massSquared source := by
  intro point
  funext index
  rw [globalSmoothScalarStressDivergence_apply, hEuler point, zero_mul]
  rfl

/-- Main global conservation theorem: once the true local Euler--Lagrange
equations vanish, `div_g T = 0` is closed globally.  No hypothesis beyond the
single residual atlas-rebasing bridge is used. -/
theorem globalSmoothScalarStressDivergence_eq_zero_of_localEuler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (hEuler : CanonicalAtlasLocalScalarEulerEquations period hPeriod metric
      field bridge massSquared source) :
    GlobalSmoothScalarStressConserved period hPeriod metric field bridge
      massSquared source :=
  globalSmoothScalarStressDivergence_eq_zero_of_globalEuler
    period hPeriod metric field bridge massSquared source
      (globalSmoothScalarEulerResidual_eq_zero_of_localEuler
        period hPeriod metric field bridge massSquared source hEuler)

/-- Compact closure statement exposing both the descended Euler equation and
global stress conservation. -/
theorem global_scalar_stress_conservation4D_closure
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real)
    (hEuler : CanonicalAtlasLocalScalarEulerEquations period hPeriod metric
      field bridge massSquared source) :
    (∀ point : EffectiveQuotient period hPeriod,
      globalSmoothScalarEulerResidual period hPeriod metric field bridge
        massSquared source point = 0) ∧
      GlobalSmoothScalarStressConserved period hPeriod metric field bridge
        massSquared source :=
  ⟨globalSmoothScalarEulerResidual_eq_zero_of_localEuler
      period hPeriod metric field bridge massSquared source hEuler,
    globalSmoothScalarStressDivergence_eq_zero_of_localEuler
      period hPeriod metric field bridge massSquared source hEuler⟩

end

end P0EFTJanusMappingTorusGlobalScalarStressConservation4D
end JanusFormal
