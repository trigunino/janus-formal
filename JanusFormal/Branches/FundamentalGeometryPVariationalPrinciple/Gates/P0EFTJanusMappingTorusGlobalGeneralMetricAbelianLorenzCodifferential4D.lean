import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalAbelianLorenzCodifferential4D

/-!
# Global Lorenz codifferential for a supplied general metric

This gate reuses the local Lorenz operator and its full transition law to
descend `div_g (A^sharp)` for any supplied smooth general Lorentz metric.
The canonical intrinsic operator is one specialization.  The associated
Faddeev--Popov operator is the actual composite `delta_g d`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusGlobalAbelianLorenzCodifferential4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pointwise Lorenz value selected from the canonical total holonomic atlas. -/
def globalGeneralMetricAbelianLorenzValue
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  localAbelianLorenzDivergence period hPeriod metric potential component
    witness.patch witness.coordinate

/-- The selected value agrees with every holonomic-chart representative. -/
theorem globalGeneralMetricAbelianLorenzValue_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
        component (patch.coordinateMap coordinate) =
      localAbelianLorenzDivergence period hPeriod metric potential component
        patch coordinate := by
  unfold globalGeneralMetricAbelianLorenzValue
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod
      (patch.coordinateMap coordinate)
  exact localAbelianLorenzDivergence_transition period hPeriod metric
    potential component witness.patch patch witness.coordinate coordinate
      witness.coordinate_eq

/-- One component of the descended Lorenz field is smooth. -/
def globalGeneralMetricAbelianLorenzComponent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    SmoothScalarField period hPeriod where
  toFun :=
    globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
      component
  contMDiff_toFun := by
    intro point
    let witness :=
      canonicalPhysicalScalarEulerChartWitness period hPeriod point
    rw [← witness.coordinate_eq]
    let hLocal :=
      witness.patch.coordinateMap_isLocalDiffeomorph witness.coordinate
    have hRepresentative :
        ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
          (localAbelianLorenzDivergence period hPeriod metric potential
              component witness.patch ∘ hLocal.localInverse)
          (witness.patch.coordinateMap witness.coordinate) :=
      (localAbelianLorenzDivergence_contDiff period hPeriod metric potential
        component witness.patch)
        |>.contMDiff.contMDiffAt.comp _
          hLocal.localInverse_contMDiffAt
    apply hRepresentative.congr_of_eventuallyEq
    filter_upwards [hLocal.localInverse_eventuallyEq_right] with nearby hNearby
    have hRight :
        witness.patch.coordinateMap (hLocal.localInverse nearby) = nearby := by
      simpa only [Function.comp_apply, id_eq] using hNearby
    change
      globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
          component nearby =
        localAbelianLorenzDivergence period hPeriod metric potential component
          witness.patch (hLocal.localInverse nearby)
    calc
      globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
          component nearby =
          globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
            component
              (witness.patch.coordinateMap (hLocal.localInverse nearby)) :=
        congrArg
          (globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
            component) hRight.symm
      _ = _ :=
        globalGeneralMetricAbelianLorenzValue_eq_local period hPeriod metric
          potential component witness.patch (hLocal.localInverse nearby)

/-- Genuine global `delta_g A = div_g (A^sharp)` for a supplied metric. -/
def globalGeneralMetricAbelianLorenzCodifferential
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 2) Real).symm (fun component =>
      globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
        component point)
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 2) Real).symm.contDiff.contMDiff.comp
    rw [contMDiff_pi_space]
    intro component
    exact
      (globalGeneralMetricAbelianLorenzComponent period hPeriod metric
        potential component).contMDiff_toFun

@[simp]
theorem globalGeneralMetricAbelianLorenzCodifferential_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (component : Fin 2) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
        potential point component =
      globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
        component point :=
  rfl

theorem globalGeneralMetricAbelianLorenzCodifferential_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
        (first + second) =
      globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
          first +
        globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
          second := by
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply (EuclideanSpace.equiv (Fin 2) Real).injective
  funext component
  change
    globalGeneralMetricAbelianLorenzValue period hPeriod metric
        (first + second) component point =
      globalGeneralMetricAbelianLorenzValue period hPeriod metric first
          component point +
        globalGeneralMetricAbelianLorenzValue period hPeriod metric second
          component point
  unfold globalGeneralMetricAbelianLorenzValue
  exact localAbelianLorenzDivergence_add period hPeriod metric first second
    component
    (canonicalPhysicalScalarEulerChartWitness period hPeriod point).patch
    (canonicalPhysicalScalarEulerChartWitness period hPeriod point).coordinate

theorem globalGeneralMetricAbelianLorenzCodifferential_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
        (scalar • potential) =
      scalar •
        globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
          potential := by
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply (EuclideanSpace.equiv (Fin 2) Real).injective
  funext component
  change
    globalGeneralMetricAbelianLorenzValue period hPeriod metric
        (scalar • potential) component point =
      scalar *
        globalGeneralMetricAbelianLorenzValue period hPeriod metric potential
          component point
  unfold globalGeneralMetricAbelianLorenzValue
  exact localAbelianLorenzDivergence_smul period hPeriod metric scalar
    potential component
    (canonicalPhysicalScalarEulerChartWitness period hPeriod point).patch
    (canonicalPhysicalScalarEulerChartWitness period hPeriod point).coordinate

/-- The supplied-metric Lorenz codifferential is real-linear in `A`. -/
def globalGeneralMetricAbelianLorenzCodifferentialLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun :=
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
  map_add' :=
    globalGeneralMetricAbelianLorenzCodifferential_add period hPeriod metric
  map_smul' :=
    globalGeneralMetricAbelianLorenzCodifferential_smul period hPeriod metric

/-- The actual Faddeev--Popov operator `delta_g d`. -/
def globalGeneralMetricAbelianFaddeevPopov
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra :=
  globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
    (exactGaugePotential period hPeriod parameter)

/-- `delta_g d` bundled as the composition of the two existing linear maps. -/
def globalGeneralMetricAbelianFaddeevPopovLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra →ₗ[Real]
      SmoothQuotientField period hPeriod GaugeLieAlgebra :=
  (globalGeneralMetricAbelianLorenzCodifferentialLinearMap period hPeriod
    metric).comp (abelianGaugeGenerator period hPeriod)

@[simp]
theorem globalGeneralMetricAbelianFaddeevPopovLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    globalGeneralMetricAbelianFaddeevPopovLinearMap period hPeriod metric
        parameter =
      globalGeneralMetricAbelianFaddeevPopov period hPeriod metric parameter :=
  rfl

/-- In every chart, `delta_g d` is the covariant scalar wave of `g`. -/
theorem globalGeneralMetricAbelianFaddeevPopov_apply_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod metric parameter
        (patch.coordinateMap coordinate) component =
      covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (ghostComponent period hPeriod parameter component) coordinate) := by
  rw [globalGeneralMetricAbelianFaddeevPopov,
    globalGeneralMetricAbelianLorenzCodifferential_apply,
    globalGeneralMetricAbelianLorenzValue_eq_local,
    localAbelianLorenzDivergence_exact]

/-- The previous canonical Lorenz operator is exactly the intrinsic-metric
specialization of the supplied-metric construction. -/
theorem globalGeneralMetricAbelianLorenzCodifferential_intrinsic
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) potential =
      canonicalGlobalAbelianLorenzCodifferential period hPeriod potential := by
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply (EuclideanSpace.equiv (Fin 2) Real).injective
  funext component
  rfl

end
end P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
end JanusFormal
