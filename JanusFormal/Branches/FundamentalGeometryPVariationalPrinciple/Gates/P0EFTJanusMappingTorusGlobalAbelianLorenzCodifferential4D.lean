import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarWave4D

/-!
# Global abelian Lorenz codifferential

The local Levi--Civita divergence of the metric-raised intrinsic gauge
potential is chart-independent.  It therefore defines a smooth global
`U(1)^2`-valued scalar field and a real-linear operator on genuine smooth
abelian gauge potentials.  On an exact potential it is the componentwise
canonical scalar wave.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalAbelianLorenzCodifferential4D

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
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusGlobalSmoothScalarWave4D

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

/-- Pointwise global Lorenz divergence selected from the canonical total
holonomic atlas. -/
def canonicalGlobalAbelianLorenzCodifferentialValue
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  localAbelianLorenzDivergence period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    potential component witness.patch witness.coordinate

/-- The selected global value agrees with the Lorenz divergence in every
holonomic chart. -/
theorem canonicalGlobalAbelianLorenzCodifferentialValue_eq_local
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod potential
        component (patch.coordinateMap coordinate) =
      localAbelianLorenzDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        potential component patch coordinate := by
  unfold canonicalGlobalAbelianLorenzCodifferentialValue
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod
      (patch.coordinateMap coordinate)
  exact localAbelianLorenzDivergence_transition period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    potential component witness.patch patch witness.coordinate coordinate
      witness.coordinate_eq

/-- One scalar component of the global Lorenz codifferential is smooth. -/
def canonicalGlobalAbelianLorenzCodifferentialComponent
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    SmoothScalarField period hPeriod where
  toFun :=
    canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod potential
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
          (localAbelianLorenzDivergence period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              potential component witness.patch ∘
            hLocal.localInverse)
          (witness.patch.coordinateMap witness.coordinate) :=
      (localAbelianLorenzDivergence_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        potential component witness.patch)
        |>.contMDiff.contMDiffAt.comp _
          hLocal.localInverse_contMDiffAt
    apply hRepresentative.congr_of_eventuallyEq
    filter_upwards [hLocal.localInverse_eventuallyEq_right] with nearby hNearby
    have hRight :
        witness.patch.coordinateMap (hLocal.localInverse nearby) = nearby := by
      simpa only [Function.comp_apply, id_eq] using hNearby
    change
      canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod potential
          component nearby =
        localAbelianLorenzDivergence period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          potential component witness.patch (hLocal.localInverse nearby)
    calc
      canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod potential
          component nearby =
          canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod
            potential component
              (witness.patch.coordinateMap (hLocal.localInverse nearby)) :=
        congrArg
          (canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod
            potential component) hRight.symm
      _ = _ :=
        canonicalGlobalAbelianLorenzCodifferentialValue_eq_local period hPeriod
          potential component witness.patch (hLocal.localInverse nearby)

/-- Genuine smooth global Lorenz codifferential on intrinsic abelian gauge
potentials, with convention `δ A = div_g (A♯)`. -/
def canonicalGlobalAbelianLorenzCodifferential
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 2) Real).symm (fun component =>
      canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod potential
        component point)
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 2) Real).symm.contDiff.contMDiff.comp
    rw [contMDiff_pi_space]
    intro component
    exact
      (canonicalGlobalAbelianLorenzCodifferentialComponent period hPeriod
        potential component).contMDiff_toFun

@[simp]
theorem canonicalGlobalAbelianLorenzCodifferential_apply
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (component : Fin 2) :
    canonicalGlobalAbelianLorenzCodifferential period hPeriod potential point
        component =
      canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod potential
        component point :=
  rfl

theorem canonicalGlobalAbelianLorenzCodifferential_add
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    canonicalGlobalAbelianLorenzCodifferential period hPeriod (first + second) =
      canonicalGlobalAbelianLorenzCodifferential period hPeriod first +
        canonicalGlobalAbelianLorenzCodifferential period hPeriod second := by
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply (EuclideanSpace.equiv (Fin 2) Real).injective
  funext component
  change
    canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod
        (first + second) component point =
      canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod first
          component point +
        canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod second
          component point
  unfold canonicalGlobalAbelianLorenzCodifferentialValue
  exact localAbelianLorenzDivergence_add period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) first second component
      (canonicalPhysicalScalarEulerChartWitness period hPeriod point).patch
      (canonicalPhysicalScalarEulerChartWitness period hPeriod point).coordinate

theorem canonicalGlobalAbelianLorenzCodifferential_smul
    (scalar : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    canonicalGlobalAbelianLorenzCodifferential period hPeriod
        (scalar • potential) =
      scalar •
        canonicalGlobalAbelianLorenzCodifferential period hPeriod potential := by
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply (EuclideanSpace.equiv (Fin 2) Real).injective
  funext component
  change
    canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod
        (scalar • potential) component point =
      scalar *
        canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod
          potential component point
  unfold canonicalGlobalAbelianLorenzCodifferentialValue
  exact localAbelianLorenzDivergence_smul period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) scalar potential
      component
      (canonicalPhysicalScalarEulerChartWitness period hPeriod point).patch
      (canonicalPhysicalScalarEulerChartWitness period hPeriod point).coordinate

/-- The global Lorenz codifferential is a real-linear operator. -/
def canonicalGlobalAbelianLorenzCodifferentialLinearMap :
    SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun := canonicalGlobalAbelianLorenzCodifferential period hPeriod
  map_add' := canonicalGlobalAbelianLorenzCodifferential_add period hPeriod
  map_smul' := canonicalGlobalAbelianLorenzCodifferential_smul period hPeriod

@[simp]
theorem canonicalGlobalAbelianLorenzCodifferentialLinearMap_apply
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    canonicalGlobalAbelianLorenzCodifferentialLinearMap period hPeriod
        potential =
      canonicalGlobalAbelianLorenzCodifferential period hPeriod potential :=
  rfl

/-- Componentwise canonical scalar wave on a genuine global gauge-algebra
field. -/
def canonicalGlobalGaugeSmoothScalarWave
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 2) Real).symm (fun component =>
      canonicalGlobalSmoothScalarWave period hPeriod
        (ghostComponent period hPeriod parameter component) point)
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 2) Real).symm.contDiff.contMDiff.comp
    rw [contMDiff_pi_space]
    intro component
    exact
      (canonicalGlobalSmoothScalarWave period hPeriod
        (ghostComponent period hPeriod parameter component)).contMDiff_toFun

@[simp]
theorem canonicalGlobalGaugeSmoothScalarWave_apply
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod)
    (component : Fin 2) :
    canonicalGlobalGaugeSmoothScalarWave period hPeriod parameter point
        component =
      canonicalGlobalSmoothScalarWave period hPeriod
        (ghostComponent period hPeriod parameter component) point :=
  rfl

/-- With the declared plus-divergence convention, the Lorenz codifferential of
an exact gauge potential is exactly the componentwise canonical scalar wave. -/
theorem canonicalGlobalAbelianLorenzCodifferential_exact
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    canonicalGlobalAbelianLorenzCodifferential period hPeriod
        (exactGaugePotential period hPeriod parameter) =
      canonicalGlobalGaugeSmoothScalarWave period hPeriod parameter := by
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply (EuclideanSpace.equiv (Fin 2) Real).injective
  funext component
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  change
    canonicalGlobalAbelianLorenzCodifferentialValue period hPeriod
        (exactGaugePotential period hPeriod parameter) component
          (witness.patch.coordinateMap witness.coordinate) =
      canonicalGlobalSmoothScalarWave period hPeriod
        (ghostComponent period hPeriod parameter component)
          (witness.patch.coordinateMap witness.coordinate)
  rw [canonicalGlobalAbelianLorenzCodifferentialValue_eq_local,
    canonicalGlobalSmoothScalarWave_eq_local,
    localAbelianLorenzDivergence_exact]
  rfl

end
end P0EFTJanusMappingTorusGlobalAbelianLorenzCodifferential4D
end JanusFormal
