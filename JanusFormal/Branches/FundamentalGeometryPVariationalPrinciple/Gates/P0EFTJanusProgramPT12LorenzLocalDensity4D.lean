import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorenzSmoothScalarLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricCurrentLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D

/-! The actual Lorenz operator equals weighted divergence of its raised potential. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LorenzLocalDensity4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

open P0EFTJanusProgramPT12CanonicalCurrentPullback4D
open P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D

open P0EFTJanusProgramPT12CanonicalCurrentLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D

open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D

theorem localLorenz_eq_densityDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    localAbelianLorenzDivergence period hPeriod metric potential component patch coordinate =
      holonomicLocalDensityDivergence (localMetricVolumeFactor period hPeriod metric patch)
        (localRaisedAbelianGaugePotential period hPeriod metric potential component patch) coordinate := by
  let density := localMetricVolumeFactor period hPeriod metric patch
  let field := localRaisedAbelianGaugePotential period hPeriod metric potential component patch
  have hDensity : DifferentiableAt Real density coordinate :=
    (localMetricVolumeFactor_contDiff period hPeriod metric patch).differentiable (by simp) coordinate
  have hNe : density coordinate ≠ 0 := localMetricVolumeFactor_ne_zero period hPeriod metric patch coordinate
  have hField : DifferentiableAt Real field coordinate :=
    (localRaisedAbelianGaugePotential_contDiff period hPeriod metric potential component patch).differentiable
      (by simp) coordinate
  have hComponent (index : Fin 4) : DifferentiableAt Real (fun current => field current index) coordinate := by
    fun_prop
  have hGamma (upper first second : Fin 4) :
      localLeviCivitaChristoffel period hPeriod metric patch coordinate upper first second =
        localLeviCivitaChristoffel period hPeriod metric patch coordinate upper second first :=
    (localLeviCivitaConnectionJet period hPeriod metric patch coordinate).torsionFree upper first second
  have hTerm (index : Fin 4) :
      fderiv Real (fun current => density current * field current index) coordinate (Pi.single index 1) /
          density coordinate =
        fderiv Real (fun current => field current index) coordinate (Pi.single index 1) +
          ∑ contracted : Fin 4, localLeviCivitaChristoffel period hPeriod metric patch coordinate
            contracted contracted index * field coordinate index := by
    have hProduct := congrArg (fun derivative : Vector4 →L[Real] Real => derivative (Pi.single index 1))
      (fderiv_mul hDensity (hComponent index))
    change fderiv Real (fun current => density current * field current index) coordinate
        (Pi.single index 1) = _ at hProduct
    simp only [add_apply, smul_apply, smul_eq_mul] at hProduct
    rw [hProduct]
    have hDerivative := localMetricVolumeFactor_fderiv_basis_eq_christoffelTrace
      period hPeriod metric patch coordinate index
    change fderiv Real density coordinate (Pi.single index 1) = _ at hDerivative
    rw [hDerivative]
    simp_rw [hGamma _ index _, ← Finset.sum_mul]
    change (density coordinate * _ + _ * (density coordinate * _)) / density coordinate = _
    field_simp [hNe]
  change localAbelianLorenzDivergence period hPeriod metric potential component patch coordinate =
    holonomicLocalDensityDivergence density field coordinate
  unfold holonomicLocalDensityDivergence
  rw [Finset.sum_div]
  simp_rw [hTerm]
  unfold localAbelianLorenzDivergence
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact congrArg (fun connection =>
    (∑ index : Fin 4, fderiv Real (fun current => field current index) coordinate
      (Pi.single index 1)) + connection)
    (Finset.sum_comm (f := fun first second : Fin 4 =>
      localLeviCivitaChristoffel period hPeriod metric patch coordinate first first second *
        field coordinate second))

end
end P0EFTJanusProgramPT12LorenzLocalDensity4D
end JanusFormal
