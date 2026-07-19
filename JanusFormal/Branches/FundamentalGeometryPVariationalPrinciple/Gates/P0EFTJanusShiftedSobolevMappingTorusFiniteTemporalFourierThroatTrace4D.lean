import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

/-!
# Throat trace of finite temporal Fourier fields

The genuine smooth throat trace remains injective on the finite temporal
Fourier subspace.  Consequently, homogeneous Dirichlet data on this subspace
force every finite Fourier coefficient to vanish.

This is only a finite-mode temporal statement.  It does not construct a
Sobolev completion or an unconditional Sobolev trace theorem.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierThroatTrace4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

variable (period : Real) [hPeriodPos : Fact (0 < period)]

private abbrev sphereData :=
  reflectedSphereData period hPeriodPos.out.ne'

private abbrev throatData :=
  fixedEquatorData period hPeriodPos.out.ne'

private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period)

private abbrev EffectiveThroat :=
  MappingTorus (throatData period)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period) :=
  reflectedSphereQuotientChartedSpace period hPeriodPos.out.ne'

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period) :=
  reflectedSphereQuotient_isManifold period hPeriodPos.out.ne'

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period) :=
  fixedThroatQuotientChartedSpace period hPeriodPos.out.ne'

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period) :=
  fixedThroatQuotient_isManifold period hPeriodPos.out.ne'

/-- A fixed equatorial point used only to observe every temporal value on the
embedded throat. -/
private def temporalThroatAnchor : EquatorialTwoSphere :=
  ⟨fun index => if index = (1 : Fin 4) then 1 else 0, by
    constructor
    · simp [OnUnitThreeSphere, radiusSquared]
    · simp⟩

/-- Restriction of the genuine quotient realization to the genuine smooth
throat, as a real-linear map. -/
def finiteTemporalFourierThroatTraceLinearMap :
    FiniteTemporalFourierCoefficients →ₗ[Real]
      SmoothThroatField period hPeriodPos.out.ne' Complex :=
  (throatTraceLinearMap period hPeriodPos.out.ne' Complex).comp
    (finiteTemporalFourierFieldLinearMap period)

/-- The throat sees the full time circle at one fixed equatorial point, so no
finite temporal Fourier coefficient is lost by restriction. -/
theorem finiteTemporalFourierThroatTraceLinearMap_injective :
    Function.Injective
      (finiteTemporalFourierThroatTraceLinearMap period) := by
  intro first second hEqual
  apply temporalFourierPolynomialCircleLinearMap_injective period
  apply ContinuousMap.ext
  intro circlePoint
  induction circlePoint using QuotientAddGroup.induction_on with
  | H time =>
      have hValue := congrArg
        (fun field : SmoothThroatField period hPeriodPos.out.ne' Complex =>
          field (mappingTorusMk (throatData period)
            ⟨temporalThroatAnchor, time⟩)) hEqual
      change
        finiteTemporalFourierFieldLinearMap period first
              (fixedThroatQuotientInclusion period hPeriodPos.out.ne'
                (mappingTorusMk (throatData period)
                  ⟨temporalThroatAnchor, time⟩)) =
          finiteTemporalFourierFieldLinearMap period second
              (fixedThroatQuotientInclusion period hPeriodPos.out.ne'
                (mappingTorusMk (throatData period)
                  ⟨temporalThroatAnchor, time⟩)) at hValue
      rw [fixedThroatQuotientInclusion_mk] at hValue
      simpa only [finiteTemporalFourierField_mk_eq_circle,
        fixedThroatCoverInclusion] using hValue

/-- On the finite temporal Fourier subspace, homogeneous smooth Dirichlet data
are equivalent to vanishing of the coefficient sequence. -/
theorem finiteTemporalFourierField_satisfiesDirichlet_zero_iff
    (coefficients : FiniteTemporalFourierCoefficients) :
    SatisfiesDirichlet period hPeriodPos.out.ne' Complex 0
        (finiteTemporalFourierFieldLinearMap period coefficients) ↔
      coefficients = 0 := by
  change finiteTemporalFourierThroatTraceLinearMap period coefficients = 0 ↔
    coefficients = 0
  constructor
  · intro hTrace
    apply finiteTemporalFourierThroatTraceLinearMap_injective period
    simpa using hTrace
  · rintro rfl
    exact map_zero _

end

end P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierThroatTrace4D
end JanusFormal
