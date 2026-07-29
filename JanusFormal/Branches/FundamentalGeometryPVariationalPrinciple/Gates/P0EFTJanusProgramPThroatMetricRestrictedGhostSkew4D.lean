import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D

/-!
# Restriction-scoped throat ghost bridge

An arbitrary quotient ghost need not be tangent to the fixed throat.  This
gate records the exact derivative-of-inclusion condition for a genuine throat
restriction.  No throat-metric skew-adjointness statement is made here: that
requires a concrete tensor pullback orbit, pairing invariance, and an
independently proved derivative/action identification.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricRestrictedGhostSkew4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
open P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusProgramPCoadjointAntifieldBRST4D
open P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D
open P0EFTJanusProgramPThroatMetricTensorModule4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Exact tangency/restriction datum for a quotient ghost along the embedded
fixed throat. -/
structure BulkGhostThroatRestrictionData
    (bulkGhost : CInfinityDiffeomorphismGhost period hPeriod) where
  throatGhost : CInfinityThroatGhost period hPeriod
  inclusion_related :
    ∀ point : EffectiveThroat period hPeriod,
      mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point
          (throatGhost point) =
        bulkGhost (fixedThroatQuotientInclusion period hPeriod point)

/-- The genuine quotient-time ghost restricts to the genuine throat-time
ghost through the derivative of the fixed-throat inclusion. -/
theorem effectiveTimeTranslationGhost_inclusion_related
    (point : EffectiveThroat period hPeriod) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod) point
        (throatTimeTranslationGhost period hPeriod point) =
      smoothGhostToCInfinity period hPeriod
        (effectiveTimeTranslationGhost period hPeriod)
        (fixedThroatQuotientInclusion period hPeriod point) := by
  change mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point
      (throatTimeTranslationVelocity period hPeriod point) =
    effectiveTimeTranslationVelocity period hPeriod
      (fixedThroatQuotientInclusion period hPeriod point)
  rw [throatTimeTranslationVelocity_eq_curve_mfderiv,
    effectiveTimeTranslationVelocity_eq_timeFlow_mfderiv]
  have hCurve :
      MDifferentiableAt 𝓘(Real, Real) throatCoverModelWithCorners
        (fun parameter : Real =>
          throatTimeFlow period hPeriod parameter point) 0 :=
    (((throatJointTimeFlow_contMDiff period hPeriod).comp
      (contMDiff_id.prodMk contMDiff_const)).congr
        (fun _ => rfl)).mdifferentiableAt (by simp)
  have hInclusion :
      MDifferentiableAt throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        (throatTimeFlow period hPeriod 0 point) :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hComp := mfderiv_comp_apply 0 hInclusion hCurve (1 : Real)
  rw [throatTimeFlow_zero] at hComp
  rw [show
      fixedThroatQuotientInclusion period hPeriod ∘
          (fun parameter : Real =>
            throatTimeFlow period hPeriod parameter point) =
        (fun parameter : Real =>
          effectiveTimeFlow period hPeriod parameter
            (fixedThroatQuotientInclusion period hPeriod point)) by
      funext parameter
      exact fixedThroatQuotientInclusion_timeFlow
        period hPeriod parameter point] at hComp
  exact hComp.symm

/-- Concrete, non-vacuous restriction certificate for the complete time
translation subgroup. -/
def effectiveTimeTranslationBulkGhostThroatRestriction :
    BulkGhostThroatRestrictionData period hPeriod
      (smoothGhostToCInfinity period hPeriod
        (effectiveTimeTranslationGhost period hPeriod)) where
  throatGhost := throatTimeTranslationGhost period hPeriod
  inclusion_related :=
    effectiveTimeTranslationGhost_inclusion_related period hPeriod

end
end P0EFTJanusProgramPThroatMetricRestrictedGhostSkew4D
end JanusFormal
