import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationBoundaryDomainBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterActionVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarDirichletOrientedGreenStokesClosure4D

/-!
# Program P boundary tangents feed the physical scalar Green--Stokes domain

The common Program P domain fixes the complete throat trace along every
admissible variation curve.  Hence each scalar matter component of an
admissible tangent has homogeneous Dirichlet trace.  This derives the
Dirichlet input of the oriented Green--Stokes closure from the existing
Program P domain; no additional boundary axiom is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBoundaryTangentGreenStokes4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMappingTorusScalarSeparatedBoundaryCondition4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarDirichletOrientedGreenStokesClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Every scalar matter component of a Program P boundary tangent has zero
throat trace.  This is the homogeneous Dirichlet condition on variations,
derived from preservation of the fixed background boundary datum. -/
theorem programPBoundaryTangent_matterComponent_homogeneousDirichlet
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (hVariation :
      variation ∈ programPBoundaryTangentDomain4D period hPeriod domain)
    (component : MatterComponentIndex) :
    SatisfiesDirichlet period hPeriod Real 0
      (matterVariationComponentFamily period hPeriod
        variation.independent.matter component) := by
  have hVariedBoundary := hVariation (1 : Real)
  unfold SatisfiesIndependentBoundary at hVariedBoundary
  have hTrace :
      independentBoundaryTrace period hPeriod
          (independentFieldCurve period hPeriod domain.configuration
            variation.independent 1) =
        independentBoundaryTrace period hPeriod domain.configuration :=
    hVariedBoundary.trans domain.boundary_coherent.symm
  have hMatter := congrArg IndependentBoundaryData.matter hTrace
  rcases component with ⟨sector, coordinate⟩
  fin_cases sector
  · have hSector := congrArg Prod.fst hMatter
    unfold SatisfiesDirichlet
    apply SmoothThroatField.ext period hPeriod Real
    intro point
    have hPoint := congrArg
      (fun field : SmoothThroatField period hPeriod MatterFiber => field point)
      hSector
    have hZero :
        variation.independent.matter.1
          (fixedThroatQuotientInclusion period hPeriod point) = 0 := by
      simp only [independentBoundaryTrace, independentFieldCurve,
        throatTrace_apply, one_smul] at hPoint
      change domain.configuration.matter.1
          (fixedThroatQuotientInclusion period hPeriod point) +
            variation.independent.matter.1
              (fixedThroatQuotientInclusion period hPeriod point) =
        domain.configuration.matter.1
          (fixedThroatQuotientInclusion period hPeriod point) at hPoint
      simpa using hPoint
    exact congrArg (EuclideanSpace.proj coordinate) hZero
  · have hSector := congrArg Prod.snd hMatter
    unfold SatisfiesDirichlet
    apply SmoothThroatField.ext period hPeriod Real
    intro point
    have hPoint := congrArg
      (fun field : SmoothThroatField period hPeriod MatterFiber => field point)
      hSector
    have hZero :
        variation.independent.matter.2
          (fixedThroatQuotientInclusion period hPeriod point) = 0 := by
      simp only [independentBoundaryTrace, independentFieldCurve,
        throatTrace_apply, one_smul] at hPoint
      change domain.configuration.matter.2
          (fixedThroatQuotientInclusion period hPeriod point) +
            variation.independent.matter.2
              (fixedThroatQuotientInclusion period hPeriod point) =
        domain.configuration.matter.2
          (fixedThroatQuotientInclusion period hPeriod point) at hPoint
      simpa using hPoint
    exact congrArg (EuclideanSpace.proj coordinate) hZero

/-- Program P boundary tangency therefore supplies exactly the separated
Dirichlet condition used by the oriented Green--Stokes theorem. -/
theorem programPBoundaryTangent_matterComponent_canonicalDirichlet
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (hVariation :
      variation ∈ programPBoundaryTangentDomain4D period hPeriod domain)
    (component : MatterComponentIndex) :
    CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod
      (matterVariationComponentFamily period hPeriod
        variation.independent.matter component) :=
  canonicalLatitudeScalarDirichletBoundaryCondition_of_homogeneousDirichlet
    period hPeriod _ (programPBoundaryTangent_matterComponent_homogeneousDirichlet
      period hPeriod domain variation hVariation component)

/-- Scalar field selected from one matter component of a complete Program P
variation. -/
abbrev programPBoundaryTangentScalarComponent
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex) :
    SmoothQuotientField period hPeriod Real :=
  matterVariationComponentFamily period hPeriod
    variation.independent.matter component

/-- Measured oriented Green--Stokes closure for two Program P boundary
tangents.  Both Dirichlet facts are conclusions derived from tangent-domain
membership rather than extra inputs. -/
theorem programPBoundaryTangents_measuredGreenStokes_certificate
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (massSquared : Real)
    (fieldVariation testVariation :
      ProgramPCompleteVariation4D period hPeriod)
    (hFieldVariation :
      fieldVariation ∈
        programPBoundaryTangentDomain4D period hPeriod domain)
    (hTestVariation :
      testVariation ∈
        programPBoundaryTangentDomain4D period hPeriod domain)
    (fieldComponent testComponent : MatterComponentIndex) :
    let field := programPBoundaryTangentScalarComponent period hPeriod
      fieldVariation fieldComponent
    let test := programPBoundaryTangentScalarComponent period hPeriod
      testVariation testComponent
    CanonicalLatitudeScalarDirichletBoundaryCondition
        period hPeriod field ∧
      CanonicalLatitudeScalarDirichletBoundaryCondition
        period hPeriod test ∧
      cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test = 0 ∧
      2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
            field test Set.univ =
          -cutBulkGlobalOrientedScalarCurrentIntegral
            period hPeriod field test ∧
      cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
        field test Set.univ = 0 := by
  dsimp only [programPBoundaryTangentScalarComponent]
  have hField :=
    programPBoundaryTangent_matterComponent_canonicalDirichlet
      period hPeriod domain fieldVariation hFieldVariation fieldComponent
  have hTest :=
    programPBoundaryTangent_matterComponent_canonicalDirichlet
      period hPeriod domain testVariation hTestVariation testComponent
  exact ⟨hField, hTest,
    canonicalPhysicalScalarDirichlet_orientedBoundary_zero
      period hPeriod _ _ hField hTest,
    canonicalPhysicalScalarDirichlet_measuredGreenStokes
      period hPeriod massSquared _ _,
    canonicalPhysicalScalarDirichlet_cutBulkDivergence_zero
      period hPeriod massSquared _ _ hField hTest⟩

/-- Complete metric Green--Stokes closure for Euler components of two Program
P boundary tangents.  No independent boundary hypothesis occurs. -/
theorem programPBoundaryTangents_metricGreenStokes_certificate
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (massSquared : Real)
    (fieldVariation testVariation :
      ProgramPCompleteVariation4D period hPeriod)
    (hFieldVariation :
      fieldVariation ∈
        programPBoundaryTangentDomain4D period hPeriod domain)
    (hTestVariation :
      testVariation ∈
        programPBoundaryTangentDomain4D period hPeriod domain)
    (fieldComponent testComponent : MatterComponentIndex)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared (programPBoundaryTangentScalarComponent period hPeriod
        fieldVariation fieldComponent))
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared (programPBoundaryTangentScalarComponent period hPeriod
        testVariation testComponent)) :
    let field := programPBoundaryTangentScalarComponent period hPeriod
      fieldVariation fieldComponent
    let test := programPBoundaryTangentScalarComponent period hPeriod
      testVariation testComponent
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
          period hPeriod massSquared field test =
        -cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test ∧
      canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
        period hPeriod massSquared field test = 0 := by
  dsimp only [programPBoundaryTangentScalarComponent] at hFieldEuler hTestEuler ⊢
  have hField :=
    programPBoundaryTangent_matterComponent_canonicalDirichlet
      period hPeriod domain fieldVariation hFieldVariation fieldComponent
  have hTest :=
    programPBoundaryTangent_matterComponent_canonicalDirichlet
      period hPeriod domain testVariation hTestVariation testComponent
  exact ⟨canonicalPhysicalScalarDirichlet_metricGreenStokes
      period hPeriod massSquared _ _ hFieldEuler hTestEuler hField hTest,
    canonicalPhysicalScalarDirichlet_metricDivergence_zero
      period hPeriod massSquared _ _ hFieldEuler hTestEuler hField hTest⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPBoundaryTangentGreenStokes4D
end JanusFormal
