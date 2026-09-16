import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

/-! # A nonzero smooth diffeomorphism antighost -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12PureAntighostNonzeroWitness4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalVolumePreservingFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowEuclideanSpan4D
open P0EFTJanusMappingTorusCanonicalTenFlowRadialGenerator4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def witnessSphere : UnitThreeSphere :=
  ⟨![0, 1, 0, 0], by
    norm_num [OnUnitThreeSphere, radiusSquared, Fin.sum_univ_succ]⟩

private def witnessCover :
    MappingTorusCover (reflectedSphereData period hPeriod) :=
  ⟨witnessSphere, 0⟩

/-- The canonical time flow supplies a nonzero smooth antighost. -/
theorem exists_nonzero_globalDiffeomorphismAntighostField :
    ∃ antighost : GlobalDiffeomorphismAntighostField period hPeriod,
      antighost ≠ 0 := by
  let point := witnessCover period hPeriod
  let index := canonicalFlowIndexEquivFinTen CanonicalFlowIndex.time
  have hAt :
      canonicalTenFlowGeneratorAt period hPeriod
          (mappingTorusMk (reflectedSphereData period hPeriod) point)
          CanonicalFlowIndex.time ≠ 0 := by
    intro hZero
    have hRadial := canonicalQuotientRadialDerivativeEquiv_generator
      period hPeriod CanonicalFlowIndex.time point
    change (canonicalFlowGenerator period hPeriod
      (canonicalVolumePreservingFlow period hPeriod CanonicalFlowIndex.time)
      (mappingTorusMk (reflectedSphereData period hPeriod) point)) = 0 at hZero
    rw [hZero, map_zero] at hRadial
    exact (coverRadialMap_ne_zero period hPeriod point)
      (by simpa [canonicalEuclideanFlowGenerator] using hRadial.symm)
  have hField : canonicalTenFlowVectorField period hPeriod index ≠ 0 := by
    intro hZero
    apply hAt
    have hValue := congrArg
      (fun field : SmoothTangentField period hPeriod =>
        field (mappingTorusMk (reflectedSphereData period hPeriod) point)) hZero
    simpa [index, canonicalTenFlowVectorField_apply, canonicalTenFlowFrame]
      using hValue
  refine ⟨⟨canonicalTenFlowVectorField period hPeriod index⟩, ?_⟩
  intro hZero
  apply hField
  exact congrArg GlobalDiffeomorphismAntighostField.field hZero

end
end P0EFTJanusProgramPT12PureAntighostNonzeroWitness4D
end JanusFormal
