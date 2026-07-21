import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationGlobalMetricD9Projection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationBoundaryDomainBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D

/-!
# General-metric BV BRST on the complete Program-P variation

The general Lorentz BV doublet already consists of genuine smooth global
symmetric tensors, exactly the type stored in the full-metric slot of
`ProgramPCompleteVariation4D`.  This gate installs its even tensor pair in
that slot, proves that the existing BRST replaces it by the antifield pair,
tracks the same replacement through the D9 projection and the genuine throat
trace, and records its interaction with the current Program-P boundary
domain.

The current boundary-domain predicate depends only on the independent-field
curve, so it is unchanged by these completion slots.  This is an exact
compatibility statement, not a claim that the full metric BV Dirichlet data
has already been added to that predicate.
-/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationBoundaryDomainBridge4D
open P0EFTJanusCompleteVariationGlobalMetricD9Projection4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
open P0EFTJanusD9CanonicalGlobalTensorHolonomicMetricCompletion4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusReflectionFixedThroat

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Read a two-sector smooth tensor pair as the sector-indexed full metric
slot used by the complete Program-P variation. -/
def generalMetricTensorPairSector
    (tensors : SmoothGeneralMetricTensorPair period hPeriod)
    (sector : Sector) : SmoothSymmetricCovariantTwoTensor period hPeriod :=
  match sector with
  | .plus => tensors.1
  | .minus => tensors.2

/-- Read the corresponding throat tensor pair sectorwise. -/
def generalMetricThroatTensorPairSector
    (tensors : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (sector : Sector) : SmoothSymmetricThroatCovariantTwoTensor period hPeriod :=
  match sector with
  | .plus => tensors.1
  | .minus => tensors.2

/-- Attach the even tensor part of a genuine general-metric BV phase to the
same complete variation carrying an arbitrary independent-field direction. -/
def completeVariationWithGeneralMetricBV
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    ProgramPCompleteVariation4D period hPeriod :=
  completeVariationWithGlobalMetric period hPeriod variation
    (generalMetricTensorPairSector period hPeriod phase.1)

@[simp] theorem completeVariationWithGeneralMetricBV_independent
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    (completeVariationWithGeneralMetricBV period hPeriod variation phase).independent =
      variation :=
  rfl

@[simp] theorem completeVariationWithGeneralMetricBV_fullMetric
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector) :
    (completeVariationWithGeneralMetricBV period hPeriod variation phase
      ).fullMetricPerturbation sector =
      generalMetricTensorPairSector period hPeriod phase.1 sector :=
  rfl

/-- The existing BV differential `Q(h,h⁺)=(h⁺,0)` is represented exactly in
the full-metric slot of the complete variation. -/
theorem completeVariationWithGeneralMetricBV_BRST_fullMetric
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector) :
    (completeVariationWithGeneralMetricBV period hPeriod variation
      (smoothGeneralMetricBVBRST period hPeriod phase)
      ).fullMetricPerturbation sector =
      generalMetricTensorPairSector period hPeriod phase.2 sector :=
  rfl

/-- Two BRST applications give the canonical complete inclusion with a zero
full-metric slot; all nonmetric independent data is retained unchanged. -/
theorem completeVariationWithGeneralMetricBV_BRST_square
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    completeVariationWithGeneralMetricBV period hPeriod variation
        (smoothGeneralMetricBVBRST period hPeriod
          (smoothGeneralMetricBVBRST period hPeriod phase)) =
      independentCompleteVariation period hPeriod variation := by
  rw [smoothGeneralMetricBVBRST_square_zero]
  have hMetric :
      generalMetricTensorPairSector period hPeriod
          (smoothGeneralMetricBVZero period hPeriod).1 =
        fun _ => zeroSymmetricTensor period hPeriod := by
    funext sector
    cases sector <;> rfl
  unfold completeVariationWithGeneralMetricBV
  rw [hMetric]
  rfl

/-- The D9 metric observation of the same complete variation is exactly the
six spatial coefficients of the BV tensor selected in that sector. -/
theorem completeVariationWithGeneralMetricBV_metricPerturbationAt
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector)
    (point : EffectiveThroat period hPeriod) :
    (completeVariationWithGeneralMetricBV period hPeriod variation phase
      ).metricPerturbationAt period hPeriod sector point =
      d9FullMetricProjection
        (d9TensorChartMetricVariation period hPeriod
          (generalMetricTensorPairSector period hPeriod phase.1 sector)
          (selectedD9ThroatHolonomicPatch period hPeriod point)
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)) :=
  rfl

/-- After BRST, that same D9 observation reads the antifield tensor rather
than an unrelated metric direction. -/
theorem completeVariationWithGeneralMetricBV_BRST_metricPerturbationAt
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector)
    (point : EffectiveThroat period hPeriod) :
    (completeVariationWithGeneralMetricBV period hPeriod variation
      (smoothGeneralMetricBVBRST period hPeriod phase)
      ).metricPerturbationAt period hPeriod sector point =
      d9FullMetricProjection
        (d9TensorChartMetricVariation period hPeriod
          (generalMetricTensorPairSector period hPeriod phase.2 sector)
          (selectedD9ThroatHolonomicPatch period hPeriod point)
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)) :=
  rfl

/-- Genuine throat restriction of the complete metric slot is the selected
component of the already-constructed BV boundary trace. -/
theorem completeVariationWithGeneralMetricBV_throatTrace
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector) :
    smoothSymmetricTensorThroatTrace period hPeriod
        ((completeVariationWithGeneralMetricBV period hPeriod variation phase
          ).fullMetricPerturbation sector) =
      generalMetricThroatTensorPairSector period hPeriod
        (smoothGeneralMetricBVThroatTrace period hPeriod phase).1 sector := by
  cases sector <;> rfl

/-- Restriction to the throat and the complete-variation realization commute
with the metric BV differential. -/
theorem completeVariationWithGeneralMetricBV_BRST_throatTrace
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector) :
    smoothSymmetricTensorThroatTrace period hPeriod
        ((completeVariationWithGeneralMetricBV period hPeriod variation
          (smoothGeneralMetricBVBRST period hPeriod phase)
          ).fullMetricPerturbation sector) =
      generalMetricThroatTensorPairSector period hPeriod
        (smoothThroatGeneralMetricBVBRST period hPeriod
          (smoothGeneralMetricBVThroatTrace period hPeriod phase)).1 sector := by
  rw [← smoothGeneralMetricBVThroatTrace_commutes_BRST period hPeriod phase]
  cases sector <;> rfl

/-- Exact interaction with the currently implemented Program-P boundary
domain: the BV completion is admissible precisely when its unchanged
independent-field direction is admissible. -/
theorem completeVariationWithGeneralMetricBV_mem_boundaryDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    completeVariationWithGeneralMetricBV period hPeriod variation phase ∈
        programPBoundaryTangentDomain4D period hPeriod domain ↔
      variation ∈ independentBoundaryTangentDomain4D period hPeriod domain :=
  Iff.rfl

/-- Consequently the phase and its BRST image obey exactly the same current
Program-P boundary-domain condition. -/
theorem completeVariationWithGeneralMetricBV_BRST_mem_boundaryDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    completeVariationWithGeneralMetricBV period hPeriod variation
        (smoothGeneralMetricBVBRST period hPeriod phase) ∈
        programPBoundaryTangentDomain4D period hPeriod domain ↔
      completeVariationWithGeneralMetricBV period hPeriod variation phase ∈
        programPBoundaryTangentDomain4D period hPeriod domain := by
  rw [completeVariationWithGeneralMetricBV_mem_boundaryDomain_iff,
    completeVariationWithGeneralMetricBV_mem_boundaryDomain_iff]

end

end P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
end JanusFormal
