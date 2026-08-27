import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D

/-!
# Exact reconstruction of the actual throat gauge covector

The coefficients used by the actual Candidate-A throat gauge extractor are
proved to reconstruct the pulled-back covector exactly in the centered tangent
trivialization.  The statement holds throughout that trivialization's base
set, and specializes both to the intrinsic jet value at its center and to the
transported `EuclideanR3` value evaluated directly on the ambient Candidate-A
potential through the differential of the fixed-throat inclusion.

No chart-overlap law, global descent, normal datum, full structured background
or connection compatibility is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeTrivializationReconstruction4D

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualBulkBackgroundChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-! ## The centered tangent equivalence -/

/-- The continuous linear equivalence supplied by the tangent trivialization
at its center.  Naming it once avoids duplicating its dependent base-set
witness in the exact reconstruction statements below. -/
def throatGaugeCenteredTangentEquiv
    (anchor : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod anchor ≃L[Real]
      ThroatCoverCoordinates :=
  (trivializationAt ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod) anchor).continuousLinearEquivAt
      Real anchor
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor)

/-! ## Reconstruction on the centered trivialization domain -/

/-- The finite coefficient expansion is exactly the intrinsic throat
covector read in the tangent trivialization centered at `anchor`. -/
theorem throatGaugeCovectorCoordinates_eq_trivializedPullback
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet) :
    throatGaugeCovectorCoordinates period hPeriod potential component anchor
        current =
      (potential.toFun component current).comp
        (((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) anchor).continuousLinearEquivAt
              Real current hCurrent).symm :
          ThroatCoverCoordinates →L[Real]
            ThroatTangentFiber period hPeriod current) := by
  let trivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) anchor
  have hFrame (index : Fin 3) :
      trivialization.localFrame (𝕜 := Real) throatRadialReferenceBasis index
          current =
        (trivialization.continuousLinearEquivAt Real current hCurrent).symm
          (throatRadialReferenceBasis index) := by
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      trivialization throatRadialReferenceBasis hCurrent]
    rfl
  have hRepr (vector : ThroatCoverCoordinates) (index : Fin 3) :
      throatRadialReferenceBasis.repr vector index =
        throatRadialReferenceEquiv.symm vector index := by
    rfl
  apply ContinuousLinearMap.ext
  intro vector
  rw [throatGaugeCovectorCoordinates_apply]
  change
    (∑ index : Fin 3,
      potential.toFun component current
          (trivialization.localFrame (𝕜 := Real)
            throatRadialReferenceBasis index current) *
        throatRadialReferenceEquiv.symm vector index) =
      potential.toFun component current
        ((trivialization.continuousLinearEquivAt Real current hCurrent).symm
          vector)
  conv_rhs => rw [← throatRadialReferenceBasis.sum_repr vector]
  simp only [map_sum, map_smul, hFrame, hRepr, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- For the actual Candidate-A potential, reconstruction holds at every point
of the centered trivialization base set and is exactly the ambient bulk
potential composed with the fixed-throat differential. -/
theorem globalCandidateAThroatGaugeCovectorCoordinates_eq_bulkPullback
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet) :
    throatGaugeCovectorCoordinates period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data sector)
        component anchor current =
      ((globalCandidateABulkPotentialBySector period hPeriod data sector).toFun
        component (fixedThroatQuotientInclusion period hPeriod current)).comp
        ((mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) current).comp
          (((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) anchor).continuousLinearEquivAt
              Real current hCurrent).symm :
            ThroatCoverCoordinates →L[Real]
              ThroatTangentFiber period hPeriod current)) := by
  rw [throatGaugeCovectorCoordinates_eq_trivializedPullback
    period hPeriod
      (globalCandidateAThroatPotentialBySector period hPeriod data sector)
      component anchor current hCurrent]
  apply ContinuousLinearMap.ext
  intro vector
  change
    (globalCandidateAThroatPotentialBySector period hPeriod data sector).toFun
        component current
        (((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor).continuousLinearEquivAt
            Real current hCurrent).symm vector) = _
  exact globalCandidateAThroatPotentialBySector_apply period hPeriod data
    sector component current
      (((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).continuousLinearEquivAt
          Real current hCurrent).symm vector)

/-! ## Center and physical-carrier specializations -/

/-- At the center, the intrinsic second-jet value is exactly the pulled-back
potential in the centered tangent trivialization. -/
theorem globalCandidateAThroatGaugeSecondOrderJetAt_value_eq_trivializedPullback
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod) :
    (globalCandidateAThroatGaugeSecondOrderJetAt period hPeriod data sector
        component anchor).value =
      ((globalCandidateAThroatPotentialBySector period hPeriod data sector).toFun
        component anchor).comp
        ((throatGaugeCenteredTangentEquiv period hPeriod anchor).symm :
          ThroatCoverCoordinates →L[Real]
            ThroatTangentFiber period hPeriod anchor) := by
  rw [globalCandidateAThroatGaugeSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value]
  unfold throatGaugeCovectorChartGerm
  rw [Function.comp_apply, extChartAt_to_inv]
  exact throatGaugeCovectorCoordinates_eq_trivializedPullback
    period hPeriod
      (globalCandidateAThroatPotentialBySector period hPeriod data sector)
      component anchor anchor
      (mem_baseSet_trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor)

/-- The transported physical-carrier value is the actual ambient Candidate-A
potential evaluated on the differential of the fixed-throat inclusion. -/
theorem globalCandidateAThroatGaugeEuclideanSecondOrderJetAt_value_eq_bulkPullback
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod)
    (vector : EuclideanR3) :
    (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt period hPeriod data
        sector component anchor).value vector =
      (globalCandidateABulkPotentialBySector period hPeriod data sector).toFun
        component (fixedThroatQuotientInclusion period hPeriod anchor)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) anchor
          ((throatGaugeCenteredTangentEquiv period hPeriod anchor).symm
            (throatRadialReferenceEquiv vector))) := by
  rw [globalCandidateAThroatGaugeEuclideanSecondOrderJetAt,
    transportThroatGaugeSecondOrderJetToEuclidean_value_apply,
    globalCandidateAThroatGaugeSecondOrderJetAt_value_eq_trivializedPullback]
  change
    (globalCandidateAThroatPotentialBySector period hPeriod data sector).toFun
        component anchor
        ((throatGaugeCenteredTangentEquiv period hPeriod anchor).symm
          (throatRadialReferenceEquiv vector)) = _
  exact globalCandidateAThroatPotentialBySector_apply period hPeriod data
      sector component anchor
        ((throatGaugeCenteredTangentEquiv period hPeriod anchor).symm
          (throatRadialReferenceEquiv vector))

end
end P0EFTJanusProgramPActualThroatGaugeTrivializationReconstruction4D
end JanusFormal
