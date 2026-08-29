import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteFullActionFrechetC2Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConcreteEinsteinMaxwellLineC2Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteMatterLineC2Closure4D

/-!
# Complete concrete Fréchet assembly on a Dirac measure

Candidate A and the Einstein--Maxwell blocks are closed by exact pointwise
`C²` evaluation on `Measure.dirac point`.  The matter block remains governed
by `ConcreteMatterLineC2Criterion`.  Robin, true LL and finite BV use their
existing exact linewise Taylor closures.  No claim for a general candidate
measure is made.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConcreteFullActionFrechetDiracAssembly4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothDiagonalInteraction4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusCoDiagonalLorentzRootFirstDerivative
open P0EFTJanusGlobalDiagonalInteractionDensity4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPConcreteFullActionFrechetBridge4D
open P0EFTJanusProgramPConcreteFullActionFrechetC2Closure4D
open P0EFTJanusMappingTorusConcreteEinsteinMaxwellLineC2Closure4D
open P0EFTJanusProgramPConcreteMatterLineC2Closure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance localRealNormedAddCommGroup : NormedAddCommGroup Real :=
  inferInstance

local instance localRealNormedSpace : NormedSpace Real Real :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup Real :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module Real Real :=
  localRealNormedSpace.toModule

private theorem two_le_infty : (2 : ℕ∞ω) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-! ## Candidate A on one atom -/

private theorem globalDiagonalTwoSectorDensity_contDiffOn_two
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (globalDiagonalTwoSectorDensity interactionScale coefficients)
      ambientPositiveScalePairDomain := by
  have hDirect :=
    coDiagonalInteractionDensity_contDiffOn interactionScale coefficients
  have hExchanged : ContDiffOn Real ∞
      (exchangedDiagonalInteractionDensity interactionScale coefficients)
      ambientPositiveScalePairDomain := by
    rw [ambientPositiveScalePairDomain_isOpen.contDiffOn_iff]
    intro scalePair hScalePair
    unfold exchangedDiagonalInteractionDensity
    exact
      (hDirect.contDiffAt
        (ambientPositiveScalePairDomain_isOpen.mem_nhds
          ((scalePairExchange_mem_domain_iff scalePair).2 hScalePair))).comp
        scalePair scalePairExchange.contDiff.contDiffAt
  exact (hDirect.add hExchanged).of_le (two_le_infty)

private theorem candidateAScalePairCurve_contDiff_two
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 2
      (fun parameter =>
        scalePairField period hPeriod
          (metricCurve period hPeriod metrics variation parameter) point) := by
  rw [show
      (fun parameter =>
        scalePairField period hPeriod
          (metricCurve period hPeriod metrics variation parameter) point) =
      fun parameter =>
        (positiveScaleCurve period hPeriod
            (plusScaleField period hPeriod metrics)
            variation.plusLogDirection parameter point,
          positiveScaleCurve period hPeriod
            (minusScaleField period hPeriod metrics)
            variation.minusLogDirection parameter point) by
    funext parameter
    exact scalePairField_metricCurve period hPeriod metrics variation
      parameter point]
  fun_prop

theorem candidateADensityCurve_point_contDiff_two
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 2
      (fun parameter =>
        candidateADensityCurve period hPeriod interactionScale coefficients
          metrics variation parameter point) := by
  change ContDiff Real 2
    (globalDiagonalTwoSectorDensity interactionScale coefficients ∘
      fun parameter =>
        scalePairField period hPeriod
          (metricCurve period hPeriod metrics variation parameter) point)
  rw [contDiff_iff_contDiffAt]
  intro parameter
  exact
    ((globalDiagonalTwoSectorDensity_contDiffOn_two interactionScale coefficients)
      |>.contDiffAt
        (ambientPositiveScalePairDomain_isOpen.mem_nhds
          (scalePairField_mem_domain period hPeriod
            (metricCurve period hPeriod metrics variation parameter) point))).comp
      parameter
      (candidateAScalePairCurve_contDiff_two period hPeriod metrics variation
        point).contDiffAt

theorem candidateAActionCurve_dirac_contDiff_two
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 2
      (candidateAActionCurve period hPeriod (Measure.dirac point)
        interactionScale coefficients metrics variation) := by
  rw [show
      candidateAActionCurve period hPeriod (Measure.dirac point)
          interactionScale coefficients metrics variation =
        fun parameter =>
          candidateADensityCurve period hPeriod interactionScale coefficients
            metrics variation parameter point by
    funext parameter
    simp [candidateAActionCurve, candidateAAction, candidateADensityCurve]]
  exact candidateADensityCurve_point_contDiff_two period hPeriod
    interactionScale coefficients metrics variation point

/-! ## Six-slot record and complete nine-block bridge -/

/-- All six formerly missing linewise slots on the explicitly stated Dirac
sector.  Matter is closed only through its non-circular concrete criterion. -/
def fullMetricFiniteBVDiracMissingC2Slots
    (point : EffectiveQuotient period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields (Measure.dirac point))
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (junction : SmoothThroatField period hPeriod Real)
    (bvField : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion)
    (matterCriterion :
      ConcreteMatterLineC2Criterion period hPeriod (Measure.dirac point)
        matterContract.massSquared fields direction.base.physical) :
    FullMetricLineMissingC2Slots period hPeriod (Measure.dirac point)
      interactionScale coefficients fields matterContract kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
      couplings completion direction := by
  let einsteinMaxwell :=
    fullMetricFiniteBVLineBlocks_dirac_einsteinMaxwell_c2 period hPeriod point
      interactionScale coefficients fields matterContract kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
      couplings completion direction
  exact
    { candidateA := by
        change ContDiff Real 2
          (candidateAActionCurve period hPeriod (Measure.dirac point)
            interactionScale coefficients fields.metrics
              direction.base.physical.complete.independent.metrics)
        exact candidateAActionCurve_dirac_contDiff_two period hPeriod
          interactionScale coefficients fields.metrics
          direction.base.physical.complete.independent.metrics point
      matter :=
        fullMetricFiniteBVLineBlocks_matter_contDiff_two period hPeriod
          (Measure.dirac point) interactionScale coefficients fields
          matterContract kPlus kMinus bulkPlus bulkMinus robinMeasure frame
          llMeasure junction bvField couplings completion direction
          matterCriterion
      einsteinHilbertPlus := einsteinMaxwell.einsteinHilbertPlus
      einsteinHilbertMinus := einsteinMaxwell.einsteinHilbertMinus
      maxwellPlus := einsteinMaxwell.maxwellPlus
      maxwellMinus := einsteinMaxwell.maxwellMinus }

/-- Complete concrete nine-block Fréchet bridge on one candidate-measure atom.
The result is unconditional in Candidate A, EH±, Maxwell±, Robin, true LL and
finite BV; its only supplied analytic input is the displayed matter criterion.
-/
def fullMetricFiniteBVDiracConcreteFrechetBridge
    (point : EffectiveQuotient period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields (Measure.dirac point))
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (junction : SmoothThroatField period hPeriod Real)
    (bvField : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion)
    (matterCriterion :
      ConcreteMatterLineC2Criterion period hPeriod (Measure.dirac point)
        matterContract.massSquared fields direction.base.physical) :
    ConcreteFullActionFrechetBridge Real Real
      (fullMetricFiniteBVAffineActionCurve period hPeriod (Measure.dirac point)
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction) :=
  fullMetricFiniteBVLineConcreteFrechetBridge period hPeriod
    (Measure.dirac point) interactionScale coefficients fields matterContract
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
    bvField couplings completion direction
    (fullMetricFiniteBVDiracMissingC2Slots period hPeriod point interactionScale
      coefficients fields matterContract kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure junction bvField couplings completion
      direction matterCriterion)

end

end P0EFTJanusProgramPConcreteFullActionFrechetDiracAssembly4D
end JanusFormal
