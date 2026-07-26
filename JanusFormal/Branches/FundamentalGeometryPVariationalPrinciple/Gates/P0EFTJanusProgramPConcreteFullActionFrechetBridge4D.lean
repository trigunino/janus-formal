import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinJunctionActionReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D

/-!
# Concrete one-line Fréchet bridge for the strongest proved common sector

The current concrete action API is a family of one-parameter curves, not a
normed global configuration chart.  On each such line, the genuine Robin,
true-LL and integrated finite-BV blocks have exact polynomial Taylor formulas,
so their common `ℝ` chart is unconditionally `C²`.

Candidate A, metric matter, the two Einstein--Hilbert blocks and the two
Maxwell blocks currently have directional derivative APIs but no common
linewise `C²` theorem.  `FullMetricLineMissingC2Slots` records exactly those
six remaining statements.  Supplying them constructs the full nine-block
bridge; no sectorial bridge below is advertised as a global field-space
realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConcreteFullActionFrechetBridge4D

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
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLAction4D
open P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLFiniteBVExtension4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalVariation4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusRobinJunctionActionReconstruction4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

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

/-! ## Three concrete blocks already `C²` on the common line -/

/-- The genuine Robin functional restricted to its existing affine line. -/
def robinLineAction
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction : SmoothThroatField period hPeriod Real)
    (measure : Measure (EffectiveThroat period hPeriod))
    (parameter : Real) : Real :=
  robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
    (junctionAffineCurve period hPeriod junction direction parameter) measure

/-- Exact polynomiality makes the Robin line globally `C²`. -/
theorem robinLineAction_contDiff_two
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction : SmoothThroatField period hPeriod Real)
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure] :
    ContDiff Real 2
      (robinLineAction period hPeriod kPlus kMinus bulkPlus bulkMinus
        junction direction measure) := by
  rw [show
      robinLineAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction direction measure =
        fun parameter : Real =>
          robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
              junction measure +
            parameter * robinFirstVariation period hPeriod kPlus kMinus
              bulkPlus bulkMinus junction direction measure +
            (parameter ^ 2 / 2) *
              robinHessian period hPeriod kPlus kMinus direction direction
                measure by
    funext parameter
    exact robinJunctionAction_affine_exact_taylor period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction direction measure parameter]
  fun_prop

/-- The genuine true-LL functional restricted to its synchronized full line. -/
def trueLLLineAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod))
    (parameter : Real) : Real :=
  globalPTSymmetricDifferentialLLAction period hPeriod frame
    (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
      direction.llMeasure direction.common.ll parameter) measure

/-- The exact quartic LL reconstruction is globally `C²` on the line. -/
theorem trueLLLineAction_contDiff_two
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure] :
    ContDiff Real 2
      (trueLLLineAction period hPeriod frame fields direction measure) := by
  rw [show trueLLLineAction period hPeriod frame fields direction measure =
      fun parameter : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame fields
            measure +
          parameter * fullLLEuler period hPeriod frame fields direction
            measure +
          (parameter ^ 2 / 2) *
            globalPTFullLLHessianForm period hPeriod frame fields direction
              direction measure +
          parameter ^ 3 *
            globalPTFullLLTaylorCubic period hPeriod frame fields
              direction.llAuxMetric
              (fullDirectionLLVariation period hPeriod direction) measure +
          parameter ^ 4 *
            globalPTFullLLTaylorQuartic period hPeriod frame fields
              direction.llAuxMetric
              (fullDirectionLLVariation period hPeriod direction) measure by
    funext parameter
    exact globalPTAction_fullDirection_exact_taylor period hPeriod frame fields
      direction parameter measure]
  fun_prop

/-- The genuine integrated finite-BV master action on an affine field line. -/
def finiteBVLineAction
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (parameter : Real) : Real :=
  canonicalSmoothSpacetimeBVMasterAction period hPeriod
    (smoothSpacetimeBVFieldLine period hPeriod field variation parameter)

/-- The integrated finite-BV action is exactly quadratic on every line. -/
theorem finiteBVLineAction_contDiff_two
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    ContDiff Real 2 (finiteBVLineAction period hPeriod field variation) := by
  rw [show finiteBVLineAction period hPeriod field variation =
      fun parameter : Real =>
        canonicalSmoothSpacetimeBVMasterAction period hPeriod field +
          parameter *
            canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
              field variation +
          parameter ^ 2 *
            canonicalSmoothSpacetimeBVMasterAction period hPeriod variation by
    funext parameter
    exact canonicalSmoothSpacetimeBVMasterAction_line_expansion period hPeriod
      field variation parameter]
  fun_prop

/-! ## Maximal unconditional common sub-combination -/

/-- Exactly the Robin, true-LL and finite-BV slots on one scalar line.
All other slots are zero because their `C²` pullbacks are not yet proved. -/
def robinLLFiniteBVLineBlocks
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction robinDirection : SmoothThroatField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (llDirection : FullMatterRobinLLDirections period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (bvField bvDirection :
      SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    FullCoupledActionBlocks Real where
  candidateA := 0
  matter := 0
  robin := robinLineAction period hPeriod kPlus kMinus bulkPlus bulkMinus
    junction robinDirection robinMeasure
  ll := trueLLLineAction period hPeriod frame fields llDirection llMeasure
  einsteinHilbertPlus := 0
  einsteinHilbertMinus := 0
  maxwellPlus := 0
  maxwellMinus := 0
  finiteBV := finiteBVLineAction period hPeriod bvField bvDirection

/-- Affine reparametrization of the proved Robin--LL--BV sub-combination. -/
def robinLLFiniteBVAffineActionCurve
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction robinDirection : SmoothThroatField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (llDirection : FullMatterRobinLLDirections period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (bvField bvDirection :
      SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (configuration variation parameter : Real) : Real :=
  fullCoupledAction
    (robinLLFiniteBVLineBlocks period hPeriod kPlus kMinus bulkPlus bulkMinus
      junction robinDirection robinMeasure frame fields llDirection llMeasure
      bvField bvDirection)
    (configuration + parameter • variation)

/-- Unconditional `ConcreteFullActionFrechetBridge` for the maximal concrete
sub-combination whose common linewise `C²` regularity is already proved. -/
def robinLLFiniteBVLineConcreteFrechetBridge
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction robinDirection : SmoothThroatField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (llDirection : FullMatterRobinLLDirections period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (bvField bvDirection :
      SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    ConcreteFullActionFrechetBridge Real Real
      (robinLLFiniteBVAffineActionCurve period hPeriod kPlus kMinus bulkPlus
        bulkMinus junction robinDirection robinMeasure frame fields llDirection
        llMeasure bvField bvDirection) where
  Configuration := Real
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  encodeConfiguration := id
  encodeVariation := id
  blocks :=
    robinLLFiniteBVLineBlocks period hPeriod kPlus kMinus bulkPlus bulkMinus
      junction robinDirection robinMeasure frame fields llDirection llMeasure
      bvField bvDirection
  affineCurve := fun configuration variation parameter =>
    configuration + parameter • variation
  affineCurve_zero := by
    intro configuration variation
    simp
  curve_agreement := by
    intro configuration variation parameter
    rfl
  blocks_c2 := by
    intro configuration
    refine
      { candidateA := by
          change ContDiffAt Real 2 (fun _ : Real => (0 : Real))
            (id configuration)
          exact contDiffAt_const
        matter := by
          change ContDiffAt Real 2 (fun _ : Real => (0 : Real))
            (id configuration)
          exact contDiffAt_const
        robin :=
          (robinLineAction_contDiff_two period hPeriod kPlus kMinus bulkPlus
            bulkMinus junction robinDirection robinMeasure).contDiffAt
        ll :=
          (trueLLLineAction_contDiff_two period hPeriod frame fields llDirection
            llMeasure).contDiffAt
        einsteinHilbertPlus := by
          change ContDiffAt Real 2 (fun _ : Real => (0 : Real))
            (id configuration)
          exact contDiffAt_const
        einsteinHilbertMinus := by
          change ContDiffAt Real 2 (fun _ : Real => (0 : Real))
            (id configuration)
          exact contDiffAt_const
        maxwellPlus := by
          change ContDiffAt Real 2 (fun _ : Real => (0 : Real))
            (id configuration)
          exact contDiffAt_const
        maxwellMinus := by
          change ContDiffAt Real 2 (fun _ : Real => (0 : Real))
            (id configuration)
          exact contDiffAt_const
        finiteBV :=
          (finiteBVLineAction_contDiff_two period hPeriod bvField
            bvDirection).contDiffAt }

/-! ## Exact six slots still needed for the complete concrete line -/

/-- The nine genuine scalar blocks of the strongest existing full-metric
Candidate-A/matter/Robin/LL/EH/Maxwell/BV action curve. -/
def fullMetricFiniteBVLineBlocks
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
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
        fields completion) :
    FullCoupledActionBlocks Real where
  candidateA :=
    candidateAActionCurve period hPeriod candidateMeasure interactionScale
      coefficients fields.metrics
        direction.base.physical.complete.independent.metrics
  matter :=
    programPMetricMatterActionCurve period hPeriod candidateMeasure
      matterContract.massSquared fields direction.base.physical
  robin :=
    robinLineAction period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      direction.base.physical.robin robinMeasure
  ll :=
    trueLLLineAction period hPeriod frame fields
      (toFullMatterRobinLLDirections period hPeriod direction.base.physical)
      llMeasure
  einsteinHilbertPlus :=
    intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings
      direction.plusGravityLine candidateMeasure
  einsteinHilbertMinus :=
    intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings
      direction.minusGravityLine candidateMeasure
  maxwellPlus :=
    intrinsicMaxwellMetricGaugeActionCurve period hPeriod
      direction.plusGravityLine direction.plusMaxwellLine candidateMeasure
  maxwellMinus :=
    intrinsicMaxwellMetricGaugeActionCurve period hPeriod
      direction.minusGravityLine direction.minusMaxwellLine candidateMeasure
  finiteBV :=
    finiteBVLineAction period hPeriod bvField direction.base.bv

/-- The block decomposition is definitionally the strongest existing concrete
full-metric finite-BV action curve. -/
theorem fullMetricFiniteBVLineBlocks_sum
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
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
    (parameter : Real) :
    fullCoupledAction
        (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
          interactionScale coefficients fields matterContract kPlus kMinus
          bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
          couplings completion direction)
        parameter =
      candidateACoupledEinsteinMaxwellFullMetricFiniteBVActionCurve
        period hPeriod candidateMeasure interactionScale coefficients fields
        matterContract kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure junction bvField couplings completion direction parameter := by
  unfold fullCoupledAction fullMetricFiniteBVLineBlocks
    candidateACoupledEinsteinMaxwellFullMetricFiniteBVActionCurve
    candidateACoupledFiniteBVActionCurve
    candidateACoupledMetricMatterRobinTrueLLActionCurve
    robinLineAction trueLLLineAction finiteBVLineAction
  ring

/-- Exactly the six linewise `C²` statements not supplied by existing gates.
Robin, true LL and integrated finite BV are intentionally absent. -/
structure FullMetricLineMissingC2Slots
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
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
        fields completion) : Prop where
  candidateA :
    ContDiff Real 2
      (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction).candidateA
  matter :
    ContDiff Real 2
      (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction).matter
  einsteinHilbertPlus :
    ContDiff Real 2
      (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction).einsteinHilbertPlus
  einsteinHilbertMinus :
    ContDiff Real 2
      (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction).einsteinHilbertMinus
  maxwellPlus :
    ContDiff Real 2
      (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction).maxwellPlus
  maxwellMinus :
    ContDiff Real 2
      (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction).maxwellMinus

/-- Affine reparametrization of the complete existing concrete action line. -/
def fullMetricFiniteBVAffineActionCurve
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
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
    (configuration variation parameter : Real) : Real :=
  candidateACoupledEinsteinMaxwellFullMetricFiniteBVActionCurve
    period hPeriod candidateMeasure interactionScale coefficients fields
    matterContract kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
    junction bvField couplings completion direction
    (configuration + parameter • variation)

/-- The full concrete line bridge follows from precisely the six missing
linewise regularity slots, with the other three discharged by exact Taylor
theorems above. -/
def fullMetricFiniteBVLineConcreteFrechetBridge
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
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
    (remaining :
      FullMetricLineMissingC2Slots period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction) :
    ConcreteFullActionFrechetBridge Real Real
      (fullMetricFiniteBVAffineActionCurve period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction) where
  Configuration := Real
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  encodeConfiguration := id
  encodeVariation := id
  blocks :=
    fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
      interactionScale coefficients fields matterContract kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
      couplings completion direction
  affineCurve := fun configuration variation parameter =>
    configuration + parameter • variation
  affineCurve_zero := by
    intro configuration variation
    simp
  curve_agreement := by
    intro configuration variation parameter
    exact fullMetricFiniteBVLineBlocks_sum period hPeriod candidateMeasure
      interactionScale coefficients fields matterContract kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
      couplings completion direction _
  blocks_c2 := by
    intro configuration
    refine
      { candidateA := remaining.candidateA.contDiffAt
        matter := remaining.matter.contDiffAt
        robin :=
          (robinLineAction_contDiff_two period hPeriod kPlus kMinus bulkPlus
            bulkMinus junction direction.base.physical.robin
            robinMeasure).contDiffAt
        ll :=
          (trueLLLineAction_contDiff_two period hPeriod frame fields
            (toFullMatterRobinLLDirections period hPeriod
              direction.base.physical) llMeasure).contDiffAt
        einsteinHilbertPlus :=
          remaining.einsteinHilbertPlus.contDiffAt
        einsteinHilbertMinus :=
          remaining.einsteinHilbertMinus.contDiffAt
        maxwellPlus := remaining.maxwellPlus.contDiffAt
        maxwellMinus := remaining.maxwellMinus.contDiffAt
        finiteBV :=
          (finiteBVLineAction_contDiff_two period hPeriod bvField
            direction.base.bv).contDiffAt }

end

end P0EFTJanusProgramPConcreteFullActionFrechetBridge4D
end JanusFormal
