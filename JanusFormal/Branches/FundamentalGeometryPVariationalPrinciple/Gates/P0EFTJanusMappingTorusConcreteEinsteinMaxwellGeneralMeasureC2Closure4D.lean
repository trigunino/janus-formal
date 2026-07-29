import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConcreteEinsteinMaxwellLineC2Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompactParametricIntegralC2
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# General finite-measure C² closure of the Einstein--Maxwell lines

The existing regular Einstein--Maxwell lines provide pointwise smoothness in
the line parameter and the exact first density derivative.  They do not
provide joint parameter--point continuity or a typed second density
derivative.  The two criteria below add exactly those missing analytic data.

As in the concrete Candidate-A closure, joint continuity on a compact
parameter slab times the compact quotient gives uniform bounds.  Finite
measure then permits differentiating the integral twice.  No integrated
`ContDiff` conclusion occurs in either criterion.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Closure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusCompactParametricIntegralC2
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPConcreteFullActionFrechetBridge4D
open P0EFTJanusMappingTorusConcreteEinsteinMaxwellLineC2Closure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance localRealNormedAddCommGroup : NormedAddCommGroup Real :=
  inferInstance

local instance localRealNormedSpace : NormedSpace Real Real :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup Real :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module Real Real :=
  localRealNormedSpace.toModule

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

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

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

/-! ## Exact additional criteria absent from `Regular...` -/

/-- Minimal extra data needed to integrate an EH metric line twice.
The exact first density derivative is already supplied by the regular line. -/
structure EinsteinHilbertMetricLineC2Criterion
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod) where
  secondDerivative : Real → SmoothScalarField period hPeriod
  density_jointContinuous : Continuous
    (fun input : Real × EffectiveQuotient period hPeriod =>
      regularEinsteinHilbertDensityField period hPeriod couplings
        (line.data input.1) input.2)
  firstDerivative_jointContinuous : Continuous
    (fun input : Real × EffectiveQuotient period hPeriod =>
      regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
        couplings line input.1 input.2)
  secondDerivative_jointContinuous : Continuous
    (fun input : Real × EffectiveQuotient period hPeriod =>
      secondDerivative input.1 input.2)
  firstDerivative_hasDerivAt : ∀ parameter point,
    HasDerivAt
      (fun varied =>
        regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
          couplings line varied point)
      (secondDerivative parameter point) parameter

/-- Minimal extra data needed to integrate a varying-metric Maxwell line
twice.  Its exact first density derivative is already proved. -/
structure MaxwellMetricGaugeLineC2Criterion
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity) where
  secondDerivative : Real → SmoothScalarField period hPeriod
  density_jointContinuous : Continuous
    (fun input : Real × EffectiveQuotient period hPeriod =>
      (gravity.data input.1).metric.volume input.2 *
        (-(1 / 4 : Real) * line.pairing input.1 input.2))
  firstDerivative_jointContinuous : Continuous
    (fun input : Real × EffectiveQuotient period hPeriod =>
      regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
        gravity line input.1 input.2)
  secondDerivative_jointContinuous : Continuous
    (fun input : Real × EffectiveQuotient period hPeriod =>
      secondDerivative input.1 input.2)
  firstDerivative_hasDerivAt : ∀ parameter point,
    HasDerivAt
      (fun varied =>
        regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
          gravity line varied point)
      (secondDerivative parameter point) parameter

/-! ## General finite-measure line theorems -/

theorem einsteinHilbertMetricActionCurve_contDiff_two
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (criterion :
      EinsteinHilbertMetricLineC2Criterion period hPeriod couplings line) :
    ContDiff Real 2
      (intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings line
        measure) := by
  have hIntegrated := integral_contDiff_two_of_jointContinuous_compact
    (measure := measure)
    (density := fun parameter point =>
      regularEinsteinHilbertDensityField period hPeriod couplings
        (line.data parameter) point)
    (firstDerivative := fun parameter point =>
      regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
        couplings line parameter point)
    (secondDerivative := fun parameter point =>
      criterion.secondDerivative parameter point)
    criterion.density_jointContinuous
    criterion.firstDerivative_jointContinuous
    criterion.secondDerivative_jointContinuous
    (fun parameter point =>
      regularEinsteinHilbertDensityField_metricLine_hasDerivAt period hPeriod
        couplings line parameter point)
    criterion.firstDerivative_hasDerivAt
  change ContDiff Real 2
    (fun parameter =>
      ∫ point,
        regularEinsteinHilbertDensityField period hPeriod couplings
          (line.data parameter) point ∂measure)
  exact hIntegrated

theorem maxwellMetricGaugeActionCurve_contDiff_two
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (criterion :
      MaxwellMetricGaugeLineC2Criterion period hPeriod gravity line) :
    ContDiff Real 2
      (intrinsicMaxwellMetricGaugeActionCurve period hPeriod gravity line
        measure) := by
  have hIntegrated := integral_contDiff_two_of_jointContinuous_compact
    (measure := measure)
    (density := fun parameter point =>
      (gravity.data parameter).metric.volume point *
        (-(1 / 4 : Real) * line.pairing parameter point))
    (firstDerivative := fun parameter point =>
      regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
        gravity line parameter point)
    (secondDerivative := fun parameter point =>
      criterion.secondDerivative parameter point)
    criterion.density_jointContinuous
    criterion.firstDerivative_jointContinuous
    criterion.secondDerivative_jointContinuous
    (fun parameter point =>
      intrinsicMaxwellDensity_metricGaugeLine_hasDerivAt period hPeriod
        gravity line parameter point)
    criterion.firstDerivative_hasDerivAt
  change ContDiff Real 2
    (fun parameter =>
      ∫ point,
        (gravity.data parameter).metric.volume point *
          (-(1 / 4 : Real) * line.pairing parameter point) ∂measure)
  exact hIntegrated

/-- The four non-circular analytic criteria for one full-metric direction. -/
structure EinsteinMaxwellGeneralMeasureC2Criterion
    (couplings : EinsteinHilbertCouplings)
    (fields : IndependentFields period hPeriod)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion) where
  einsteinHilbertPlus :
    EinsteinHilbertMetricLineC2Criterion period hPeriod couplings
      direction.plusGravityLine
  einsteinHilbertMinus :
    EinsteinHilbertMetricLineC2Criterion period hPeriod couplings
      direction.minusGravityLine
  maxwellPlus :
    MaxwellMetricGaugeLineC2Criterion period hPeriod
      direction.plusGravityLine direction.plusMaxwellLine
  maxwellMinus :
    MaxwellMetricGaugeLineC2Criterion period hPeriod
      direction.minusGravityLine direction.minusMaxwellLine

/-- Under exactly the missing joint `C²` density data, all four genuine
Einstein--Maxwell fields of `FullMetricLineMissingC2Slots` are `C²` for every
finite measure on the compact quotient. -/
theorem fullMetricFiniteBVLineBlocks_einsteinMaxwell_contDiff_two
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure candidateMeasure]
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
    (criterion :
      EinsteinMaxwellGeneralMeasureC2Criterion period hPeriod couplings fields
        completion direction) :
    EinsteinMaxwellLineC2Slots
      (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction) where
  einsteinHilbertPlus := by
    change ContDiff Real 2
      (intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings
        direction.plusGravityLine candidateMeasure)
    exact einsteinHilbertMetricActionCurve_contDiff_two period hPeriod
      candidateMeasure couplings direction.plusGravityLine
      criterion.einsteinHilbertPlus
  einsteinHilbertMinus := by
    change ContDiff Real 2
      (intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings
        direction.minusGravityLine candidateMeasure)
    exact einsteinHilbertMetricActionCurve_contDiff_two period hPeriod
      candidateMeasure couplings direction.minusGravityLine
      criterion.einsteinHilbertMinus
  maxwellPlus := by
    change ContDiff Real 2
      (intrinsicMaxwellMetricGaugeActionCurve period hPeriod
        direction.plusGravityLine direction.plusMaxwellLine candidateMeasure)
    exact maxwellMetricGaugeActionCurve_contDiff_two period hPeriod
      candidateMeasure direction.plusGravityLine direction.plusMaxwellLine
      criterion.maxwellPlus
  maxwellMinus := by
    change ContDiff Real 2
      (intrinsicMaxwellMetricGaugeActionCurve period hPeriod
        direction.minusGravityLine direction.minusMaxwellLine candidateMeasure)
    exact maxwellMetricGaugeActionCurve_contDiff_two period hPeriod
      candidateMeasure direction.minusGravityLine direction.minusMaxwellLine
      criterion.maxwellMinus

end

end P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Closure4D
end JanusFormal
