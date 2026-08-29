import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Closure4D

/-!
# Exact realization frontier for general-measure Einstein--Maxwell C²

The regular line contracts already imply pointwise `C²` density regularity.
This file extracts the canonical pointwise second derivatives and proves that
the remaining general finite-measure criterion is equivalent to joint
parameter--point continuity plus a smooth-field lift of those canonical
derivatives.  Thus no derivative hypothesis remains hidden in the criterion.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Realization4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
open P0EFTJanusMappingTorusConcreteEinsteinMaxwellLineC2Closure4D
open P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Closure4D

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

/-! ## Canonical pointwise second derivatives -/

theorem einsteinHilbertMetricFirstVariation_pointwise_contDiff_one
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 1
      (fun parameter =>
        regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
          couplings line parameter point) := by
  let density := fun parameter =>
    regularEinsteinHilbertDensityField period hPeriod couplings
      (line.data parameter) point
  have hDensity : ContDiff Real 2 density :=
    einsteinHilbertMetricLine_density_contDiff_two period hPeriod
      couplings line point
  have hDerivative : ContDiff Real 1 (deriv density) :=
    hDensity.deriv'
  have hEq :
      (fun parameter =>
        regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
          couplings line parameter point) =
        deriv density := by
    funext parameter
    exact
      (regularEinsteinHilbertDensityField_metricLine_hasDerivAt period hPeriod
        couplings line parameter point).deriv.symm
  rw [hEq]
  exact hDerivative

def einsteinHilbertMetricCanonicalSecondVariation
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  deriv
    (fun varied =>
      regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
        couplings line varied point)
    parameter

theorem einsteinHilbertMetricFirstVariation_hasCanonicalSecondDerivAt
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
          couplings line varied point)
      (einsteinHilbertMetricCanonicalSecondVariation period hPeriod
        couplings line parameter point)
      parameter := by
  exact
    ((einsteinHilbertMetricFirstVariation_pointwise_contDiff_one period hPeriod
      couplings line point).differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem maxwellMetricGaugeFirstVariation_pointwise_contDiff_one
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 1
      (fun parameter =>
        regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
          gravity line parameter point) := by
  let density := fun parameter =>
    (gravity.data parameter).metric.volume point *
      (-(1 / 4 : Real) * line.pairing parameter point)
  have hDensity : ContDiff Real 2 density :=
    maxwellMetricGaugeLine_density_contDiff_two period hPeriod
      gravity line point
  have hDerivative : ContDiff Real 1 (deriv density) :=
    hDensity.deriv'
  have hEq :
      (fun parameter =>
        regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
          gravity line parameter point) =
        deriv density := by
    funext parameter
    exact
      (intrinsicMaxwellDensity_metricGaugeLine_hasDerivAt period hPeriod
        gravity line parameter point).deriv.symm
  rw [hEq]
  exact hDerivative

def maxwellMetricGaugeCanonicalSecondVariation
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  deriv
    (fun varied =>
      regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
        gravity line varied point)
    parameter

theorem maxwellMetricGaugeFirstVariation_hasCanonicalSecondDerivAt
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
          gravity line varied point)
      (maxwellMetricGaugeCanonicalSecondVariation period hPeriod
        gravity line parameter point)
      parameter := by
  exact
    ((maxwellMetricGaugeFirstVariation_pointwise_contDiff_one period hPeriod
      gravity line point).differentiable (by norm_num)).differentiableAt.hasDerivAt

/-! ## Exact mixed-regularity frontier -/

def EinsteinHilbertMetricLineJointC2Data
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod) : Prop :=
  Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        regularEinsteinHilbertDensityField period hPeriod couplings
          (line.data input.1) input.2) ∧
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
          couplings line input.1 input.2) ∧
    ∃ secondDerivative : Real → SmoothScalarField period hPeriod,
      (∀ parameter point,
        secondDerivative parameter point =
          einsteinHilbertMetricCanonicalSecondVariation period hPeriod
            couplings line parameter point) ∧
      Continuous
        (fun input : Real × EffectiveQuotient period hPeriod =>
          secondDerivative input.1 input.2)

theorem einsteinHilbertMetricLineC2Criterion_nonempty_iff
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod) :
    Nonempty
        (EinsteinHilbertMetricLineC2Criterion period hPeriod couplings line) ↔
      EinsteinHilbertMetricLineJointC2Data period hPeriod couplings line := by
  constructor
  · rintro ⟨criterion⟩
    refine ⟨criterion.density_jointContinuous,
      criterion.firstDerivative_jointContinuous, ?_⟩
    refine ⟨criterion.secondDerivative, ?_, ?_⟩
    · intro parameter point
      exact (criterion.firstDerivative_hasDerivAt parameter point).deriv.symm
    · exact criterion.secondDerivative_jointContinuous
  · rintro ⟨hDensity, hFirst, secondDerivative, hCanonical, hSecond⟩
    refine ⟨{
      secondDerivative := secondDerivative
      density_jointContinuous := hDensity
      firstDerivative_jointContinuous := hFirst
      secondDerivative_jointContinuous := hSecond
      firstDerivative_hasDerivAt := ?_
    }⟩
    intro parameter point
    rw [hCanonical parameter point]
    exact
      einsteinHilbertMetricFirstVariation_hasCanonicalSecondDerivAt
        period hPeriod couplings line parameter point

def MaxwellMetricGaugeLineJointC2Data
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity) :
    Prop :=
  Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        (gravity.data input.1).metric.volume input.2 *
          (-(1 / 4 : Real) * line.pairing input.1 input.2)) ∧
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
          gravity line input.1 input.2) ∧
    ∃ secondDerivative : Real → SmoothScalarField period hPeriod,
      (∀ parameter point,
        secondDerivative parameter point =
          maxwellMetricGaugeCanonicalSecondVariation period hPeriod
            gravity line parameter point) ∧
      Continuous
        (fun input : Real × EffectiveQuotient period hPeriod =>
          secondDerivative input.1 input.2)

theorem maxwellMetricGaugeLineC2Criterion_nonempty_iff
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity) :
    Nonempty
        (MaxwellMetricGaugeLineC2Criterion period hPeriod gravity line) ↔
      MaxwellMetricGaugeLineJointC2Data period hPeriod gravity line := by
  constructor
  · rintro ⟨criterion⟩
    refine ⟨criterion.density_jointContinuous,
      criterion.firstDerivative_jointContinuous, ?_⟩
    refine ⟨criterion.secondDerivative, ?_, ?_⟩
    · intro parameter point
      exact (criterion.firstDerivative_hasDerivAt parameter point).deriv.symm
    · exact criterion.secondDerivative_jointContinuous
  · rintro ⟨hDensity, hFirst, secondDerivative, hCanonical, hSecond⟩
    refine ⟨{
      secondDerivative := secondDerivative
      density_jointContinuous := hDensity
      firstDerivative_jointContinuous := hFirst
      secondDerivative_jointContinuous := hSecond
      firstDerivative_hasDerivAt := ?_
    }⟩
    intro parameter point
    rw [hCanonical parameter point]
    exact
      maxwellMetricGaugeFirstVariation_hasCanonicalSecondDerivAt
        period hPeriod gravity line parameter point

def EinsteinMaxwellGeneralMeasureJointC2Data
    (couplings : EinsteinHilbertCouplings)
    (fields : IndependentFields period hPeriod)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion) : Prop :=
  EinsteinHilbertMetricLineJointC2Data period hPeriod couplings
      direction.plusGravityLine ∧
    EinsteinHilbertMetricLineJointC2Data period hPeriod couplings
      direction.minusGravityLine ∧
    MaxwellMetricGaugeLineJointC2Data period hPeriod
      direction.plusGravityLine direction.plusMaxwellLine ∧
    MaxwellMetricGaugeLineJointC2Data period hPeriod
      direction.minusGravityLine direction.minusMaxwellLine

theorem einsteinMaxwellGeneralMeasureC2Criterion_nonempty_iff
    (couplings : EinsteinHilbertCouplings)
    (fields : IndependentFields period hPeriod)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion) :
    Nonempty
        (EinsteinMaxwellGeneralMeasureC2Criterion period hPeriod couplings
          fields completion direction) ↔
      EinsteinMaxwellGeneralMeasureJointC2Data period hPeriod couplings
        fields completion direction := by
  constructor
  · rintro ⟨criterion⟩
    exact
      ⟨(einsteinHilbertMetricLineC2Criterion_nonempty_iff period hPeriod
          couplings direction.plusGravityLine).mp
          ⟨criterion.einsteinHilbertPlus⟩,
        (einsteinHilbertMetricLineC2Criterion_nonempty_iff period hPeriod
          couplings direction.minusGravityLine).mp
          ⟨criterion.einsteinHilbertMinus⟩,
        (maxwellMetricGaugeLineC2Criterion_nonempty_iff period hPeriod
          direction.plusGravityLine direction.plusMaxwellLine).mp
          ⟨criterion.maxwellPlus⟩,
        (maxwellMetricGaugeLineC2Criterion_nonempty_iff period hPeriod
          direction.minusGravityLine direction.minusMaxwellLine).mp
          ⟨criterion.maxwellMinus⟩⟩
  · rintro ⟨hEinsteinPlus, hEinsteinMinus, hMaxwellPlus, hMaxwellMinus⟩
    obtain ⟨einsteinPlus⟩ :=
      (einsteinHilbertMetricLineC2Criterion_nonempty_iff period hPeriod
        couplings direction.plusGravityLine).mpr hEinsteinPlus
    obtain ⟨einsteinMinus⟩ :=
      (einsteinHilbertMetricLineC2Criterion_nonempty_iff period hPeriod
        couplings direction.minusGravityLine).mpr hEinsteinMinus
    obtain ⟨maxwellPlus⟩ :=
      (maxwellMetricGaugeLineC2Criterion_nonempty_iff period hPeriod
        direction.plusGravityLine direction.plusMaxwellLine).mpr hMaxwellPlus
    obtain ⟨maxwellMinus⟩ :=
      (maxwellMetricGaugeLineC2Criterion_nonempty_iff period hPeriod
        direction.minusGravityLine direction.minusMaxwellLine).mpr hMaxwellMinus
    exact ⟨{
      einsteinHilbertPlus := einsteinPlus
      einsteinHilbertMinus := einsteinMinus
      maxwellPlus := maxwellPlus
      maxwellMinus := maxwellMinus
    }⟩

end

end P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Realization4D
end JanusFormal
