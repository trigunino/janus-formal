import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalVariation4D

/-!
# Finite-BV extension of the coupled Candidate-A action

The genuine integrated finite-BV master action is added as an independent
factor to the coupled Candidate-A, scalar-matter, Robin and true-LL action.
Its first variation and symmetric Hessian are derived from the same quadratic
master functional.

This does not identify the finite constant BV phase with a Maxwell or
Einstein--Hilbert field, and it does not supply either missing bulk action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLFiniteBVExtension4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusCandidateAIntegratedMetricHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMixedHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMetricHessian4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
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

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The finite master first variation is symmetric in its two arguments. -/
private theorem finiteMetricBVMasterFirstVariation_symmetric
    (first second : FiniteMetricBVPhase) :
    finiteMetricBVMasterFirstVariation first second =
      finiteMetricBVMasterFirstVariation second first := by
  rw [finiteMetricBVMasterFirstVariation_coordinate_expansion,
    finiteMetricBVMasterFirstVariation_coordinate_expansion]
  have hFirst :
      (∑ coordinate : PositiveMetricCoordinate,
        first.2 (coordinate, 1) * second.1 (coordinate, 0)) =
      ∑ coordinate : PositiveMetricCoordinate,
        second.1 (coordinate, 0) * first.2 (coordinate, 1) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  have hSecond :
      (∑ coordinate : PositiveMetricCoordinate,
        first.1 (coordinate, 0) * second.2 (coordinate, 1)) =
      ∑ coordinate : PositiveMetricCoordinate,
        second.2 (coordinate, 1) * first.1 (coordinate, 0) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [hFirst, hSecond]
  ring

/-- Affine dependence of the finite master first variation on its base
field. -/
private theorem finiteMetricBVMasterFirstVariation_add_smul_left
    (field varied test : FiniteMetricBVPhase) (parameter : Real) :
    finiteMetricBVMasterFirstVariation
        (field + parameter • varied) test =
      finiteMetricBVMasterFirstVariation field test +
        parameter * finiteMetricBVMasterFirstVariation varied test := by
  rw [finiteMetricBVMasterFirstVariation_coordinate_expansion,
    finiteMetricBVMasterFirstVariation_coordinate_expansion,
    finiteMetricBVMasterFirstVariation_coordinate_expansion]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have hFirstSmul :
      (parameter • varied).1 = parameter • varied.1 := rfl
  have hSecondSmul :
      (parameter • varied).2 = parameter • varied.2 := rfl
  rw [hFirstSmul, hSecondSmul]
  simp only [Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The actual Hessian of the integrated finite-BV master action. -/
def canonicalSmoothSpacetimeBVMasterHessian
    (first second : SmoothFiniteMetricBVSpacetimeField period hPeriod) : Real :=
  canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod first second

/-- The integrated finite-BV Hessian is symmetric. -/
theorem canonicalSmoothSpacetimeBVMasterHessian_symmetric
    (first second : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothSpacetimeBVMasterHessian period hPeriod first second =
      canonicalSmoothSpacetimeBVMasterHessian period hPeriod second first := by
  unfold canonicalSmoothSpacetimeBVMasterHessian
    canonicalSmoothSpacetimeBVMasterFirstVariation
  apply integral_congr_ae
  filter_upwards [] with point
  rw [smoothSpacetimeBVMasterFirstVariationDensity_apply,
    smoothSpacetimeBVMasterFirstVariationDensity_apply]
  exact finiteMetricBVMasterFirstVariation_symmetric
    (first point) (second point)

/-- The first variation evaluated along an affine BV base-field curve. -/
def canonicalSmoothSpacetimeBVMasterEulerCurve
    (field test varied : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (parameter : Real) : Real :=
  canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
    (smoothSpacetimeBVFieldLine period hPeriod field varied parameter) test

theorem canonicalSmoothSpacetimeBVMasterFirstVariation_fieldLine
    (field test varied : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (parameter : Real) :
    canonicalSmoothSpacetimeBVMasterEulerCurve period hPeriod
        field test varied parameter =
      canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod field test +
        parameter *
          canonicalSmoothSpacetimeBVMasterHessian period hPeriod varied test := by
  have hField :=
    smoothSpacetimeBVMasterFirstVariationDensity_integrable period hPeriod
      field test
  have hVaried :=
    smoothSpacetimeBVMasterFirstVariationDensity_integrable period hPeriod
      varied test
  unfold canonicalSmoothSpacetimeBVMasterEulerCurve
    canonicalSmoothSpacetimeBVMasterFirstVariation
    canonicalSmoothSpacetimeBVMasterHessian
  calc
    ∫ point,
        smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
          (smoothSpacetimeBVFieldLine period hPeriod field varied parameter)
          test point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ point,
        (smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
            field test point +
          parameter *
            smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
              varied test point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          filter_upwards [] with point
          rw [smoothSpacetimeBVMasterFirstVariationDensity_apply,
            smoothSpacetimeBVFieldLine_apply,
            smoothSpacetimeBVMasterFirstVariationDensity_apply,
            smoothSpacetimeBVMasterFirstVariationDensity_apply]
          exact finiteMetricBVMasterFirstVariation_add_smul_left
            (field point) (varied point) (test point) parameter
    _ = _ := by
      rw [integral_add hField (hVaried.const_mul parameter),
        integral_const_mul]
      rfl

/-- Differentiating the genuine BV Euler coefficient gives its Hessian. -/
theorem canonicalSmoothSpacetimeBVMasterEulerCurve_hasDerivAt
    (field test varied : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    HasDerivAt
      (canonicalSmoothSpacetimeBVMasterEulerCurve period hPeriod
        field test varied)
      (canonicalSmoothSpacetimeBVMasterHessian period hPeriod varied test)
      0 := by
  rw [show canonicalSmoothSpacetimeBVMasterEulerCurve period hPeriod
      field test varied =
    fun parameter : Real =>
      canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod field test +
        parameter *
          canonicalSmoothSpacetimeBVMasterHessian period hPeriod varied test by
    funext parameter
    exact canonicalSmoothSpacetimeBVMasterFirstVariation_fieldLine
      period hPeriod field test varied parameter]
  simpa using
    (((hasDerivAt_id (𝕜 := Real) 0).mul_const
      (canonicalSmoothSpacetimeBVMasterHessian period hPeriod varied test))
        |>.const_add
          (canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
            field test))

/-- Independent physical and finite-BV tangent directions. -/
structure CandidateACoupledFiniteBVVariation where
  physical : ProgramPRobinCompleteVariation4D period hPeriod
  bv : SmoothFiniteMetricBVSpacetimeField period hPeriod

/-- Sum of the coupled physical action curve and the genuine finite-BV master
action curve. -/
def candidateACoupledFiniteBVActionCurve
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
    (direction : CandidateACoupledFiniteBVVariation period hPeriod)
    (parameter : Real) : Real :=
  candidateACoupledMetricMatterRobinTrueLLActionCurve period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      direction.physical parameter +
    canonicalSmoothSpacetimeBVMasterAction period hPeriod
      (smoothSpacetimeBVFieldLine period hPeriod bvField direction.bv parameter)

/-- First-variation coefficient of the extended action. -/
def candidateACoupledFiniteBVEuler
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
    (direction : CandidateACoupledFiniteBVVariation period hPeriod) : Real :=
  candidateACoupledMetricMatterRobinTrueLLEuler period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      direction.physical +
    canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
      bvField direction.bv

/-- The extended Euler coefficient is the derivative of one summed action
curve. -/
theorem candidateACoupledFiniteBVActionCurve_hasDerivAt
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
    (direction : CandidateACoupledFiniteBVVariation period hPeriod)
    (candidateContract : DominatedCandidateAVariationContract period hPeriod
      candidateMeasure interactionScale coefficients fields.metrics
      direction.physical.complete.independent.metrics)
    (metricMatterContract : DominatedIndependentMetricMatterVariationContract
      period hPeriod candidateMeasure matterContract.massSquared fields
      direction.physical) :
    HasDerivAt
      (candidateACoupledFiniteBVActionCurve period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        direction)
      (candidateACoupledFiniteBVEuler period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        direction)
      0 := by
  unfold candidateACoupledFiniteBVActionCurve
    candidateACoupledFiniteBVEuler
  exact
    (candidateACoupledMetricMatterRobinTrueLLAction_hasDerivAt period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      direction.physical candidateContract metricMatterContract).add
    (canonicalSmoothSpacetimeBVMasterAction_line_hasDerivAt period hPeriod
      bvField direction.bv)

/-- Completed Hessian of the physical sector plus the actual finite-BV
Hessian. -/
def candidateACoupledFiniteBVCompletedHessian
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (first second : CandidateACoupledFiniteBVVariation period hPeriod) : Real :=
  candidateACoupledMetricCompletedSectorialHessian period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus robinMeasure frame llMeasure first.physical second.physical +
    canonicalSmoothSpacetimeBVMasterHessian period hPeriod first.bv second.bv

/-- The completed physical-plus-BV Hessian is symmetric. -/
theorem candidateACoupledFiniteBVCompletedHessian_symmetric
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (first second : CandidateACoupledFiniteBVVariation period hPeriod)
    (contract : CandidateAGlobalDensityC2Contract interactionScale
      coefficients) :
    candidateACoupledFiniteBVCompletedHessian period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        robinMeasure frame llMeasure first second =
      candidateACoupledFiniteBVCompletedHessian period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        robinMeasure frame llMeasure second first := by
  unfold candidateACoupledFiniteBVCompletedHessian
  rw [candidateACoupledMetricCompletedSectorialHessian_symmetric period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus robinMeasure frame llMeasure first.physical second.physical
      contract,
    canonicalSmoothSpacetimeBVMasterHessian_symmetric period hPeriod
      first.bv second.bv]

/-- Euler curve whose derivative contains every currently supplied physical
and finite-BV Hessian slot. -/
def candidateACoupledFiniteBVCompletedEulerCurve
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
    (test varied : CandidateACoupledFiniteBVVariation period hPeriod)
    (parameter : Real) : Real :=
  candidateACoupledMetricCompletedEulerCurve period hPeriod candidateMeasure
      interactionScale coefficients fields matterContract kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure junction test.physical
      varied.physical parameter +
    canonicalSmoothSpacetimeBVMasterEulerCurve period hPeriod bvField
      test.bv varied.bv parameter

@[simp]
theorem candidateACoupledFiniteBVCompletedEulerCurve_zero
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
    (test varied : CandidateACoupledFiniteBVVariation period hPeriod) :
    candidateACoupledFiniteBVCompletedEulerCurve period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        bvField test varied 0 =
      candidateACoupledFiniteBVEuler period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField test := by
  simp [candidateACoupledFiniteBVCompletedEulerCurve,
    candidateACoupledFiniteBVEuler,
    canonicalSmoothSpacetimeBVMasterEulerCurve,
    smoothSpacetimeBVFieldLine]

/-- The completed Euler curve differentiates to the complete supplied
physical-plus-BV Hessian. -/
theorem candidateACoupledFiniteBVCompletedEulerCurve_hasDerivAt
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
    (test varied : CandidateACoupledFiniteBVVariation period hPeriod)
    (candidateContract : DominatedCandidateASecondVariationContract
      period hPeriod candidateMeasure interactionScale coefficients
      fields.metrics test.physical.complete.independent.metrics
      varied.physical.complete.independent.metrics)
    (pureMetricContract :
      DominatedIndependentMatterMetricSecondVariationContract period hPeriod
        candidateMeasure matterContract.massSquared fields
        test.physical.complete.independent.metrics
        varied.physical.complete.independent.metrics)
    (variedMetricTestMatterContract :
      DominatedIndependentMetricMatterMixedVariationContract period hPeriod
        candidateMeasure matterContract.massSquared fields
        varied.physical.complete.independent.metrics
        test.physical.complete.independent.matter)
    (testMetricVariedMatterContract :
      DominatedIndependentMetricMatterMixedVariationContract period hPeriod
        candidateMeasure matterContract.massSquared fields
        test.physical.complete.independent.metrics
        varied.physical.complete.independent.matter) :
    HasDerivAt
      (candidateACoupledFiniteBVCompletedEulerCurve period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        bvField test varied)
      (candidateACoupledFiniteBVCompletedHessian period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus robinMeasure frame llMeasure test varied)
      0 := by
  unfold candidateACoupledFiniteBVCompletedEulerCurve
    candidateACoupledFiniteBVCompletedHessian
  have hPhysical :=
    candidateACoupledMetricCompletedEulerCurve_hasDerivAt period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      test.physical varied.physical candidateContract pureMetricContract
      variedMetricTestMatterContract testMetricVariedMatterContract
  have hBV :=
    canonicalSmoothSpacetimeBVMasterEulerCurve_hasDerivAt period hPeriod
      bvField test.bv varied.bv
  refine (hPhysical.add hBV).congr_deriv ?_
  rw [canonicalSmoothSpacetimeBVMasterHessian_symmetric period hPeriod
    varied.bv test.bv]

end

end P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLFiniteBVExtension4D
end JanusFormal
