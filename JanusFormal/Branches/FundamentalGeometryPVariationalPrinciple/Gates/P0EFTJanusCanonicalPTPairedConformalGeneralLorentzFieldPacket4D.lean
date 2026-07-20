import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalDecoratedConformalCandidateA4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalDecoratedGeneralLorentzFieldPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusNontrivialFieldTimeAction4D

/-! # PT-paired conformal general-Lorentz field packet -/

namespace JanusFormal
namespace P0EFTJanusCanonicalPTPairedConformalGeneralLorentzFieldPacket4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusCanonicalDecoratedProgramPFieldDomain4D
open P0EFTJanusCanonicalDecoratedConformalCandidateA4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Ambient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (Ambient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω (Ambient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- PT partner of a positive conformal scale. -/
def ptPairedConformalScale
    (scale : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod :=
  ptPullback period hPeriod Real scale

theorem ptPairedConformalScale_pos
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) (point) :
    0 < ptPairedConformalScale period hPeriod scale point :=
  hScale (reflectedSpherePT period hPeriod point)

/-- Conformal rescaling commutes exactly with analytic PT pullback. -/
theorem conformalSmoothGeneralLorentzMetric_ptPullback
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    smoothGeneralLorentzMetricPTPullback period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale) =
      conformalSmoothGeneralLorentzMetric period hPeriod
        (ptPairedConformalScale period hPeriod scale)
        (ptPairedConformalScale_pos period hPeriod scale hScale) := by
  apply smoothGeneralLorentzMetric_ext period hPeriod
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  have hBase := congrArg
    (fun tensor : SmoothSymmetricCovariantTwoTensor period hPeriod =>
      tensor.tensor point first second)
    (intrinsicSmoothTensor_pt_fixed period hPeriod)
  change scale (reflectedSpherePT period hPeriod point) *
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (reflectedSpherePT period hPeriod point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point second) =
    scale (reflectedSpherePT period hPeriod point) *
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        point first second
  exact congrArg (fun value => scale (reflectedSpherePT period hPeriod point) * value)
    hBase

/-- The conformal metric and its PT-pulled partner form a fixed pair under
simultaneous PT and sector exchange. -/
theorem ptPairedConformalMetricPair_pt_fixed
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    smoothGeneralLorentzMetricPTExchange period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale,
          conformalSmoothGeneralLorentzMetric period hPeriod
            (ptPairedConformalScale period hPeriod scale)
            (ptPairedConformalScale_pos period hPeriod scale hScale)) =
      (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale,
        conformalSmoothGeneralLorentzMetric period hPeriod
          (ptPairedConformalScale period hPeriod scale)
          (ptPairedConformalScale_pos period hPeriod scale hScale)) := by
  apply Prod.ext
  · change smoothGeneralLorentzMetricPTPullback period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod
          (ptPairedConformalScale period hPeriod scale)
          (ptPairedConformalScale_pos period hPeriod scale hScale)) =
      conformalSmoothGeneralLorentzMetric period hPeriod scale hScale
    rw [conformalSmoothGeneralLorentzMetric_ptPullback]
    congr 1
    exact ptPullback_involutive period hPeriod Real scale
  · change smoothGeneralLorentzMetricPTPullback period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale) =
      conformalSmoothGeneralLorentzMetric period hPeriod
        (ptPairedConformalScale period hPeriod scale)
        (ptPairedConformalScale_pos period hPeriod scale hScale)
    exact conformalSmoothGeneralLorentzMetric_ptPullback period hPeriod
      scale hScale

/-- Candidate-A root/density data and the full non-metric field packet carried
by a potentially distinct PT-paired conformal metric pair. -/
structure CanonicalPTPairedConformalGeneralLorentzFieldPacket
    (scale : SmoothScalarField period hPeriod) where
  candidate : CanonicalDecoratedConformalCandidateA period hPeriod scale
    (ptPairedConformalScale period hPeriod scale)
  generalFields : GeneralLorentzIndependentFields period hPeriod
  generalBoundary : GeneralLorentzIndependentBoundaryData period hPeriod

def canonicalPTPairedConformalGeneralLorentzFields
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    GeneralLorentzIndependentFields period hPeriod :=
  let partner := ptPairedConformalScale period hPeriod scale
  let hPartner := ptPairedConformalScale_pos period hPeriod scale hScale
  let candidate := canonicalDecoratedConformalCandidateA period hPeriod scale
    partner hScale hPartner
  let fields := canonicalPositiveOperatorFields period hPeriod
  { metrics := (candidate.plusMetric, candidate.minusMetric)
    matter := fields.matter
    gauge := fields.gauge
    ghosts := fields.ghosts
    auxiliaries := fields.auxiliaries
    llAuxMetric := fields.llAuxMetric
    llMeasure := fields.llMeasure
    llField := fields.llField }

def canonicalPTPairedConformalGeneralLorentzFieldPacket
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    CanonicalPTPairedConformalGeneralLorentzFieldPacket period hPeriod scale :=
  let partner := ptPairedConformalScale period hPeriod scale
  let hPartner := ptPairedConformalScale_pos period hPeriod scale hScale
  let candidate := canonicalDecoratedConformalCandidateA period hPeriod scale
    partner hScale hPartner
  let fields := canonicalPTPairedConformalGeneralLorentzFields period hPeriod
    scale hScale
  { candidate := candidate
    generalFields := fields
    generalBoundary :=
      generalLorentzIndependentBoundaryTrace period hPeriod fields }

theorem canonicalPTPairedConformalGeneralLorentzFields_scaffold
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    diagonalScaffold period hPeriod
        (canonicalPTPairedConformalGeneralLorentzFields period hPeriod scale
          hScale) =
      canonicalPositiveOperatorFields period hPeriod :=
  rfl

@[simp] theorem canonicalPTPairedConformalGeneralLorentzFieldPacket_metrics
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    let package := canonicalPTPairedConformalGeneralLorentzFieldPacket
      period hPeriod scale hScale
    package.generalFields.metrics =
      (package.candidate.plusMetric, package.candidate.minusMetric) :=
  rfl

theorem canonicalPTPairedConformalGeneralLorentzFields_pt_fixed
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    generalLorentzIndependentExchange period hPeriod
        (canonicalPTPairedConformalGeneralLorentzFields period hPeriod scale
          hScale) =
      canonicalPTPairedConformalGeneralLorentzFields period hPeriod scale
        hScale := by
  have hNonmetric :
      independentExchange period hPeriod
          (canonicalPositiveOperatorFields period hPeriod) =
        canonicalPositiveOperatorFields period hPeriod :=
    (ptMatchedIndependent_iff_fixed_exchange period hPeriod _).1
      (canonicalPositiveOperatorFields_ptMatched period hPeriod)
  apply GeneralLorentzIndependentFields.ext
  · change smoothGeneralLorentzMetricPTExchange period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale,
          conformalSmoothGeneralLorentzMetric period hPeriod
            (ptPairedConformalScale period hPeriod scale)
            (ptPairedConformalScale_pos period hPeriod scale hScale)) = _
    exact ptPairedConformalMetricPair_pt_fixed period hPeriod scale hScale
  · exact congrArg IndependentFields.matter hNonmetric
  · exact congrArg IndependentFields.gauge hNonmetric
  · exact congrArg IndependentFields.ghosts hNonmetric
  · exact congrArg IndependentFields.auxiliaries hNonmetric
  · exact congrArg IndependentFields.llAuxMetric hNonmetric
  · exact congrArg IndependentFields.llMeasure hNonmetric
  · exact congrArg IndependentFields.llField hNonmetric

theorem canonicalPTPairedConformalGeneralLorentzFieldPacket_root_square
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    let package := canonicalPTPairedConformalGeneralLorentzFieldPacket
      period hPeriod scale hScale
    package.candidate.rootOperator.comp package.candidate.rootOperator =
      package.candidate.relativeOperator :=
  canonicalDecoratedConformalCandidateA_rootOperator_square period hPeriod
    scale (ptPairedConformalScale period hPeriod scale) hScale
    (ptPairedConformalScale_pos period hPeriod scale hScale)

theorem canonicalPTPairedConformalGeneralLorentzFieldPacket_satisfies_boundary
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    let package := canonicalPTPairedConformalGeneralLorentzFieldPacket
      period hPeriod scale hScale
    SatisfiesGeneralLorentzIndependentBoundary period hPeriod
      package.generalBoundary package.generalFields :=
  rfl

theorem canonicalPTPairedConformalGeneralLorentzBoundary_pt_fixed
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point) :
    let package := canonicalPTPairedConformalGeneralLorentzFieldPacket
      period hPeriod scale hScale
    generalLorentzIndependentBoundaryExchange period hPeriod
        package.generalBoundary = package.generalBoundary := by
  change generalLorentzIndependentBoundaryExchange period hPeriod
      (generalLorentzIndependentBoundaryTrace period hPeriod
        (canonicalPTPairedConformalGeneralLorentzFields period hPeriod scale
          hScale)) =
    generalLorentzIndependentBoundaryTrace period hPeriod
      (canonicalPTPairedConformalGeneralLorentzFields period hPeriod scale
        hScale)
  rw [← generalLorentzIndependentBoundaryTrace_exchange,
    canonicalPTPairedConformalGeneralLorentzFields_pt_fixed]

private abbrev AmbientCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (AmbientCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

/-- First odd periodic time mode, descended to the genuine quotient. -/
def periodicSineCoverField :
    P0EFTJanusMappingTorusSmoothDeckInvariantFields4D.SmoothDeckInvariantField
      period hPeriod Real where
  toFun := fun point => Real.sin ((2 * Real.pi / period) * point.time)
  contMDiff_toFun := by
    let productEquiv :=
      coverHomeomorphProd (reflectedSphereData period hPeriod)
    have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      productEquiv
    have hTime : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point : AmbientCover period hPeriod => point.time) :=
      contMDiff_snd.comp hTo
    exact Real.contDiff_sin.contMDiff.comp (contMDiff_const.mul hTime)
  deck_invariant := by
    intro winding point
    change Real.sin
        ((2 * Real.pi / period) *
          (point.time + (winding : Real) * period)) =
      Real.sin ((2 * Real.pi / period) * point.time)
    have hArgument :
        (2 * Real.pi / period) *
            (point.time + (winding : Real) * period) =
          (2 * Real.pi / period) * point.time +
            (winding : Real) * (2 * Real.pi) := by
      field_simp [hPeriod]
    rw [hArgument]
    exact Real.sin_add_int_mul_two_pi _ winding

def periodicSineQuotientField : SmoothScalarField period hPeriod :=
  descendSmooth period hPeriod Real (periodicSineCoverField period hPeriod)

@[simp] theorem periodicSineQuotientField_mk
    (point : AmbientCover period hPeriod) :
    periodicSineQuotientField period hPeriod
        (mappingTorusMk (reflectedSphereData period hPeriod) point) =
      Real.sin ((2 * Real.pi / period) * point.time) :=
  rfl

/-- Explicit positive conformal factor whose odd time mode is not PT-fixed. -/
def explicitPositivePTScale : SmoothScalarField period hPeriod where
  toFun := fun point => 2 + periodicSineQuotientField period hPeriod point
  contMDiff_toFun :=
    contMDiff_const.add
      (periodicSineQuotientField period hPeriod).contMDiff_toFun

theorem explicitPositivePTScale_pos (point) :
    0 < explicitPositivePTScale period hPeriod point := by
  induction point using Quotient.inductionOn with
  | _ point =>
      change 0 < 2 + Real.sin ((2 * Real.pi / period) * point.time)
      linarith [Real.neg_one_le_sin ((2 * Real.pi / period) * point.time)]

private def ptQuarterWitness : Ambient period hPeriod :=
  effectiveTimeFlow period hPeriod (period / 4)
    (timeFlowWitnessPoint period hPeriod)

private theorem quarterArgument (hPeriod : period ≠ 0) :
    (2 * Real.pi / period) * (period / 4) = Real.pi / 2 := by
  field_simp [hPeriod] <;> ring

private theorem explicitPositivePTScale_quarter :
    explicitPositivePTScale period hPeriod
        (ptQuarterWitness period hPeriod) = 3 := by
  change 2 + periodicSineQuotientField period hPeriod
      (effectiveTimeFlow period hPeriod (period / 4)
        (timeFlowWitnessPoint period hPeriod)) = 3
  unfold timeFlowWitnessPoint
  rw [effectiveTimeFlow_mk, periodicSineQuotientField_mk]
  change 2 + Real.sin ((2 * Real.pi / period) * (0 + period / 4)) = 3
  rw [zero_add, quarterArgument period hPeriod, Real.sin_pi_div_two]
  norm_num

private theorem explicitPositivePTScale_partner_quarter :
    ptPairedConformalScale period hPeriod
        (explicitPositivePTScale period hPeriod)
        (ptQuarterWitness period hPeriod) = 1 := by
  change explicitPositivePTScale period hPeriod
      (reflectedSpherePT period hPeriod
        (effectiveTimeFlow period hPeriod (period / 4)
          (timeFlowWitnessPoint period hPeriod))) = 1
  rw [reflectedSpherePT_effectiveTimeFlow]
  change 2 + periodicSineQuotientField period hPeriod
      (effectiveTimeFlow period hPeriod (-(period / 4))
        (reflectedSpherePT period hPeriod
          (timeFlowWitnessPoint period hPeriod))) = 1
  unfold timeFlowWitnessPoint
  rw [reflectedSpherePT_mk_timeReverse, effectiveTimeFlow_mk,
    periodicSineQuotientField_mk]
  simp only [coverTimeTranslation, timeReverseCover]
  rw [neg_zero]
  change 2 + Real.sin ((2 * Real.pi / period) * (0 + -(period / 4))) = 1
  rw [zero_add, show -(period / 4) = -(period) / 4 by ring,
    show (2 * Real.pi / period) * (-period / 4) = -(Real.pi / 2) by
      field_simp [hPeriod] <;> ring]
  simp
  norm_num

/-- Concrete positive scale and its PT partner are genuinely distinct. -/
theorem explicitPositivePTScale_ne_partner :
    explicitPositivePTScale period hPeriod ≠
      ptPairedConformalScale period hPeriod
        (explicitPositivePTScale period hPeriod) := by
  intro hEqual
  have hValue := congrArg
    (fun field : SmoothScalarField period hPeriod =>
      field (ptQuarterWitness period hPeriod)) hEqual
  rw [explicitPositivePTScale_quarter,
    explicitPositivePTScale_partner_quarter] at hValue
  norm_num at hValue

/-- Positive conformal rescaling remembers its scalar factor. -/
theorem conformalSmoothGeneralLorentzMetric_injective_scale
    {first second : SmoothScalarField period hPeriod}
    (hFirst : ∀ point, 0 < first point)
    (hSecond : ∀ point, 0 < second point)
    (hMetric :
      conformalSmoothGeneralLorentzMetric period hPeriod first hFirst =
        conformalSmoothGeneralLorentzMetric period hPeriod second hSecond) :
    first = second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases (intrinsicSmoothGeneralLorentzMetric period hPeriod).lorentzian point with
    ⟨frame, hFrame⟩
  let timelike : CoverCoordinates := (0, 1)
  let tangent := frame.symm timelike
  have hBase :
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
          tangent tangent = -1 := by
    rw [hFrame]
    simp [timelike, tangent, modelMinkowskiPair]
  have hValue := congrArg
    (fun metric : SmoothGeneralLorentzMetric period hPeriod =>
      metric.tensor.tensor point tangent tangent) hMetric
  change first point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
          tangent tangent =
      second point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
          tangent tangent at hValue
  rw [hBase] at hValue
  linarith

/-- The explicit positive scale produces two genuinely different PT-paired
Lorentz metrics. -/
theorem explicitPositivePTConformalMetrics_ne :
    conformalSmoothGeneralLorentzMetric period hPeriod
        (explicitPositivePTScale period hPeriod)
        (explicitPositivePTScale_pos period hPeriod) ≠
      conformalSmoothGeneralLorentzMetric period hPeriod
        (ptPairedConformalScale period hPeriod
          (explicitPositivePTScale period hPeriod))
        (ptPairedConformalScale_pos period hPeriod
          (explicitPositivePTScale period hPeriod)
          (explicitPositivePTScale_pos period hPeriod)) := by
  intro hMetric
  apply explicitPositivePTScale_ne_partner period hPeriod
  exact conformalSmoothGeneralLorentzMetric_injective_scale period hPeriod
    (explicitPositivePTScale_pos period hPeriod)
    (ptPairedConformalScale_pos period hPeriod
      (explicitPositivePTScale period hPeriod)
      (explicitPositivePTScale_pos period hPeriod)) hMetric

/-- Fully explicit canonical field packet with a non-diagonal PT metric pair. -/
def explicitDistinctPTPairedConformalGeneralLorentzFieldPacket :
    CanonicalPTPairedConformalGeneralLorentzFieldPacket period hPeriod
      (explicitPositivePTScale period hPeriod) :=
  canonicalPTPairedConformalGeneralLorentzFieldPacket period hPeriod
    (explicitPositivePTScale period hPeriod)
    (explicitPositivePTScale_pos period hPeriod)

theorem explicitDistinctPTPairedConformalGeneralLorentzFieldPacket_metrics_ne :
    let package :=
      explicitDistinctPTPairedConformalGeneralLorentzFieldPacket period hPeriod
    package.generalFields.metrics.1 ≠ package.generalFields.metrics.2 := by
  change conformalSmoothGeneralLorentzMetric period hPeriod
        (explicitPositivePTScale period hPeriod)
        (explicitPositivePTScale_pos period hPeriod) ≠
      conformalSmoothGeneralLorentzMetric period hPeriod
        (ptPairedConformalScale period hPeriod
          (explicitPositivePTScale period hPeriod))
        (ptPairedConformalScale_pos period hPeriod
          (explicitPositivePTScale period hPeriod)
          (explicitPositivePTScale_pos period hPeriod))
  exact explicitPositivePTConformalMetrics_ne period hPeriod

end
end P0EFTJanusCanonicalPTPairedConformalGeneralLorentzFieldPacket4D
end JanusFormal
