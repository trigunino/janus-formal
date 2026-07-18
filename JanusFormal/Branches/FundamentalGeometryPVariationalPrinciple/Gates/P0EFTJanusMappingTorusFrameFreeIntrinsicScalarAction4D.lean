import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

/-!
# Frame-free intrinsic scalar action on the effective D8 quotient

The scalar Lagrangian is a scalar; its Lorentz volume belongs in the
integration measure.  Keeping these two objects separate removes the false
global-frame requirement of `RegularGeneralLorentzMetric`.

The construction below uses no global tangent frame.  Its only measure-level
input is a finite nonzero Borel measure.  A Dirac measure closes a genuinely
nonzero integrated branch.  Identifying a distinguished input with the
canonical smooth Lorentz volume remains the isolated geometric measure
contract; no zero measure is used here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFrameFreeIntrinsicScalarAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

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

/-- Frame-free regularity domain for a scalar coupled to one intrinsic
Lorentz metric.  The smooth representative is tied to the genuine
inverse-metric contraction; no tangent-frame coefficient occurs. -/
structure IntrinsicRegularScalar
    (metric : SmoothGeneralLorentzMetric period hPeriod) where
  field : SmoothScalarField period hPeriod
  kineticContraction : SmoothScalarField period hPeriod
  kineticContraction_eq : ∀ point,
    kineticContraction point =
      inverseMetricContraction period hPeriod metric point
        (scalarDifferential period hPeriod field point)
        (scalarDifferential period hPeriod field point)

/-- Intrinsic scalar Lagrangian, interpreted as a density relative to the
chosen volume measure. -/
def frameFreeScalarDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : IntrinsicRegularScalar period hPeriod metric) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    1 / 2 * data.kineticContraction point -
      1 / 2 * massSquared * (data.field point) ^ 2
  contMDiff_toFun :=
    (contMDiff_const.mul data.kineticContraction.contMDiff_toFun).sub
      ((contMDiff_const.mul contMDiff_const).mul
        (data.field.contMDiff_toFun.pow 2))

theorem frameFreeScalarDensity_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : IntrinsicRegularScalar period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeScalarDensity period hPeriod metric massSquared data point =
      1 / 2 * inverseMetricContraction period hPeriod metric point
          (scalarDifferential period hPeriod data.field point)
          (scalarDifferential period hPeriod data.field point) -
        1 / 2 * massSquared * (data.field point) ^ 2 := by
  change 1 / 2 * data.kineticContraction point -
      1 / 2 * massSquared * (data.field point) ^ 2 = _
  rw [data.kineticContraction_eq point]

/-- Exact measure interface needed after the frame-free split.  Finiteness
gives integrability on compact D8 and nonzeroness excludes the former vacuous
zero-measure branch. -/
structure FiniteNonzeroActionMeasure where
  measure : Measure (EffectiveQuotient period hPeriod)
  finite : IsFiniteMeasure measure
  nonzero : measure ≠ 0

/-- Every point supplies a concrete finite nonzero action measure.  This is a
formal nontriviality witness, not a claim that a Dirac mass is Lorentz volume. -/
def diracActionMeasure
    (point : EffectiveQuotient period hPeriod) :
    FiniteNonzeroActionMeasure period hPeriod where
  measure := Measure.dirac point
  finite := inferInstance
  nonzero := Measure.dirac_ne_zero

theorem frameFreeScalarDensity_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : IntrinsicRegularScalar period hPeriod metric)
    (volume : FiniteNonzeroActionMeasure period hPeriod) :
    Integrable (frameFreeScalarDensity period hPeriod metric massSquared data)
      volume.measure := by
  letI := volume.finite
  exact (frameFreeScalarDensity period hPeriod metric massSquared data)
    |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Integrated intrinsic action with no global tangent frame. -/
def frameFreeScalarAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : IntrinsicRegularScalar period hPeriod metric)
    (volume : FiniteNonzeroActionMeasure period hPeriod) : Real :=
  ∫ point, frameFreeScalarDensity period hPeriod metric massSquared data point
    ∂volume.measure

private def constantScalarField (value : Real) :
    SmoothScalarField period hPeriod where
  toFun := fun _ => value
  contMDiff_toFun := contMDiff_const

/-- Constants give an unconditional nonempty frame-free regularity domain for
every genuine Lorentz metric, including the intrinsic quotient metric. -/
def constantIntrinsicRegularScalar
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (value : Real) : IntrinsicRegularScalar period hPeriod metric where
  field := constantScalarField period hPeriod value
  kineticContraction := constantScalarField period hPeriod 0
  kineticContraction_eq := by
    intro point
    have hDifferential : scalarDifferential period hPeriod
        (constantScalarField period hPeriod value) point = 0 := by
      apply ContinuousLinearMap.ext
      intro tangent
      simp only [scalarDifferential, constantScalarField, mfderiv_const]
      change (0 : Real) = 0
      rfl
    rw [hDifferential]
    simp only [constantScalarField, inverseMetricContraction, map_zero]

theorem intrinsicRegularScalar_nonempty
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Nonempty (IntrinsicRegularScalar period hPeriod metric) :=
  ⟨constantIntrinsicRegularScalar period hPeriod metric 0⟩

@[simp]
theorem frameFreeScalarDensity_constant
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared value : Real)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeScalarDensity period hPeriod metric massSquared
        (constantIntrinsicRegularScalar period hPeriod metric value) point =
      -(1 / 2 * massSquared * value ^ 2) := by
  simp [frameFreeScalarDensity, constantIntrinsicRegularScalar,
    constantScalarField]

/-- Every finite nonzero volume input gives a nonzero constant-field action;
the result is ready to consume a future canonical Lorentz volume measure. -/
theorem intrinsicMetric_constantAction_nonzero
    (volume : FiniteNonzeroActionMeasure period hPeriod) :
    frameFreeScalarAction period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) 2
        (constantIntrinsicRegularScalar period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) 1)
        volume ≠ 0 := by
  letI := volume.finite
  letI : NeZero volume.measure := ⟨volume.nonzero⟩
  rw [show frameFreeScalarAction period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) 2
      (constantIntrinsicRegularScalar period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) 1) volume =
        -volume.measure.real Set.univ by
    simp [frameFreeScalarAction]]
  exact neg_ne_zero.mpr measureReal_univ_ne_zero

/-- The integrated branch is genuinely nonzero on every point mass. -/
theorem intrinsicMetric_diracAction_nonzero
    (point : EffectiveQuotient period hPeriod) :
    frameFreeScalarAction period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) 2
        (constantIntrinsicRegularScalar period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) 1)
        (diracActionMeasure period hPeriod point) ≠ 0 := by
  exact intrinsicMetric_constantAction_nonzero period hPeriod
    (diracActionMeasure period hPeriod point)

end

end P0EFTJanusMappingTorusFrameFreeIntrinsicScalarAction4D
end JanusFormal
