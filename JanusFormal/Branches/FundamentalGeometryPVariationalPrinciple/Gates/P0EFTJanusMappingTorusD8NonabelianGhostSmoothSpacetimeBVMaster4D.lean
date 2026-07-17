import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D

/-!
# Pointwise BV master model on the smooth D8 spacetime quotient

The same finite 32-dimensional BV phase used on the throat is promoted
fibrewise to smooth fields on the actual compact reflected-sphere mapping
torus. Its BRST operator is smooth and square-zero, its finite odd bracket
satisfies the classical master equation pointwise and after integration, and
its master density has a nonzero canonical spacetime integral.

This is a constant finite BV phase bundle over spacetime. It is not a BV
construction for general tensor metrics and does not assert a nonlocal
functional antibracket on the infinite-dimensional field space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D

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

/-- Smooth sections of the constant finite BV phase bundle over the actual D8
spacetime quotient. -/
abbrev SmoothFiniteMetricBVSpacetimeField :=
  SmoothQuotientField period hPeriod FiniteMetricBVPhase

private def finiteMetricBVBRSTContinuous :
    FiniteMetricBVPhase →L[Real] FiniteMetricBVPhase :=
  LinearMap.toContinuousLinearMap finiteMetricBVBRST

private def finiteMetricCEDifferentialContinuous :
    FiniteMetricCEField →L[Real] FiniteMetricCEField :=
  LinearMap.toContinuousLinearMap finiteMetricCEDifferential

/-! ## Smooth spacetime BRST and master density -/

/-- Fibrewise finite BRST differential on smooth spacetime BV fields. -/
def smoothSpacetimeBVBRST
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    SmoothFiniteMetricBVSpacetimeField period hPeriod where
  toFun point := finiteMetricBVBRST (field point)
  contMDiff_toFun :=
    (finiteMetricBVBRSTContinuous.contDiff.contMDiff).comp
      field.contMDiff_toFun

@[simp]
theorem smoothSpacetimeBVBRST_apply
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVBRST period hPeriod field point =
      finiteMetricBVBRST (field point) :=
  rfl

/-- The smooth spacetime BRST differential remains square-zero. -/
theorem smoothSpacetimeBVBRST_square_zero
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    smoothSpacetimeBVBRST period hPeriod
        (smoothSpacetimeBVBRST period hPeriod field) = 0 := by
  apply SmoothQuotientField.ext period hPeriod FiniteMetricBVPhase
  intro point
  exact finiteMetricBVBRST_square_zero (field point)

/-- Spacetime BRST restricts to the already constructed throat BRST. -/
theorem smoothSpacetimeBVBRST_throatTrace
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    throatTrace period hPeriod FiniteMetricBVPhase
        (smoothSpacetimeBVBRST period hPeriod field) =
      smoothThroatBVBRST period hPeriod
        (throatTrace period hPeriod FiniteMetricBVPhase field) := by
  apply SmoothThroatField.ext period hPeriod FiniteMetricBVPhase
  intro point
  rfl

private theorem finiteMetricBVMasterAction_contDiff :
    ContDiff Real ω finiteMetricBVMasterAction := by
  unfold finiteMetricBVMasterAction finiteMetricDot
  apply ContDiff.sum
  intro coordinate _
  apply ContDiff.sum
  intro slot _
  exact ((contDiff_apply Real Real (coordinate, slot)).comp contDiff_snd).mul
    ((contDiff_apply Real Real (coordinate, slot)).comp
      (finiteMetricCEDifferentialContinuous.contDiff.comp contDiff_fst))

/-- Smooth spacetime master density obtained from the finite master
Hamiltonian in every fibre. -/
def smoothSpacetimeBVMasterDensity
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun point := finiteMetricBVMasterAction (field point)
  contMDiff_toFun :=
    finiteMetricBVMasterAction_contDiff.contMDiff.comp
      field.contMDiff_toFun

@[simp]
theorem smoothSpacetimeBVMasterDensity_apply
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVMasterDensity period hPeriod field point =
      finiteMetricBVMasterAction (field point) :=
  rfl

/-- The spacetime master density restricts to the throat master density. -/
theorem smoothSpacetimeBVMasterDensity_throatTrace
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    throatTrace period hPeriod Real
        (smoothSpacetimeBVMasterDensity period hPeriod field) =
      smoothThroatBVMasterDensity period hPeriod
        (throatTrace period hPeriod FiniteMetricBVPhase field) := by
  apply SmoothThroatField.ext period hPeriod Real
  intro point
  rfl

/-! ## Pointwise classical master equation -/

theorem smoothSpacetimeBV_classical_master_equation_pointwise
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        finiteMetricBVMasterObservable (field point) = 0 :=
  finiteMetricBV_classical_master_equation (field point)

theorem smoothSpacetimeBVMaster_generates_field_pointwise
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteMetricCEIndex) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        (finiteBVFieldCoordinateObservable index) (field point) =
      (smoothSpacetimeBVBRST period hPeriod field point).1 index :=
  finiteMetricBVMaster_generates_field (field point) index

theorem smoothSpacetimeBVMaster_generates_antifield_pointwise
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteMetricCEIndex) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        (finiteBVAntifieldCoordinateObservable index) (field point) =
      (smoothSpacetimeBVBRST period hPeriod field point).2 index :=
  finiteMetricBVMaster_generates_antifield (field point) index

/-! ## Canonical spacetime integral and nonzero witness -/

/-- Master action integrated against the installed canonical spacetime
Lorentz-volume measure. -/
def canonicalSmoothSpacetimeBVMasterAction
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) : Real :=
  ∫ point, smoothSpacetimeBVMasterDensity period hPeriod field point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

theorem smoothSpacetimeBVMasterDensity_integrable
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    Integrable (smoothSpacetimeBVMasterDensity period hPeriod field)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact
    (smoothSpacetimeBVMasterDensity period hPeriod field).contMDiff_toFun.continuous
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace
          (smoothSpacetimeBVMasterDensity period hPeriod field))

/-- Explicit finite phase on which the master Hamiltonian is one. -/
def smoothSpacetimeBVWitnessPhase : FiniteMetricBVPhase :=
  (finiteMetricBasis ((((0 : Fin 2), (0 : Fin 4)), 0)),
    finiteMetricBasis ((((0 : Fin 2), (0 : Fin 4)), 1)))

/-- Constant smooth spacetime section carrying the nonzero finite phase. -/
def smoothSpacetimeBVWitnessField :
    SmoothFiniteMetricBVSpacetimeField period hPeriod where
  toFun _ := smoothSpacetimeBVWitnessPhase
  contMDiff_toFun := contMDiff_const

@[simp]
theorem smoothSpacetimeBVWitnessField_apply
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVWitnessField period hPeriod point =
      smoothSpacetimeBVWitnessPhase :=
  rfl

@[simp]
theorem smoothSpacetimeBVWitnessDensity
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVMasterDensity period hPeriod
        (smoothSpacetimeBVWitnessField period hPeriod) point = 1 := by
  change finiteMetricBVMasterAction smoothSpacetimeBVWitnessPhase = 1
  exact finiteMetricBVMasterAction_witness

theorem canonicalSmoothSpacetimeBVMasterAction_witness :
    canonicalSmoothSpacetimeBVMasterAction period hPeriod
        (smoothSpacetimeBVWitnessField period hPeriod) =
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod Set.univ).toReal := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  rw [canonicalSmoothSpacetimeBVMasterAction]
  calc
    ∫ point, smoothSpacetimeBVMasterDensity period hPeriod
        (smoothSpacetimeBVWitnessField period hPeriod) point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
        ∫ _point, (1 : Real)
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
            apply integral_congr_ae
            filter_upwards [] with point
            exact smoothSpacetimeBVWitnessDensity period hPeriod point
    _ = _ := by simp [measureReal_def]

/-- The canonical integrated spacetime master action is genuinely nonzero. -/
theorem canonicalSmoothSpacetimeBVMasterAction_nonzero :
    canonicalSmoothSpacetimeBVMasterAction period hPeriod ≠ 0 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  intro hZero
  have hWitness :
      canonicalSmoothSpacetimeBVMasterAction period hPeriod
          (smoothSpacetimeBVWitnessField period hPeriod) = 0 := by
    rw [hZero]
    rfl
  rw [canonicalSmoothSpacetimeBVMasterAction_witness] at hWitness
  exact (ENNReal.toReal_ne_zero.2
    ⟨(Measure.measure_univ_ne_zero).2
      (intrinsicCanonicalLorentzVolumeMeasure_ne_zero period hPeriod),
      measure_ne_top _ _⟩) hWitness

/-! ## Integrated classical master equation -/

/-- Pointwise self-antibracket packaged as a smooth scalar spacetime field. -/
def smoothSpacetimeBVMasterSelfBracketDensity
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun point := finiteBVOddAntibracket finiteMetricBVMasterObservable
    finiteMetricBVMasterObservable (field point)
  contMDiff_toFun := by
    have hZero :
        (fun point : EffectiveQuotient period hPeriod =>
          finiteBVOddAntibracket finiteMetricBVMasterObservable
            finiteMetricBVMasterObservable (field point)) =
          fun _ => 0 := by
      funext point
      exact finiteMetricBV_classical_master_equation (field point)
    rw [hZero]
    exact contMDiff_const

@[simp]
theorem smoothSpacetimeBVMasterSelfBracketDensity_apply
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVMasterSelfBracketDensity period hPeriod field point =
      finiteBVOddAntibracket finiteMetricBVMasterObservable
        finiteMetricBVMasterObservable (field point) :=
  rfl

@[simp]
theorem smoothSpacetimeBVMasterSelfBracketDensity_zero
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    smoothSpacetimeBVMasterSelfBracketDensity period hPeriod field = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact finiteMetricBV_classical_master_equation (field point)

/-- Canonical integral of the pointwise finite BV self-antibracket. -/
def canonicalSmoothSpacetimeBVMasterSelfBracket
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) : Real :=
  ∫ point, smoothSpacetimeBVMasterSelfBracketDensity period hPeriod field point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

theorem smoothSpacetimeBVMasterSelfBracketDensity_integrable
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    Integrable
      (smoothSpacetimeBVMasterSelfBracketDensity period hPeriod field)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [smoothSpacetimeBVMasterSelfBracketDensity_zero]
  change Integrable (0 : EffectiveQuotient period hPeriod → Real)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  exact integrable_zero (EffectiveQuotient period hPeriod) Real
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Integrated classical master equation on the canonical smooth D8
spacetime quotient. -/
theorem canonicalSmoothSpacetimeBV_integrated_classical_master_equation
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothSpacetimeBVMasterSelfBracket period hPeriod field = 0 := by
  unfold canonicalSmoothSpacetimeBVMasterSelfBracket
  rw [smoothSpacetimeBVMasterSelfBracketDensity_zero]
  change (∫ _point, (0 : Real)
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0
  simp

end
end P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
end JanusFormal
