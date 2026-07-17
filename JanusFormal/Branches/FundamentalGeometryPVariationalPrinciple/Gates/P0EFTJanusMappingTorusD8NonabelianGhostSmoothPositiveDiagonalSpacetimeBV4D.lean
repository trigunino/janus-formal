import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalPTCovariance4D

/-!
# BV master model on the smooth positive diagonal spacetime cone

The eight logarithms of an actual smooth positive diagonal metric pair are
coupled to eight smooth metric ghosts and their shifted antifields.  The
existing corrected finite CE/BV differential lifts exactly to this nonlinear
positive cone: its square is the pointed zero represented by the unit metric
in logarithmic coordinates.  The canonical odd bracket, pointwise and
integrated CME, and PT covariance are inherited without a new measure
contract.

This is a fixed-frame diagonal/logarithmic cone.  It is not yet the BV theory
of arbitrary Lorentzian tensor metrics, derivative-dependent or nonlocal
functionals, or a completed infinite-dimensional cotangent space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostSmoothPositiveDiagonalSpacetimeBV4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVPTCovariance4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalPTCovariance4D

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

abbrev SmoothPositiveMetricLogField :=
  SmoothQuotientField period hPeriod (PositiveMetricCoordinate → Real)

abbrev SmoothPositiveMetricAntifield :=
  SmoothQuotientField period hPeriod FiniteMetricCEField

/-! ## Global logarithmic chart of the positive diagonal cone -/

/-- One of the eight positive spacetime metric magnitudes. -/
def positiveSpacetimeMetricMagnitude
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (coordinate : PositiveMetricCoordinate) :
    SmoothQuotientField period hPeriod Real where
  toFun point := if coordinate.1 = 0 then
      metrics.plusMagnitude point coordinate.2
    else metrics.minusMagnitude point coordinate.2
  contMDiff_toFun := by
    by_cases hSheet : coordinate.1 = 0
    · simp only [hSheet, if_true]
      exact (contMDiff_pi_space.mp metrics.plusMagnitude.contMDiff_toFun)
        coordinate.2
    · simp only [hSheet, if_false]
      exact (contMDiff_pi_space.mp metrics.minusMagnitude.contMDiff_toFun)
        coordinate.2

theorem positiveSpacetimeMetricMagnitude_pos
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (coordinate : PositiveMetricCoordinate)
    (point : EffectiveQuotient period hPeriod) :
    0 < positiveSpacetimeMetricMagnitude period hPeriod
      metrics coordinate point := by
  simp only [positiveSpacetimeMetricMagnitude]
  split_ifs
  · exact metrics.plus_pos point coordinate.2
  · exact metrics.minus_pos point coordinate.2

/-- All eight smooth logarithmic metric coordinates on spacetime. -/
def positiveSpacetimeMetricLogField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothPositiveMetricLogField period hPeriod where
  toFun point coordinate := Real.log
    (positiveSpacetimeMetricMagnitude period hPeriod metrics coordinate point)
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro coordinate point
    have hSmooth :
        ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ω
          (positiveSpacetimeMetricMagnitude period hPeriod metrics coordinate)
          point :=
      (positiveSpacetimeMetricMagnitude period hPeriod metrics coordinate)
        |>.contMDiff_toFun.contMDiffAt
    exact
      (Real.contDiffAt_log.2
        (positiveSpacetimeMetricMagnitude_pos period hPeriod metrics coordinate
          point).ne').contMDiffAt.comp point hSmooth

/-- Inverse logarithmic chart: arbitrary smooth logs exponentiate to a
strictly-positive diagonal metric pair. -/
def smoothPositiveDiagonalMetricPairOfLog
    (logs : SmoothPositiveMetricLogField period hPeriod) :
    SmoothPositiveDiagonalMetricPair period hPeriod where
  plusMagnitude :=
    { toFun := fun point i => Real.exp (logs point (0, i))
      contMDiff_toFun := by
        rw [contMDiff_pi_space]
        intro i
        exact Real.contDiff_exp.contMDiff.comp
          ((contMDiff_pi_space.mp logs.contMDiff_toFun) (0, i)) }
  minusMagnitude :=
    { toFun := fun point i => Real.exp (logs point (1, i))
      contMDiff_toFun := by
        rw [contMDiff_pi_space]
        intro i
        exact Real.contDiff_exp.contMDiff.comp
          ((contMDiff_pi_space.mp logs.contMDiff_toFun) (1, i)) }
  plus_pos := fun _ _ => Real.exp_pos _
  minus_pos := fun _ _ => Real.exp_pos _

@[simp]
theorem positiveSpacetimeMetricLogField_ofLog_apply
    (logs : SmoothPositiveMetricLogField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (coordinate : PositiveMetricCoordinate) :
    positiveSpacetimeMetricLogField period hPeriod
        (smoothPositiveDiagonalMetricPairOfLog period hPeriod logs)
        point coordinate = logs point coordinate := by
  rcases coordinate with ⟨sheet, i⟩
  fin_cases sheet <;>
    simp [positiveSpacetimeMetricLogField,
      positiveSpacetimeMetricMagnitude,
      smoothPositiveDiagonalMetricPairOfLog]

/-! ## Positive metric/ghost/antifield phase and corrected BRST -/

/-- Actual positive diagonal metrics, their logarithmic ghosts and shifted
antifields. -/
@[ext]
structure SmoothPositiveDiagonalMetricBVSpacetimeField where
  metrics : SmoothPositiveDiagonalMetricPair period hPeriod
  metricGhost : SmoothPositiveMetricLogField period hPeriod
  antifield : SmoothPositiveMetricAntifield period hPeriod

/-- CE field whose odd slot is the metric ghost and whose even slot is the
actual logarithm of the positive metric. -/
def positiveDiagonalMetricCEField
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    SmoothQuotientField period hPeriod FiniteMetricCEField where
  toFun point index := if index.2 = 0 then
      field.metricGhost point index.1
    else positiveSpacetimeMetricLogField period hPeriod field.metrics
      point index.1
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro index
    by_cases hSlot : index.2 = 0
    · simp only [hSlot, if_true]
      exact (contMDiff_pi_space.mp field.metricGhost.contMDiff_toFun) index.1
    · simp only [hSlot, if_false]
      exact (contMDiff_pi_space.mp
        (positiveSpacetimeMetricLogField period hPeriod field.metrics).contMDiff_toFun)
          index.1

/-- Embedding of the nonlinear cone phase into the smooth finite BV phase. -/
def positiveDiagonalMetricBVPhaseField
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    SmoothFiniteMetricBVSpacetimeField period hPeriod where
  toFun point :=
    (positiveDiagonalMetricCEField period hPeriod field point,
      field.antifield point)
  contMDiff_toFun :=
    (contMDiff_prod_module_iff _).2
      ⟨(positiveDiagonalMetricCEField period hPeriod field).contMDiff_toFun,
        field.antifield.contMDiff_toFun⟩

@[simp]
theorem positiveDiagonalMetricBVPhaseField_metricLog
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (coordinate : PositiveMetricCoordinate) :
    (positiveDiagonalMetricBVPhaseField period hPeriod field point).1
        (coordinate, 1) =
      positiveSpacetimeMetricLogField period hPeriod field.metrics
        point coordinate := by
  simp [positiveDiagonalMetricBVPhaseField, positiveDiagonalMetricCEField]

@[simp]
theorem positiveDiagonalMetricBVPhaseField_metricGhost
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (coordinate : PositiveMetricCoordinate) :
    (positiveDiagonalMetricBVPhaseField period hPeriod field point).1
        (coordinate, 0) = field.metricGhost point coordinate := by
  simp [positiveDiagonalMetricBVPhaseField, positiveDiagonalMetricCEField]

private def finiteMetricCETransposeContinuous :
    FiniteMetricCEField →L[Real] FiniteMetricCEField :=
  LinearMap.toContinuousLinearMap finiteMetricCETranspose

private def smoothPositiveMetricAntifieldBRST
    (antifield : SmoothPositiveMetricAntifield period hPeriod) :
    SmoothPositiveMetricAntifield period hPeriod where
  toFun point := finiteMetricCETranspose (antifield point)
  contMDiff_toFun :=
    finiteMetricCETransposeContinuous.contDiff.contMDiff.comp
      antifield.contMDiff_toFun

/-- Corrected BV differential lifted through the global logarithmic chart. -/
def smoothPositiveDiagonalMetricBVBRST
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod where
  metrics := smoothPositiveDiagonalMetricPairOfLog period hPeriod
    field.metricGhost
  metricGhost := 0
  antifield := smoothPositiveMetricAntifieldBRST period hPeriod field.antifield

/-- Pointed zero of the logarithmic cone: unit metric, zero ghost and zero
antifield. -/
def smoothPositiveDiagonalMetricBVZero :
    SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod where
  metrics := smoothPositiveDiagonalMetricPairOfLog period hPeriod 0
  metricGhost := 0
  antifield := 0

theorem positiveDiagonalMetricBVPhaseField_BRST
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    positiveDiagonalMetricBVPhaseField period hPeriod
        (smoothPositiveDiagonalMetricBVBRST period hPeriod field) =
      smoothSpacetimeBVBRST period hPeriod
        (positiveDiagonalMetricBVPhaseField period hPeriod field) := by
  apply SmoothQuotientField.ext period hPeriod FiniteMetricBVPhase
  intro point
  apply Prod.ext
  · funext index
    rcases index with ⟨coordinate, slot⟩
    fin_cases slot
    · change (0 : PositiveMetricCoordinate → Real) coordinate = 0
      rfl
    · simp [positiveDiagonalMetricBVPhaseField,
        positiveDiagonalMetricCEField,
        smoothPositiveDiagonalMetricBVBRST,
        smoothSpacetimeBVBRST_apply, finiteMetricBVBRST,
        finiteMetricCEDifferential,
        positiveSpacetimeMetricLogField_ofLog_apply]
  · rfl

theorem smoothPositiveDiagonalMetricBVBRST_square_zero
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    smoothPositiveDiagonalMetricBVBRST period hPeriod
        (smoothPositiveDiagonalMetricBVBRST period hPeriod field) =
      smoothPositiveDiagonalMetricBVZero period hPeriod := by
  apply SmoothPositiveDiagonalMetricBVSpacetimeField.ext
  · rfl
  · rfl
  · apply SmoothQuotientField.ext period hPeriod FiniteMetricCEField
    intro point
    exact finiteMetricCETranspose_square_zero (field.antifield point)

/-! ## Restricted odd bracket and master equation -/

/-- Pointwise represented odd bracket restricted to the positive metric cone. -/
def smoothPositiveDiagonalMetricBVOddAntibracketDensity
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  finiteBVOddAntibracket first.observable second.observable
    (positiveDiagonalMetricBVPhaseField period hPeriod field point)

theorem smoothPositiveDiagonalMetricBV_canonical_coordinate_bracket
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod)
    (first second : FiniteMetricCEIndex)
    (point : EffectiveQuotient period hPeriod) :
    smoothPositiveDiagonalMetricBVOddAntibracketDensity period hPeriod
        (⟨finiteBVFieldCoordinateObservable first,
          contDiff_apply _ _ first |>.comp contDiff_fst,
          contDiff_const, contDiff_const⟩ : SmoothUltralocalBVFunctional)
        (⟨finiteBVAntifieldCoordinateObservable second,
          contDiff_apply _ _ second |>.comp contDiff_snd,
          contDiff_const, contDiff_const⟩ : SmoothUltralocalBVFunctional)
        field point = if first = second then 1 else 0 :=
  finiteBVOddAntibracket_field_antifield first second
    (positiveDiagonalMetricBVPhaseField period hPeriod field point)

/-- Canonical integrated represented bracket restricted to the cone. -/
def canonicalSmoothPositiveDiagonalMetricBVOddAntibracket
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) : Real :=
  canonicalSpacetimeUltralocalBVOddAntibracket period hPeriod first second
    (positiveDiagonalMetricBVPhaseField period hPeriod field)

theorem smoothPositiveDiagonalMetricBVOddAntibracketDensity_integrable
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    Integrable
      (smoothPositiveDiagonalMetricBVOddAntibracketDensity period hPeriod
        first second field)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  canonicalSpacetimeUltralocalBVOddAntibracket_integrable period hPeriod
    first second (positiveDiagonalMetricBVPhaseField period hPeriod field)

/-- Master density restricted to the actual positive metric cone. -/
def smoothPositiveDiagonalMetricBVMasterDensity
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :=
  smoothSpacetimeBVMasterDensity period hPeriod
    (positiveDiagonalMetricBVPhaseField period hPeriod field)

/-- Canonical master action restricted to the cone. -/
def canonicalSmoothPositiveDiagonalMetricBVMasterAction
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) : Real :=
  canonicalSmoothSpacetimeBVMasterAction period hPeriod
    (positiveDiagonalMetricBVPhaseField period hPeriod field)

theorem smoothPositiveDiagonalMetricBVMasterDensity_integrable
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    Integrable (smoothPositiveDiagonalMetricBVMasterDensity period hPeriod field)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  smoothSpacetimeBVMasterDensity_integrable period hPeriod
    (positiveDiagonalMetricBVPhaseField period hPeriod field)

private def positiveMetricBVWitnessCoordinate : PositiveMetricCoordinate :=
  (0, 0)

private def smoothPositiveMetricBVWitnessGhost :
    SmoothPositiveMetricLogField period hPeriod where
  toFun _ coordinate :=
    if coordinate = positiveMetricBVWitnessCoordinate then 1 else 0
  contMDiff_toFun := contMDiff_const

private def smoothPositiveMetricBVWitnessAntifield :
    SmoothPositiveMetricAntifield period hPeriod where
  toFun _ := finiteMetricBasis (positiveMetricBVWitnessCoordinate, 1)
  contMDiff_toFun := contMDiff_const

/-- Explicit positive-cone state carrying the existing nonzero master phase. -/
def smoothPositiveDiagonalMetricBVWitness :
    SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod where
  metrics := smoothPositiveDiagonalMetricPairOfLog period hPeriod 0
  metricGhost := smoothPositiveMetricBVWitnessGhost period hPeriod
  antifield := smoothPositiveMetricBVWitnessAntifield period hPeriod

theorem positiveDiagonalMetricBVPhaseField_witness :
    positiveDiagonalMetricBVPhaseField period hPeriod
        (smoothPositiveDiagonalMetricBVWitness period hPeriod) =
      smoothSpacetimeBVWitnessField period hPeriod := by
  apply SmoothQuotientField.ext period hPeriod FiniteMetricBVPhase
  intro point
  apply Prod.ext
  · funext index
    rcases index with ⟨coordinate, slot⟩
    fin_cases slot
    · simp [positiveDiagonalMetricBVPhaseField,
        positiveDiagonalMetricCEField,
        smoothPositiveDiagonalMetricBVWitness,
        smoothPositiveMetricBVWitnessGhost,
        smoothSpacetimeBVWitnessField, smoothSpacetimeBVWitnessPhase,
        finiteMetricBasis, positiveMetricBVWitnessCoordinate]
    · simp [positiveDiagonalMetricBVPhaseField,
        positiveDiagonalMetricCEField,
        smoothPositiveDiagonalMetricBVWitness,
        smoothSpacetimeBVWitnessField, smoothSpacetimeBVWitnessPhase,
        positiveSpacetimeMetricLogField_ofLog_apply,
        finiteMetricBasis]
      change (0 : PositiveMetricCoordinate → Real) coordinate = 0
      rfl
  · rfl

theorem canonicalSmoothPositiveDiagonalMetricBVMasterAction_witness :
    canonicalSmoothPositiveDiagonalMetricBVMasterAction period hPeriod
        (smoothPositiveDiagonalMetricBVWitness period hPeriod) =
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod Set.univ).toReal := by
  unfold canonicalSmoothPositiveDiagonalMetricBVMasterAction
  rw [positiveDiagonalMetricBVPhaseField_witness]
  exact canonicalSmoothSpacetimeBVMasterAction_witness period hPeriod

theorem canonicalSmoothPositiveDiagonalMetricBVMasterAction_nonzero :
    canonicalSmoothPositiveDiagonalMetricBVMasterAction period hPeriod ≠ 0 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  intro hZero
  have hWitness := congrFun hZero
    (smoothPositiveDiagonalMetricBVWitness period hPeriod)
  rw [canonicalSmoothPositiveDiagonalMetricBVMasterAction_witness] at hWitness
  exact (ENNReal.toReal_ne_zero.2
    ⟨(Measure.measure_univ_ne_zero).2
      (intrinsicCanonicalLorentzVolumeMeasure_ne_zero period hPeriod),
      measure_ne_top _ _⟩) hWitness

theorem smoothPositiveDiagonalMetricBV_classical_master_equation_pointwise
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothPositiveDiagonalMetricBVOddAntibracketDensity period hPeriod
        smoothSpacetimeBVMasterUltralocalFunctional
        smoothSpacetimeBVMasterUltralocalFunctional field point = 0 :=
  finiteMetricBV_classical_master_equation
    (positiveDiagonalMetricBVPhaseField period hPeriod field point)

theorem canonicalSmoothPositiveDiagonalMetricBV_integrated_CME
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothPositiveDiagonalMetricBVOddAntibracket period hPeriod
        smoothSpacetimeBVMasterUltralocalFunctional
        smoothSpacetimeBVMasterUltralocalFunctional field = 0 :=
  canonicalSmoothSpacetimeBV_ultralocal_integrated_classical_master_equation
    period hPeriod (positiveDiagonalMetricBVPhaseField period hPeriod field)

/-! ## PT/exchange on the positive cone -/

def smoothPositiveMetricGhostPT
    (ghost : SmoothPositiveMetricLogField period hPeriod) :
    SmoothPositiveMetricLogField period hPeriod where
  toFun point coordinate := ghost
    (reflectedSpherePT period hPeriod point)
    (positiveMetricCoordinatePTEquiv coordinate)
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro coordinate
    exact ((contMDiff_pi_space.mp ghost.contMDiff_toFun)
      (positiveMetricCoordinatePTEquiv coordinate)).comp
        (reflectedSpherePT_contMDiff period hPeriod)

private def finiteMetricCEPTExchangeContinuous :
    FiniteMetricCEField →L[Real] FiniteMetricCEField :=
  LinearMap.toContinuousLinearMap finiteMetricCEPTExchange

def smoothPositiveMetricAntifieldPT
    (antifield : SmoothPositiveMetricAntifield period hPeriod) :
    SmoothPositiveMetricAntifield period hPeriod where
  toFun point := finiteMetricCEPTExchange
    (antifield (reflectedSpherePT period hPeriod point))
  contMDiff_toFun :=
    finiteMetricCEPTExchangeContinuous.contDiff.contMDiff.comp
      (antifield.contMDiff_toFun.comp
        (reflectedSpherePT_contMDiff period hPeriod))

theorem positiveSpacetimeMetricLogField_ptExchange_apply
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (coordinate : PositiveMetricCoordinate) :
    positiveSpacetimeMetricLogField period hPeriod
        (ptExchange period hPeriod metrics) point coordinate =
      positiveSpacetimeMetricLogField period hPeriod metrics
        (reflectedSpherePT period hPeriod point)
        (positiveMetricCoordinatePTEquiv coordinate) := by
  rcases coordinate with ⟨sheet, i⟩
  fin_cases sheet <;>
    simp [positiveSpacetimeMetricLogField,
      positiveSpacetimeMetricMagnitude, ptExchange,
      positiveMetricCoordinatePTEquiv]

theorem ptExchange_smoothPositiveDiagonalMetricPairOfLog
    (logs : SmoothPositiveMetricLogField period hPeriod) :
    ptExchange period hPeriod
        (smoothPositiveDiagonalMetricPairOfLog period hPeriod logs) =
      smoothPositiveDiagonalMetricPairOfLog period hPeriod
        (smoothPositiveMetricGhostPT period hPeriod logs) := by
  apply SmoothPositiveDiagonalMetricPair.ext
  · apply SmoothQuotientField.ext period hPeriod _
    intro point
    funext i
    simp [ptExchange, smoothPositiveDiagonalMetricPairOfLog,
      smoothPositiveMetricGhostPT, positiveMetricCoordinatePTEquiv]
  · apply SmoothQuotientField.ext period hPeriod _
    intro point
    funext i
    simp [ptExchange, smoothPositiveDiagonalMetricPairOfLog,
      smoothPositiveMetricGhostPT, positiveMetricCoordinatePTEquiv]

def smoothPositiveDiagonalMetricBVPT
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod where
  metrics := ptExchange period hPeriod field.metrics
  metricGhost := smoothPositiveMetricGhostPT period hPeriod field.metricGhost
  antifield := smoothPositiveMetricAntifieldPT period hPeriod field.antifield

theorem positiveDiagonalMetricBVPhaseField_pt_apply
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    positiveDiagonalMetricBVPhaseField period hPeriod
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) point =
      finiteMetricBVPTExchange
        (positiveDiagonalMetricBVPhaseField period hPeriod field
          (reflectedSpherePT period hPeriod point)) := by
  apply Prod.ext
  · funext index
    rcases index with ⟨coordinate, slot⟩
    fin_cases slot
    · rfl
    · exact positiveSpacetimeMetricLogField_ptExchange_apply
        period hPeriod field.metrics point coordinate
  · rfl

theorem positiveDiagonalMetricBVPhaseField_pt
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    positiveDiagonalMetricBVPhaseField period hPeriod
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) =
      smoothSpacetimeBVPT period hPeriod
        (positiveDiagonalMetricBVPhaseField period hPeriod field) := by
  apply SmoothQuotientField.ext period hPeriod FiniteMetricBVPhase
  intro point
  rw [smoothSpacetimeBVPT_apply]
  exact positiveDiagonalMetricBVPhaseField_pt_apply period hPeriod field point

theorem smoothPositiveDiagonalMetricBVPT_involutive
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    smoothPositiveDiagonalMetricBVPT period hPeriod
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) = field := by
  apply SmoothPositiveDiagonalMetricBVSpacetimeField.ext
  · exact ptExchange_involutive period hPeriod field.metrics
  · apply SmoothQuotientField.ext period hPeriod
      (PositiveMetricCoordinate → Real)
    intro point
    funext coordinate
    simp [smoothPositiveDiagonalMetricBVPT, smoothPositiveMetricGhostPT]
  · apply SmoothQuotientField.ext period hPeriod FiniteMetricCEField
    intro point
    simp [smoothPositiveDiagonalMetricBVPT, smoothPositiveMetricAntifieldPT]

theorem smoothPositiveDiagonalMetricBVPT_commutes_BRST
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    smoothPositiveDiagonalMetricBVPT period hPeriod
        (smoothPositiveDiagonalMetricBVBRST period hPeriod field) =
      smoothPositiveDiagonalMetricBVBRST period hPeriod
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) := by
  apply SmoothPositiveDiagonalMetricBVSpacetimeField.ext
  · exact ptExchange_smoothPositiveDiagonalMetricPairOfLog period hPeriod
      field.metricGhost
  · apply SmoothQuotientField.ext period hPeriod
      (PositiveMetricCoordinate → Real)
    intro point
    funext coordinate
    rfl
  · apply SmoothQuotientField.ext period hPeriod FiniteMetricCEField
    intro point
    exact finiteMetricCEPTExchange_commutes_transpose
      (field.antifield (reflectedSpherePT period hPeriod point))

theorem smoothPositiveDiagonalMetricBVOddAntibracketDensity_pt
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothPositiveDiagonalMetricBVOddAntibracketDensity period hPeriod
        (smoothUltralocalBVFunctionalPT first)
        (smoothUltralocalBVFunctionalPT second)
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) point =
      smoothPositiveDiagonalMetricBVOddAntibracketDensity period hPeriod
        first second field (reflectedSpherePT period hPeriod point) := by
  unfold smoothPositiveDiagonalMetricBVOddAntibracketDensity
  rw [positiveDiagonalMetricBVPhaseField_pt_apply]
  change finiteBVOddAntibracket
      (finiteBVObservablePT first.observable)
      (finiteBVObservablePT second.observable) _ = _
  rw [finiteBVOddAntibracket_pt_naturality,
    finiteMetricBVPTExchange_involutive]

theorem smoothPositiveDiagonalMetricBV_classical_master_equation_pointwise_pt
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothPositiveDiagonalMetricBVOddAntibracketDensity period hPeriod
        (smoothUltralocalBVFunctionalPT
          smoothSpacetimeBVMasterUltralocalFunctional)
        (smoothUltralocalBVFunctionalPT
          smoothSpacetimeBVMasterUltralocalFunctional)
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) point = 0 := by
  rw [smoothPositiveDiagonalMetricBVOddAntibracketDensity_pt]
  exact smoothPositiveDiagonalMetricBV_classical_master_equation_pointwise
    period hPeriod field (reflectedSpherePT period hPeriod point)

theorem canonicalSmoothPositiveDiagonalMetricBVMasterAction_pt
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothPositiveDiagonalMetricBVMasterAction period hPeriod
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) =
      canonicalSmoothPositiveDiagonalMetricBVMasterAction period hPeriod field := by
  unfold canonicalSmoothPositiveDiagonalMetricBVMasterAction
  rw [positiveDiagonalMetricBVPhaseField_pt]
  exact canonicalSmoothSpacetimeBVMasterAction_pt period hPeriod
    (positiveDiagonalMetricBVPhaseField period hPeriod field)

theorem canonicalSmoothPositiveDiagonalMetricBVOddAntibracket_pt
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothPositiveDiagonalMetricBVOddAntibracket period hPeriod
        (smoothUltralocalBVFunctionalPT first)
        (smoothUltralocalBVFunctionalPT second)
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) =
      canonicalSmoothPositiveDiagonalMetricBVOddAntibracket period hPeriod
        first second field := by
  unfold canonicalSmoothPositiveDiagonalMetricBVOddAntibracket
  rw [positiveDiagonalMetricBVPhaseField_pt]
  exact canonicalSpacetimeUltralocalBVOddAntibracket_pt period hPeriod
    first second (positiveDiagonalMetricBVPhaseField period hPeriod field)

theorem canonicalSmoothPositiveDiagonalMetricBV_integrated_CME_pt
    (field : SmoothPositiveDiagonalMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothPositiveDiagonalMetricBVOddAntibracket period hPeriod
        (smoothUltralocalBVFunctionalPT
          smoothSpacetimeBVMasterUltralocalFunctional)
        (smoothUltralocalBVFunctionalPT
          smoothSpacetimeBVMasterUltralocalFunctional)
        (smoothPositiveDiagonalMetricBVPT period hPeriod field) = 0 := by
  rw [canonicalSmoothPositiveDiagonalMetricBVOddAntibracket_pt period hPeriod]
  exact canonicalSmoothPositiveDiagonalMetricBV_integrated_CME
    period hPeriod field

end
end P0EFTJanusMappingTorusD8NonabelianGhostSmoothPositiveDiagonalSpacetimeBV4D
end JanusFormal
