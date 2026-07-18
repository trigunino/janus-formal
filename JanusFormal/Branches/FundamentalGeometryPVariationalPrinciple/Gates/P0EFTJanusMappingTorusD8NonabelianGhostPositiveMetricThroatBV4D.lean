import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

/-!
# Positive diagonal metric and first antifield extension on the throat

The two positive diagonal metric magnitudes are restricted to the fixed
throat and described by their eight logarithmic coordinates.  The explicit
throat rotation action is tangent to this open cone: its multiplicative
integral curve stays strictly positive for every real parameter.  The
unconditional corrected throat differential then acts componentwise and
retains parity oddness, the Koszul Leibniz rule and square zero.

The last section adds a finite-coordinate, parity-shifted antifield copy and
its canonical coordinate pairing.  This is a concrete first BV seed; no
classical master equation is claimed here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev ThroatScalar := CInfinityThroatScalarField period hPeriod
private abbrev Coefficient := GhostCoefficientExterior
private abbrev ThroatTotal := LLThroatExteriorScalarAlgebra period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The eight logarithmic coordinates: two metric sheets and four diagonal
magnitudes on each sheet. -/
abbrev PositiveMetricCoordinate := Fin 2 × Fin 4

/-- The complete positive diagonal cone after restriction to the throat,
with genuine `C∞` magnitudes. -/
structure CInfinityPositiveDiagonalThroatMetricPair where
  plusMagnitude : Fin 4 → ThroatScalar period hPeriod
  minusMagnitude : Fin 4 → ThroatScalar period hPeriod
  plus_pos : ∀ point i, 0 < plusMagnitude i point
  minus_pos : ∀ point i, 0 < minusMagnitude i point

@[ext]
theorem CInfinityPositiveDiagonalThroatMetricPair.ext
    {first second :
      CInfinityPositiveDiagonalThroatMetricPair period hPeriod}
    (hPlus : first.plusMagnitude = second.plusMagnitude)
    (hMinus : first.minusMagnitude = second.minusMagnitude) :
    first = second := by
  cases first
  cases second
  cases hPlus
  cases hMinus
  rfl

private def smoothCoefficientThroatCoordinate
    (field : SmoothQuotientField period hPeriod Coefficients4)
    (i : Fin 4) : ThroatScalar period hPeriod :=
  ⟨fun point =>
      field (fixedThroatQuotientInclusion period hPeriod point) i,
    (((contMDiff_pi_space.mp field.contMDiff_toFun) i).comp
      ((fixedThroatQuotientInclusion_contMDiff period hPeriod).of_le
        (by simp))).of_le (by simp)⟩

/-- Canonical restriction of the existing global positive metric pair to the
fixed throat. -/
def positiveDiagonalMetricThroatTrace
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    CInfinityPositiveDiagonalThroatMetricPair period hPeriod where
  plusMagnitude := fun i =>
    smoothCoefficientThroatCoordinate period hPeriod metrics.plusMagnitude i
  minusMagnitude := fun i =>
    smoothCoefficientThroatCoordinate period hPeriod metrics.minusMagnitude i
  plus_pos := fun point i =>
    metrics.plus_pos (fixedThroatQuotientInclusion period hPeriod point) i
  minus_pos := fun point i =>
    metrics.minus_pos (fixedThroatQuotientInclusion period hPeriod point) i

/-- Coordinate selector for the two positive metric sheets. -/
def positiveThroatMetricMagnitude
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (coordinate : PositiveMetricCoordinate) : ThroatScalar period hPeriod :=
  if coordinate.1 = 0 then
    metrics.plusMagnitude coordinate.2
  else
    metrics.minusMagnitude coordinate.2

theorem positiveThroatMetricMagnitude_pos
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (coordinate : PositiveMetricCoordinate)
    (point : EffectiveThroat period hPeriod) :
    0 < positiveThroatMetricMagnitude period hPeriod metrics coordinate point := by
  simp only [positiveThroatMetricMagnitude]
  split_ifs
  · exact metrics.plus_pos point coordinate.2
  · exact metrics.minus_pos point coordinate.2

/-- Global logarithmic coordinate on the positive cone. -/
def positiveThroatMetricLogCoordinate
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (coordinate : PositiveMetricCoordinate) : ThroatScalar period hPeriod :=
  ⟨fun point =>
      Real.log
        (positiveThroatMetricMagnitude period hPeriod metrics coordinate point),
    by
      intro point
      have hSmooth :
          ContMDiffAt throatCoverModelWithCorners 𝓘(Real, Real) ∞
            (positiveThroatMetricMagnitude period hPeriod metrics coordinate)
            point :=
        (positiveThroatMetricMagnitude period hPeriod metrics coordinate)
          |>.contMDiff.contMDiffAt
      exact
        (Real.contDiffAt_log.2
          (positiveThroatMetricMagnitude_pos period hPeriod metrics coordinate
            point).ne').contMDiffAt.comp point
          hSmooth⟩

/-- Pointwise exponential of a smooth throat scalar. -/
def throatScalarExp (scalar : ThroatScalar period hPeriod) :
    ThroatScalar period hPeriod :=
  ⟨fun point => Real.exp (scalar point),
    Real.contDiff_exp.contMDiff.comp scalar.contMDiff⟩

/-- Multiplicative chart curve through a positive metric.  It is defined for
every smooth logarithmic direction and every real parameter. -/
def positiveThroatMetricExponentiate
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (direction : PositiveMetricCoordinate → ThroatScalar period hPeriod)
    (time : Real) :
    CInfinityPositiveDiagonalThroatMetricPair period hPeriod where
  plusMagnitude := fun i =>
    metrics.plusMagnitude i *
      throatScalarExp period hPeriod (time • direction (0, i))
  minusMagnitude := fun i =>
    metrics.minusMagnitude i *
      throatScalarExp period hPeriod (time • direction (1, i))
  plus_pos := fun point i =>
    mul_pos (metrics.plus_pos point i) (Real.exp_pos _)
  minus_pos := fun point i =>
    mul_pos (metrics.minus_pos point i) (Real.exp_pos _)

@[simp]
theorem positiveThroatMetricExponentiate_zero
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (direction : PositiveMetricCoordinate → ThroatScalar period hPeriod) :
    positiveThroatMetricExponentiate period hPeriod metrics direction 0 =
      metrics := by
  apply CInfinityPositiveDiagonalThroatMetricPair.ext
  · funext i
    apply ContMDiffMap.ext
    intro point
    simp [positiveThroatMetricExponentiate, throatScalarExp]
  · funext i
    apply ContMDiffMap.ext
    intro point
    simp [positiveThroatMetricExponentiate, throatScalarExp]

/-- Exact affine law in the plus logarithmic chart.  In particular the
chosen direction is the infinitesimal logarithmic variation. -/
theorem positiveThroatMetricExponentiate_plus_log
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (direction : PositiveMetricCoordinate → ThroatScalar period hPeriod)
    (time : Real) (i : Fin 4) (point : EffectiveThroat period hPeriod) :
    Real.log
        ((positiveThroatMetricExponentiate period hPeriod metrics direction time).plusMagnitude
          i point) =
      Real.log (metrics.plusMagnitude i point) +
        time * direction (0, i) point := by
  change Real.log
      (metrics.plusMagnitude i point *
        Real.exp (time * direction (0, i) point)) = _
  rw [Real.log_mul (metrics.plus_pos point i).ne'
    (Real.exp_ne_zero _), Real.log_exp]

/-- Exact affine law in the minus logarithmic chart. -/
theorem positiveThroatMetricExponentiate_minus_log
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (direction : PositiveMetricCoordinate → ThroatScalar period hPeriod)
    (time : Real) (i : Fin 4) (point : EffectiveThroat period hPeriod) :
    Real.log
        ((positiveThroatMetricExponentiate period hPeriod metrics direction time).minusMagnitude
          i point) =
      Real.log (metrics.minusMagnitude i point) +
        time * direction (1, i) point := by
  change Real.log
      (metrics.minusMagnitude i point *
        Real.exp (time * direction (1, i) point)) = _
  rw [Real.log_mul (metrics.minus_pos point i).ne'
    (Real.exp_ne_zero _), Real.log_exp]

/-- The logarithmic direction gives the actual plus-magnitude derivative at
the origin of the positive chart curve. -/
theorem positiveThroatMetricExponentiate_plus_hasDerivAt
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (direction : PositiveMetricCoordinate → ThroatScalar period hPeriod)
    (i : Fin 4) (point : EffectiveThroat period hPeriod) :
    HasDerivAt
        (fun time =>
          (positiveThroatMetricExponentiate period hPeriod metrics direction time)
            |>.plusMagnitude i point)
        (metrics.plusMagnitude i point * direction (0, i) point) 0 := by
  let velocity := direction (0, i) point
  have hInner : HasDerivAt (fun time : Real => time * velocity) velocity 0 :=
    hasDerivAt_mul_const velocity
  simpa [positiveThroatMetricExponentiate, throatScalarExp, velocity] using
    hInner.exp.const_mul (metrics.plusMagnitude i point)

/-- The logarithmic direction gives the actual minus-magnitude derivative at
the origin of the positive chart curve. -/
theorem positiveThroatMetricExponentiate_minus_hasDerivAt
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (direction : PositiveMetricCoordinate → ThroatScalar period hPeriod)
    (i : Fin 4) (point : EffectiveThroat period hPeriod) :
    HasDerivAt
        (fun time =>
          (positiveThroatMetricExponentiate period hPeriod metrics direction time)
            |>.minusMagnitude i point)
        (metrics.minusMagnitude i point * direction (1, i) point) 0 := by
  let velocity := direction (1, i) point
  have hInner : HasDerivAt (fun time : Real => time * velocity) velocity 0 :=
    hasDerivAt_mul_const velocity
  simpa [positiveThroatMetricExponentiate, throatScalarExp, velocity] using
    hInner.exp.const_mul (metrics.minusMagnitude i point)

/-- Explicit infinitesimal rotation action on all eight logarithmic metric
coordinates. -/
def positiveThroatMetricAxisLogAction
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (axis : Fin 3) :
    PositiveMetricCoordinate → ThroatScalar period hPeriod :=
  fun coordinate =>
    throatScalarLieDerivative period hPeriod
      (throatSpatialRotationGhost period hPeriod axis)
      (positiveThroatMetricLogCoordinate period hPeriod metrics coordinate)

/-- The same infinitesimal action in the original positive magnitude chart:
`delta m = m * L_X(log m)`. -/
def positiveThroatMetricAxisMagnitudeAction
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (axis : Fin 3) :
    PositiveMetricCoordinate → ThroatScalar period hPeriod :=
  fun coordinate =>
    positiveThroatMetricMagnitude period hPeriod metrics coordinate *
      positiveThroatMetricAxisLogAction period hPeriod metrics axis coordinate

/-- The multiplicative curve integrating one axis action never leaves the
strictly-positive metric domain. -/
def positiveThroatMetricAxisCurve
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (axis : Fin 3) (time : Real) :
    CInfinityPositiveDiagonalThroatMetricPair period hPeriod :=
  positiveThroatMetricExponentiate period hPeriod metrics
    (positiveThroatMetricAxisLogAction period hPeriod metrics axis) time

theorem positiveThroatMetricAxisCurve_plus_pos
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (axis : Fin 3) (time : Real)
    (point : EffectiveThroat period hPeriod) (i : Fin 4) :
    0 < (positiveThroatMetricAxisCurve period hPeriod metrics axis time).plusMagnitude
      i point :=
  (positiveThroatMetricAxisCurve period hPeriod metrics axis time).plus_pos
    point i

theorem positiveThroatMetricAxisCurve_minus_pos
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (axis : Fin 3) (time : Real)
    (point : EffectiveThroat period hPeriod) (i : Fin 4) :
    0 < (positiveThroatMetricAxisCurve period hPeriod metrics axis time).minusMagnitude
      i point :=
  (positiveThroatMetricAxisCurve period hPeriod metrics axis time).minus_pos
    point i

theorem positiveThroatMetricAxisCurve_plus_hasDerivAt
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (axis : Fin 3) (point : EffectiveThroat period hPeriod) (i : Fin 4) :
    HasDerivAt
        (fun time =>
          (positiveThroatMetricAxisCurve period hPeriod metrics axis time)
            |>.plusMagnitude i point)
        (positiveThroatMetricAxisMagnitudeAction period hPeriod metrics axis
          (0, i) point) 0 := by
  simpa [positiveThroatMetricAxisCurve,
    positiveThroatMetricAxisMagnitudeAction,
    positiveThroatMetricMagnitude] using
      positiveThroatMetricExponentiate_plus_hasDerivAt period hPeriod metrics
        (positiveThroatMetricAxisLogAction period hPeriod metrics axis) i point

theorem positiveThroatMetricAxisCurve_minus_hasDerivAt
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod)
    (axis : Fin 3) (point : EffectiveThroat period hPeriod) (i : Fin 4) :
    HasDerivAt
        (fun time =>
          (positiveThroatMetricAxisCurve period hPeriod metrics axis time)
            |>.minusMagnitude i point)
        (positiveThroatMetricAxisMagnitudeAction period hPeriod metrics axis
          (1, i) point) 0 := by
  simpa [positiveThroatMetricAxisCurve,
    positiveThroatMetricAxisMagnitudeAction,
    positiveThroatMetricMagnitude] using
      positiveThroatMetricExponentiate_minus_hasDerivAt period hPeriod metrics
        (positiveThroatMetricAxisLogAction period hPeriod metrics axis) i point

/-! ## Componentwise corrected BRST algebra -/

abbrev PositiveMetricThroatBRSTSector :=
  PositiveMetricCoordinate → ThroatTotal period hPeriod

/-- Even embedding of a positive metric through its global logarithmic
coordinates. -/
def evenPositiveThroatMetricLogFields
    (metrics : CInfinityPositiveDiagonalThroatMetricPair period hPeriod) :
    PositiveMetricThroatBRSTSector period hPeriod :=
  fun coordinate => (1 : Coefficient) ⊗ₜ[Real]
    positiveThroatMetricLogCoordinate period hPeriod metrics coordinate

/-- The unconditional corrected throat BRST differential on all eight metric
logarithms. -/
def positiveMetricThroatBRST :
    PositiveMetricThroatBRSTSector period hPeriod →ₗ[Real]
      PositiveMetricThroatBRSTSector period hPeriod :=
  LinearMap.pi fun coordinate =>
    (throatCorrectedCombinedLinear period hPeriod).comp
      (LinearMap.proj coordinate)

@[simp]
theorem positiveMetricThroatBRST_apply
    (fields : PositiveMetricThroatBRSTSector period hPeriod)
    (coordinate : PositiveMetricCoordinate) :
    positiveMetricThroatBRST period hPeriod fields coordinate =
      throatCorrectedCombinedLinear period hPeriod (fields coordinate) :=
  rfl

/-- Componentwise grade involution. -/
def positiveMetricThroatParity
    (fields : PositiveMetricThroatBRSTSector period hPeriod) :
    PositiveMetricThroatBRSTSector period hPeriod :=
  fun coordinate =>
    throatExteriorScalarParity period hPeriod (fields coordinate)

theorem positiveMetricThroatParity_neg
    (fields : PositiveMetricThroatBRSTSector period hPeriod) :
    positiveMetricThroatParity period hPeriod (-fields) =
      -positiveMetricThroatParity period hPeriod fields := by
  funext coordinate
  exact map_neg (throatExteriorScalarParity period hPeriod)
    (fields coordinate)

theorem positiveMetricThroatParity_involutive
    (fields : PositiveMetricThroatBRSTSector period hPeriod) :
    positiveMetricThroatParity period hPeriod
        (positiveMetricThroatParity period hPeriod fields) = fields := by
  funext coordinate
  exact throatExteriorScalarParity_involutive period hPeriod
    (fields coordinate)

theorem positiveMetricThroatBRST_parity_odd
    (fields : PositiveMetricThroatBRSTSector period hPeriod) :
    positiveMetricThroatParity period hPeriod
        (positiveMetricThroatBRST period hPeriod fields) =
      -positiveMetricThroatBRST period hPeriod
        (positiveMetricThroatParity period hPeriod fields) := by
  funext coordinate
  exact throatCorrectedCombinedLinear_parity_odd period hPeriod
    (fields coordinate)

theorem positiveMetricThroatBRST_leibniz
    (first second : PositiveMetricThroatBRSTSector period hPeriod) :
    positiveMetricThroatBRST period hPeriod (first * second) =
      positiveMetricThroatBRST period hPeriod first * second +
        positiveMetricThroatParity period hPeriod first *
          positiveMetricThroatBRST period hPeriod second := by
  funext coordinate
  exact throatCorrectedCombinedLinear_leibniz period hPeriod
    (first coordinate) (second coordinate)

theorem positiveMetricThroatBRST_square_zero
    (fields : PositiveMetricThroatBRSTSector period hPeriod) :
    positiveMetricThroatBRST period hPeriod
        (positiveMetricThroatBRST period hPeriod fields) = 0 := by
  funext coordinate
  exact throatCorrectedCombinedLinear_square_zero period hPeriod
    (fields coordinate)

/-- Existing LL blocks enlarged by the positive metric trace. -/
abbrev LLThroatWithPositiveMetricBRST :=
  PositiveMetricThroatBRSTSector period hPeriod ×
    LLThroatLinearBRST period hPeriod

def unconditionalCorrectedLLThroatWithPositiveMetricBRST :
    LLThroatWithPositiveMetricBRST period hPeriod →ₗ[Real]
      LLThroatWithPositiveMetricBRST period hPeriod :=
  (positiveMetricThroatBRST period hPeriod).prodMap
    (unconditionalCorrectedLLThroatRotationBRST period hPeriod)

theorem unconditionalCorrectedLLThroatWithPositiveMetricBRST_square_zero
    (fields : LLThroatWithPositiveMetricBRST period hPeriod) :
    unconditionalCorrectedLLThroatWithPositiveMetricBRST period hPeriod
        (unconditionalCorrectedLLThroatWithPositiveMetricBRST
          period hPeriod fields) = 0 := by
  apply Prod.ext
  · exact positiveMetricThroatBRST_square_zero period hPeriod fields.1
  · exact unconditionalCorrectedLLThroatRotationBRST_square_zero
      period hPeriod fields.2

/-- Canonical embedding of all current throat data, including the positive
metric traces, into the enlarged unconditional BRST complex. -/
def independentLLThroatWithPositiveMetricBRSTFields
    (fields : IndependentFields period hPeriod) :
    LLThroatWithPositiveMetricBRST period hPeriod :=
  (evenPositiveThroatMetricLogFields period hPeriod
      (positiveDiagonalMetricThroatTrace period hPeriod fields.metrics),
    independentLLThroatLinearBRSTFields period hPeriod fields)

theorem independentLLThroatWithPositiveMetricBRSTFields_square_zero
    (fields : IndependentFields period hPeriod) :
    unconditionalCorrectedLLThroatWithPositiveMetricBRST period hPeriod
        (unconditionalCorrectedLLThroatWithPositiveMetricBRST period hPeriod
          (independentLLThroatWithPositiveMetricBRSTFields
            period hPeriod fields)) = 0 :=
  unconditionalCorrectedLLThroatWithPositiveMetricBRST_square_zero
    period hPeriod _

/-! ## First finite-coordinate antifield extension -/

/-- A parity-shifted coordinate antifield for each positive metric logarithm.
The first factor is the metric field and the second its antifield copy. -/
abbrev PositiveMetricFirstBVDoublet :=
  PositiveMetricThroatBRSTSector period hPeriod ×
    PositiveMetricThroatBRSTSector period hPeriod

/-- Shifted parity: ordinary parity on fields and its negative on
antifields. -/
def positiveMetricFirstBVParity
    (fields : PositiveMetricFirstBVDoublet period hPeriod) :
    PositiveMetricFirstBVDoublet period hPeriod :=
  (positiveMetricThroatParity period hPeriod fields.1,
    -positiveMetricThroatParity period hPeriod fields.2)

/-- BRST differential on the first field/antifield doublet.  The transpose
sign is the finite-coordinate BV sign. -/
def positiveMetricFirstBVBRST :
    PositiveMetricFirstBVDoublet period hPeriod →ₗ[Real]
      PositiveMetricFirstBVDoublet period hPeriod :=
  (positiveMetricThroatBRST period hPeriod).prodMap
    (-positiveMetricThroatBRST period hPeriod)

@[simp]
theorem positiveMetricFirstBVParity_fst
    (fields : PositiveMetricFirstBVDoublet period hPeriod) :
    (positiveMetricFirstBVParity period hPeriod fields).1 =
      positiveMetricThroatParity period hPeriod fields.1 :=
  rfl

@[simp]
theorem positiveMetricFirstBVParity_snd
    (fields : PositiveMetricFirstBVDoublet period hPeriod) :
    (positiveMetricFirstBVParity period hPeriod fields).2 =
      -positiveMetricThroatParity period hPeriod fields.2 :=
  rfl

@[simp]
theorem positiveMetricFirstBVBRST_fst
    (fields : PositiveMetricFirstBVDoublet period hPeriod) :
    (positiveMetricFirstBVBRST period hPeriod fields).1 =
      positiveMetricThroatBRST period hPeriod fields.1 :=
  rfl

@[simp]
theorem positiveMetricFirstBVBRST_snd
    (fields : PositiveMetricFirstBVDoublet period hPeriod) :
    (positiveMetricFirstBVBRST period hPeriod fields).2 =
      -positiveMetricThroatBRST period hPeriod fields.2 :=
  rfl

theorem positiveMetricFirstBVParity_involutive
    (fields : PositiveMetricFirstBVDoublet period hPeriod) :
    positiveMetricFirstBVParity period hPeriod
        (positiveMetricFirstBVParity period hPeriod fields) = fields := by
  apply Prod.ext
  · exact positiveMetricThroatParity_involutive period hPeriod fields.1
  · funext coordinate
    change -throatExteriorScalarParity period hPeriod
        (-throatExteriorScalarParity period hPeriod (fields.2 coordinate)) =
      fields.2 coordinate
    rw [map_neg, neg_neg]
    exact throatExteriorScalarParity_involutive period hPeriod
      (fields.2 coordinate)

theorem positiveMetricFirstBVBRST_parity_odd
    (fields : PositiveMetricFirstBVDoublet period hPeriod) :
    positiveMetricFirstBVParity period hPeriod
        (positiveMetricFirstBVBRST period hPeriod fields) =
      -positiveMetricFirstBVBRST period hPeriod
        (positiveMetricFirstBVParity period hPeriod fields) := by
  apply Prod.ext
  · exact positiveMetricThroatBRST_parity_odd
      period hPeriod fields.1
  · rw [positiveMetricFirstBVParity_snd,
      positiveMetricFirstBVBRST_snd,
      positiveMetricThroatParity_neg, neg_neg, Prod.snd_neg,
      positiveMetricFirstBVBRST_snd,
      positiveMetricFirstBVParity_snd, map_neg, neg_neg]
    exact positiveMetricThroatBRST_parity_odd period hPeriod fields.2

theorem positiveMetricFirstBVBRST_square_zero
    (fields : PositiveMetricFirstBVDoublet period hPeriod) :
    positiveMetricFirstBVBRST period hPeriod
        (positiveMetricFirstBVBRST period hPeriod fields) = 0 := by
  apply Prod.ext
  · exact positiveMetricThroatBRST_square_zero period hPeriod fields.1
  · rw [positiveMetricFirstBVBRST_snd,
      positiveMetricFirstBVBRST_snd, map_neg, neg_neg]
    exact positiveMetricThroatBRST_square_zero period hPeriod fields.2

/-- Canonical finite-coordinate field/antifield evaluation. -/
def positiveMetricCanonicalBVPairing
    (antifield field : PositiveMetricThroatBRSTSector period hPeriod) :
    ThroatTotal period hPeriod :=
  ∑ coordinate : PositiveMetricCoordinate,
    antifield coordinate * field coordinate

theorem positiveMetricCanonicalBVPairing_add_field
    (antifield first second :
      PositiveMetricThroatBRSTSector period hPeriod) :
    positiveMetricCanonicalBVPairing period hPeriod antifield
        (first + second) =
      positiveMetricCanonicalBVPairing period hPeriod antifield first +
        positiveMetricCanonicalBVPairing period hPeriod antifield second := by
  simp only [positiveMetricCanonicalBVPairing, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem positiveMetricCanonicalBVPairing_add_antifield
    (first second field : PositiveMetricThroatBRSTSector period hPeriod) :
    positiveMetricCanonicalBVPairing period hPeriod (first + second) field =
      positiveMetricCanonicalBVPairing period hPeriod first field +
        positiveMetricCanonicalBVPairing period hPeriod second field := by
  simp only [positiveMetricCanonicalBVPairing, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

end

end P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D
end JanusFormal
