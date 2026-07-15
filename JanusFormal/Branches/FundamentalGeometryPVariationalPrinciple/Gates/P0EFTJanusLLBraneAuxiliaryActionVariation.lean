import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.FinCases
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitBoundaryDensityLocalVariations

/-!
Pointwise auxiliary-field variation for a finite `2 + 1` dimensional
lightlike-brane model.

The independent fields are a symmetric auxiliary inverse metric `gammaInv`,
a symmetric induced metric, and a non-Riemannian measure density `Phi`.  The
gauge sector is the explicit two-form with `F_12 = flux`, `F_21 = -flux`; its
quadratic scalar is contracted with `gammaInv`.  We choose the smooth linear
law `L(F2) = gaugeCoupling * F2`.

The affine directional derivatives in `gammaInv`, `Phi`, and the gauge flux
are proved as actual `HasDerivAt` statements.  Auxiliary-metric stationarity
gives the algebraic stress/Virasoro constraint.  Its gauge stress has the
explicit nonzero kernel direction `e_0`, so the induced metric is degenerate
on the lightlike branch.

This is a finite pointwise model.  It supplies no auxiliary-scalar formula for
`Phi`, worldvolume PDE, determinant measure, integration, or throat solution.
-/

namespace JanusFormal
namespace P0EFTJanusLLBraneAuxiliaryActionVariation

set_option autoImplicit false

noncomputable section

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusExplicitBoundaryDensityLocalVariations

abbrev Matrix3 := P0EFTJanusExplicitBoundaryDensityLedger.Matrix3

def timeIndex : Fin 3 := 0

def spaceIndexOne : Fin 3 := 1

def spaceIndexTwo : Fin 3 := 2

/-- Gauge-invariant field-strength representative with one magnetic
component.  No gauge potential is introduced. -/
def magneticGaugeTwoForm (flux : ℝ) : Matrix3 :=
  fun row column =>
    if row = spaceIndexOne ∧ column = spaceIndexTwo then flux
    else if row = spaceIndexTwo ∧ column = spaceIndexOne then -flux
    else 0

theorem magneticGaugeTwoForm_transpose
    (flux : ℝ) :
    (magneticGaugeTwoForm flux).transpose = -magneticGaugeTwoForm flux := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [magneticGaugeTwoForm, Matrix.transpose_apply,
      spaceIndexOne, spaceIndexTwo]

/-- Finite contraction
`F2 = gamma^{ac} gamma^{bd} F_ab F_cd`. -/
def gaugeInvariantF2 (gammaInv : Matrix3) (flux : ℝ) : ℝ :=
  ∑ first : Fin 3, ∑ second : Fin 3,
    ∑ third : Fin 3, ∑ fourth : Fin 3,
      gammaInv first third * gammaInv second fourth *
        magneticGaugeTwoForm flux first second *
          magneticGaugeTwoForm flux third fourth

theorem gaugeInvariantF2_eq_minor
    (gammaInv : Matrix3) (flux : ℝ) :
    gaugeInvariantF2 gammaInv flux =
      2 * flux ^ 2 *
        (gammaInv spaceIndexOne spaceIndexOne *
            gammaInv spaceIndexTwo spaceIndexTwo -
          gammaInv spaceIndexOne spaceIndexTwo *
            gammaInv spaceIndexTwo spaceIndexOne) := by
  simp [gaugeInvariantF2, magneticGaugeTwoForm, Fin.sum_univ_succ,
    spaceIndexOne, spaceIndexTwo]
  ring

/-- Entrywise contraction used for variations of the inverse metric. -/
def matrixContraction (left right : Matrix3) : ℝ :=
  ∑ row : Fin 3, ∑ column : Fin 3, left row column * right row column

structure LLBraneAuxiliaryPointData where
  gammaInv : Matrix3
  inducedMetric : Matrix3
  Phi : ℝ
  gaugeFlux : ℝ
  gaugeCoupling : ℝ
  measureConstant : ℝ
  gammaInvSymmetric : gammaInv.transpose = gammaInv
  inducedMetricSymmetric : inducedMetric.transpose = inducedMetric

/-- Local bracket before multiplication by the non-Riemannian measure. -/
def llLocalLagrangian (data : LLBraneAuxiliaryPointData) : ℝ :=
  -(1 / 2 : ℝ) * matrixContraction data.gammaInv data.inducedMetric +
    data.gaugeCoupling * gaugeInvariantF2 data.gammaInv data.gaugeFlux

/-- The concrete LL data inhabit the independent-measure worldvolume slot
already declared by the density ledger. -/
def toWorldvolumePointData
    (data : LLBraneAuxiliaryPointData) : WorldvolumePointData where
  inducedMetric := data.inducedMetric
  measureDensity := data.Phi
  tension := data.measureConstant
  localLagrangian := llLocalLagrangian data
  inducedMetricSymmetric := data.inducedMetricSymmetric

def llAuxiliaryDensity (data : LLBraneAuxiliaryPointData) : ℝ :=
  worldvolumeDensity (toWorldvolumePointData data)

theorem llAuxiliaryDensity_eq
    (data : LLBraneAuxiliaryPointData) :
    llAuxiliaryDensity data =
      data.Phi * (llLocalLagrangian data - data.measureConstant) :=
  rfl

def gammaInvCurve
    (gammaInv variation : Matrix3) (t : ℝ) : Matrix3 :=
  gammaInv + t • variation

/-- Directional variation of the explicit `F2` polynomial. -/
def gaugeInvariantF2GammaVariation
    (gammaInv variation : Matrix3) (flux : ℝ) : ℝ :=
  2 * flux ^ 2 *
    (variation spaceIndexOne spaceIndexOne *
          gammaInv spaceIndexTwo spaceIndexTwo +
      gammaInv spaceIndexOne spaceIndexOne *
          variation spaceIndexTwo spaceIndexTwo -
      variation spaceIndexOne spaceIndexTwo *
          gammaInv spaceIndexTwo spaceIndexOne -
      gammaInv spaceIndexOne spaceIndexTwo *
          variation spaceIndexTwo spaceIndexOne)

theorem gaugeInvariantF2_gammaInvCurve_quadratic
    (gammaInv variation : Matrix3) (flux t : ℝ) :
    gaugeInvariantF2 (gammaInvCurve gammaInv variation t) flux =
      gaugeInvariantF2 gammaInv flux +
        t * gaugeInvariantF2GammaVariation gammaInv variation flux +
        t ^ 2 * gaugeInvariantF2 variation flux := by
  rw [gaugeInvariantF2_eq_minor, gaugeInvariantF2_eq_minor,
    gaugeInvariantF2_eq_minor]
  simp [gammaInvCurve, gaugeInvariantF2GammaVariation,
    spaceIndexOne, spaceIndexTwo]
  ring

theorem quadraticScalar_hasDerivAt
    (base linear quadratic : ℝ) :
    HasDerivAt
      (fun t : ℝ => base + t * linear + t ^ 2 * quadratic) linear 0 := by
  have hAffine := affineScalar_hasDerivAt base linear
  have hSquare : HasDerivAt (fun t : ℝ => t * t) 0 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))
    exact h.congr_deriv (by norm_num)
  have hQuadratic : HasDerivAt
      (fun t : ℝ => t * t * quadratic) 0 0 := by
    have h := hSquare.mul_const quadratic
    exact h.congr_deriv (by ring)
  have hTotal := hAffine.add hQuadratic
  have hCorrect := hTotal.congr_deriv (by ring)
  exact hCorrect.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      simp only [Pi.add_apply]
      ring)

theorem gaugeInvariantF2_gammaInvCurve_hasDerivAt
    (gammaInv variation : Matrix3) (flux : ℝ) :
    HasDerivAt
      (fun t : ℝ => gaugeInvariantF2
        (gammaInvCurve gammaInv variation t) flux)
      (gaugeInvariantF2GammaVariation gammaInv variation flux) 0 := by
  have hDerivative := quadraticScalar_hasDerivAt
    (gaugeInvariantF2 gammaInv flux)
    (gaugeInvariantF2GammaVariation gammaInv variation flux)
    (gaugeInvariantF2 variation flux)
  exact hDerivative.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      gaugeInvariantF2_gammaInvCurve_quadratic
        gammaInv variation flux t)

/-- Gamma variation of the local bracket. -/
def llLocalGammaVariation
    (data : LLBraneAuxiliaryPointData) (variation : Matrix3) : ℝ :=
  -(1 / 2 : ℝ) * matrixContraction variation data.inducedMetric +
    data.gaugeCoupling *
      gaugeInvariantF2GammaVariation data.gammaInv variation data.gaugeFlux

def llAuxiliaryDensityGammaCurve
    (data : LLBraneAuxiliaryPointData) (variation : Matrix3) (t : ℝ) : ℝ :=
  data.Phi *
    (-(1 / 2 : ℝ) *
        matrixContraction
          (gammaInvCurve data.gammaInv variation t) data.inducedMetric +
      data.gaugeCoupling *
        gaugeInvariantF2
          (gammaInvCurve data.gammaInv variation t) data.gaugeFlux -
      data.measureConstant)

def llAuxiliaryDensityGammaVariation
    (data : LLBraneAuxiliaryPointData) (variation : Matrix3) : ℝ :=
  data.Phi * llLocalGammaVariation data variation

theorem llAuxiliaryDensityGammaCurve_quadratic
    (data : LLBraneAuxiliaryPointData) (variation : Matrix3) (t : ℝ) :
    llAuxiliaryDensityGammaCurve data variation t =
      llAuxiliaryDensity data +
        t * llAuxiliaryDensityGammaVariation data variation +
        t ^ 2 *
          (data.Phi * data.gaugeCoupling *
            gaugeInvariantF2 variation data.gaugeFlux) := by
  rw [llAuxiliaryDensity_eq]
  unfold llAuxiliaryDensityGammaCurve
  rw [gaugeInvariantF2_gammaInvCurve_quadratic]
  simp [llAuxiliaryDensityGammaVariation,
    llLocalGammaVariation, llLocalLagrangian, matrixContraction,
    gammaInvCurve, Fin.sum_univ_succ]
  ring

theorem llAuxiliaryDensityGammaCurve_hasDerivAt
    (data : LLBraneAuxiliaryPointData) (variation : Matrix3) :
    HasDerivAt (llAuxiliaryDensityGammaCurve data variation)
      (llAuxiliaryDensityGammaVariation data variation) 0 := by
  have hDerivative := quadraticScalar_hasDerivAt
    (llAuxiliaryDensity data)
    (llAuxiliaryDensityGammaVariation data variation)
    (data.Phi * data.gaugeCoupling *
      gaugeInvariantF2 variation data.gaugeFlux)
  exact hDerivative.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      llAuxiliaryDensityGammaCurve_quadratic data variation t)

def llAuxiliaryDensityPhiCurve
    (data : LLBraneAuxiliaryPointData) (variation t : ℝ) : ℝ :=
  (data.Phi + t * variation) *
    (llLocalLagrangian data - data.measureConstant)

def llAuxiliaryDensityPhiVariation
    (data : LLBraneAuxiliaryPointData) (variation : ℝ) : ℝ :=
  variation * (llLocalLagrangian data - data.measureConstant)

theorem llAuxiliaryDensityPhiCurve_affine
    (data : LLBraneAuxiliaryPointData) (variation t : ℝ) :
    llAuxiliaryDensityPhiCurve data variation t =
      llAuxiliaryDensity data +
        t * llAuxiliaryDensityPhiVariation data variation := by
  rw [llAuxiliaryDensity_eq]
  simp [llAuxiliaryDensityPhiCurve, llAuxiliaryDensityPhiVariation]
  ring

theorem llAuxiliaryDensityPhiCurve_hasDerivAt
    (data : LLBraneAuxiliaryPointData) (variation : ℝ) :
    HasDerivAt (llAuxiliaryDensityPhiCurve data variation)
      (llAuxiliaryDensityPhiVariation data variation) 0 := by
  have hDerivative := affineScalar_hasDerivAt
    (llAuxiliaryDensity data)
    (llAuxiliaryDensityPhiVariation data variation)
  exact hDerivative.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      llAuxiliaryDensityPhiCurve_affine data variation t)

/-- Flux derivative of the explicit `F2` polynomial. -/
def gaugeInvariantF2FluxVariation
    (gammaInv : Matrix3) (flux variation : ℝ) : ℝ :=
  4 * flux * variation *
    (gammaInv spaceIndexOne spaceIndexOne *
        gammaInv spaceIndexTwo spaceIndexTwo -
      gammaInv spaceIndexOne spaceIndexTwo *
        gammaInv spaceIndexTwo spaceIndexOne)

theorem gaugeInvariantF2_fluxCurve_quadratic
    (gammaInv : Matrix3) (flux variation t : ℝ) :
    gaugeInvariantF2 gammaInv (flux + t * variation) =
      gaugeInvariantF2 gammaInv flux +
        t * gaugeInvariantF2FluxVariation gammaInv flux variation +
        t ^ 2 * gaugeInvariantF2 gammaInv variation := by
  rw [gaugeInvariantF2_eq_minor, gaugeInvariantF2_eq_minor,
    gaugeInvariantF2_eq_minor]
  unfold gaugeInvariantF2FluxVariation
  ring

theorem gaugeInvariantF2_fluxCurve_hasDerivAt
    (gammaInv : Matrix3) (flux variation : ℝ) :
    HasDerivAt
      (fun t : ℝ => gaugeInvariantF2 gammaInv (flux + t * variation))
      (gaugeInvariantF2FluxVariation gammaInv flux variation) 0 := by
  have hDerivative := quadraticScalar_hasDerivAt
    (gaugeInvariantF2 gammaInv flux)
    (gaugeInvariantF2FluxVariation gammaInv flux variation)
    (gaugeInvariantF2 gammaInv variation)
  exact hDerivative.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      gaugeInvariantF2_fluxCurve_quadratic
        gammaInv flux variation t)

def llAuxiliaryDensityFluxCurve
    (data : LLBraneAuxiliaryPointData) (variation t : ℝ) : ℝ :=
  data.Phi *
    (-(1 / 2 : ℝ) *
        matrixContraction data.gammaInv data.inducedMetric +
      data.gaugeCoupling *
        gaugeInvariantF2 data.gammaInv (data.gaugeFlux + t * variation) -
      data.measureConstant)

def llAuxiliaryDensityFluxVariation
    (data : LLBraneAuxiliaryPointData) (variation : ℝ) : ℝ :=
  data.Phi * data.gaugeCoupling *
    gaugeInvariantF2FluxVariation data.gammaInv data.gaugeFlux variation

theorem llAuxiliaryDensityFluxCurve_quadratic
    (data : LLBraneAuxiliaryPointData) (variation t : ℝ) :
    llAuxiliaryDensityFluxCurve data variation t =
      llAuxiliaryDensity data +
        t * llAuxiliaryDensityFluxVariation data variation +
        t ^ 2 *
          (data.Phi * data.gaugeCoupling *
            gaugeInvariantF2 data.gammaInv variation) := by
  rw [llAuxiliaryDensity_eq]
  unfold llAuxiliaryDensityFluxCurve
  rw [gaugeInvariantF2_fluxCurve_quadratic]
  simp [llAuxiliaryDensityFluxVariation,
    llLocalLagrangian]
  ring

theorem llAuxiliaryDensityFluxCurve_hasDerivAt
    (data : LLBraneAuxiliaryPointData) (variation : ℝ) :
    HasDerivAt (llAuxiliaryDensityFluxCurve data variation)
      (llAuxiliaryDensityFluxVariation data variation) 0 := by
  have hDerivative := quadraticScalar_hasDerivAt
    (llAuxiliaryDensity data)
    (llAuxiliaryDensityFluxVariation data variation)
    (data.Phi * data.gaugeCoupling *
      gaugeInvariantF2 data.gammaInv variation)
  exact hDerivative.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t =>
      llAuxiliaryDensityFluxCurve_quadratic data variation t)

/-- Gradient of `F2` with respect to the ambient matrix entries. -/
def gaugeF2Stress (gammaInv : Matrix3) (flux : ℝ) : Matrix3 :=
  Matrix.single spaceIndexOne spaceIndexOne
      (2 * flux ^ 2 * gammaInv spaceIndexTwo spaceIndexTwo) +
    Matrix.single spaceIndexTwo spaceIndexTwo
      (2 * flux ^ 2 * gammaInv spaceIndexOne spaceIndexOne) -
    Matrix.single spaceIndexOne spaceIndexTwo
      (2 * flux ^ 2 * gammaInv spaceIndexTwo spaceIndexOne) -
    Matrix.single spaceIndexTwo spaceIndexOne
      (2 * flux ^ 2 * gammaInv spaceIndexOne spaceIndexTwo)

theorem gaugeInvariantF2GammaVariation_eq_contraction
    (gammaInv variation : Matrix3) (flux : ℝ) :
    gaugeInvariantF2GammaVariation gammaInv variation flux =
      matrixContraction variation (gaugeF2Stress gammaInv flux) := by
  simp [gaugeInvariantF2GammaVariation, matrixContraction, gaugeF2Stress,
    Matrix.single, Fin.sum_univ_succ, spaceIndexOne,
    spaceIndexTwo]
  ring

/-- Algebraic auxiliary stress/Virasoro tensor. -/
def auxiliaryStress (data : LLBraneAuxiliaryPointData) : Matrix3 :=
  -(1 / 2 : ℝ) • data.inducedMetric +
    data.gaugeCoupling • gaugeF2Stress data.gammaInv data.gaugeFlux

theorem gaugeF2Stress_symmetric
    (gammaInv : Matrix3) (flux : ℝ)
    (hGamma : gammaInv.transpose = gammaInv) :
    (gaugeF2Stress gammaInv flux).transpose =
      gaugeF2Stress gammaInv flux := by
  have hOffDiagonal := congrFun
    (congrFun hGamma spaceIndexOne) spaceIndexTwo
  simp [Matrix.transpose_apply, spaceIndexOne, spaceIndexTwo] at hOffDiagonal
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [gaugeF2Stress, Matrix.transpose_apply, Matrix.single,
      spaceIndexOne, spaceIndexTwo, hOffDiagonal]

theorem auxiliaryStress_symmetric
    (data : LLBraneAuxiliaryPointData) :
    (auxiliaryStress data).transpose = auxiliaryStress data := by
  have hGauge := gaugeF2Stress_symmetric data.gammaInv data.gaugeFlux
    data.gammaInvSymmetric
  ext row column
  have hMetricEntry := congrFun
    (congrFun data.inducedMetricSymmetric row) column
  have hGaugeEntry := congrFun (congrFun hGauge row) column
  simp [Matrix.transpose_apply] at hMetricEntry hGaugeEntry ⊢
  simp [auxiliaryStress, hMetricEntry, hGaugeEntry]

theorem llLocalGammaVariation_eq_stressContraction
    (data : LLBraneAuxiliaryPointData) (variation : Matrix3) :
    llLocalGammaVariation data variation =
      matrixContraction variation (auxiliaryStress data) := by
  rw [llLocalGammaVariation,
    gaugeInvariantF2GammaVariation_eq_contraction]
  simp [matrixContraction, auxiliaryStress, Fin.sum_univ_succ]
  ring

theorem llAuxiliaryDensityGammaVariation_eq_stressContraction
    (data : LLBraneAuxiliaryPointData) (variation : Matrix3) :
    llAuxiliaryDensityGammaVariation data variation =
      data.Phi * matrixContraction variation (auxiliaryStress data) := by
  rw [llAuxiliaryDensityGammaVariation,
    llLocalGammaVariation_eq_stressContraction]

def GammaStationary (data : LLBraneAuxiliaryPointData) : Prop :=
  ∀ variation : Matrix3,
    variation.transpose = variation →
      llAuxiliaryDensityGammaVariation data variation = 0

def PhiStationary (data : LLBraneAuxiliaryPointData) : Prop :=
  ∀ variation : ℝ, llAuxiliaryDensityPhiVariation data variation = 0

theorem matrixContraction_single_left
    (row column : Fin 3) (matrix : Matrix3) :
    matrixContraction (Matrix.single row column 1) matrix =
      matrix row column := by
  classical
  unfold matrixContraction
  rw [Finset.sum_eq_single row]
  · rw [Finset.sum_eq_single column]
    · simp
    · intro other _ hOther
      simp [Matrix.single, Ne.symm hOther]
    · simp
  · intro other _ hOther
    simp [Matrix.single, Ne.symm hOther]
  · simp

def symmetricMatrixUnit (row column : Fin 3) : Matrix3 :=
  Matrix.single row column 1 + Matrix.single column row 1

theorem symmetricMatrixUnit_transpose
    (row column : Fin 3) :
    (symmetricMatrixUnit row column).transpose =
      symmetricMatrixUnit row column := by
  simp [symmetricMatrixUnit, add_comm]

theorem matrixContraction_add_left
    (first second matrix : Matrix3) :
    matrixContraction (first + second) matrix =
      matrixContraction first matrix + matrixContraction second matrix := by
  simp [matrixContraction, add_mul, Finset.sum_add_distrib]

theorem matrixContraction_symmetricMatrixUnit
    (row column : Fin 3) (matrix : Matrix3) :
    matrixContraction (symmetricMatrixUnit row column) matrix =
      matrix row column + matrix column row := by
  rw [symmetricMatrixUnit, matrixContraction_add_left,
    matrixContraction_single_left, matrixContraction_single_left]

/-- For nonzero non-Riemannian measure, gamma stationarity is exactly the
algebraic Virasoro constraint. -/
theorem gammaStationary_iff_auxiliaryStress_eq_zero
    (data : LLBraneAuxiliaryPointData) (hPhi : data.Phi ≠ 0) :
    GammaStationary data ↔ auxiliaryStress data = 0 := by
  constructor
  · intro hStationary
    ext row column
    have hEntry := hStationary (symmetricMatrixUnit row column)
      (symmetricMatrixUnit_transpose row column)
    rw [llAuxiliaryDensityGammaVariation_eq_stressContraction,
      matrixContraction_symmetricMatrixUnit] at hEntry
    have hSum := (mul_eq_zero.mp hEntry).resolve_left hPhi
    have hSymmetry := congrFun
      (congrFun (auxiliaryStress_symmetric data) row) column
    simp [Matrix.transpose_apply] at hSymmetry
    rw [hSymmetry] at hSum
    have hZero : auxiliaryStress data row column = 0 := by
      linarith
    simpa using hZero
  · intro hStress variation _hVariationSymmetric
    rw [llAuxiliaryDensityGammaVariation_eq_stressContraction, hStress]
    simp [matrixContraction]

theorem phiStationary_iff_measure_constraint
    (data : LLBraneAuxiliaryPointData) :
    PhiStationary data ↔
      llLocalLagrangian data - data.measureConstant = 0 := by
  constructor
  · intro hStationary
    simpa [llAuxiliaryDensityPhiVariation] using hStationary 1
  · intro hConstraint variation
    simp [llAuxiliaryDensityPhiVariation, hConstraint]

def nullGaugeDirection : Fin 3 → ℝ :=
  fun index => if index = timeIndex then 1 else 0

theorem nullGaugeDirection_ne_zero : nullGaugeDirection ≠ 0 := by
  intro hZero
  have hEntry := congrFun hZero timeIndex
  simp [nullGaugeDirection] at hEntry

theorem gaugeF2Stress_mulVec_nullGaugeDirection
    (gammaInv : Matrix3) (flux : ℝ) :
    Matrix.mulVec (gaugeF2Stress gammaInv flux) nullGaugeDirection = 0 := by
  ext row
  fin_cases row <;>
    simp [Matrix.mulVec, dotProduct, gaugeF2Stress, nullGaugeDirection,
      Matrix.single, timeIndex, spaceIndexOne,
      spaceIndexTwo]

theorem inducedMetric_eq_gaugeStress_of_auxiliaryStress_zero
    (data : LLBraneAuxiliaryPointData)
    (hStress : auxiliaryStress data = 0) :
    data.inducedMetric =
      (2 * data.gaugeCoupling) •
        gaugeF2Stress data.gammaInv data.gaugeFlux := by
  ext row column
  have hEntry := congrFun (congrFun hStress row) column
  simp [auxiliaryStress] at hEntry ⊢
  linarith

theorem inducedMetric_mulVec_nullGaugeDirection_of_auxiliaryStress_zero
    (data : LLBraneAuxiliaryPointData)
    (hStress : auxiliaryStress data = 0) :
    Matrix.mulVec data.inducedMetric nullGaugeDirection = 0 := by
  rw [inducedMetric_eq_gaugeStress_of_auxiliaryStress_zero data hStress]
  ext row
  fin_cases row <;>
    simp [Matrix.mulVec, dotProduct, gaugeF2Stress, nullGaugeDirection,
      Matrix.single, timeIndex, spaceIndexOne,
      spaceIndexTwo]

/-- Pointwise lightlike branch: nonzero measure and gauge sector, with both
auxiliary equations stationary. -/
def LightlikeAuxiliaryBranch (data : LLBraneAuxiliaryPointData) : Prop :=
  data.Phi ≠ 0 ∧ data.gaugeFlux ≠ 0 ∧ data.gaugeCoupling ≠ 0 ∧
    GammaStationary data ∧ PhiStationary data

theorem lightlikeBranch_constraints
    (data : LLBraneAuxiliaryPointData)
    (hBranch : LightlikeAuxiliaryBranch data) :
    auxiliaryStress data = 0 ∧
      llLocalLagrangian data - data.measureConstant = 0 := by
  exact ⟨(gammaStationary_iff_auxiliaryStress_eq_zero data hBranch.1).mp
      hBranch.2.2.2.1,
    (phiStationary_iff_measure_constraint data).mp hBranch.2.2.2.2⟩

/-- Explicit nonzero kernel witness for the induced metric on the branch. -/
theorem lightlikeBranch_inducedMetric_has_nonzero_kernel
    (data : LLBraneAuxiliaryPointData)
    (hBranch : LightlikeAuxiliaryBranch data) :
    nullGaugeDirection ≠ 0 ∧
      Matrix.mulVec data.inducedMetric nullGaugeDirection = 0 := by
  refine ⟨nullGaugeDirection_ne_zero, ?_⟩
  exact inducedMetric_mulVec_nullGaugeDirection_of_auxiliaryStress_zero data
    (lightlikeBranch_constraints data hBranch).1

end

end P0EFTJanusLLBraneAuxiliaryActionVariation
end JanusFormal
