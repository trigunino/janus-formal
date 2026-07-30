import Mathlib.Analysis.Normed.Operator.Compact.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D

/-!
# Continuum heat regulator for the signed SpinC matter Hessian

The physical matter Hessian already has the exact signed coefficient
`2 D + massSquared` on two sectors.  This gate reuses the complete geometric
signed mode labels, their literal multiplicities, and the positive-level D10
identification.  The undoubled zero-sphere tower is controlled by the existing
circle heat sum, while both nonzero Dirac branches are finite copies of the
already summable multiplicity-aware D10 heat spectrum.

The elementary bound
`(2 λ + m)² ≥ 2 λ² - m²`
then proves unconditional summability for every real mass coefficient and
every positive heat time.  An explicit rank-one expansion below makes the
actual completed matter heat operator nuclear and compact.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD10ContinuumHeatRegulator4D
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCModeDecomposition4D
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D
open scoped ENNReal lp

variable (period : Real) (hPeriod : period ≠ 0)

/-- Explicit coordinates of the complete signed matter spectrum: the
undoubled zero-sphere circle tower, plus two branches of every positive D10
mode. -/
abbrev PrimitiveSpinCSignedHeatCoordinate4D :=
  (NormalRootChoice × Int) ⊕
    (PrimitiveSpinCDiracBranch ×
      ProgramPD10Mode4D
        (PrimitiveSpinCSpectralData period hPeriod))

/-- Positive signed geometric modes are exactly a branch label times the
existing multiplicity-aware D10 modes. -/
def primitiveSpinCGeometricSignedPositiveHeatCoordinateEquiv :
    (NormalRootChoice × PrimitiveSpinCSignedNonzeroMode) ≃
      (PrimitiveSpinCDiracBranch ×
        ProgramPD10Mode4D
          (PrimitiveSpinCSpectralData period hPeriod)) where
  toFun mode :=
    (mode.2.branch,
      { separatedMode :=
          { sphereLevel := mode.2.level
            circleMode := mode.2.circleMode
            rootChoice := mode.1 }
        sphereMultiplicityIndex :=
          primitiveSpinCSignedNonzeroMultiplicityEquiv
            period hPeriod mode.2.branch mode.2.level
            mode.2.multiplicity })
  invFun coordinate :=
    (coordinate.2.separatedMode.rootChoice,
      { branch := coordinate.1
        level := coordinate.2.separatedMode.sphereLevel
        multiplicity :=
          (primitiveSpinCSignedNonzeroMultiplicityEquiv
            period hPeriod coordinate.1
              coordinate.2.separatedMode.sphereLevel).symm
            coordinate.2.sphereMultiplicityIndex
        circleMode := coordinate.2.separatedMode.circleMode })
  left_inv := by
    rintro ⟨choice, ⟨branch, level, multiplicity, circleMode⟩⟩
    simp
  right_inv := by
    rintro ⟨branch, ⟨⟨level, circleMode, choice⟩, multiplicity⟩⟩
    simp

/-- Exact reindexing of all signed matter labels. -/
def primitiveSpinCGeometricSignedHeatCoordinateEquiv :
    PrimitiveSpinCGeometricSignedMode ≃
      PrimitiveSpinCSignedHeatCoordinate4D period hPeriod :=
  (Equiv.prodSumDistrib
      NormalRootChoice
      PrimitiveSpinCUnsignedZeroMode
      PrimitiveSpinCSignedNonzeroMode).trans
    (Equiv.sumCongr
      ((Equiv.refl NormalRootChoice).prodCongr
        primitiveSpinCZeroProductEquiv)
      (primitiveSpinCGeometricSignedPositiveHeatCoordinateEquiv
        period hPeriod))

/-- Gaussian of the unshifted signed first-order eigenvalue. -/
def primitiveSpinCGeometricSignedBaseHeatWeight
    (time : HeatTime)
    (mode : PrimitiveSpinCGeometricSignedMode) : Real :=
  Real.exp
    (-time.1 *
      primitiveSpinCGeometricSignedEigenvalue
        period hPeriod mode ^ 2)

/-- Same Gaussian in the explicit zero/D10 coordinates. -/
def primitiveSpinCGeometricSignedCoordinateHeatWeight
    (time : HeatTime) :
    PrimitiveSpinCSignedHeatCoordinate4D period hPeriod → Real
  | .inl mode =>
      d7CircleHeatWeight
        (PrimitiveSpinCSpectralData period hPeriod)
        time mode.1 mode.2
  | .inr mode =>
      programPD10HeatWeight
        (PrimitiveSpinCSpectralData period hPeriod)
        time mode.2

theorem primitiveSpinCGeometricSignedCoordinateHeatWeight_nonnegative
    (time : HeatTime)
    (coordinate :
      PrimitiveSpinCSignedHeatCoordinate4D period hPeriod) :
    0 ≤ primitiveSpinCGeometricSignedCoordinateHeatWeight
      period hPeriod time coordinate := by
  rcases coordinate with coordinate | coordinate
  · exact (Real.exp_pos _).le
  · exact programPD10HeatWeight_nonnegative
      (PrimitiveSpinCSpectralData period hPeriod)
      time coordinate.2

theorem primitiveSpinCGeometricSignedCoordinateHeatWeight_summable
    (time : HeatTime) :
    Summable
      (primitiveSpinCGeometricSignedCoordinateHeatWeight
        period hPeriod time) := by
  apply Summable.sum
  · change Summable (fun mode : NormalRootChoice × Int =>
      d7CircleHeatWeight
        (PrimitiveSpinCSpectralData period hPeriod)
        time mode.1 mode.2)
    apply (summable_prod_of_nonneg (fun mode =>
      (Real.exp_pos _).le)).2
    constructor
    · intro choice
      exact d7CircleHeatWeight_summable
        (PrimitiveSpinCSpectralData period hPeriod)
        time choice
    · exact Summable.of_finite
  · change Summable
      (fun mode : PrimitiveSpinCDiracBranch ×
          ProgramPD10Mode4D
            (PrimitiveSpinCSpectralData period hPeriod) =>
        programPD10HeatWeight
          (PrimitiveSpinCSpectralData period hPeriod)
          time mode.2)
    apply (summable_prod_of_nonneg (fun mode =>
      programPD10HeatWeight_nonnegative
        (PrimitiveSpinCSpectralData period hPeriod)
        time mode.2)).2
    constructor
    · intro _
      exact programPD10HeatWeight_summable
        (PrimitiveSpinCSpectralData period hPeriod)
        time
    · exact Summable.of_finite

theorem primitiveSpinCGeometricSignedBaseHeatWeight_eq_coordinate
    (time : HeatTime)
    (mode : PrimitiveSpinCGeometricSignedMode) :
    primitiveSpinCGeometricSignedBaseHeatWeight
        period hPeriod time mode =
      primitiveSpinCGeometricSignedCoordinateHeatWeight
        period hPeriod time
        (primitiveSpinCGeometricSignedHeatCoordinateEquiv
          period hPeriod mode) := by
  rcases mode with ⟨choice, mode⟩
  cases mode with
  | inl zeroMode =>
      rcases zeroMode with ⟨multiplicity, circleMode⟩
      unfold primitiveSpinCGeometricSignedBaseHeatWeight
        primitiveSpinCGeometricSignedCoordinateHeatWeight
        primitiveSpinCGeometricSignedHeatCoordinateEquiv
        primitiveSpinCGeometricSignedEigenvalue
        d7CircleHeatWeight
      rfl
  | inr nonzeroMode =>
      rcases nonzeroMode with
        ⟨branch, level, multiplicity, circleMode⟩
      unfold primitiveSpinCGeometricSignedBaseHeatWeight
        primitiveSpinCGeometricSignedCoordinateHeatWeight
        primitiveSpinCGeometricSignedHeatCoordinateEquiv
        primitiveSpinCGeometricSignedPositiveHeatCoordinateEquiv
        programPD10HeatWeight
      rw [primitiveSpinCGeometricSignedEigenvalue_sq]
      change
        Real.exp (-time.1 *
          (primitiveSpinCFullSphereEigenvalueSquared (level + 1) +
            circleEigenvalue
              (PrimitiveSpinCSpectralData period hPeriod)
              choice circleMode ^ 2)) =
        Real.exp (-time.1 *
          (sphereEigenvalueSquared
              (PrimitiveSpinCSpectralData period hPeriod) level +
            circleEigenvalue
              (PrimitiveSpinCSpectralData period hPeriod)
              choice circleMode ^ 2))
      rw [primitiveSpinCFull_positiveSphereEigenvalue_agrees
        period hPeriod level]

/-- Explicit multiplicities and both signed branches still give a summable
unshifted Gaussian. -/
theorem primitiveSpinCGeometricSignedBaseHeatWeight_summable
    (time : HeatTime) :
    Summable
      (primitiveSpinCGeometricSignedBaseHeatWeight
        period hPeriod time) := by
  have hReindexed :
      Summable
        (primitiveSpinCGeometricSignedCoordinateHeatWeight
          period hPeriod time ∘
            primitiveSpinCGeometricSignedHeatCoordinateEquiv
              period hPeriod) :=
    (primitiveSpinCGeometricSignedHeatCoordinateEquiv
      period hPeriod).summable_iff.mpr
        (primitiveSpinCGeometricSignedCoordinateHeatWeight_summable
          period hPeriod time)
  exact hReindexed.congr fun mode =>
    (primitiveSpinCGeometricSignedBaseHeatWeight_eq_coordinate
      period hPeriod time mode).symm

/-- Exact two-sector matter heat weight used in the assembled physical
Hessian regulator. -/
def programPSpinCMatterHeatWeight
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) : Real :=
  Real.exp
    (-time.1 *
      (primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode.2 + massSquared) ^ 2)

theorem programPSpinCMatterHeatWeight_eq_global
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    programPSpinCMatterHeatWeight
        period hPeriod massSquared time mode =
      programPGlobalPhysicalSpectralHessianHeatWeight
        period hPeriod covector spectralData massSquared time
          (.inr (.inl mode)) :=
  rfl

theorem programPSpinCMatterHeatWeight_nonnegative
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    0 ≤ programPSpinCMatterHeatWeight
      period hPeriod massSquared time mode :=
  (Real.exp_pos _).le

theorem programPSpinCMatterHeatWeight_le_one
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    programPSpinCMatterHeatWeight
      period hPeriod massSquared time mode ≤ 1 := by
  unfold programPSpinCMatterHeatWeight
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr time.2.le) (sq_nonneg _)

/-- Positive time doubled for the Gaussian comparison. -/
def programPSpinCMatterDominatingHeatTime
    (time : HeatTime) : HeatTime :=
  ⟨2 * time.1, mul_pos (by norm_num) time.2⟩

theorem programPSpinCMatterHeatWeight_le_dominating
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    programPSpinCMatterHeatWeight
        period hPeriod massSquared time mode ≤
      Real.exp (time.1 * massSquared ^ 2) *
        primitiveSpinCGeometricSignedBaseHeatWeight
          period hPeriod
          (programPSpinCMatterDominatingHeatTime time)
          mode.2 := by
  let eigenvalue :=
    primitiveSpinCGeometricSignedEigenvalue
      period hPeriod mode.2
  have hQuadratic :
      2 * eigenvalue ^ 2 - massSquared ^ 2 ≤
        (2 * eigenvalue + massSquared) ^ 2 := by
    nlinarith [sq_nonneg (eigenvalue + massSquared)]
  have hExponent :
      -time.1 * (2 * eigenvalue + massSquared) ^ 2 ≤
        time.1 * massSquared ^ 2 -
          (2 * time.1) * eigenvalue ^ 2 := by
    nlinarith [time.2]
  unfold programPSpinCMatterHeatWeight
    primitiveSpinCGeometricSignedKineticHessianWeight
    primitiveSpinCGeometricSignedBaseHeatWeight
    programPSpinCMatterDominatingHeatTime
  change
    Real.exp (-time.1 * (2 * eigenvalue + massSquared) ^ 2) ≤
      Real.exp (time.1 * massSquared ^ 2) *
        Real.exp (-(2 * time.1) * eigenvalue ^ 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The full two-sector, massive signed SpinC Gaussian is summable without
additional spectral hypotheses. -/
theorem programPSpinCMatterHeatWeight_summable
    (massSquared : Real)
    (time : HeatTime) :
    Summable
      (programPSpinCMatterHeatWeight
        period hPeriod massSquared time) := by
  have hBase :
      Summable
        (primitiveSpinCGeometricSignedBaseHeatWeight
          period hPeriod
          (programPSpinCMatterDominatingHeatTime time)) :=
    primitiveSpinCGeometricSignedBaseHeatWeight_summable
      period hPeriod
      (programPSpinCMatterDominatingHeatTime time)
  have hOneSector :
      Summable (fun mode : PrimitiveSpinCGeometricSignedMode =>
        programPSpinCMatterHeatWeight
          period hPeriod massSquared time
          (Sector.plus, mode)) := by
    apply
      ((hBase.mul_left
        (Real.exp (time.1 * massSquared ^ 2))).of_nonneg_of_le
          (fun _ => programPSpinCMatterHeatWeight_nonnegative
            period hPeriod massSquared time _))
    intro mode
    exact programPSpinCMatterHeatWeight_le_dominating
      period hPeriod massSquared time (Sector.plus, mode)
  apply (summable_prod_of_nonneg
    (programPSpinCMatterHeatWeight_nonnegative
      period hPeriod massSquared time)).2
  constructor
  · intro sector
    exact hOneSector.congr fun mode => by
      cases sector <;> rfl
  · exact Summable.of_finite

/-- Completed complex coefficient space of the exact two-sector signed
matter block. -/
abbrev ProgramPSpinCMatterHeatHilbert4D :=
  ComplexDiagonalHilbert
    (Sector × PrimitiveSpinCGeometricSignedMode)

/-- Coordinatewise signed matter Gaussian. -/
def programPSpinCMatterHeatLinearMap
    (massSquared : Real)
    (time : HeatTime) :
    ProgramPSpinCMatterHeatHilbert4D →ₗ[Complex]
      ProgramPSpinCMatterHeatHilbert4D where
  toFun state := ⟨fun mode =>
    (programPSpinCMatterHeatWeight
      period hPeriod massSquared time mode : Complex) * state mode, by
      refine state.2.mono' ?_
      intro mode
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (programPSpinCMatterHeatWeight_nonnegative
            period hPeriod massSquared time mode)]
      simpa using mul_le_mul_of_nonneg_right
        (programPSpinCMatterHeatWeight_le_one
          period hPeriod massSquared time mode)
        (norm_nonneg (state mode))⟩
  map_add' := by
    intro first second
    ext mode
    simp [mul_add]
  map_smul' := by
    intro scalar state
    ext mode
    simp [mul_left_comm]

/-- Bounded heat contraction of the exact signed matter Hessian. -/
def programPSpinCMatterHeatOperator
    (massSquared : Real)
    (time : HeatTime) :
    ProgramPSpinCMatterHeatHilbert4D →L[Complex]
      ProgramPSpinCMatterHeatHilbert4D :=
  (programPSpinCMatterHeatLinearMap
    period hPeriod massSquared time).mkContinuous 1 (by
      intro state
      rw [one_mul]
      apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
      intro mode
      change
        ‖(programPSpinCMatterHeatWeight
          period hPeriod massSquared time mode : Complex) *
            state mode‖ ≤ ‖state mode‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (programPSpinCMatterHeatWeight_nonnegative
            period hPeriod massSquared time mode)]
      exact mul_le_of_le_one_left (norm_nonneg (state mode))
        (programPSpinCMatterHeatWeight_le_one
          period hPeriod massSquared time mode))

@[simp]
theorem programPSpinCMatterHeatOperator_apply
    (massSquared : Real)
    (time : HeatTime)
    (state : ProgramPSpinCMatterHeatHilbert4D)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    programPSpinCMatterHeatOperator
        period hPeriod massSquared time state mode =
      (programPSpinCMatterHeatWeight
        period hPeriod massSquared time mode : Complex) *
        state mode :=
  rfl

theorem programPSpinCMatterHeatOperator_opNorm_le_one
    (massSquared : Real)
    (time : HeatTime) :
    ‖programPSpinCMatterHeatOperator
      period hPeriod massSquared time‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Canonical basis of the exact signed matter coefficient completion. -/
def programPSpinCMatterHeatBasis :
    HilbertBasis
      (Sector × PrimitiveSpinCGeometricSignedMode)
      Complex ProgramPSpinCMatterHeatHilbert4D :=
  HilbertBasis.ofRepr
    (LinearIsometryEquiv.refl Complex
      ProgramPSpinCMatterHeatHilbert4D)

@[simp]
theorem programPSpinCMatterHeatBasis_eq_single
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    programPSpinCMatterHeatBasis mode =
      lp.single 2 mode (1 : Complex) := by
  rw [← HilbertBasis.repr_symm_single
    programPSpinCMatterHeatBasis mode]
  change programPSpinCMatterHeatBasis.repr.symm
    (lp.single 2 mode (1 : Complex)) =
      lp.single 2 mode (1 : Complex)
  rw [show programPSpinCMatterHeatBasis.repr =
      LinearIsometryEquiv.refl Complex
        ProgramPSpinCMatterHeatHilbert4D by rfl]
  simpa only [LinearIsometryEquiv.coe_refl, id_eq] using
    (LinearIsometryEquiv.refl Complex
      ProgramPSpinCMatterHeatHilbert4D).symm_apply_apply
        (lp.single 2 mode (1 : Complex))

theorem programPSpinCMatterHeatBasis_norm
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    ‖programPSpinCMatterHeatBasis mode‖ = 1 :=
  (HilbertBasis.orthonormal
    programPSpinCMatterHeatBasis).1 mode

/-- One rank-one component of the completed signed matter heat operator. -/
def programPSpinCMatterHeatRankOne
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    ProgramPSpinCMatterHeatHilbert4D →L[Complex]
      ProgramPSpinCMatterHeatHilbert4D :=
  (lp.evalCLM Complex
      (fun _ : Sector × PrimitiveSpinCGeometricSignedMode =>
        Complex) 2 mode).smulRight
    ((programPSpinCMatterHeatWeight
      period hPeriod massSquared time mode : Complex) •
        programPSpinCMatterHeatBasis mode)

@[simp]
theorem programPSpinCMatterHeatRankOne_apply
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode)
    (state : ProgramPSpinCMatterHeatHilbert4D) :
    programPSpinCMatterHeatRankOne
        period hPeriod massSquared time mode state =
      state mode •
        ((programPSpinCMatterHeatWeight
          period hPeriod massSquared time mode : Complex) •
            programPSpinCMatterHeatBasis mode) :=
  rfl

theorem programPSpinCMatterHeatRankOne_isCompact
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    IsCompactOperator
      (programPSpinCMatterHeatRankOne
        period hPeriod massSquared time mode) := by
  exact
    (isCompactOperator_of_locallyCompactSpace_dom
      (lp.evalCLM Complex
        (fun _ : Sector × PrimitiveSpinCGeometricSignedMode =>
          Complex) 2 mode)).clm_comp
      (ContinuousLinearMap.toSpanSingleton Complex
        ((programPSpinCMatterHeatWeight
          period hPeriod massSquared time mode : Complex) •
            programPSpinCMatterHeatBasis mode))

private theorem programPSpinCMatterEvalCLM_opNorm_le_one
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    ‖lp.evalCLM Complex
      (fun _ : Sector × PrimitiveSpinCGeometricSignedMode =>
        Complex) 2 mode‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro state
  change ‖state mode‖ ≤ 1 * ‖state‖
  simpa using lp.norm_apply_le_norm
    (by norm_num : (2 : ENNReal) ≠ 0) state mode

theorem programPSpinCMatterHeatRankOne_opNorm_le
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    ‖programPSpinCMatterHeatRankOne
      period hPeriod massSquared time mode‖ ≤
        programPSpinCMatterHeatWeight
          period hPeriod massSquared time mode := by
  rw [programPSpinCMatterHeatRankOne,
    ContinuousLinearMap.norm_smulRight_apply,
    norm_smul, programPSpinCMatterHeatBasis_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      (programPSpinCMatterHeatWeight_nonnegative
        period hPeriod massSquared time mode)]
  exact mul_le_of_le_one_left
    (programPSpinCMatterHeatWeight_nonnegative
      period hPeriod massSquared time mode)
    (programPSpinCMatterEvalCLM_opNorm_le_one mode)

theorem programPSpinCMatterHeatRankOne_norm_summable
    (massSquared : Real)
    (time : HeatTime) :
    Summable (fun mode :
        Sector × PrimitiveSpinCGeometricSignedMode =>
      ‖programPSpinCMatterHeatRankOne
        period hPeriod massSquared time mode‖) :=
  (programPSpinCMatterHeatWeight_summable
    period hPeriod massSquared time).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (programPSpinCMatterHeatRankOne_opNorm_le
        period hPeriod massSquared time)

theorem programPSpinCMatterHeatRankOne_summable
    (massSquared : Real)
    (time : HeatTime) :
    Summable
      (programPSpinCMatterHeatRankOne
        period hPeriod massSquared time) :=
  Summable.of_norm
    (programPSpinCMatterHeatRankOne_norm_summable
      period hPeriod massSquared time)

/-- Arbitrary finite spectral truncation of the matter heat operator. -/
def programPSpinCMatterHeatFiniteTruncation
    (massSquared : Real)
    (time : HeatTime)
    (cutoff :
      Finset (Sector × PrimitiveSpinCGeometricSignedMode)) :
    ProgramPSpinCMatterHeatHilbert4D →L[Complex]
      ProgramPSpinCMatterHeatHilbert4D :=
  ∑ mode ∈ cutoff,
    programPSpinCMatterHeatRankOne
      period hPeriod massSquared time mode

theorem programPSpinCMatterHeatFiniteTruncation_isCompact
    (massSquared : Real)
    (time : HeatTime)
    (cutoff :
      Finset (Sector × PrimitiveSpinCGeometricSignedMode)) :
    IsCompactOperator
      (programPSpinCMatterHeatFiniteTruncation
        period hPeriod massSquared time cutoff) := by
  classical
  unfold programPSpinCMatterHeatFiniteTruncation
  refine Finset.sum_induction
    (programPSpinCMatterHeatRankOne
      period hPeriod massSquared time)
    (fun operator => IsCompactOperator operator)
    (fun _ _ hFirst hSecond => hFirst.add hSecond)
    isCompactOperator_zero ?_
  intro mode _
  exact programPSpinCMatterHeatRankOne_isCompact
    period hPeriod massSquared time mode

/-- Operator-norm sum of all signed matter rank-one heat components. -/
def programPSpinCMatterHeatNuclearSum
    (massSquared : Real)
    (time : HeatTime) :
    ProgramPSpinCMatterHeatHilbert4D →L[Complex]
      ProgramPSpinCMatterHeatHilbert4D :=
  ∑' mode : Sector × PrimitiveSpinCGeometricSignedMode,
    programPSpinCMatterHeatRankOne
      period hPeriod massSquared time mode

theorem programPSpinCMatterHeatRankOne_on_basis
    (massSquared : Real)
    (time : HeatTime)
    (mode other :
      Sector × PrimitiveSpinCGeometricSignedMode) :
    programPSpinCMatterHeatRankOne
        period hPeriod massSquared time mode
        (programPSpinCMatterHeatBasis other) =
      if mode = other then
        (programPSpinCMatterHeatWeight
          period hPeriod massSquared time other : Complex) •
            programPSpinCMatterHeatBasis other
      else 0 := by
  by_cases hMode : mode = other
  · subst mode
    simp [programPSpinCMatterHeatRankOne_apply,
      programPSpinCMatterHeatBasis_eq_single]
  · simp [programPSpinCMatterHeatRankOne_apply,
      programPSpinCMatterHeatBasis_eq_single,
      lp.single_apply, hMode]

theorem programPSpinCMatterHeatNuclearSum_on_basis
    (massSquared : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    programPSpinCMatterHeatNuclearSum
        period hPeriod massSquared time
        (programPSpinCMatterHeatBasis mode) =
      (programPSpinCMatterHeatWeight
        period hPeriod massSquared time mode : Complex) •
          programPSpinCMatterHeatBasis mode := by
  rw [programPSpinCMatterHeatNuclearSum]
  rw [show
      (∑' other : Sector × PrimitiveSpinCGeometricSignedMode,
        programPSpinCMatterHeatRankOne
          period hPeriod massSquared time other)
          (programPSpinCMatterHeatBasis mode) =
        ∑' other : Sector × PrimitiveSpinCGeometricSignedMode,
          programPSpinCMatterHeatRankOne
            period hPeriod massSquared time other
            (programPSpinCMatterHeatBasis mode) by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply Complex
        ProgramPSpinCMatterHeatHilbert4D
        (programPSpinCMatterHeatBasis mode)).map_tsum
          (programPSpinCMatterHeatRankOne_summable
            period hPeriod massSquared time)]
  rw [tsum_eq_single mode]
  · simp
  · intro other hOther
    simp [hOther]

theorem programPSpinCMatterHeatNuclearSum_eq_operator
    (massSquared : Real)
    (time : HeatTime) :
    programPSpinCMatterHeatNuclearSum
        period hPeriod massSquared time =
      programPSpinCMatterHeatOperator
        period hPeriod massSquared time := by
  have hDense : Dense
      (Submodule.span Complex
        (Set.range programPSpinCMatterHeatBasis) :
          Set ProgramPSpinCMatterHeatHilbert4D) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact HilbertBasis.dense_span
      programPSpinCMatterHeatBasis
  apply ContinuousLinearMap.ext_on
    (s := Set.range programPSpinCMatterHeatBasis) hDense
  rintro _ ⟨mode, rfl⟩
  rw [programPSpinCMatterHeatNuclearSum_on_basis]
  ext other
  rw [programPSpinCMatterHeatOperator_apply,
    programPSpinCMatterHeatBasis_eq_single]
  by_cases hOther : other = mode
  · subst other
    rfl
  · change
      (programPSpinCMatterHeatWeight
          period hPeriod massSquared time mode : Complex) *
          ((lp.single 2 mode (1 : Complex) :
            ProgramPSpinCMatterHeatHilbert4D) other) =
        (programPSpinCMatterHeatWeight
          period hPeriod massSquared time other : Complex) *
          ((lp.single 2 mode (1 : Complex) :
            ProgramPSpinCMatterHeatHilbert4D) other)
    rw [lp.single_apply]
    simp [hOther]

theorem programPSpinCMatterHeatFiniteTruncation_tendsto_operator
    (massSquared : Real)
    (time : HeatTime) :
    Filter.Tendsto
      (programPSpinCMatterHeatFiniteTruncation
        period hPeriod massSquared time)
      Filter.atTop
      (nhds (programPSpinCMatterHeatOperator
        period hPeriod massSquared time)) := by
  rw [← programPSpinCMatterHeatNuclearSum_eq_operator
    period hPeriod massSquared time]
  exact
    (programPSpinCMatterHeatRankOne_summable
      period hPeriod massSquared time).hasSum

theorem programPSpinCMatterHeatOperator_isCompact
    (massSquared : Real)
    (time : HeatTime) :
    IsCompactOperator
      (programPSpinCMatterHeatOperator
        period hPeriod massSquared time) := by
  apply isCompactOperator_of_tendsto
    (programPSpinCMatterHeatFiniteTruncation_tendsto_operator
      period hPeriod massSquared time)
  exact Filter.Eventually.of_forall fun cutoff =>
    programPSpinCMatterHeatFiniteTruncation_isCompact
      period hPeriod massSquared time cutoff

/-- Explicit nuclear certificate for the complete two-sector signed SpinC
matter heat operator. -/
structure ProgramPSpinCMatterHeatNuclearCertificate4D
    (massSquared : Real)
    (time : HeatTime) where
  components :
    (Sector × PrimitiveSpinCGeometricSignedMode) →
      (ProgramPSpinCMatterHeatHilbert4D →L[Complex]
        ProgramPSpinCMatterHeatHilbert4D)
  summable_norm :
    Summable (fun mode => ‖components mode‖)
  operator_eq_tsum :
    programPSpinCMatterHeatOperator
        period hPeriod massSquared time =
      ∑' mode, components mode
  operator_compact :
    IsCompactOperator
      (programPSpinCMatterHeatOperator
        period hPeriod massSquared time)
  trace_eq :
    (∑' mode : Sector × PrimitiveSpinCGeometricSignedMode,
      programPSpinCMatterHeatWeight
        period hPeriod massSquared time mode) =
      ∑' mode : Sector × PrimitiveSpinCGeometricSignedMode,
        programPSpinCMatterHeatWeight
          period hPeriod massSquared time mode

def programPSpinCMatterHeatNuclearCertificate4D
    (massSquared : Real)
    (time : HeatTime) :
    ProgramPSpinCMatterHeatNuclearCertificate4D
      period hPeriod massSquared time where
  components :=
    programPSpinCMatterHeatRankOne
      period hPeriod massSquared time
  summable_norm :=
    programPSpinCMatterHeatRankOne_norm_summable
      period hPeriod massSquared time
  operator_eq_tsum :=
    (programPSpinCMatterHeatNuclearSum_eq_operator
      period hPeriod massSquared time).symm
  operator_compact :=
    programPSpinCMatterHeatOperator_isCompact
      period hPeriod massSquared time
  trace_eq := rfl

/-- Terminal unconditional heat gate for the matter block already present
in the global physical Hessian regulator. -/
theorem programPSpinCMatterContinuumHeat_nuclear_gate
    (massSquared : Real)
    (time : HeatTime) :
    Nonempty
      (ProgramPSpinCMatterHeatNuclearCertificate4D
        period hPeriod massSquared time) :=
  ⟨programPSpinCMatterHeatNuclearCertificate4D
    period hPeriod massSquared time⟩

end
end P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D
end JanusFormal
