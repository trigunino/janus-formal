import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalProperShiftFredholm4D
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusSeparatedSpectrumProperness

/-!
# Geometric signed primitive SpinC Fredholm realization

The complete primitive coefficient labels are equipped with the actual
mapping-torus period, both normal roots and both nonzero first-order Dirac
branches.  Properness is proved from the separated-spectrum coercivity
theorem.  Consequently every real mass shift gives a self-adjoint Fredholm
maximal operator with only finitely many resonant zero modes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusComplexDiagonalProperShiftFredholm4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusInfiniteL2DiracDomain
open P0EFTJanusSeparatedSpectrumProperness
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

/-- Complete first-order labels: both normal roots, one undoubled zero-sphere
tower, and both Dirac branches at every positive sphere level. -/
abbrev PrimitiveSpinCGeometricSignedMode :=
  NormalRootChoice × PrimitiveSpinCSignedMode

local instance primitiveSpinCGeometricSignedModeDecidableEq :
    DecidableEq PrimitiveSpinCGeometricSignedMode :=
  Classical.decEq _

/-- Forget only the independent nonzero Dirac-branch label. -/
def primitiveSpinCGeometricSignedModeToFullMode
    (mode : PrimitiveSpinCGeometricSignedMode) :
    PrimitiveSpinCGeometricFullMode :=
  (mode.1, primitiveSpinCSignedModeToFullMode mode.2)

/-- Geometrically scaled signed first-order primitive SpinC eigenvalue. -/
def primitiveSpinCGeometricSignedEigenvalue
    (mode : PrimitiveSpinCGeometricSignedMode) : Real :=
  match mode.2 with
  | .inl zeroMode =>
      circleEigenvalue
        (PrimitiveSpinCSpectralData period hPeriod)
        mode.1 zeroMode.2
  | .inr nonzeroMode =>
      primitiveSpinCDiracBranchSign nonzeroMode.branch *
        Real.sqrt
          (primitiveSpinCGeometricSquaredEigenvalue period hPeriod
            (primitiveSpinCGeometricSignedModeToFullMode mode))

/-- Squaring the signed first-order value recovers the existing geometric
SpinC Laplacian coefficient exactly. -/
theorem primitiveSpinCGeometricSignedEigenvalue_sq
    (mode : PrimitiveSpinCGeometricSignedMode) :
    primitiveSpinCGeometricSignedEigenvalue period hPeriod mode ^ 2 =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod
        (primitiveSpinCGeometricSignedModeToFullMode mode) := by
  rcases mode with ⟨choice, mode⟩
  cases mode with
  | inl zeroMode =>
      rcases zeroMode with ⟨multiplicity, circleMode⟩
      simp [primitiveSpinCGeometricSignedEigenvalue,
        primitiveSpinCGeometricSignedModeToFullMode,
        primitiveSpinCSignedModeToFullMode,
        primitiveSpinCGeometricSquaredEigenvalue,
        primitiveSpinCFullSphereEigenvalueSquared]
  | inr nonzeroMode =>
      rw [primitiveSpinCGeometricSignedEigenvalue, mul_pow,
        primitiveSpinCDiracBranchSign_sq, one_mul,
        Real.sq_sqrt
          (primitiveSpinCGeometricSquaredEigenvalue_nonnegative
            period hPeriod
            (primitiveSpinCGeometricSignedModeToFullMode
              (choice, Sum.inr nonzeroMode)))]

/-- Absolute first-order value equals the positive geometric frequency. -/
theorem primitiveSpinCGeometricSignedEigenvalue_abs
    (mode : PrimitiveSpinCGeometricSignedMode) :
    |primitiveSpinCGeometricSignedEigenvalue period hPeriod mode| =
      Real.sqrt
        (primitiveSpinCGeometricSquaredEigenvalue period hPeriod
          (primitiveSpinCGeometricSignedModeToFullMode mode)) := by
  calc
    |primitiveSpinCGeometricSignedEigenvalue period hPeriod mode| =
        Real.sqrt
          (primitiveSpinCGeometricSignedEigenvalue
            period hPeriod mode ^ 2) := by
      symm
      exact Real.sqrt_sq_eq_abs _
    _ = _ := by
      rw [primitiveSpinCGeometricSignedEigenvalue_sq]

/-- Positive frequency on the unsigned complete geometric labels. -/
def primitiveSpinCGeometricFrequency
    (mode : PrimitiveSpinCGeometricFullMode) : Real :=
  Real.sqrt
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode)

/-- Map a full level to the legacy separated positive-level indexing.  Levels
zero and one share separated level zero; this harmless finite fiber is why
the properness proof uses an injective numerical code below. -/
def primitiveSpinCGeometricFullModeToProductMode
    (mode : PrimitiveSpinCGeometricFullMode) : ProductDiracMode where
  sphereLevel := mode.2.1.1.pred
  circleMode := mode.2.2
  rootChoice := mode.1

theorem
    primitiveSpinCGeometricFullModeToProductMode_spectrum_le
    (mode : PrimitiveSpinCGeometricFullMode) :
    productDiracEigenvalueSquared
        (PrimitiveSpinCSpectralData period hPeriod)
        (primitiveSpinCGeometricFullModeToProductMode mode) ≤
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode + 2 := by
  rcases mode with ⟨choice, ⟨⟨level, multiplicity⟩, circleMode⟩⟩
  cases level with
  | zero =>
      change
        sphereEigenvalueSquared
              (PrimitiveSpinCSpectralData period hPeriod) 0 +
            circleEigenvalue
              (PrimitiveSpinCSpectralData period hPeriod)
              choice circleMode ^ 2 ≤
          primitiveSpinCFullSphereEigenvalueSquared 0 +
            circleEigenvalue
              (PrimitiveSpinCSpectralData period hPeriod)
              choice circleMode ^ 2 + 2
      rw [← primitiveSpinCFull_positiveSphereEigenvalue_agrees
        period hPeriod 0]
      norm_num [primitiveSpinCFullSphereEigenvalueSquared]
      simpa [add_comm] using
        (le_refl
          (2 +
            circleEigenvalue
              (PrimitiveSpinCSpectralData period hPeriod)
              choice circleMode ^ 2))
  | succ level =>
      change
        sphereEigenvalueSquared
              (PrimitiveSpinCSpectralData period hPeriod) level +
            circleEigenvalue
              (PrimitiveSpinCSpectralData period hPeriod)
              choice circleMode ^ 2 ≤
          primitiveSpinCFullSphereEigenvalueSquared level.succ +
            circleEigenvalue
              (PrimitiveSpinCSpectralData period hPeriod)
              choice circleMode ^ 2 + 2
      rw [primitiveSpinCFull_positiveSphereEigenvalue_agrees
        period hPeriod level]
      linarith

/-- Injective numerical code used only to prove finite spectral sublevels. -/
def primitiveSpinCGeometricFullModeCode
    (mode : PrimitiveSpinCGeometricFullMode) :
    Nat × (Nat × (Int × NormalRootChoice)) :=
  (mode.2.1.1, (mode.2.1.2.val, (mode.2.2, mode.1)))

theorem primitiveSpinCGeometricFullModeCode_injective :
    Function.Injective primitiveSpinCGeometricFullModeCode := by
  rintro ⟨choice₁, ⟨⟨level₁, multiplicity₁⟩, circle₁⟩⟩
    ⟨choice₂, ⟨⟨level₂, multiplicity₂⟩, circle₂⟩⟩ hEqual
  simp only [primitiveSpinCGeometricFullModeCode,
    Prod.mk.injEq] at hEqual
  rcases hEqual with
    ⟨hLevel, hMultiplicity, hCircle, hChoice⟩
  subst choice₂
  subst level₂
  subst circle₂
  have : multiplicity₁ = multiplicity₂ := Fin.ext hMultiplicity
  subst multiplicity₂
  rfl

/-- Properness of the geometrically scaled positive frequency, including the
previously missing zero-sphere tower and all multiplicities. -/
theorem primitiveSpinCGeometricFrequency_proper :
    ComplexDiagonalProperWeight PrimitiveSpinCGeometricFullMode
      (primitiveSpinCGeometricFrequency period hPeriod) := by
  constructor
  intro bound
  let radius : Real := Real.sqrt (bound ^ 2 + 2)
  obtain ⟨cutoff, hBox⟩ :=
    separated_dirac_weight_coercive
      (PrimitiveSpinCSpectralData period hPeriod) radius
  let codeBox :
      Set (Nat × (Nat × (Int × NormalRootChoice))) :=
    Set.Iic (cutoff + 1) ×ˢ
      (Set.Iic (1 + 2 * (cutoff + 1)) ×ˢ
        (Set.Icc (-(cutoff : Int)) (cutoff : Int) ×ˢ Set.univ))
  have hCodeBoxFinite : codeBox.Finite := by
    exact
      (Set.finite_Iic (cutoff + 1)).prod
        ((Set.finite_Iic (1 + 2 * (cutoff + 1))).prod
          ((Set.finite_Icc (-(cutoff : Int)) (cutoff : Int)).prod
            Set.finite_univ))
  apply Set.Finite.of_finite_image
      (f := primitiveSpinCGeometricFullModeCode)
  · apply hCodeBoxFinite.subset
    rintro code ⟨mode, hMode, rfl⟩
    have hFrequencyNonnegative :
        0 ≤ primitiveSpinCGeometricFrequency period hPeriod mode :=
      Real.sqrt_nonneg _
    have hFrequency :
        primitiveSpinCGeometricFrequency period hPeriod mode ≤ bound := by
      simpa [abs_of_nonneg hFrequencyNonnegative] using hMode
    have hSquared :
        primitiveSpinCGeometricSquaredEigenvalue
            period hPeriod mode ≤ bound ^ 2 := by
      have hSquare :=
        Real.sq_sqrt
          (primitiveSpinCGeometricSquaredEigenvalue_nonnegative
            period hPeriod mode)
      have hBoundNonnegative : 0 ≤ bound :=
        hFrequencyNonnegative.trans hFrequency
      rw [← hSquare]
      exact
        (sq_le_sq₀ hFrequencyNonnegative hBoundNonnegative).2
          hFrequency
    let productMode :=
      primitiveSpinCGeometricFullModeToProductMode mode
    have hProductSquared :
        productDiracEigenvalueSquared
            (PrimitiveSpinCSpectralData period hPeriod) productMode ≤
          bound ^ 2 + 2 :=
      (primitiveSpinCGeometricFullModeToProductMode_spectrum_le
        period hPeriod mode).trans (by linarith)
    have hProductWeight :
        separatedDiracWeight
            (PrimitiveSpinCSpectralData period hPeriod) productMode ≤
          radius := by
      have hProductNonnegative :
          0 ≤ productDiracEigenvalueSquared
            (PrimitiveSpinCSpectralData period hPeriod) productMode :=
        (product_spectrum_has_positive_gap
          (PrimitiveSpinCSpectralData period hPeriod) productMode).le
      have hProductSquare :
          separatedDiracWeight
                (PrimitiveSpinCSpectralData period hPeriod) productMode ^ 2 =
            productDiracEigenvalueSquared
              (PrimitiveSpinCSpectralData period hPeriod) productMode := by
        exact Real.sq_sqrt hProductNonnegative
      have hRadiusSquare : radius ^ 2 = bound ^ 2 + 2 := by
        exact Real.sq_sqrt (by positivity)
      have hWeightNonnegative :=
        separated_dirac_weight_nonnegative
          (PrimitiveSpinCSpectralData period hPeriod) productMode
      have hRadiusNonnegative : 0 ≤ radius := Real.sqrt_nonneg _
      nlinarith
    have hProductBox :
        productModeBoundingBox cutoff productMode := by
      apply hBox
      change
        ‖(separatedDiracWeight
          (PrimitiveSpinCSpectralData period hPeriod) productMode :
          Complex)‖ ≤ radius
      simpa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (separated_dirac_weight_nonnegative
            (PrimitiveSpinCSpectralData period hPeriod) productMode)]
        using hProductWeight
    rcases mode with
      ⟨choice, ⟨⟨level, multiplicity⟩, circleMode⟩⟩
    have hProductLevel := hProductBox.1
    have hCircleLower := hProductBox.2.1
    have hCircleUpper := hProductBox.2.2
    change level.pred ≤ cutoff at hProductLevel
    change -(cutoff : Int) ≤ circleMode at hCircleLower
    change circleMode ≤ (cutoff : Int) at hCircleUpper
    have hLevel : level ≤ cutoff + 1 := by
      cases level with
      | zero => omega
      | succ level =>
          change level ≤ cutoff at hProductLevel
          omega
    have hMultiplicity :
        multiplicity.val ≤ 1 + 2 * (cutoff + 1) := by
      have hMultiplicityLt := multiplicity.isLt
      unfold primitiveSphereModeDegeneracy at hMultiplicityLt
      omega
    exact
      ⟨hLevel,
        ⟨hMultiplicity,
          ⟨⟨hCircleLower, hCircleUpper⟩, Set.mem_univ choice⟩⟩⟩
  · exact primitiveSpinCGeometricFullModeCode_injective.injOn

/-- The branch label is retained in this code, so forgetting it has no
hidden infinite fibers. -/
def primitiveSpinCGeometricSignedModeCode
    (mode : PrimitiveSpinCGeometricSignedMode) :
    PrimitiveSpinCGeometricFullMode ×
      Option PrimitiveSpinCDiracBranch :=
  (primitiveSpinCGeometricSignedModeToFullMode mode,
    match mode.2 with
    | .inl _ => none
    | .inr nonzeroMode => some nonzeroMode.branch)

theorem primitiveSpinCGeometricSignedModeCode_injective :
    Function.Injective primitiveSpinCGeometricSignedModeCode := by
  rintro ⟨choice₁, mode₁⟩ ⟨choice₂, mode₂⟩ hEqual
  cases mode₁ with
  | inl zero₁ =>
      cases mode₂ with
      | inl zero₂ =>
          rcases zero₁ with ⟨multiplicity₁, circle₁⟩
          rcases zero₂ with ⟨multiplicity₂, circle₂⟩
          have hFull := congrArg Prod.fst hEqual
          change
            (choice₁,
                ((⟨0, multiplicity₁⟩ : PrimitiveSpinCFullSphereMode),
                  circle₁)) =
              (choice₂,
                ((⟨0, multiplicity₂⟩ : PrimitiveSpinCFullSphereMode),
                  circle₂)) at hFull
          have hChoice := congrArg (fun mode => mode.1) hFull
          have hSphere := congrArg (fun mode => mode.2.1) hFull
          have hCircle := congrArg (fun mode => mode.2.2) hFull
          change choice₁ = choice₂ at hChoice
          change circle₁ = circle₂ at hCircle
          have hMultiplicity : HEq multiplicity₁ multiplicity₂ :=
            (Sigma.mk.inj_iff.mp hSphere).2
          subst choice₂
          subst circle₂
          have : multiplicity₁ = multiplicity₂ :=
            eq_of_heq hMultiplicity
          subst multiplicity₂
          rfl
      | inr nonzero₂ =>
          have hTag := congrArg Prod.snd hEqual
          simp [primitiveSpinCGeometricSignedModeCode] at hTag
  | inr nonzero₁ =>
      cases mode₂ with
      | inl zero₂ =>
          have hTag := congrArg Prod.snd hEqual
          simp [primitiveSpinCGeometricSignedModeCode] at hTag
      | inr nonzero₂ =>
          rcases nonzero₁ with
            ⟨branch₁, level₁, multiplicity₁, circle₁⟩
          rcases nonzero₂ with
            ⟨branch₂, level₂, multiplicity₂, circle₂⟩
          have hTag := congrArg Prod.snd hEqual
          change some branch₁ = some branch₂ at hTag
          have hBranch : branch₁ = branch₂ := Option.some.inj hTag
          subst branch₂
          have hFull := congrArg Prod.fst hEqual
          change
            (choice₁,
                ((⟨level₁ + 1, multiplicity₁⟩ :
                    PrimitiveSpinCFullSphereMode), circle₁)) =
              (choice₂,
                ((⟨level₂ + 1, multiplicity₂⟩ :
                    PrimitiveSpinCFullSphereMode), circle₂)) at hFull
          have hChoice := congrArg (fun mode => mode.1) hFull
          have hSphere := congrArg (fun mode => mode.2.1) hFull
          have hCircle := congrArg (fun mode => mode.2.2) hFull
          change choice₁ = choice₂ at hChoice
          change circle₁ = circle₂ at hCircle
          have hLevelSucc :
              level₁ + 1 = level₂ + 1 :=
            congrArg Sigma.fst hSphere
          have hLevel : level₁ = level₂ := by omega
          have hMultiplicity : HEq multiplicity₁ multiplicity₂ :=
            (Sigma.mk.inj_iff.mp hSphere).2
          subst choice₂
          subst level₂
          subst circle₂
          have : multiplicity₁ = multiplicity₂ :=
            eq_of_heq hMultiplicity
          subst multiplicity₂
          rfl

/-- The actual signed first-order spectrum is proper. -/
theorem primitiveSpinCGeometricSignedEigenvalue_proper :
    ComplexDiagonalProperWeight PrimitiveSpinCGeometricSignedMode
      (primitiveSpinCGeometricSignedEigenvalue period hPeriod) := by
  constructor
  intro bound
  let fullSublevel : Set PrimitiveSpinCGeometricFullMode :=
    {mode | |primitiveSpinCGeometricFrequency period hPeriod mode| ≤ bound}
  let codeSublevel :
      Set (PrimitiveSpinCGeometricFullMode ×
        Option PrimitiveSpinCDiracBranch) :=
    fullSublevel ×ˢ Set.univ
  have hFullFinite : fullSublevel.Finite :=
    (primitiveSpinCGeometricFrequency_proper
      period hPeriod).finite_sublevel bound
  have hCodeFinite : codeSublevel.Finite :=
    hFullFinite.prod Set.finite_univ
  apply Set.Finite.of_finite_image
      (f := primitiveSpinCGeometricSignedModeCode)
  · apply hCodeFinite.subset
    rintro code ⟨mode, hMode, rfl⟩
    constructor
    · change
        |primitiveSpinCGeometricFrequency period hPeriod
          (primitiveSpinCGeometricSignedModeToFullMode mode)| ≤ bound
      unfold primitiveSpinCGeometricFrequency
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [← primitiveSpinCGeometricSignedEigenvalue_abs]
      exact hMode
    · exact Set.mem_univ _
  · exact primitiveSpinCGeometricSignedModeCode_injective.injOn

/-- The kinetic action is `Re ⟨ψ,Dψ⟩`, hence its real Hessian coefficient is
`2D` rather than `D`. -/
def primitiveSpinCGeometricSignedKineticHessianWeight
    (mode : PrimitiveSpinCGeometricSignedMode) : Real :=
  2 * primitiveSpinCGeometricSignedEigenvalue period hPeriod mode

theorem primitiveSpinCGeometricSignedKineticHessianWeight_proper :
    ComplexDiagonalProperWeight PrimitiveSpinCGeometricSignedMode
      (primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod) := by
  exact
    ComplexDiagonalProperWeight.scale
      PrimitiveSpinCGeometricSignedMode
      (primitiveSpinCGeometricSignedEigenvalue_proper period hPeriod)
      2 (by norm_num)

/-- Exact one-mode mixed second difference of
`λ x² + massSquared/2 x²`.  This fixes the action-Hessian normalization
`2λ + massSquared`. -/
theorem primitiveSpinCGeometricSignedModeAction_mixedSecondDifference
    (mode : PrimitiveSpinCGeometricSignedMode)
    (massSquared base first second firstScale secondScale : Real) :
    let eigenvalue :=
      primitiveSpinCGeometricSignedEigenvalue period hPeriod mode
    let action := fun value : Real =>
      eigenvalue * value ^ 2 + massSquared / 2 * value ^ 2
    action (base + firstScale * first + secondScale * second) -
          action (base + firstScale * first) -
          action (base + secondScale * second) + action base =
      firstScale * secondScale *
        (primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) * first * second := by
  dsimp [primitiveSpinCGeometricSignedKineticHessianWeight]
  ring

/-- Finite-zero-gap datum for the actual coefficient Hessian `2D + m²`. -/
def primitiveSpinCGeometricSignedActionHessianFiniteZeroGap
    (massSquared : Real) :
    ComplexDiagonalFiniteZeroGap PrimitiveSpinCGeometricSignedMode
      (fun mode =>
        primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) :=
  complexDiagonalFiniteZeroGap_of_proper_shift
    PrimitiveSpinCGeometricSignedMode
    (primitiveSpinCGeometricSignedKineticHessianWeight period hPeriod)
    (primitiveSpinCGeometricSignedKineticHessianWeight_proper
      period hPeriod)
    massSquared

/-- Maximal first-order geometric SpinC operator with an arbitrary mass
coefficient. -/
abbrev primitiveSpinCGeometricSignedMassOperator
    (mass : Real) :=
  complexDiagonalOperator PrimitiveSpinCGeometricSignedMode
    (fun mode =>
      primitiveSpinCGeometricSignedEigenvalue period hPeriod mode + mass)

/-- Its underlying real realization, matching a real variational Hessian. -/
abbrev primitiveSpinCGeometricSignedMassRealOperator
    (mass : Real) :=
  complexDiagonalRealOperator PrimitiveSpinCGeometricSignedMode
    (fun mode =>
      primitiveSpinCGeometricSignedEigenvalue period hPeriod mode + mass)

def primitiveSpinCGeometricSignedMassFiniteZeroGap
    (mass : Real) :
    ComplexDiagonalFiniteZeroGap PrimitiveSpinCGeometricSignedMode
      (fun mode =>
        primitiveSpinCGeometricSignedEigenvalue period hPeriod mode + mass) :=
  complexDiagonalFiniteZeroGap_of_proper_shift
    PrimitiveSpinCGeometricSignedMode
    (primitiveSpinCGeometricSignedEigenvalue period hPeriod)
    (primitiveSpinCGeometricSignedEigenvalue_proper period hPeriod)
    mass

theorem primitiveSpinCGeometricSignedMassOperator_selfAdjoint
    (mass : Real) :
    IsSelfAdjoint
      (primitiveSpinCGeometricSignedMassOperator period hPeriod mass) :=
  complexDiagonalOperator_isSelfAdjoint PrimitiveSpinCGeometricSignedMode
    (fun mode =>
      primitiveSpinCGeometricSignedEigenvalue period hPeriod mode + mass)

theorem primitiveSpinCGeometricSignedMassOperator_fredholm
    (mass : Real) :
    IsClosed
        (LinearMap.range
          (primitiveSpinCGeometricSignedMassOperator
            period hPeriod mass).toFun :
          Set (ComplexDiagonalHilbert
            PrimitiveSpinCGeometricSignedMode)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (primitiveSpinCGeometricSignedMassOperator
            period hPeriod mass).toFun) ∧
      FiniteDimensional Complex
        (ComplexDiagonalOperatorCokernel
          PrimitiveSpinCGeometricSignedMode
          (fun mode =>
            primitiveSpinCGeometricSignedEigenvalue
              period hPeriod mode + mass)) :=
  complexDiagonalOperator_fredholm_of_proper_shift
    PrimitiveSpinCGeometricSignedMode
    (primitiveSpinCGeometricSignedEigenvalue period hPeriod)
    (primitiveSpinCGeometricSignedEigenvalue_proper period hPeriod)
    mass

theorem primitiveSpinCGeometricSignedMassRealOperator_fredholm
    (mass : Real) :
    IsClosed
        (LinearMap.range
          (primitiveSpinCGeometricSignedMassRealOperator
            period hPeriod mass).toFun :
          Set (ComplexDiagonalHilbert
            PrimitiveSpinCGeometricSignedMode)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (primitiveSpinCGeometricSignedMassRealOperator
            period hPeriod mass).toFun) ∧
      FiniteDimensional Real
        (ComplexDiagonalRealOperatorCokernel
          PrimitiveSpinCGeometricSignedMode
          (fun mode =>
            primitiveSpinCGeometricSignedEigenvalue
              period hPeriod mode + mass)) := by
  letI :
      InnerProductSpace Real
        (ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode) :=
    InnerProductSpace.complexToReal
  letI :
      Star (ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode
        →ₗ.[Real]
        ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode) :=
    LinearPMap.instStar
  exact complexDiagonalRealOperator_fredholm_of_proper_shift
    PrimitiveSpinCGeometricSignedMode
    (primitiveSpinCGeometricSignedEigenvalue period hPeriod)
    (primitiveSpinCGeometricSignedEigenvalue_proper period hPeriod)
    mass

end
end P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
end JanusFormal
