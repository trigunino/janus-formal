import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D

/-!
# Explicit normal-root modes and global primitive zero-sphere tower

The ambient half-spinor generator has eigenvalue `i` on `(1,i)`.  Combining
that rotating spin frame with the quarter-root character converts the cover
coefficient into an ordinary periodic or antiperiodic Fourier mode.  The
Levi-Civita spin correction removes the frame contribution, leaving exactly
the quarter-shifted normal-root momentum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

/-- Continuous realization of the D9 matter/half-spinor identification. -/
def d9MatterFiberHalfSpinorContinuousLinearEquiv :
    MatterFiber ≃L[Real] AmbientHalfSpinor2 :=
  matterFiberHalfSpinorLinearEquiv.toContinuousLinearEquiv

/-- The `+i` eigenvector of the ambient half-spinor deck generator. -/
def ambientHalfGammaPositiveEigenvector : AmbientHalfSpinor2 :=
  ![1, Complex.I]

theorem ambientHalfGammaPositiveEigenvector_eigen :
    ambientHalfGammaGenerator *ᵥ
        ambientHalfGammaPositiveEigenvector =
      Complex.I • ambientHalfGammaPositiveEigenvector := by
  funext index
  fin_cases index <;>
    simp [ambientHalfGammaGenerator,
      ambientHalfGammaPositiveEigenvector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Complex.I_mul_I]

/-- Matter coordinate spanning the chosen rotating half-spinor line. -/
def d9MatterGammaPositiveEigenvector : MatterFiber :=
  matterFiberHalfSpinorLinearEquiv.symm
    ambientHalfGammaPositiveEigenvector

/-- Complex scalar action transported to the real D9 matter fiber. -/
def d9MatterComplexAction
    (scalar : Complex) (matter : MatterFiber) : MatterFiber :=
  matterFiberHalfSpinorLinearEquiv.symm
    (scalar • matterFiberHalfSpinorLinearEquiv matter)

@[simp]
theorem matterFiberHalfSpinorLinearEquiv_d9MatterComplexAction
    (scalar : Complex) (matter : MatterFiber) :
    matterFiberHalfSpinorLinearEquiv
        (d9MatterComplexAction scalar matter) =
      scalar • matterFiberHalfSpinorLinearEquiv matter := by
  simp [d9MatterComplexAction]

@[simp]
theorem d9MatterComplexAction_one (matter : MatterFiber) :
    d9MatterComplexAction 1 matter = matter := by
  apply matterFiberHalfSpinorLinearEquiv.injective
  simp

theorem d9MatterComplexAction_mul
    (first second : Complex) (matter : MatterFiber) :
    d9MatterComplexAction (first * second) matter =
      d9MatterComplexAction first
        (d9MatterComplexAction second matter) := by
  apply matterFiberHalfSpinorLinearEquiv.injective
  simp [mul_smul]

theorem d9MatterSpinorMonodromy_complexAction
    (choice : NormalRootChoice) (winding : Int)
    (scalar : Complex) (matter : MatterFiber) :
    d9MatterSpinorMonodromy choice winding
        (d9MatterComplexAction scalar matter) =
      d9MatterComplexAction scalar
        (d9MatterSpinorMonodromy choice winding matter) :=
  d9MatterSpinorMonodromy_complex_smul
    choice winding scalar matter

/-- Continuous linear parametrization of the rotating matter eigenline. -/
def d9MatterGammaPositiveEigenlineCLM :
    Complex →L[Real] MatterFiber :=
  d9MatterFiberHalfSpinorContinuousLinearEquiv.symm
    |>.toContinuousLinearMap.comp
      ((ContinuousLinearMap.lsmul Real Complex :
          Complex →L[Real]
            AmbientHalfSpinor2 →L[Real] AmbientHalfSpinor2).flip
        ambientHalfGammaPositiveEigenvector)

@[simp]
theorem d9MatterGammaPositiveEigenlineCLM_apply
    (scalar : Complex) :
    d9MatterGammaPositiveEigenlineCLM scalar =
      d9MatterComplexAction scalar
        d9MatterGammaPositiveEigenvector :=
  rfl

/-- Generator multiplier after combining the `+i` spin-frame eigenline with
the chosen quarter-root character. -/
def normalRootSpinFrameGeneratorMultiplier :
    NormalRootChoice → Complex
  | .positiveQuarter => -1
  | .negativeQuarter => 1

@[simp]
theorem normalRootSpinFrameGeneratorMultiplier_sq
    (choice : NormalRootChoice) :
    normalRootSpinFrameGeneratorMultiplier choice *
        normalRootSpinFrameGeneratorMultiplier choice = 1 := by
  cases choice <;>
    simp [normalRootSpinFrameGeneratorMultiplier]

/-- Actual integer Fourier index of the rotating cover coefficient. -/
def normalRootSpinFrameModeIndex :
    NormalRootChoice → Int → Int
  | .positiveQuarter, mode => 2 * mode + 1
  | .negativeQuarter, mode => 2 * mode

theorem normalRootModeNumerator_eq_spinFrame
    (choice : NormalRootChoice) (mode : Int) :
    normalRootModeNumerator choice mode =
      2 * normalRootSpinFrameModeIndex choice mode - 1 := by
  cases choice <;>
    simp [normalRootModeNumerator,
      normalRootSpinFrameModeIndex] <;> ring

/-- Ordinary Fourier frequency seen in the rotating spin frame. -/
def normalRootSpinFrameFrequency
    (choice : NormalRootChoice) (mode : Int) : Real :=
  Real.pi * (normalRootSpinFrameModeIndex choice mode : Real) / period

/-- The Levi--Civita frame correction removes one half-turn per period. -/
def normalRootLeviCivitaCorrectedFrequency
    (choice : NormalRootChoice) (mode : Int) : Real :=
  normalRootSpinFrameFrequency period choice mode -
    Real.pi / (2 * period)

theorem normalRootLeviCivitaCorrectedFrequency_eq
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (mode : Int) :
    normalRootLeviCivitaCorrectedFrequency period choice mode =
      Real.pi * (normalRootModeNumerator choice mode : Real) /
        (2 * period) := by
  rw [normalRootLeviCivitaCorrectedFrequency,
    normalRootSpinFrameFrequency,
    normalRootModeNumerator_eq_spinFrame]
  push_cast
  field_simp [hPeriod]

/-- After squaring, the signed cover period agrees with the absolute period
used by the spectral completion. -/
theorem normalRootLeviCivitaCorrectedFrequency_sq_eq_circle
    (choice : NormalRootChoice) (mode : Int) :
    normalRootLeviCivitaCorrectedFrequency period choice mode ^ 2 =
      circleEigenvalue
        (PrimitiveSpinCSpectralData period hPeriod) choice mode ^ 2 := by
  rw [normalRootLeviCivitaCorrectedFrequency_eq
    period hPeriod choice mode]
  unfold circleEigenvalue
  change
    (Real.pi * (normalRootModeNumerator choice mode : Real) /
        (2 * period)) ^ 2 =
      (Real.pi * (normalRootModeNumerator choice mode : Real) /
        (2 * |period|)) ^ 2
  rw [div_pow, div_pow]
  simp only [mul_pow, sq_abs]

/-- Real phase in the rotating spin frame. -/
def normalRootSpinFramePhaseAngle
    (choice : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) : Real :=
  Real.pi *
      (normalRootSpinFrameModeIndex choice mode : Real) /
    period * point.time

/-- Smooth unit complex coefficient of a normal-root mode upstairs. -/
def normalRootSpinFramePhase
    (choice : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) : Complex :=
  (Real.cos
      (normalRootSpinFramePhaseAngle
        period hPeriod choice mode point) : Complex) +
    (Real.sin
      (normalRootSpinFramePhaseAngle
        period hPeriod choice mode point) : Complex) *
      Complex.I

/-- Equivalent exponential expression for the rotating-frame phase. -/
def normalRootSpinFrameExponential
    (choice : NormalRootChoice) (mode : Int) (time : Real) : Complex :=
  Complex.exp
    ((((normalRootSpinFrameFrequency period choice mode : Real) : Complex) *
        Complex.I) * (time : Complex))

theorem normalRootSpinFrameExponential_eq_phase
    (choice : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    normalRootSpinFrameExponential period choice mode point.time =
      normalRootSpinFramePhase period hPeriod choice mode point := by
  rw [normalRootSpinFrameExponential]
  convert Complex.exp_mul_I
    (normalRootSpinFrameFrequency period choice mode * point.time) using 1 <;>
    simp [normalRootSpinFramePhase,
      normalRootSpinFramePhaseAngle,
      normalRootSpinFrameFrequency] <;>
    ring

theorem normalRootSpinFrameCos_hasDerivAt
    (choice : NormalRootChoice) (mode : Int) (time : Real) :
    HasDerivAt
      (fun input : Real =>
        Real.cos
          (normalRootSpinFrameFrequency period choice mode * input))
      (-Real.sin
          (normalRootSpinFrameFrequency period choice mode * time) *
        normalRootSpinFrameFrequency period choice mode)
      time := by
  have hLinear :
      HasDerivAt
        (fun input : Real =>
          normalRootSpinFrameFrequency period choice mode * input)
        (normalRootSpinFrameFrequency period choice mode) time := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id time).const_mul
        (normalRootSpinFrameFrequency period choice mode)
  exact
    (Real.hasDerivAt_cos
      (normalRootSpinFrameFrequency period choice mode * time)).comp
        time hLinear

theorem normalRootSpinFrameSin_hasDerivAt
    (choice : NormalRootChoice) (mode : Int) (time : Real) :
    HasDerivAt
      (fun input : Real =>
        Real.sin
          (normalRootSpinFrameFrequency period choice mode * input))
      (Real.cos
          (normalRootSpinFrameFrequency period choice mode * time) *
        normalRootSpinFrameFrequency period choice mode)
      time := by
  have hLinear :
      HasDerivAt
        (fun input : Real =>
          normalRootSpinFrameFrequency period choice mode * input)
        (normalRootSpinFrameFrequency period choice mode) time := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id time).const_mul
        (normalRootSpinFrameFrequency period choice mode)
  exact
    (Real.hasDerivAt_sin
      (normalRootSpinFrameFrequency period choice mode * time)).comp
        time hLinear

/-- Right multiplication by a fixed complex scalar as a real-linear map. -/
def normalModeComplexRightMulRealCLM (scalar : Complex) :
    Complex →L[Real] Complex :=
  (ContinuousLinearMap.toSpanSingleton Complex scalar).restrictScalars Real

@[simp]
theorem normalModeComplexRightMulRealCLM_apply
    (scalar value : Complex) :
    normalModeComplexRightMulRealCLM scalar value =
      value * scalar :=
  rfl

theorem fixedThroatCoverTime_contMDiff :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (MappingTorusCover.time :
        ThroatCover period hPeriod → Real) := by
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ∞
    (coverHomeomorphProd (ThroatData period hPeriod))
  exact (contMDiff_snd.comp hTo).congr fun point => rfl

theorem normalRootSpinFramePhase_contMDiff
    (choice : NormalRootChoice) (mode : Int) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
      (normalRootSpinFramePhase
        period hPeriod choice mode) := by
  have hAngle :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
        (normalRootSpinFramePhaseAngle
          period hPeriod choice mode) := by
    exact contMDiff_const.mul
      (fixedThroatCoverTime_contMDiff period hPeriod)
  have hCos :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
        (fun point =>
          Real.cos
            (normalRootSpinFramePhaseAngle
              period hPeriod choice mode point)) :=
    Real.contDiff_cos.contMDiff.comp hAngle
  have hSin :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
        (fun point =>
          Real.sin
            (normalRootSpinFramePhaseAngle
              period hPeriod choice mode point)) :=
    Real.contDiff_sin.contMDiff.comp hAngle
  have hCosComplex :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
        (fun point =>
          (Real.cos
            (normalRootSpinFramePhaseAngle
              period hPeriod choice mode point) : Complex)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.contMDiff.comp hCos
  have hSinComplex :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
        (fun point =>
          (Real.sin
            (normalRootSpinFramePhaseAngle
              period hPeriod choice mode point) : Complex)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.contMDiff.comp hSin
  have hSinI :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Complex) ∞
        (fun point =>
          (Real.sin
            (normalRootSpinFramePhaseAngle
              period hPeriod choice mode point) : Complex) *
            Complex.I) := by
    simpa only [Function.comp_def,
      normalModeComplexRightMulRealCLM_apply] using
      (normalModeComplexRightMulRealCLM Complex.I).contMDiff.comp
        hSinComplex
  exact hCosComplex.add hSinI

theorem normalRootSpinFramePhaseAngle_deck
    (choice : NormalRootChoice) (mode winding : Int)
    (point : ThroatCover period hPeriod) :
    normalRootSpinFramePhaseAngle period hPeriod choice mode
        (winding +ᵥ point) =
      normalRootSpinFramePhaseAngle period hPeriod choice mode point +
        ((normalRootSpinFrameModeIndex choice mode * winding : Int) :
          Real) * Real.pi := by
  change
    Real.pi *
          (normalRootSpinFrameModeIndex choice mode : Real) /
        period *
        (point.time + (winding : Real) * period) =
      Real.pi *
            (normalRootSpinFrameModeIndex choice mode : Real) /
          period * point.time +
        ((normalRootSpinFrameModeIndex choice mode * winding : Int) :
          Real) * Real.pi
  push_cast
  field_simp [hPeriod] <;> ring

/-- Every deck winding acts on the rotating eigenline by this scalar. -/
def normalRootSpinFrameDeckMultiplier
    (choice : NormalRootChoice) (winding : Int) : Complex :=
  normalRootSpinFrameGeneratorMultiplier choice ^ winding

theorem normalRootSpinFramePhase_deck
    (choice : NormalRootChoice) (mode winding : Int)
    (point : ThroatCover period hPeriod) :
    normalRootSpinFramePhase period hPeriod choice mode
        (winding +ᵥ point) =
      normalRootSpinFrameDeckMultiplier choice winding *
        normalRootSpinFramePhase period hPeriod choice mode point := by
  rw [normalRootSpinFramePhase,
    normalRootSpinFramePhaseAngle_deck
      period hPeriod choice mode winding point,
    Real.cos_add_int_mul_pi,
    Real.sin_add_int_mul_pi]
  cases choice with
  | positiveQuarter =>
      have hOdd :
          Odd (normalRootSpinFrameModeIndex
            .positiveQuarter mode) := by
        refine ⟨mode, ?_⟩
        simp [normalRootSpinFrameModeIndex]
      have hSign :
          ((-1 : Real) ^
              (normalRootSpinFrameModeIndex
                .positiveQuarter mode * winding) : Real) =
            (-1 : Real) ^ winding := by
        rw [zpow_mul, hOdd.neg_one_zpow]
      rw [hSign]
      simp only [normalRootSpinFrameDeckMultiplier,
        normalRootSpinFrameGeneratorMultiplier]
      simp only [normalRootSpinFramePhase]
      push_cast
      ring
  | negativeQuarter =>
      have hEven :
          Even (normalRootSpinFrameModeIndex
            .negativeQuarter mode) := by
        refine ⟨mode, ?_⟩
        simp only [normalRootSpinFrameModeIndex]
        ring
      have hSign :
          ((-1 : Real) ^
              (normalRootSpinFrameModeIndex
                .negativeQuarter mode * winding) : Real) = 1 := by
        rw [zpow_mul, hEven.neg_one_zpow, one_zpow]
      rw [hSign]
      simp only [normalRootSpinFrameDeckMultiplier,
        normalRootSpinFrameGeneratorMultiplier, one_zpow, one_mul,
        normalRootSpinFramePhase]

/-- The installed matter monodromy has exactly the rotating-frame generator
multiplier on the chosen eigenline. -/
theorem d9MatterGammaPositiveEigenvector_monodromy_one
    (choice : NormalRootChoice) :
    d9MatterSpinorMonodromy choice 1
        d9MatterGammaPositiveEigenvector =
      d9MatterComplexAction
        (normalRootSpinFrameGeneratorMultiplier choice)
        d9MatterGammaPositiveEigenvector := by
  apply matterFiberHalfSpinorLinearEquiv.injective
  cases choice <;>
    funext index <;>
    fin_cases index <;>
    simp [d9MatterSpinorMonodromy,
      d9MatterGammaPositiveEigenvector,
      d9MatterComplexAction,
      ambientHalfGammaPositiveEigenvector,
      ambientHalfGammaGeneratorUnit,
      ambientHalfGammaGenerator,
      normalRootSpinFrameGeneratorMultiplier,
      quarterRootRepresentation, normalRootMultiplier,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Complex.I_mul_I] <;>
    ring

theorem normalRootSpinFrameGeneratorMultiplier_ne_zero
    (choice : NormalRootChoice) :
    normalRootSpinFrameGeneratorMultiplier choice ≠ 0 := by
  cases choice <;>
    simp [normalRootSpinFrameGeneratorMultiplier]

@[simp]
theorem normalRootSpinFrameGeneratorMultiplier_inv
    (choice : NormalRootChoice) :
    (normalRootSpinFrameGeneratorMultiplier choice)⁻¹ =
      normalRootSpinFrameGeneratorMultiplier choice := by
  cases choice <;>
    simp [normalRootSpinFrameGeneratorMultiplier]

theorem d9MatterGammaPositiveEigenvector_monodromy_neg_one
    (choice : NormalRootChoice) :
    d9MatterSpinorMonodromy choice (-1)
        d9MatterGammaPositiveEigenvector =
      d9MatterComplexAction
        (normalRootSpinFrameGeneratorMultiplier choice)
        d9MatterGammaPositiveEigenvector := by
  apply (d9MatterSpinorMonodromyCLE choice 1).injective
  change
    d9MatterSpinorMonodromy choice 1
        (d9MatterSpinorMonodromy choice (-1)
          d9MatterGammaPositiveEigenvector) =
      d9MatterSpinorMonodromy choice 1
        (d9MatterComplexAction
          (normalRootSpinFrameGeneratorMultiplier choice)
          d9MatterGammaPositiveEigenvector)
  calc
    d9MatterSpinorMonodromy choice 1
          (d9MatterSpinorMonodromy choice (-1)
            d9MatterGammaPositiveEigenvector) =
        d9MatterGammaPositiveEigenvector := by
      rw [← d9MatterSpinorMonodromy_add]
      norm_num
    _ =
        d9MatterComplexAction
          (normalRootSpinFrameGeneratorMultiplier choice *
            normalRootSpinFrameGeneratorMultiplier choice)
          d9MatterGammaPositiveEigenvector := by
      rw [normalRootSpinFrameGeneratorMultiplier_sq]
      simp
    _ =
        d9MatterComplexAction
          (normalRootSpinFrameGeneratorMultiplier choice)
          (d9MatterComplexAction
            (normalRootSpinFrameGeneratorMultiplier choice)
            d9MatterGammaPositiveEigenvector) :=
      d9MatterComplexAction_mul _ _ _
    _ =
        d9MatterSpinorMonodromy choice 1
          (d9MatterComplexAction
            (normalRootSpinFrameGeneratorMultiplier choice)
            d9MatterGammaPositiveEigenvector) := by
      rw [d9MatterSpinorMonodromy_complexAction,
        d9MatterGammaPositiveEigenvector_monodromy_one]

/-- Eigenline formula for every integer deck winding. -/
theorem d9MatterGammaPositiveEigenvector_monodromy
    (choice : NormalRootChoice) (winding : Int) :
    d9MatterSpinorMonodromy choice winding
        d9MatterGammaPositiveEigenvector =
      d9MatterComplexAction
        (normalRootSpinFrameDeckMultiplier choice winding)
        d9MatterGammaPositiveEigenvector := by
  unfold normalRootSpinFrameDeckMultiplier
  induction winding using Int.induction_on with
  | zero =>
      simp
  | succ winding ih =>
      calc
        d9MatterSpinorMonodromy choice (winding + 1)
              d9MatterGammaPositiveEigenvector =
            d9MatterSpinorMonodromy choice winding
              (d9MatterSpinorMonodromy choice 1
                d9MatterGammaPositiveEigenvector) :=
          d9MatterSpinorMonodromy_add choice winding 1 _
        _ =
            d9MatterSpinorMonodromy choice winding
              (d9MatterComplexAction
                (normalRootSpinFrameGeneratorMultiplier choice)
                d9MatterGammaPositiveEigenvector) := by
          rw [d9MatterGammaPositiveEigenvector_monodromy_one]
        _ =
            d9MatterComplexAction
              (normalRootSpinFrameGeneratorMultiplier choice)
              (d9MatterSpinorMonodromy choice winding
                d9MatterGammaPositiveEigenvector) :=
          d9MatterSpinorMonodromy_complexAction _ _ _ _
        _ =
            d9MatterComplexAction
              (normalRootSpinFrameGeneratorMultiplier choice)
              (d9MatterComplexAction
                (normalRootSpinFrameGeneratorMultiplier choice ^
                  (winding : Int))
                d9MatterGammaPositiveEigenvector) := by
          rw [ih]
        _ =
            d9MatterComplexAction
              (normalRootSpinFrameGeneratorMultiplier choice ^
                ((winding : Int) + 1))
              d9MatterGammaPositiveEigenvector := by
          rw [← d9MatterComplexAction_mul,
            zpow_add_one₀
              (normalRootSpinFrameGeneratorMultiplier_ne_zero choice),
            mul_comm]
  | pred winding ih =>
      calc
        d9MatterSpinorMonodromy choice (-(winding : Int) - 1)
              d9MatterGammaPositiveEigenvector =
            d9MatterSpinorMonodromy choice (-(winding : Int))
              (d9MatterSpinorMonodromy choice (-1)
                d9MatterGammaPositiveEigenvector) :=
          d9MatterSpinorMonodromy_add choice (-(winding : Int)) (-1) _
        _ =
            d9MatterSpinorMonodromy choice (-(winding : Int))
              (d9MatterComplexAction
                (normalRootSpinFrameGeneratorMultiplier choice)
                d9MatterGammaPositiveEigenvector) := by
          rw [d9MatterGammaPositiveEigenvector_monodromy_neg_one]
        _ =
            d9MatterComplexAction
              (normalRootSpinFrameGeneratorMultiplier choice)
              (d9MatterSpinorMonodromy choice (-(winding : Int))
                d9MatterGammaPositiveEigenvector) :=
          d9MatterSpinorMonodromy_complexAction _ _ _ _
        _ =
            d9MatterComplexAction
              (normalRootSpinFrameGeneratorMultiplier choice)
              (d9MatterComplexAction
                (normalRootSpinFrameGeneratorMultiplier choice ^
                  (-(winding : Int)))
                d9MatterGammaPositiveEigenvector) := by
          rw [ih]
        _ =
            d9MatterComplexAction
              (normalRootSpinFrameGeneratorMultiplier choice ^
                (-(winding : Int) - 1))
              d9MatterGammaPositiveEigenvector := by
          rw [← d9MatterComplexAction_mul]
          rw [zpow_sub_one₀
              (normalRootSpinFrameGeneratorMultiplier_ne_zero choice),
            normalRootSpinFrameGeneratorMultiplier_inv,
            mul_comm]

/-- The smooth matter coefficient of a normal-root Fourier mode upstairs. -/
def normalRootMatterModeValue
    (choice : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) : MatterFiber :=
  d9MatterGammaPositiveEigenlineCLM
    (normalRootSpinFramePhase period hPeriod choice mode point)

theorem normalRootMatterModeValue_contMDiff
    (choice : NormalRootChoice) (mode : Int) :
    ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real MatterFiber) ∞
      (normalRootMatterModeValue period hPeriod choice mode) := by
  exact d9MatterGammaPositiveEigenlineCLM.contDiff.contMDiff.comp
    (normalRootSpinFramePhase_contMDiff
      period hPeriod choice mode)

theorem normalRootMatterModeValue_deck
    (choice : NormalRootChoice) (mode winding : Int)
    (point : ThroatCover period hPeriod) :
    normalRootMatterModeValue period hPeriod choice mode
        (winding +ᵥ point) =
      d9MatterSpinorMonodromy choice winding
        (normalRootMatterModeValue
          period hPeriod choice mode point) := by
  simp only [normalRootMatterModeValue,
    d9MatterGammaPositiveEigenlineCLM_apply]
  rw [normalRootSpinFramePhase_deck,
    d9MatterSpinorMonodromy_complexAction,
    d9MatterGammaPositiveEigenvector_monodromy,
    ← d9MatterComplexAction_mul,
    mul_comm]

/-- Genuine smooth matter lift in either quarter-root sector. -/
def normalRootMatterModeLift
    (choice : NormalRootChoice) (mode : Int) :
    SmoothThroatMatterSpinorLift period hPeriod choice where
  toFun := normalRootMatterModeValue period hPeriod choice mode
  contMDiff_toFun :=
    normalRootMatterModeValue_contMDiff
      period hPeriod choice mode
  deck_equivariant := by
    intro winding point
    rw [throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
    exact normalRootMatterModeValue_deck
      period hPeriod choice mode winding point

/-- Put either normal-root tower into its corresponding component of the
fixed positive-quarter doubled bundle. -/
def primitiveSpinCNormalModeDoubledLift
    (sector : NormalRootChoice) (mode : Int) :
    SmoothThroatDoubledMatterSpinorLift
      period hPeriod .positiveQuarter :=
  match sector with
  | .positiveQuarter =>
      { first :=
          normalRootMatterModeLift
            period hPeriod .positiveQuarter mode
        second := 0 }
  | .negativeQuarter =>
      { first := 0
        second :=
          normalRootMatterModeLift
            period hPeriod .negativeQuarter mode }

/-- Local gauges of the global primitive SpinC zero-sphere mode. -/
def primitiveSpinCGeometricZeroModeLocalGaugeFamily
    (sector : NormalRootChoice) (mode : Int) :
    SmoothPrimitiveSpinCLocalGaugeFamily
      period hPeriod .positiveQuarter :=
  primitiveSpinCTensorLocalGaugeFamily
    period hPeriod .positiveQuarter
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode)
    primitiveMonopoleZeroLocalScalarFamily

/-- Explicit global smooth primitive SpinC section: the charge-one Hopf zero
mode tensored with a quarter-shifted normal-root Fourier mode. -/
def primitiveSpinCGeometricZeroModeSection
    (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (primitiveSpinCGeometricZeroModeLocalGaugeFamily
    period hPeriod sector mode).toSmoothSection
      period hPeriod .positiveQuarter

/-- Constant complex multiples of the explicit matter modes. -/
def normalRootScaledMatterModeValue
    (coefficient : Complex)
    (choice : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) : MatterFiber :=
  d9MatterGammaPositiveEigenlineCLM
    (coefficient *
      normalRootSpinFramePhase period hPeriod choice mode point)

/-- Real and imaginary representatives reconstruct an arbitrary complex
multiple of the matter mode. -/
theorem normalRootScaledMatterModeValue_eq_re_im
    (coefficient : Complex)
    (choice : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    coefficient.re •
          normalRootMatterModeValue
            period hPeriod choice mode point +
        coefficient.im •
          normalRootScaledMatterModeValue
            period hPeriod Complex.I choice mode point =
      normalRootScaledMatterModeValue
        period hPeriod coefficient choice mode point := by
  simp only [normalRootMatterModeValue,
    normalRootScaledMatterModeValue]
  rw [← map_smul, ← map_smul, ← map_add]
  apply congrArg d9MatterGammaPositiveEigenlineCLM
  change
    (coefficient.re : Complex) *
          normalRootSpinFramePhase period hPeriod choice mode point +
        (coefficient.im : Complex) *
          (Complex.I *
            normalRootSpinFramePhase period hPeriod choice mode point) =
      coefficient *
        normalRootSpinFramePhase period hPeriod choice mode point
  rw [← mul_assoc, ← add_mul]
  congr 1
  apply Complex.ext <;> simp

theorem normalRootScaledMatterModeValue_contMDiff
    (coefficient : Complex)
    (choice : NormalRootChoice) (mode : Int) :
    ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real MatterFiber) ∞
      (normalRootScaledMatterModeValue
        period hPeriod coefficient choice mode) := by
  exact d9MatterGammaPositiveEigenlineCLM.contDiff.contMDiff.comp
    (by
      simpa only [Function.comp_def,
        normalModeComplexRightMulRealCLM_apply, mul_comm] using
        (normalModeComplexRightMulRealCLM coefficient).contMDiff.comp
          (normalRootSpinFramePhase_contMDiff
            period hPeriod choice mode))

theorem normalRootScaledMatterModeValue_deck
    (coefficient : Complex)
    (choice : NormalRootChoice) (mode winding : Int)
    (point : ThroatCover period hPeriod) :
    normalRootScaledMatterModeValue
        period hPeriod coefficient choice mode (winding +ᵥ point) =
      d9MatterSpinorMonodromy choice winding
        (normalRootScaledMatterModeValue
          period hPeriod coefficient choice mode point) := by
  simp only [normalRootScaledMatterModeValue,
    d9MatterGammaPositiveEigenlineCLM_apply]
  rw [normalRootSpinFramePhase_deck,
    d9MatterSpinorMonodromy_complexAction,
    d9MatterGammaPositiveEigenvector_monodromy,
    ← d9MatterComplexAction_mul]
  apply congrArg
    (fun scalar : Complex =>
      d9MatterComplexAction scalar d9MatterGammaPositiveEigenvector)
  ring

def normalRootScaledMatterModeLift
    (coefficient : Complex)
    (choice : NormalRootChoice) (mode : Int) :
    SmoothThroatMatterSpinorLift period hPeriod choice where
  toFun :=
    normalRootScaledMatterModeValue
      period hPeriod coefficient choice mode
  contMDiff_toFun :=
    normalRootScaledMatterModeValue_contMDiff
      period hPeriod coefficient choice mode
  deck_equivariant := by
    intro winding point
    rw [throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
    exact normalRootScaledMatterModeValue_deck
      period hPeriod coefficient choice mode winding point

def primitiveSpinCScaledNormalModeDoubledLift
    (coefficient : Complex)
    (sector : NormalRootChoice) (mode : Int) :
    SmoothThroatDoubledMatterSpinorLift
      period hPeriod .positiveQuarter :=
  match sector with
  | .positiveQuarter =>
      { first :=
          normalRootScaledMatterModeLift
            period hPeriod coefficient .positiveQuarter mode
        second := 0 }
  | .negativeQuarter =>
      { first := 0
        second :=
          normalRootScaledMatterModeLift
            period hPeriod coefficient .negativeQuarter mode }

def primitiveSpinCGeometricScaledZeroModeSection
    (coefficient : Complex)
    (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (primitiveSpinCTensorLocalGaugeFamily
    period hPeriod .positiveQuarter
    (primitiveSpinCScaledNormalModeDoubledLift
      period hPeriod coefficient sector mode)
    primitiveMonopoleZeroLocalScalarFamily).toSmoothSection
      period hPeriod .positiveQuarter

/-- Second real representative of a complex zero-tower coordinate. -/
def primitiveSpinCGeometricZeroModeImaginarySection
    (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  primitiveSpinCGeometricScaledZeroModeSection
    period hPeriod Complex.I sector mode

end
end P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
end JanusFormal
