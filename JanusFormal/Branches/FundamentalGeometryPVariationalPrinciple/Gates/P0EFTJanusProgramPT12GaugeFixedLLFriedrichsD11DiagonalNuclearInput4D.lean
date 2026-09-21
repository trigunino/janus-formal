import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsAmbientHilbertBasis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFriedrichsShiftedInverseSquare4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicDiagonalNuclear4D

/-!
# Diagonal D11 logarithmic factor on the ambient Friedrichs basis

The D11 variation vanishes on both realified spectral copies.  On an LL
eigenvector it is diagonal with coefficient
`(2 * a) * (lambda + a ^ 2)⁻¹`.  Thus only an LL-indexed weighted summability
hypothesis remains for the physical relative sandwich.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsD11DiagonalNuclearInput4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap Topology
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsAmbientHilbertBasis4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreenDifferentiable4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicDiagonalNuclear4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicFactorization4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicNuclear4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLFriedrichsShiftedInverseSquare4D
open P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

local instance programPT12D11DiagonalModeDecidableEq
    (iota : Type) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

variable (period : Real) (hPeriod : period ≠ 0)

/-- Mode type of the realified spectral block and LL eigenblock. -/
abbrev ProgramPT12GaugeFixedLLFriedrichsD11DiagonalMode
    (iota LLMode : Type) :=
  (ProgramPGlobalGaugeFixedSpectralHessianMode iota ⊕
    ProgramPGlobalGaugeFixedSpectralHessianMode iota) ⊕ LLMode

/-- Diagonal coefficient of `G₁₁(a) A₁₁'(a)`. -/
def programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient
    {configuration : GlobalFieldConfiguration period hPeriod}
    {LLMode : Type} [DecidableEq LLMode]
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    {iota : Type}
    (parameter : Real) :
    ProgramPT12GaugeFixedLLFriedrichsD11DiagonalMode iota LLMode → Real
  | .inl _ => 0
  | .inr mode =>
      (2 * parameter) *
        (llSpectral.eigenvalue mode + parameter ^ 2)⁻¹

/-- The D11 LL resolvent is diagonal in the supplied Friedrichs basis. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_on_basis
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (parameter : Real) (mode : LLMode) :
    programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter (llSpectral.basis mode) =
      (llSpectral.eigenvalue mode + parameter ^ 2)⁻¹ •
        llSpectral.basis mode := by
  simpa [programPT12GaugeFixedLLFriedrichsD11LLResolvent,
    programPT12GaugeFixedLLFriedrichsD11Shift] using
    (P0EFTJanusProgramPT12LLFriedrichsShiftedInverseSquare4D.CanonicalLLFriedrichsInverseSquareData.shiftedResolvent_on_basis
        period hPeriod llSpectral
      (parameter ^ 2) (sq_nonneg parameter) mode)

@[simp]
theorem programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis_spectral
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (mode : ProgramPGlobalGaugeFixedSpectralHessianMode iota ⊕
      ProgramPGlobalGaugeFixedSpectralHessianMode iota) :
    programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
        period hPeriod analysis llSpectral (.inl mode) =
      WithLp.toLp 2
        (complexHilbertBasisToReal
            (complexDiagonalBasis
              (ProgramPGlobalGaugeFixedSpectralHessianMode iota))
            (fun _ _ => real_inner_eq_re_inner Complex _ _) mode,
          (0 : CanonicalLLL2 period hPeriod analysis)) := by
  change
    hilbertBasisL2Product
        (complexHilbertBasisToReal
          (complexDiagonalBasis
            (ProgramPGlobalGaugeFixedSpectralHessianMode iota))
          (fun _ _ => real_inner_eq_re_inner Complex _ _))
        llSpectral.basis (.inl mode) = _
  rw [hilbertBasisL2Product_apply]
  rfl

@[simp]
theorem programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (mode : LLMode) :
    programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
        (iota := iota) period hPeriod analysis llSpectral (.inr mode) =
      WithLp.toLp 2
        ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota),
          llSpectral.basis mode) := by
  change
    hilbertBasisL2Product
        (complexHilbertBasisToReal
          (complexDiagonalBasis
            (ProgramPGlobalGaugeFixedSpectralHessianMode iota))
          (fun _ _ => real_inner_eq_re_inner Complex _ _))
        llSpectral.basis (.inr mode) = _
  rw [hilbertBasisL2Product_apply]
  rfl

/-- The spectral part of the ambient basis is killed by the D11 variation. -/
@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11Variation_on_spectral_basis
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (parameter : Real)
    (mode : ProgramPGlobalGaugeFixedSpectralHessianMode iota ⊕
      ProgramPGlobalGaugeFixedSpectralHessianMode iota) :
    programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter
        (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
          period hPeriod analysis llSpectral (.inl mode)) = 0 := by
  rw [programPT12GaugeFixedLLFriedrichsD11VariationOperator_apply]
  simp

/-- The LL part of the ambient basis is multiplied by `2a` by the variation. -/
@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11Variation_on_ll_basis
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (parameter : Real) (mode : LLMode) :
    programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter
        (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
          period hPeriod analysis llSpectral (.inr mode)) =
      WithLp.toLp 2
        ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota),
          (2 * parameter) • llSpectral.basis mode) := by
  rw [programPT12GaugeFixedLLFriedrichsD11VariationOperator_apply]
  simp

/-- Before stabilization, the Green block composed with the variation is
already diagonal in the full ambient basis. -/
theorem programPT12GaugeFixedLLFriedrichsD11Green_comp_variation_on_basis
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (parameter : Real)
    (mode : ProgramPT12GaugeFixedLLFriedrichsD11DiagonalMode iota LLMode) :
    (programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter).comp
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter)
      (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
        period hPeriod analysis llSpectral mode) =
      programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient
          (iota := iota) period hPeriod llSpectral parameter mode •
        programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
          period hPeriod analysis llSpectral mode := by
  rcases mode with mode | mode
  · rw [ContinuousLinearMap.comp_apply,
      programPT12GaugeFixedLLFriedrichsD11Variation_on_spectral_basis,
      map_zero]
    simp [programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient]
  · rw [ContinuousLinearMap.comp_apply,
      programPT12GaugeFixedLLFriedrichsD11Variation_on_ll_basis]
    simp only [programPT12GaugeFixedLLFriedrichsD11GreenOperator,
      withLpTwoProdMap_apply, map_zero, map_smul]
    rw [programPT12GaugeFixedLLFriedrichsD11LLResolvent_on_basis,
      programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis_ll]
    simp [programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient, smul_smul]
    rw [← WithLp.toLp_smul]
    congr 1
    simp

/-- Stabilization does not change the diagonal formula because the kernel
projection vanishes after the D11 variation. -/
theorem programPT12GaugeFixedLLFriedrichsD11Stabilized_comp_variation_on_basis
    {couplings : GlobalCandidateAActionCouplings}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {iota : Type} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (parameter : Real)
    (mode : ProgramPT12GaugeFixedLLFriedrichsD11DiagonalMode iota LLMode) :
    ((programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          parameter).comp
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter))
      (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
        period hPeriod analysis llSpectral mode) =
      programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient
          (iota := iota) period hPeriod llSpectral parameter mode •
        programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
          period hPeriod analysis llSpectral mode := by
  let basis := programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
    (iota := iota) period hPeriod analysis llSpectral
  let variation := programPT12GaugeFixedLLFriedrichsD11VariationOperator
    (iota := iota) period hPeriod analysis parameter
  let kernel := programPT12GaugeFixedLLFriedrichsD11KernelProjection
    period hPeriod covector couplings.matterMassSquared analysis
  have hKernelComposition :=
    programPT12GaugeFixedLLFriedrichsD11KernelProjection_comp_variation
      (couplings := couplings) period hPeriod configuration analysis covector
        parameter
  have hKernel : kernel (variation (basis mode)) = 0 := by
    have hApply := congrArg (fun operator => operator (basis mode))
      hKernelComposition
    simpa [kernel, variation, ContinuousLinearMap.comp_apply] using hApply
  rw [ContinuousLinearMap.comp_apply]
  calc
    programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter (variation (basis mode)) =
        programPT12GaugeFixedLLFriedrichsD11GreenOperator
            period hPeriod d9Ellipticity couplings.matterMassSquared analysis
              parameter (variation (basis mode)) +
          kernel (variation (basis mode)) := rfl
    _ = programPT12GaugeFixedLLFriedrichsD11GreenOperator
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter (variation (basis mode)) := by rw [hKernel, add_zero]
    _ = programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient
          (iota := iota) period hPeriod llSpectral parameter mode •
        basis mode := by
      exact programPT12GaugeFixedLLFriedrichsD11Green_comp_variation_on_basis
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          llSpectral parameter mode

/-- The nonzero LL diagonal coefficients are square summable. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLCoefficient_squareSummable
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (parameter : Real) :
    Summable (fun mode =>
      |(2 * parameter) *
        (llSpectral.eigenvalue mode + parameter ^ 2)⁻¹| ^ 2) := by
  have hSummable :=
    (P0EFTJanusProgramPT12LLFriedrichsShiftedInverseSquare4D.CanonicalLLFriedrichsInverseSquareData.shiftedInverseSquareSummable
        period hPeriod llSpectral
      (parameter ^ 2) (sq_nonneg parameter)).mul_left
        ((2 * parameter) ^ 2)
  apply hSummable.congr
  intro mode
  simp only [abs_mul, abs_inv, mul_pow, sq_abs, inv_pow]

/-- Square summability on the full ambient basis; both spectral copies
contribute the zero series. -/
theorem programPT12GaugeFixedLLFriedrichsD11Coefficient_squareSummable
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {iota : Type}
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (parameter : Real) :
    Summable (fun mode :
      ProgramPT12GaugeFixedLLFriedrichsD11DiagonalMode iota LLMode =>
        |programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient
          (iota := iota) period hPeriod llSpectral parameter mode| ^ 2) := by
  refine Summable.sum
    (fun mode :
      (ProgramPGlobalGaugeFixedSpectralHessianMode iota ⊕
        ProgramPGlobalGaugeFixedSpectralHessianMode iota) ⊕ LLMode =>
      |programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient
        (iota := iota) period hPeriod llSpectral parameter mode| ^ 2) ?_ ?_
  · apply (summable_zero : Summable (fun _ :
      ProgramPGlobalGaugeFixedSpectralHessianMode iota ⊕
        ProgramPGlobalGaugeFixedSpectralHessianMode iota => (0 : Real))).congr
    intro mode
    simp [programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient]
  · apply
      (programPT12GaugeFixedLLFriedrichsD11LLCoefficient_squareSummable
        period hPeriod llSpectral parameter).congr
    intro mode
    rfl

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section Physical

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

/-- Exact LL-supported weighted nuclear input after the D11 diagonal
coefficient has been computed. -/
structure PhysicalRelativeLogarithmicLLDiagonalInput4D
    {iota : Type} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (LLMode : Type) [DecidableEq LLMode] where
  llSpectral : CanonicalLLFriedrichsInverseSquareData
    period hPeriod analysis LLMode
  llWeightedNuclearSummable : ∀ (parameter :
      PhysicalRelativeNondegenerateParameter period hPeriod configuration data
        analysis chart sameAction physical covector),
    Summable (fun mode =>
      |(2 * parameter.1) *
          (llSpectral.eigenvalue mode + parameter.1 ^ 2)⁻¹| *
        ‖programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
            period hPeriod d9Ellipticity couplings.matterMassSquared analysis
              parameter.1
          (programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle
            period hPeriod configuration data analysis chart sameAction physical
              d9Ellipticity parameter.1
            (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
              (iota := iota) period hPeriod analysis llSpectral (.inr mode)))‖)

namespace PhysicalRelativeLogarithmicLLDiagonalInput4D

/-- The convenient stronger LL image-square estimate implies the exact
weighted nuclear input by Holder with the computed coefficient estimate. -/
def ofLLImageSquareSummable
    {iota : Type} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    {LLMode : Type} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (llImageSquareSummable : ∀ (parameter :
        PhysicalRelativeNondegenerateParameter period hPeriod configuration data
          analysis chart sameAction physical covector),
      Summable (fun mode =>
        ‖programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
            period hPeriod d9Ellipticity couplings.matterMassSquared analysis
              parameter.1
          (programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle
            period hPeriod configuration data analysis chart sameAction physical
              d9Ellipticity parameter.1
            (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
              (iota := iota) period hPeriod analysis llSpectral (.inr mode)))‖ ^ 2)) :
    PhysicalRelativeLogarithmicLLDiagonalInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity LLMode where
  llSpectral := llSpectral
  llWeightedNuclearSummable := by
    intro parameter
    let imageNorm : LLMode → Real := fun mode =>
      ‖programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter.1
        (programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter.1
          (programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
            (iota := iota) period hPeriod analysis llSpectral (.inr mode)))‖
    have hCoefficientRpow : Summable (fun mode : LLMode =>
        |(2 * parameter.1) *
          (llSpectral.eigenvalue mode + parameter.1 ^ 2)⁻¹| ^
            (2 : Real)) := by
      simpa only [Real.rpow_two] using
        programPT12GaugeFixedLLFriedrichsD11LLCoefficient_squareSummable
          period hPeriod llSpectral parameter.1
    have hImageRpow : Summable (fun mode : LLMode =>
        imageNorm mode ^ (2 : Real)) := by
      simpa only [Real.rpow_two, imageNorm] using
        llImageSquareSummable parameter
    exact Real.summable_mul_of_Lp_Lq_of_nonneg
      (p := (2 : Real)) (q := (2 : Real))
      (f := fun mode : LLMode =>
        |(2 * parameter.1) *
          (llSpectral.eigenvalue mode + parameter.1 ^ 2)⁻¹|)
      (g := imageNorm)
      Real.HolderConjugate.two_two
      (fun _ => abs_nonneg _)
      (fun _ => norm_nonneg _)
      hCoefficientRpow hImageRpow

/-- The exact LL-only weighted estimate supplies the ambient diagonal nuclear
input; both spectral copies contribute zero. -/
def toDiagonalNuclearInput
    {iota : Type} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    {LLMode : Type} [DecidableEq LLMode]
    (input : PhysicalRelativeLogarithmicLLDiagonalInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity LLMode) :
    PhysicalRelativeLogarithmicDiagonalNuclearInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity
        (ProgramPT12GaugeFixedLLFriedrichsD11DiagonalMode iota LLMode) where
  basis := programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
    period hPeriod analysis input.llSpectral
  coefficient := fun parameter =>
    programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient
      (iota := iota) period hPeriod input.llSpectral parameter.1
  right_on_basis := by
    intro parameter mode
    exact
      programPT12GaugeFixedLLFriedrichsD11Stabilized_comp_variation_on_basis
        period hPeriod configuration analysis d9Ellipticity input.llSpectral
          parameter.1 mode
  weighted_nuclearSummable := by
    intro parameter
    apply Summable.sum _
    · apply (summable_zero : Summable (fun _ :
        ProgramPGlobalGaugeFixedSpectralHessianMode iota ⊕
          ProgramPGlobalGaugeFixedSpectralHessianMode iota => (0 : Real))).congr
      intro mode
      simp [programPT12GaugeFixedLLFriedrichsD11DiagonalCoefficient]
    · apply (input.llWeightedNuclearSummable parameter).congr
      intro mode
      rfl

/-- Public LL-to-diagonal checkpoint. -/
theorem llDiagonalInput_gate
    {iota : Type} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    {LLMode : Type} [DecidableEq LLMode]
    (input : PhysicalRelativeLogarithmicLLDiagonalInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity LLMode) :
    Nonempty
      (PhysicalRelativeLogarithmicDiagonalNuclearInput4D
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity
          (ProgramPT12GaugeFixedLLFriedrichsD11DiagonalMode iota LLMode)) :=
  ⟨input.toDiagonalNuclearInput period hPeriod configuration data analysis
    chart sameAction physical⟩

end PhysicalRelativeLogarithmicLLDiagonalInput4D
end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsD11DiagonalNuclearInput4D
end JanusFormal
