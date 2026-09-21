import Mathlib.Analysis.InnerProductSpace.Spectrum
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D

/-!
# T12 LL Friedrichs spectral heat bridge

The compact inverse already gives finite-dimensional eigenspaces and spectral
completeness.  A summable inverse square of the Friedrichs eigenvalues is the
single quantitative input used here to obtain the positive-time Gaussian heat
sum and the existing `ProgramPLL2EllipticHeatData` package.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal LinearPMap
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl
local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- Nonzero eigenspaces of the compact LL inverse have finite multiplicity. -/
theorem canonicalLLWeakL2Inverse_finiteDimensional_eigenspace
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0) :
    FiniteDimensional Real
      (Module.End.eigenspace
        (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap
        eigenvalue) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (canonicalLLWeakL2Inverse_isCompact period hPeriod analysis)
    eigenvalue hEigenvalue

/-- Compact self-adjoint spectral completeness of the LL inverse. -/
theorem canonicalLLWeakL2Inverse_spectral_complete
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        (canonicalLLWeakL2Inverse period hPeriod analysis).toLinearMap
        eigenvalue).orthogonal = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (canonicalLLWeakL2Inverse_isCompact period hPeriod analysis)
    (canonicalLLWeakL2Inverse_isSelfAdjoint
      period hPeriod analysis).isSymmetric

/-- An eigenbasis of the genuine Friedrichs realization together with the
expected three-dimensional Schatten input `A⁻²` trace class. -/
structure CanonicalLLFriedrichsInverseSquareData
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (Mode : Type*) [DecidableEq Mode] where
  basis : HilbertBasis Mode Real (CanonicalLLL2 period hPeriod analysis)
  eigenvalue : Mode → Real
  basis_mem_domain : ∀ mode,
    basis mode ∈ (canonicalLLFriedrichsJacobi
      period hPeriod analysis).domain
  operator_on_basis : ∀ mode,
    canonicalLLFriedrichsJacobi period hPeriod analysis
        ⟨basis mode, basis_mem_domain mode⟩ =
      eigenvalue mode • basis mode
  eigenvalue_ne_zero : ∀ mode, eigenvalue mode ≠ 0
  inverseSquareSummable :
    Summable (fun mode => (eigenvalue mode ^ 2)⁻¹)

namespace CanonicalLLFriedrichsInverseSquareData

theorem heatSummable
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {Mode : Type*} [DecidableEq Mode]
    (spectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis Mode)
    (time : HeatTime) :
    Summable (fun mode =>
      Real.exp (-time.1 * spectral.eigenvalue mode ^ 2)) := by
  have hMajorant : Summable (fun mode =>
      (Real.exp (-1) * time.1⁻¹) *
        (spectral.eigenvalue mode ^ 2)⁻¹) :=
    spectral.inverseSquareSummable.mul_left
      (Real.exp (-1) * time.1⁻¹)
  apply hMajorant.of_nonneg_of_le
  · intro mode
    exact (Real.exp_pos _).le
  · intro mode
    let energy := spectral.eigenvalue mode ^ 2
    have hEnergy : 0 < energy :=
      sq_pos_of_ne_zero (spectral.eigenvalue_ne_zero mode)
    have hProduct : 0 < time.1 * energy := mul_pos time.2 hEnergy
    calc
      Real.exp (-time.1 * spectral.eigenvalue mode ^ 2) =
          Real.exp (-(time.1 * energy)) := by
            simp only [energy, neg_mul]
      _ ≤ Real.exp (-1) / (time.1 * energy) := by
        apply (le_div_iff₀ hProduct).2
        simpa [mul_comm] using
          Real.mul_exp_neg_le_exp_neg_one (time.1 * energy)
      _ = (Real.exp (-1) * time.1⁻¹) *
          (spectral.eigenvalue mode ^ 2)⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv, energy]
        ring

/-- The Friedrichs realization satisfies the existing LL heat contract once
the inverse-square spectral datum is supplied. -/
def toProgramPLL2EllipticHeatData
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {Mode : Type*} [DecidableEq Mode]
    (spectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis Mode) :
    ProgramPLL2EllipticHeatData period hPeriod
      (analysis.llH1Data period hPeriod) Mode where
  operator := canonicalLLFriedrichsJacobi period hPeriod analysis
  smoothCore :=
    canonicalLLFriedrichsSmoothDomainLinearMap period hPeriod analysis
  smoothCore_coe := by
    intro direction
    exact canonicalLLFriedrichsSmoothDomainElement_value
      period hPeriod analysis direction
  domain_dense :=
    canonicalLLFriedrichsJacobi_domain_dense period hPeriod analysis
  selfAdjoint :=
    canonicalLLFriedrichsJacobi_isSelfAdjoint period hPeriod analysis
  hessian_pairing := by
    intro first second
    change inner Real
        (canonicalLLFriedrichsJacobi period hPeriod analysis
          (canonicalLLFriedrichsSmoothDomainElement
            period hPeriod analysis first))
        (llH1SmoothToFluxL2 period hPeriod
          (analysis.llH1Data period hPeriod) second) = _
    rw [← canonicalLLFriedrichsSmoothDomainElement_value
      period hPeriod analysis second]
    exact canonicalLLFriedrichsJacobi_smooth_pairing
      period hPeriod analysis first second
  referenceParameter := 0
  resolvent := canonicalLLWeakL2Inverse period hPeriod analysis
  resolvent_mem_domain := by
    intro source
    exact (canonicalLLFriedrichsDomainElement
      period hPeriod analysis source).property
  resolvent_right_inverse := by
    intro source
    simp only [zero_smul, sub_zero]
    convert canonicalLLFriedrichsJacobi_on_response
      period hPeriod analysis source using 1
    apply congrArg (canonicalLLFriedrichsJacobi period hPeriod analysis)
    apply Subtype.ext
    rfl
  resolvent_left_inverse := by
    intro field
    simp only [zero_smul, sub_zero]
    exact canonicalLLWeakL2Inverse_friedrichsJacobi
      period hPeriod analysis field
  resolvent_compact :=
    canonicalLLWeakL2Inverse_isCompact period hPeriod analysis
  basis := spectral.basis
  eigenvalue := spectral.eigenvalue
  basis_mem_domain := spectral.basis_mem_domain
  operator_on_basis := spectral.operator_on_basis
  heatSummable := spectral.heatSummable period hPeriod

/-- Positive T12 LL heat/nuclear gate under the single inverse-square Weyl
input, without assuming heat summability itself. -/
theorem nuclearHeat_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    {Mode : Type*} [DecidableEq Mode]
    (spectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis Mode)
    (time : HeatTime) :
    IsCompactOperator
        (programPLL2HeatOperator period hPeriod
          (spectral.toProgramPLL2EllipticHeatData period hPeriod) time) ∧
      Summable (fun mode =>
        ‖programPLL2HeatRankOne period hPeriod
          (spectral.toProgramPLL2EllipticHeatData period hPeriod)
          time mode‖) := by
  exact ⟨programPLL2HeatOperator_isCompact period hPeriod
      (spectral.toProgramPLL2EllipticHeatData period hPeriod) time,
    programPLL2HeatRankOne_norm_summable period hPeriod
      (spectral.toProgramPLL2EllipticHeatData period hPeriod) time⟩

end CanonicalLLFriedrichsInverseSquareData

end
end P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D
end JanusFormal
