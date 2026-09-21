import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

/-!
# T12 LL Friedrichs spectral basis

The compact, self-adjoint, injective LL inverse already determines a complete
Friedrichs eigenbasis.  The Weyl inverse-square summability remains the sole
quantitative input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFriedrichsSpectralBasis4D

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
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

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

/-- The structural spectral packet, without a Weyl summability assumption. -/
structure CanonicalLLFriedrichsSpectralBasisData
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) where
  Mode : Type
  modeDecidableEq : DecidableEq Mode
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

private theorem exists_compact_symmetric_injective_eigenbasis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E]
    (operator : E →L[Real] E)
    (hCompact : IsCompactOperator operator)
    (hSymmetric : operator.IsSymmetric)
    (hInjective : Function.Injective operator) :
    ∃ (Mode : Type) (_ : DecidableEq Mode)
      (basis : HilbertBasis Mode Real E) (eigenvalue : Mode → Real),
      (∀ mode, operator (basis mode) = eigenvalue mode • basis mode) ∧
      (∀ mode, eigenvalue mode ≠ 0) := by
  classical
  let Index : (eigenvalue : Real) →
      Set (Module.End.eigenspace operator.toLinearMap eigenvalue) :=
    fun eigenvalue =>
    Classical.choose
      (exists_hilbertBasis Real
        (Module.End.eigenspace operator.toLinearMap eigenvalue))
  let eigenbasis : ∀ eigenvalue,
      HilbertBasis (Index eigenvalue) Real
        (Module.End.eigenspace operator.toLinearMap eigenvalue) :=
    fun eigenvalue =>
      Classical.choose
        (Classical.choose_spec
          (exists_hilbertBasis Real
            (Module.End.eigenspace operator.toLinearMap eigenvalue)))
  let Mode := Σ eigenvalue, Index eigenvalue
  let vectors : Mode → E := fun mode =>
    ((eigenbasis mode.1 mode.2 :
      Module.End.eigenspace operator.toLinearMap mode.1) : E)
  have hOrthonormal : Orthonormal Real vectors := by
    simpa only [vectors, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] using
      hSymmetric.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
        (fun eigenvalue => (eigenbasis eigenvalue).orthonormal)
  have hSpanOrthogonal :
      (Submodule.span Real (Set.range vectors))ᗮ =
        (⊥ : Submodule Real E) := by
    rw [Submodule.eq_bot_iff]
    intro field hField
    have hAllEigenspaces :
        field ∈ (⨆ eigenvalue : Real,
          Module.End.eigenspace operator.toLinearMap eigenvalue)ᗮ := by
      rw [← Submodule.iInf_orthogonal]
      refine (Submodule.mem_iInf _).mpr ?_
      intro eigenvalue
      let eigenspace :=
        Module.End.eigenspace operator.toLinearMap eigenvalue
      have hInner : ∀ mode : Index eigenvalue,
          inner Real ((eigenbasis eigenvalue mode : eigenspace) : E) field = 0 := by
        intro mode
        exact (Submodule.mem_orthogonal
          (Submodule.span Real (Set.range vectors)) field).mp hField _
          (Submodule.subset_span ⟨⟨eigenvalue, mode⟩, rfl⟩)
      have hProjection : eigenspace.orthogonalProjectionOnto field = 0 := by
        have hSum :=
          (eigenbasis eigenvalue).hasSum_orthogonalProjectionOnto field
        have hZeroSum :
            HasSum (fun _ : Index eigenvalue => (0 : eigenspace))
              (eigenspace.orthogonalProjectionOnto field) := by
          simpa only [hInner, zero_smul] using hSum
        exact hZeroSum.unique hasSum_zero
      exact eigenspace.orthogonalProjectionOnto_eq_zero_iff.mp hProjection
    have hComplete :=
      ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
        hCompact hSymmetric
    simpa only [hComplete, Submodule.mem_bot] using hAllEigenspaces
  let basis : HilbertBasis Mode Real E :=
    HilbertBasis.mkOfOrthogonalEqBot hOrthonormal hSpanOrthogonal
  have hBasisApply : ∀ mode, basis mode = vectors mode := by
    intro mode
    exact congrFun
      (HilbertBasis.coe_mkOfOrthogonalEqBot
        hOrthonormal hSpanOrthogonal) mode
  have hEigen : ∀ mode, operator (basis mode) = mode.1 • basis mode := by
    intro mode
    rw [hBasisApply mode]
    simpa [vectors] using
      (Module.End.mem_eigenspace_iff.mp
        (eigenbasis mode.1 mode.2).property)
  have hEigenvalueNe : ∀ mode : Mode, mode.1 ≠ 0 := by
    intro mode hZero
    have hKernel : operator (basis mode) = operator 0 := by
      rw [hEigen mode, hZero, zero_smul, map_zero]
    exact (basis.orthonormal.ne_zero mode) (hInjective hKernel)
  exact ⟨Mode, Classical.decEq Mode, basis, fun mode => mode.1,
    hEigen, hEigenvalueNe⟩

/-- Compact spectral completeness constructs the full LL Friedrichs eigenbasis;
no Weyl counting input is used. -/
theorem canonicalLLFriedrichsSpectralBasisData_exists
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Nonempty (CanonicalLLFriedrichsSpectralBasisData
      period hPeriod analysis) := by
  obtain ⟨Mode, modeDecidableEq, basis, inverseEigenvalue,
      hInverseEigen, hInverseEigenvalueNe⟩ :=
    exists_compact_symmetric_injective_eigenbasis
      (canonicalLLWeakL2Inverse period hPeriod analysis)
      (canonicalLLWeakL2Inverse_isCompact period hPeriod analysis)
      (canonicalLLWeakL2Inverse_isSelfAdjoint
        period hPeriod analysis).isSymmetric
      (canonicalLLWeakL2Inverse_injective period hPeriod analysis)
  letI : DecidableEq Mode := modeDecidableEq
  have hDomain : ∀ mode,
      basis mode ∈ (canonicalLLFriedrichsJacobi
        period hPeriod analysis).domain := by
    intro mode
    rw [canonicalLLFriedrichsJacobi_domain]
    refine ⟨(inverseEigenvalue mode)⁻¹ • basis mode, ?_⟩
    change canonicalLLWeakL2Inverse period hPeriod analysis
        ((inverseEigenvalue mode)⁻¹ • basis mode) = basis mode
    rw [map_smul, hInverseEigen mode, smul_smul,
      inv_mul_cancel₀ (hInverseEigenvalueNe mode), one_smul]
  have hOperator : ∀ mode,
      canonicalLLFriedrichsJacobi period hPeriod analysis
          ⟨basis mode, hDomain mode⟩ =
        (inverseEigenvalue mode)⁻¹ • basis mode := by
    intro mode
    let source := (inverseEigenvalue mode)⁻¹ • basis mode
    have hResponse :
        canonicalLLWeakL2Inverse period hPeriod analysis source =
          basis mode := by
      dsimp only [source]
      rw [map_smul, hInverseEigen mode, smul_smul,
        inv_mul_cancel₀ (hInverseEigenvalueNe mode), one_smul]
    have hSubtype :
        (⟨basis mode, hDomain mode⟩ :
          (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) =
        canonicalLLFriedrichsDomainElement
          period hPeriod analysis source := by
      apply Subtype.ext
      exact hResponse.symm
    rw [hSubtype, canonicalLLFriedrichsJacobi_on_response]
  exact ⟨{
    Mode := Mode
    modeDecidableEq := modeDecidableEq
    basis := basis
    eigenvalue := fun mode => (inverseEigenvalue mode)⁻¹
    basis_mem_domain := hDomain
    operator_on_basis := hOperator
    eigenvalue_ne_zero := fun mode =>
      inv_ne_zero (hInverseEigenvalueNe mode)
  }⟩

namespace CanonicalLLFriedrichsSpectralBasisData

/-- Adding precisely the inverse-square Weyl estimate recovers the existing
heat/nuclear spectral datum. -/
def toInverseSquareData
    {configuration : GlobalFieldConfiguration period hPeriod}
    {analysis : GlobalAnalysisData period hPeriod configuration}
    (spectral : CanonicalLLFriedrichsSpectralBasisData
      period hPeriod analysis)
    (inverseSquareSummable :
      Summable (fun mode => (spectral.eigenvalue mode ^ 2)⁻¹)) :
    letI := spectral.modeDecidableEq
    CanonicalLLFriedrichsInverseSquareData period hPeriod analysis
      spectral.Mode := by
  letI := spectral.modeDecidableEq
  exact {
    basis := spectral.basis
    eigenvalue := spectral.eigenvalue
    basis_mem_domain := spectral.basis_mem_domain
    operator_on_basis := spectral.operator_on_basis
    eigenvalue_ne_zero := spectral.eigenvalue_ne_zero
    inverseSquareSummable := inverseSquareSummable
  }

end CanonicalLLFriedrichsSpectralBasisData

end
end P0EFTJanusProgramPT12LLFriedrichsSpectralBasis4D
end JanusFormal
