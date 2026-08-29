import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCompatibilityOperators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevPhysicalQuotient

/-!
# Completed Program-P compatibility complex

The genuine mapping-torus part consists of the covariant
curvature--Bianchi complex, the physical `L²` abelian gauge differential with
its exact global `H⁰`, quotient and closed exact-range completion, and the
common intrinsic Dirichlet domain.

The complete four-dimensional Fourier--Sobolev Saint--Venant complex is kept
as an auxiliary principal-symbol model.  It is not identified with the
physical mapping torus.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCompatibilityComplex4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness
open P0EFTJanusShiftedSobolevLatticeLorentzGram
open P0EFTJanusShiftedSobolevPhysicalQuotient
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCompatibilityOperators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeGlobalH04D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusCommonPairedD9GlobalAbelianH04D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Fixed positive weight for the auxiliary lattice compatibility complex. -/
def globalCompatibilityWeight (_mode : LatticeMode) : Real := 1

theorem globalCompatibilityWeight_pos
    (mode : LatticeMode) :
    0 < globalCompatibilityWeight mode := by
  norm_num [globalCompatibilityWeight]

abbrev GlobalCompatibilityPotentialH1 :=
  ShiftedPotentialHilbert globalCompatibilityWeight

abbrev GlobalCompatibilityMetricL2 :=
  SobolevMetricHilbert globalCompatibilityWeight

/-- Bounded order-one Gram Jacobian on the completed Sobolev scale. -/
def DK_Gram_Sobolev :
    GlobalCompatibilityPotentialH1 →L[Real]
      GlobalCompatibilityMetricL2 :=
  shiftedSobolevLorentzGram globalCompatibilityWeight

/-- Saint--Venant compatibility operator on decoded physical metric
coefficients. -/
def K_SV_Sobolev
    (tensor : GlobalCompatibilityMetricL2) :
    LatticeCurvatureCoefficient :=
  latticeSaintVenant
    (decodeWeightedMetric globalCompatibilityWeight
      globalCompatibilityWeight_pos tensor)

/-- The normed quotient by the complete zero-mode kernel. -/
abbrev GlobalCompatibilitySobolevQuotient :=
  PhysicalPotentialQuotient globalCompatibilityWeight

/-- Canonical zero-free representative space of that quotient. -/
abbrev GlobalCompatibilityZeroFreeRepresentatives :=
  ZeroFreePotentialSubspace globalCompatibilityWeight

/-- The completed Gram image remains Saint--Venant compatible. -/
theorem K_SV_Sobolev_comp_DK_Gram_Sobolev_eq_zero
    (potential : GlobalCompatibilityPotentialH1) :
    K_SV_Sobolev (DK_Gram_Sobolev potential) = 0 := by
  let sourceWeight :=
    symbolShiftedSourceWeight globalCompatibilityWeight
  have hSourceWeight : ∀ mode, 0 < sourceWeight mode := by
    intro mode
    exact symbolShiftedSourceWeight_pos globalCompatibilityWeight
      globalCompatibilityWeight_pos mode
  let decoded :=
    decodeWeightedPotential sourceWeight hSourceWeight potential
  have hDecoded :=
    decodedPotential_mem_weightedL2 sourceWeight hSourceWeight potential
  have hEncode :
      encodeWeightedPotential sourceWeight decoded hDecoded = potential := by
    exact encode_decode_weightedPotential sourceWeight hSourceWeight potential
  rw [← hEncode]
  unfold DK_Gram_Sobolev
  rw [shiftedSobolevLorentzGram_encode_eq]
  unfold K_SV_Sobolev
  rw [decode_encode_weightedMetric]
  exact latticeSaintVenant_latticeLorentzGram_eq_zero decoded

/-- The physical quotient has canonical zero-free representatives. -/
def globalCompatibilityPhysicalQuotientEquiv :
    GlobalCompatibilitySobolevQuotient ≃L[Real]
      GlobalCompatibilityZeroFreeRepresentatives :=
  physicalQuotientEquivZeroFree globalCompatibilityWeight

/-- Complete auxiliary lattice symbol/Sobolev certificate. -/
theorem auxiliary_lattice_compatibility_complex_gate :
    (∀ potential : GlobalCompatibilityPotentialH1,
        K_SV_Sobolev (DK_Gram_Sobolev potential) = 0) ∧
      (potentialZeroModeProjection globalCompatibilityWeight).range =
        (DK_Gram_Sobolev).ker ∧
      Nonempty
        (GlobalCompatibilitySobolevQuotient ≃L[Real]
          GlobalCompatibilityZeroFreeRepresentatives) ∧
      (weightedLorentzGramLinearMap globalCompatibilityWeight).range =
        CompatibleZeroFreeMetricSubspace globalCompatibilityWeight ∧
      IsClosed
        (GlobalBulkDirichletHilbertH1 period hPeriod :
          Set (GlobalBulkHilbertH1 period hPeriod)) := by
  exact ⟨K_SV_Sobolev_comp_DK_Gram_Sobolev_eq_zero,
    zeroModeProjection_range_eq_symbol_ker globalCompatibilityWeight,
    ⟨globalCompatibilityPhysicalQuotientEquiv⟩,
    weightedLorentzGram_range_eq_compatibleZeroFree
      globalCompatibilityWeight,
    globalBulkDirichletHilbertH1_isClosed period hPeriod⟩

/-- Physical compatibility closure on the genuine mapping torus.  The
curvature identity is the covariant nonlinear Bianchi complex; the
cohomological statement is for the actual linear `U(1)²` gauge differential.
No flat-torus identification is used. -/
theorem global_physical_compatibility_complex_gate
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    (∀ patch : SmoothHolonomicFrameChart4 period hPeriod,
      ∀ coordinate : IntrinsicVector4,
      ∀ first second third : IntrinsicIndex4,
        B_Bianchi period hPeriod metric (K_SV period hPeriod metric)
          patch coordinate first second third = 0) ∧
      LinearMap.ker (physicalPairedGaugeDifferentialL2 period hPeriod) =
        CommonPairedD9GlobalAbelianGhostZeroMode period hPeriod ∧
      Nonempty
        (PhysicalPairedGaugeSobolevCoreQuotient period hPeriod ≃ₗ[Real]
          LinearMap.range
            (physicalPairedGaugeDifferentialL2 period hPeriod)) ∧
      IsClosed
        (PhysicalPairedExactGaugeSobolev period hPeriod :
          Set (PhysicalPairedGaugeOneFormL2 period hPeriod)) ∧
      (∀ ghosts : PhysicalPairedGaugeGhost period hPeriod,
        physicalPairedGaugeDifferentialL2 period hPeriod ghosts ∈
          PhysicalPairedExactGaugeSobolev period hPeriod) ∧
      Nonempty
        (LinearMap.ker
            (physicalPairedGaugeDifferentialL2 period hPeriod) ≃ₗ[Real]
          GaugeLieAlgebra × GaugeLieAlgebra) ∧
      IsClosed
        (GlobalBulkDirichletHilbertH1 period hPeriod :
          Set (GlobalBulkHilbertH1 period hPeriod)) := by
  exact ⟨fun patch coordinate first second third =>
      B_Bianchi_comp_K_SV_eq_zero period hPeriod metric patch coordinate
        first second third,
    physicalPairedGaugeDifferentialL2_kernel_eq_globalZeroMode period hPeriod,
    ⟨physicalPairedGaugeSobolevCoreQuotientEquivRange period hPeriod⟩,
    physicalPairedExactGaugeSobolev_isClosed period hPeriod,
    physicalPairedGaugeDifferentialL2_mem_completion period hPeriod,
    ⟨physicalPairedGaugeZeroModeLinearEquiv period hPeriod⟩,
    globalBulkDirichletHilbertH1_isClosed period hPeriod⟩

/-- Combined physical gate plus the explicitly separate lattice-symbol
certificate. -/
theorem global_compatibility_complex_gate
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ((∀ patch : SmoothHolonomicFrameChart4 period hPeriod,
      ∀ coordinate : IntrinsicVector4,
      ∀ first second third : IntrinsicIndex4,
        B_Bianchi period hPeriod metric (K_SV period hPeriod metric)
          patch coordinate first second third = 0) ∧
      LinearMap.ker (physicalPairedGaugeDifferentialL2 period hPeriod) =
        CommonPairedD9GlobalAbelianGhostZeroMode period hPeriod ∧
      Nonempty
        (PhysicalPairedGaugeSobolevCoreQuotient period hPeriod ≃ₗ[Real]
          LinearMap.range
            (physicalPairedGaugeDifferentialL2 period hPeriod)) ∧
      IsClosed
        (PhysicalPairedExactGaugeSobolev period hPeriod :
          Set (PhysicalPairedGaugeOneFormL2 period hPeriod)) ∧
      (∀ ghosts : PhysicalPairedGaugeGhost period hPeriod,
        physicalPairedGaugeDifferentialL2 period hPeriod ghosts ∈
          PhysicalPairedExactGaugeSobolev period hPeriod) ∧
      Nonempty
        (LinearMap.ker
            (physicalPairedGaugeDifferentialL2 period hPeriod) ≃ₗ[Real]
          GaugeLieAlgebra × GaugeLieAlgebra) ∧
      IsClosed
        (GlobalBulkDirichletHilbertH1 period hPeriod :
          Set (GlobalBulkHilbertH1 period hPeriod))) ∧
    ((∀ potential : GlobalCompatibilityPotentialH1,
        K_SV_Sobolev (DK_Gram_Sobolev potential) = 0) ∧
      (potentialZeroModeProjection globalCompatibilityWeight).range =
        (DK_Gram_Sobolev).ker ∧
      Nonempty
        (GlobalCompatibilitySobolevQuotient ≃L[Real]
          GlobalCompatibilityZeroFreeRepresentatives) ∧
      (weightedLorentzGramLinearMap globalCompatibilityWeight).range =
        CompatibleZeroFreeMetricSubspace globalCompatibilityWeight ∧
      IsClosed
        (GlobalBulkDirichletHilbertH1 period hPeriod :
          Set (GlobalBulkHilbertH1 period hPeriod))) := by
  exact ⟨global_physical_compatibility_complex_gate period hPeriod metric,
    auxiliary_lattice_compatibility_complex_gate period hPeriod⟩

end
end P0EFTJanusProgramPGlobalCompatibilityComplex4D
end JanusFormal
