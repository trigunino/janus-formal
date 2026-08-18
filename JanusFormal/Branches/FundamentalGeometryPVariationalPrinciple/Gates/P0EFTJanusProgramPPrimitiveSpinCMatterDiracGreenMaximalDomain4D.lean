import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D

/-!
# Dirac Green identity to the smooth maximal SpinC matter graph

The previous maximal-domain gate isolated two analytic assertions for the
smooth primitive SpinC core and kept a separate same-action pairing.  This file
shows that all three statements follow from one mass-independent geometric
input: formal symmetry of the genuine first-order Dirac operator for the
intrinsic geometric `L²` pairing.

The signed-mode unitary identifies canonical coefficients with pairings against
normalized smooth eigensections.  The Green identity therefore gives the
exact diagonal multiplier relation.  The Fourier transform of the genuine
smooth differential expression supplies the maximal-domain image witness;
unitary conjugacy gives operator agreement.  Parseval then gives the two-sector
same-action pairing.  No independently selected coefficient sequence, domain
witness or second action is retained.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open scoped ENNReal lp LinearPMap InnerProductSpace BigOperators
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SignedMode := PrimitiveSpinCGeometricSignedMode
private abbrev OneSectorSmooth :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter
private abbrev MatterSmooth :=
  ProgramPPrimitiveSpinCMatterSmoothField period hPeriod
private abbrev MatterCoefficients :=
  ProgramPPrimitiveSpinCMatterHilbert

local instance matterCoefficientsRealInnerProductSpace :
    InnerProductSpace Real MatterCoefficients :=
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

/-! ## Canonical coefficients are geometric mode pairings -/

/-- A canonical signed Fourier coefficient is exactly the intrinsic geometric
`L²` pairing with the corresponding normalized smooth eigensection. -/
theorem primitiveSpinCOneSectorCanonicalFourierCoefficients_eq_modePairing
    (field : OneSectorSmooth period hPeriod) (mode : SignedMode) :
    primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod field
        mode =
      d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracModeSmoothVector period hPeriod mode)
        field := by
  let unitary :=
    primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod
  let basis := complexDiagonalBasis SignedMode mode
  change
    unitary.symm
        (d9PrimitiveSpinCGeometricL2Embedding period hPeriod
          .positiveQuarter field) mode = _
  calc
    _ = inner Complex basis
          (unitary.symm
            (d9PrimitiveSpinCGeometricL2Embedding period hPeriod
              .positiveQuarter field)) := by
      symm
      exact complexDiagonalBasis_inner_left SignedMode mode _
    _ = inner Complex
          (unitary basis)
          (unitary
            (unitary.symm
              (d9PrimitiveSpinCGeometricL2Embedding period hPeriod
                .positiveQuarter field))) := by
      rw [LinearIsometryEquiv.inner_map_map]
    _ = inner Complex
          (primitiveSpinCGeometricSignedDiracModeVector period hPeriod mode)
          (d9PrimitiveSpinCGeometricL2Embedding period hPeriod
            .positiveQuarter field) := by
      rw [show basis = lp.single 2 mode (1 : Complex) by
          exact complexDiagonalBasis_eq_single SignedMode mode,
        primitiveSpinCGeometricSignedDiracModeUnitary_single,
        unitary.apply_symm_apply]
      simp
    _ = _ := by
      change
        inner Complex
            ((primitiveSpinCGeometricSignedDiracModeSmoothVector
              period hPeriod mode :
                D9PrimitiveSpinCGeometricL2Completion period hPeriod
                  .positiveQuarter))
            (field : D9PrimitiveSpinCGeometricL2Completion period hPeriod
              .positiveQuarter) =
          inner Complex
            (primitiveSpinCGeometricSignedDiracModeSmoothVector
              period hPeriod mode) field
      exact UniformSpace.Completion.inner_coe _ _

/-! ## One mass-independent Green identity -/

/-- The irreducible SpinC analytic input: the genuine first-order primitive
Dirac operator is formally symmetric on the complete smooth bundle core. -/
structure ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D : Prop where
  pairing_symm :
    ∀ first second : OneSectorSmooth period hPeriod,
      d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter first
          (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod second) =
        d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter
          (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod first)
          second

/-- Formal symmetry of the first-order Dirac operator implies formal symmetry
of `2D + m²` for every real mass parameter. -/
theorem primitiveSpinCSmoothActionHessian_pairing_symm_of_dirac
    (massSquared : Real)
    (diracSymmetry :
      ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod)
    (first second : OneSectorSmooth period hPeriod) :
    d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter first
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared second) =
      d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared first) second := by
  unfold primitiveSpinCGeometricSignedActionHessianSmoothCore
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  simp_rw [d9PrimitiveSpinCGeometricL2_complex_smul]
  rw [d9PrimitiveSpinCGeometricL2Pairing_add_right,
    d9PrimitiveSpinCGeometricL2Pairing_complexScalar_right,
    d9PrimitiveSpinCGeometricL2Pairing_complexScalar_right,
    d9PrimitiveSpinCGeometricL2Pairing_add_left,
    d9PrimitiveSpinCGeometricL2Pairing_complexScalar_left,
    d9PrimitiveSpinCGeometricL2Pairing_complexScalar_left,
    diracSymmetry.pairing_symm first second]
  have hTwo : (starRingEnd Complex) (2 : Complex) = 2 := by
    exact map_ofNat (starRingEnd Complex) 2
  have hMass : (starRingEnd Complex) (massSquared : Complex) = massSquared := by
    simp
  rw [hTwo, hMass]

/-- The Green identity forces the exact signed coefficient multiplier relation
for the genuine smooth Hessian. -/
theorem primitiveSpinCSmoothActionHessian_coefficients_of_dirac
    (massSquared : Real)
    (diracSymmetry :
      ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod)
    (field : OneSectorSmooth period hPeriod) (mode : SignedMode) :
    primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field) mode =
      ((primitiveSpinCGeometricSignedKineticHessianWeight period hPeriod mode +
        massSquared : Real) : Complex) *
        primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod field
          mode := by
  rw [primitiveSpinCOneSectorCanonicalFourierCoefficients_eq_modePairing,
    primitiveSpinCOneSectorCanonicalFourierCoefficients_eq_modePairing,
    primitiveSpinCSmoothActionHessian_pairing_symm_of_dirac period hPeriod
      massSquared diracSymmetry
      (primitiveSpinCGeometricSignedDiracModeSmoothVector period hPeriod mode)
      field,
    primitiveSpinCGeometricSignedActionHessianSmoothCore_mode,
    d9PrimitiveSpinCGeometricL2_complex_smul,
    d9PrimitiveSpinCGeometricL2Pairing_complexScalar_left]
  simp

/-! ## Maximal-domain membership and operator restriction -/

/-- The Fourier transform of the genuine smooth differential expression is the
square-summable image witness required by the maximal diagonal domain. -/
theorem primitiveSpinCSmooth_mem_maximalDomain_of_dirac
    (massSquared : Real)
    (diracSymmetry :
      ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod)
    (field : OneSectorSmooth period hPeriod) :
    d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter field ∈
      primitiveSpinCGeometricSignedActionHessianGeometricDomain period hPeriod
        massSquared := by
  change
    (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm
        (d9PrimitiveSpinCGeometricL2Embedding period hPeriod
          .positiveQuarter field) ∈
      (primitiveSpinCGeometricSignedActionHessianOperator period hPeriod
        massSquared).domain
  refine
    ⟨primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field), ?_⟩
  intro mode
  simpa [primitiveSpinCOneSectorCanonicalFourierCoefficients] using
    primitiveSpinCSmoothActionHessian_coefficients_of_dirac period hPeriod
      massSquared diracSymmetry field mode

/-- The maximal geometric operator restricts exactly to the genuine smooth
`2D + m²` expression. -/
theorem primitiveSpinCSmooth_maximalOperator_agrees_of_dirac
    (massSquared : Real)
    (diracSymmetry :
      ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod)
    (field : OneSectorSmooth period hPeriod) :
    primitiveSpinCGeometricSignedActionHessianGeometricOperator period hPeriod
        massSquared
        ⟨d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
            field,
          primitiveSpinCSmooth_mem_maximalDomain_of_dirac period hPeriod
            massSquared diracSymmetry field⟩ =
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field) := by
  have hMem := primitiveSpinCSmooth_mem_maximalDomain_of_dirac period hPeriod
    massSquared diracSymmetry field
  change d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
      field ∈
    (primitiveSpinCGeometricSignedActionHessianGeometricOperator period hPeriod
      massSquared).domain at hMem
  let lifted :
      (primitiveSpinCGeometricSignedActionHessianGeometricOperator period hPeriod
        massSquared).domain :=
    ⟨d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter field,
      hMem⟩
  change
    primitiveSpinCGeometricSignedActionHessianGeometricOperator period hPeriod
        massSquared lifted = _
  apply
    (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm.injective
  rw [primitiveSpinCGeometricSignedActionHessianGeometricOperator_conjugacy
    period hPeriod massSquared lifted]
  ext mode
  rw [complexDiagonalOperator_apply]
  change
    ((primitiveSpinCGeometricSignedKineticHessianWeight period hPeriod mode +
        massSquared : Real) : Complex) *
        primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod field
          mode =
      primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field) mode
  exact
    (primitiveSpinCSmoothActionHessian_coefficients_of_dirac period hPeriod
      massSquared diracSymmetry field mode).symm

/-- The first-order Green identity constructs the complete existing
maximal-domain package. -/
def programPPrimitiveSpinCSmoothMaximalDomainData_of_diracFormalSymmetry
    (massSquared : Real)
    (diracSymmetry :
      ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod) :
    ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared where
  mem_domain :=
    primitiveSpinCSmooth_mem_maximalDomain_of_dirac period hPeriod massSquared
      diracSymmetry
  operator_agreement :=
    primitiveSpinCSmooth_maximalOperator_agrees_of_dirac period hPeriod
      massSquared diracSymmetry

/-! ## Parseval forces the same-action pairing -/

/-- One-sector Parseval identity between canonical coefficients and the
independently integrated smooth pairing. -/
theorem primitiveSpinCOneSectorCanonicalFourier_inner_weighted_eq_smooth
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared)
    (field : OneSectorSmooth period hPeriod) :
    (inner Complex
        (primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
          field)
        (primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
          massSquared domain field)).re =
      (d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter field
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field)).re := by
  let lifted :=
    primitiveSpinCSmoothMaximalDomainLift period hPeriod massSquared domain field
  have hAgreement := domain.operator_agreement field
  change
    primitiveSpinCGeometricSignedActionHessianGeometricOperator period hPeriod
        massSquared lifted =
      d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
          massSquared field) at hAgreement
  change
    (inner Complex
        ((primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm
          (d9PrimitiveSpinCGeometricL2Embedding period hPeriod
            .positiveQuarter field))
        ((primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm
          (primitiveSpinCGeometricSignedActionHessianGeometricOperator period
            hPeriod massSquared lifted))).re = _
  rw [LinearIsometryEquiv.inner_map_map, hAgreement]
  simp only [d9PrimitiveSpinCGeometricL2Embedding]
  change
    (inner Complex
      (field : D9PrimitiveSpinCGeometricL2Completion period hPeriod
        .positiveQuarter)
      (primitiveSpinCGeometricSignedActionHessianSmoothCore period hPeriod
        massSquared field : D9PrimitiveSpinCGeometricL2Completion period hPeriod
          .positiveQuarter)).re = _
  rw [UniformSpace.Completion.inner_coe]
  rfl

/-- The real two-sector coefficient pairing splits into the sum of the two
one-sector complex pairings. -/
private theorem tsum_prod_eq_sum
    {Outer Inner : Type*} [Fintype Outer]
    (f : Outer × Inner → Complex) (hf : Summable f) :
    (∑' mode, f mode) = ∑ outer, ∑' innerMode, f (outer, innerMode) := by
  rw [hf.tsum_prod, tsum_fintype]

private theorem product_inner_eq_sum
    {Outer Inner : Type*} [Fintype Outer]
    (first second : lp (fun _ : Outer × Inner => Complex) 2) :
    inner Complex first second =
      ∑ outer : Outer, ∑' innerMode : Inner,
        inner Complex (first (outer, innerMode))
          (second (outer, innerMode)) := by
  calc
    inner Complex first second =
        ∑' mode, inner Complex (first mode) (second mode) :=
      lp.inner_eq_tsum first second
    _ = ∑ outer : Outer, ∑' innerMode : Inner,
          inner Complex (first (outer, innerMode))
            (second (outer, innerMode)) :=
      tsum_prod_eq_sum _ (lp.summable_inner first second)

theorem programPPrimitiveSpinCMatterCanonicalFourier_inner_weighted_eq_sum
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared)
    (field : MatterSmooth period hPeriod) :
    inner Real
        (programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod
          field)
        (programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain
          period hPeriod massSquared domain field) =
      ∑ sector : Sector,
        (inner Complex
          (primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
            (field sector))
          (primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
            massSquared domain (field sector))).re := by
  rw [real_inner_eq_re_inner]
  unfold programPPrimitiveSpinCMatterCanonicalFourierCoefficients
    programPPrimitiveSpinCMatterCanonicalWeightedCoefficients_of_maximalDomain
  rw [product_inner_eq_sum]
  change
    RCLike.re
      (∑ sector : Sector, ∑' mode : SignedMode,
        inner Complex
          (primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
            (field sector) mode)
          (primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
            massSquared domain (field sector) mode)) = _
  simp_rw [← lp.inner_eq_tsum]
  change
    RCLike.reCLM
        (∑ sector : Sector,
          inner Complex
            (primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
              (field sector))
            (primitiveSpinCOneSectorCanonicalWeightedCoefficients period hPeriod
              massSquared domain (field sector))) = _
  rw [map_sum]
  rfl

/-- The smooth same-action field required by the older maximal-domain API is a
canonical theorem of maximal-operator agreement. -/
def programPPrimitiveSpinCMatterSmoothMaximalSameActionData_of_domain
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared) :
    ProgramPPrimitiveSpinCMatterSmoothMaximalSameActionData4D period hPeriod
      massSquared domain where
  action_pairing := by
    intro field
    unfold programPPrimitiveSpinCMatterSmoothAction
    rw [programPPrimitiveSpinCMatterCanonicalFourier_inner_weighted_eq_sum
      period hPeriod massSquared domain field]
    congr 1
    apply Finset.sum_congr rfl
    intro sector _
    exact
      (primitiveSpinCOneSectorCanonicalFourier_inner_weighted_eq_smooth
        period hPeriod massSquared domain (field sector)).symm

/-- The first-order Green identity constructs the exact smooth maximal graph
realization expected by the global Candidate-A chart. -/
def programPPrimitiveSpinCMatterSmoothGraphRealization_of_diracFormalSymmetry
    (massSquared : Real)
    (diracSymmetry :
      ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod) :=
  let domain :=
    programPPrimitiveSpinCSmoothMaximalDomainData_of_diracFormalSymmetry period
      hPeriod massSquared diracSymmetry
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_maximalDomain period
    hPeriod massSquared domain
      (programPPrimitiveSpinCMatterSmoothMaximalSameActionData_of_domain period
        hPeriod massSquared domain)

end
end P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
end JanusFormal
