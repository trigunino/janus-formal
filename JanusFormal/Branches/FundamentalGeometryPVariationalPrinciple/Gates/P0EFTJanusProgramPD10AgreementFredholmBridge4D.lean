import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D

/-!
# Fredholm transport through the Program-P D10 agreement

This gate transports the complete multiplicity-aware D10 Fredholm realization
to the geometric tangent type whenever the existing D7/D9/D10 agreement is
available.  It proves bijectivity, coercivity, compact inverse coordinates,
spectral Hessian diagonalization and strong finite-packet approximation.

The gate does not manufacture the agreement: constructing global eigenspinors
and their Fourier synthesis is a separate geometric input not contained in
the present eigenvalue-only spectral data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD10AgreementFredholmBridge4D

set_option autoImplicit false

noncomputable section

open Filter Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D

variable {period : ℝ} {hPeriod : period ≠ 0}
variable {Spinor : Type*}

/-- Geometric maximal domain supplied by one complete D7/D9/D10 agreement. -/
abbrev ProgramPAgreementFredholmDomain4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain) :=
  { variation : ProgramPCompleteVariation4D period hPeriod //
    variation ∈ agreement.fredholmDomain }

/-- Coordinates of one geometric domain vector, bundled in the maximal
spectral domain. -/
def programPAgreementFredholmCoordinateDomain4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (variation : ProgramPAgreementFredholmDomain4D domain agreement) :
    programPD10FredholmModeDomainSubmodule4D
      domain.d7d10SpectralData :=
  ⟨agreement.modeCoordinateEquiv variation.1,
    (agreement.fredholmDomain_modeAgreement variation.1).1
      variation.2⟩

/-- Squared-Dirac Fredholm operator transported back to geometric
variations. -/
def programPAgreementFredholmOperator4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain) :
    ProgramPAgreementFredholmDomain4D domain agreement →
      ProgramPCompleteVariation4D period hPeriod :=
  fun variation =>
    agreement.modeCoordinateEquiv.symm
      (programPD10FredholmModeOperator4D
        domain.d7d10SpectralData
        (programPAgreementFredholmCoordinateDomain4D
          domain agreement variation))

@[simp]
theorem programPAgreementFredholmOperator4D_coordinate
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (variation : ProgramPAgreementFredholmDomain4D domain agreement) :
    agreement.modeCoordinateEquiv
        (programPAgreementFredholmOperator4D
          domain agreement variation) =
      programPD10FredholmModeOperator4D
        domain.d7d10SpectralData
        (programPAgreementFredholmCoordinateDomain4D
          domain agreement variation) := by
  exact agreement.modeCoordinateEquiv.apply_symm_apply _

/-- Explicit geometric inverse obtained from the compact spectral inverse. -/
def programPAgreementFredholmInverse4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    ProgramPAgreementFredholmDomain4D domain agreement :=
  ⟨agreement.modeCoordinateEquiv.symm
      (programPD10FredholmInverseCLM4D
        domain.d7d10SpectralData
        (agreement.modeCoordinateEquiv variation)),
    by
      apply
        (agreement.fredholmDomain_modeAgreement _).2
      rw [agreement.modeCoordinateEquiv.apply_symm_apply]
      exact
        programPD10FredholmInverseCLM4D_mem_domain
          domain.d7d10SpectralData
          (agreement.modeCoordinateEquiv variation)⟩

theorem programPAgreementFredholmOperator4D_inverse
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    programPAgreementFredholmOperator4D domain agreement
        (programPAgreementFredholmInverse4D
          domain agreement variation) =
      variation := by
  apply agreement.modeCoordinateEquiv.injective
  rw [programPAgreementFredholmOperator4D_coordinate]
  ext mode
  simp [programPAgreementFredholmCoordinateDomain4D,
    programPAgreementFredholmInverse4D,
    ne_of_gt
      (product_spectrum_has_positive_gap
        domain.d7d10SpectralData mode.separatedMode)]

theorem programPAgreementFredholmInverse4D_operator
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (variation : ProgramPAgreementFredholmDomain4D domain agreement) :
    (programPAgreementFredholmInverse4D domain agreement
      (programPAgreementFredholmOperator4D
        domain agreement variation)).1 =
      variation.1 := by
  apply agreement.modeCoordinateEquiv.injective
  simp only [programPAgreementFredholmInverse4D,
    agreement.modeCoordinateEquiv.apply_symm_apply]
  rw [programPAgreementFredholmOperator4D_coordinate]
  exact
    programPD10FredholmInverseCLM4D_operator
      domain.d7d10SpectralData
      (programPAgreementFredholmCoordinateDomain4D
        domain agreement variation)

/-- The transported geometric maximal-domain operator is bijective. -/
theorem programPAgreementFredholmOperator4D_bijective
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain) :
    Function.Bijective
      (programPAgreementFredholmOperator4D domain agreement) := by
  constructor
  · intro first second hOperator
    apply Subtype.ext
    calc
      first.1 =
          (programPAgreementFredholmInverse4D domain agreement
            (programPAgreementFredholmOperator4D
              domain agreement first)).1 :=
        (programPAgreementFredholmInverse4D_operator
          domain agreement first).symm
      _ =
          (programPAgreementFredholmInverse4D domain agreement
            (programPAgreementFredholmOperator4D
              domain agreement second)).1 := by
        rw [hOperator]
      _ = second.1 :=
        programPAgreementFredholmInverse4D_operator
          domain agreement second
  · intro variation
    exact
      ⟨programPAgreementFredholmInverse4D
        domain agreement variation,
        programPAgreementFredholmOperator4D_inverse
          domain agreement variation⟩

/-- The abstract Fredholm domain in the agreement is exactly the geometric
boundary-preserving tangent domain. -/
theorem programPAgreementFredholmDomain4D_eq_boundaryDomain
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain) :
    agreement.fredholmDomain =
      programPBoundaryTangentDomain4D period hPeriod domain :=
  agreement.fredholmDomain_eq_boundaryDomain

/-- Quantitative coercivity transported to the geometric tangent norm. -/
theorem programPAgreementFredholmOperator4D_coercive
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (variation : ProgramPAgreementFredholmDomain4D domain agreement) :
    agreement.tangentNorm variation.1 ≤
      (1 /
        programPD10SpectralGap4D
          domain.d7d10SpectralData) *
        agreement.tangentNorm
          (programPAgreementFredholmOperator4D
            domain agreement variation) := by
  rw [agreement.modeCoordinate_isometry,
    agreement.modeCoordinate_isometry,
    programPAgreementFredholmOperator4D_coordinate]
  exact
    programPD10FredholmModeOperator4D_coercive
      domain.d7d10SpectralData
      (programPAgreementFredholmCoordinateDomain4D
        domain agreement variation)

/-- Compactness of the geometric inverse after applying the exact mode
coordinate equivalence. -/
theorem programPAgreementFredholmInverse4D_coordinates_compact
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (_agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain) :
    IsCompactOperator
      (programPD10FredholmInverseCLM4D
        domain.d7d10SpectralData) :=
  programPD10FredholmInverseCLM4D_compact
    domain.d7d10SpectralData

/-- Every complete D10 mode is an exact Hessian eigenvector in the geometric
agreement, not only the regulator modes. -/
theorem programPAgreement_modeHessian_diagonal
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (mode : ProgramPD10Mode4D domain.d7d10SpectralData) :
    agreement.actionHessian agreement.baseConfiguration
        (agreement.modeTangent mode)
        (agreement.modeTangent mode) =
      productDiracEigenvalueSquared
        domain.d7d10SpectralData mode.separatedMode := by
  calc
    agreement.actionHessian agreement.baseConfiguration
        (agreement.modeTangent mode)
        (agreement.modeTangent mode) =
      productDiracEigenvalueSquared
          domain.d7d10SpectralData mode.separatedMode *
        agreement.tangentPairing
          (agreement.modeTangent mode)
          (agreement.modeTangent mode) :=
      agreement.hessian_spectral_pairing_agreement
        mode (agreement.modeTangent mode)
    _ =
      productDiracEigenvalueSquared
          domain.d7d10SpectralData mode.separatedMode *
        agreement.modeCoordinateEquiv
          (agreement.modeTangent mode) mode := by
      rw [agreement.tangentPairing_eq_modeCoordinate]
    _ =
      productDiracEigenvalueSquared
        domain.d7d10SpectralData mode.separatedMode := by
      rw [agreement.modeCoordinate_same, mul_one]

/-- Distinct complete D10 modes are Hessian-orthogonal. -/
theorem programPAgreement_modeHessian_offDiagonal
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (first second :
      ProgramPD10Mode4D domain.d7d10SpectralData)
    (hModes : first ≠ second) :
    agreement.actionHessian agreement.baseConfiguration
        (agreement.modeTangent first)
        (agreement.modeTangent second) = 0 := by
  calc
    agreement.actionHessian agreement.baseConfiguration
        (agreement.modeTangent first)
        (agreement.modeTangent second) =
      productDiracEigenvalueSquared
          domain.d7d10SpectralData first.separatedMode *
        agreement.tangentPairing
          (agreement.modeTangent first)
          (agreement.modeTangent second) :=
      agreement.hessian_spectral_pairing_agreement
        first (agreement.modeTangent second)
    _ =
      productDiracEigenvalueSquared
          domain.d7d10SpectralData first.separatedMode *
        agreement.modeCoordinateEquiv
          (agreement.modeTangent second) first := by
      rw [agreement.tangentPairing_eq_modeCoordinate]
    _ = 0 := by
      rw [agreement.modeCoordinate_ne second first
        (Ne.symm hModes), mul_zero]

/-- Finite spectral projection transported to the geometric tangent type. -/
def programPAgreementFiniteProjection4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (modes :
      Finset (ProgramPD10Mode4D domain.d7d10SpectralData))
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    ProgramPCompleteVariation4D period hPeriod :=
  agreement.modeCoordinateEquiv.symm
    (programPD10FiniteProjection4D
      domain.d7d10SpectralData modes
      (agreement.modeCoordinateEquiv variation))

@[simp]
theorem programPAgreementFiniteProjection4D_coordinate
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (modes :
      Finset (ProgramPD10Mode4D domain.d7d10SpectralData))
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    agreement.modeCoordinateEquiv
        (programPAgreementFiniteProjection4D
          domain agreement modes variation) =
      programPD10FiniteProjection4D
        domain.d7d10SpectralData modes
        (agreement.modeCoordinateEquiv variation) := by
  exact agreement.modeCoordinateEquiv.apply_symm_apply _

/-- Unordered finite geometric packets converge in the exact transported
tangent norm. -/
theorem programPAgreementFiniteProjection4D_tendsto
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    Tendsto
      (fun modes :
          Finset (ProgramPD10Mode4D
            domain.d7d10SpectralData) =>
        agreement.tangentNorm
          (agreement.tangentAdd
            (programPAgreementFiniteProjection4D
              domain agreement modes variation)
            (agreement.tangentSMul (-1) variation)))
      atTop (𝓝 0) := by
  have hProjection :=
    programPD10FiniteProjection4D_tendsto
      domain.d7d10SpectralData
      (agreement.modeCoordinateEquiv variation)
  have hDifference :=
    hProjection.sub_const
      (agreement.modeCoordinateEquiv variation)
  simpa only [agreement.modeCoordinate_distance,
    programPAgreementFiniteProjection4D_coordinate,
    sub_self, norm_zero] using hDifference.norm

end

end P0EFTJanusProgramPD10AgreementFredholmBridge4D
end JanusFormal
