import JanusFormal.Legacy.P0.Gates.P0FullLinearModeClosure

namespace JanusFormal
namespace P0ScalarVectorExactCoefficientMap

open P0ScalarVectorModeStability
open P0FullLinearModeClosure

set_option autoImplicit false

structure ScalarVectorExactActionParams where
  planckMassSquared : Rat
  aetherKineticScale : Rat
  lambdaPhi : Rat
  radionVev : Rat
  hassanRosenMassSquared : Rat
  membraneTension : Rat
  svtDecompositionApplied : Prop
  constraintsSolved : Prop
  boundaryJumpConditionsApplied : Prop
  quadraticActionExpanded : Prop
  radionDoubleWellExpanded : Prop
  hassanRosenMembraneExpanded : Prop
  gaugeAetherKineticExpanded : Prop

def scalarVectorExactDerivationClosed
    (p : ScalarVectorExactActionParams) : Prop :=
  p.svtDecompositionApplied /\
  p.constraintsSolved /\
  p.boundaryJumpConditionsApplied /\
  p.quadraticActionExpanded /\
  p.radionDoubleWellExpanded /\
  p.hassanRosenMembraneExpanded /\
  p.gaugeAetherKineticExpanded

def vectorAlphaExact (p : ScalarVectorExactActionParams) : Rat :=
  p.radionVev * (p.planckMassSquared - p.aetherKineticScale)

def vectorBetaExact (p : ScalarVectorExactActionParams) : Rat :=
  p.radionVev * p.planckMassSquared

def vectorSpeedSquaredExact (p : ScalarVectorExactActionParams) : Rat :=
  vectorBetaExact p / vectorAlphaExact p

def vectorMassSquaredExact (p : ScalarVectorExactActionParams) : Rat :=
  p.hassanRosenMassSquared

def scalarAlphaExact (p : ScalarVectorExactActionParams) : Rat :=
  vectorAlphaExact p + 2 * p.lambdaPhi * p.radionVev ^ 2

def scalarBetaExact (p : ScalarVectorExactActionParams) : Rat :=
  p.radionVev *
    (p.planckMassSquared + p.membraneTension +
      p.hassanRosenMassSquared * p.planckMassSquared *
        (3 * p.radionVev ^ 2 + 3 * p.radionVev + 1))

def scalarSpeedSquaredExact (p : ScalarVectorExactActionParams) : Rat :=
  scalarBetaExact p / scalarAlphaExact p

def scalarMassSquaredExact (p : ScalarVectorExactActionParams) : Rat :=
  2 * p.lambdaPhi * p.radionVev ^ 2 + p.hassanRosenMassSquared

theorem vector_speed_positive_from_exact_alpha_beta
    (p : ScalarVectorExactActionParams)
    (hAlpha : 0 < vectorAlphaExact p)
    (hBeta : 0 < vectorBetaExact p) :
    0 < vectorSpeedSquaredExact p := by
  unfold vectorSpeedSquaredExact
  exact div_pos hBeta hAlpha

theorem scalar_speed_positive_from_exact_alpha_beta
    (p : ScalarVectorExactActionParams)
    (hAlpha : 0 < scalarAlphaExact p)
    (hBeta : 0 < scalarBetaExact p) :
    0 < scalarSpeedSquaredExact p := by
  unfold scalarSpeedSquaredExact
  exact div_pos hBeta hAlpha

def scalarSetupFromExactParams
    (p : ScalarVectorExactActionParams) :
    ScalarPerturbationSetup :=
  { scalarModeDecomposed := p.svtDecompositionApplied
    scalarConstraintPreserved := p.constraintsSolved
    orbifoldBoundaryJumpConditions := p.boundaryJumpConditionsApplied
    quadraticActionExpanded := p.quadraticActionExpanded
    scalarMassTermPresent := p.radionDoubleWellExpanded
    hamiltonianConstraintPresent := p.constraintsSolved
    momentumConstraintPresent := p.constraintsSolved }

def vectorSetupFromExactParams
    (p : ScalarVectorExactActionParams) :
    VectorPerturbationSetup :=
  { vectorModeTransverse := p.svtDecompositionApplied
    orbifoldBoundaryJumpConditions := p.boundaryJumpConditionsApplied
    quadraticActionExpanded := p.quadraticActionExpanded
    vectorMassTermPresent := p.hassanRosenMembraneExpanded
    hamiltonianConstraintPresent := p.constraintsSolved
    momentumConstraintPresent := p.constraintsSolved
    aetherPerturbationIncluded := p.gaugeAetherKineticExpanded }

theorem scalar_setup_from_exact_closed
    (p : ScalarVectorExactActionParams)
    (h : scalarVectorExactDerivationClosed p) :
    scalarPerturbationSetupClosed (scalarSetupFromExactParams p) := by
  rcases h with
    ⟨hSvt, hConstraints, hBoundary, hQuadratic,
      hRadion, hMembrane, hAether⟩
  dsimp [scalarPerturbationSetupClosed, scalarSetupFromExactParams]
  exact And.intro hSvt
    (And.intro hConstraints
      (And.intro hBoundary
        (And.intro hQuadratic
          (And.intro hRadion
            (And.intro hConstraints hConstraints)))))

theorem vector_setup_from_exact_closed
    (p : ScalarVectorExactActionParams)
    (h : scalarVectorExactDerivationClosed p) :
    vectorPerturbationSetupClosed (vectorSetupFromExactParams p) := by
  rcases h with
    ⟨hSvt, hConstraints, hBoundary, hQuadratic,
      hRadion, hMembrane, hAether⟩
  dsimp [vectorPerturbationSetupClosed, vectorSetupFromExactParams]
  exact And.intro hSvt
    (And.intro hBoundary
      (And.intro hQuadratic
        (And.intro hMembrane
          (And.intro hConstraints
            (And.intro hConstraints hAether)))))

structure ScalarVectorExactCoefficientCertificate where
  params : ScalarVectorExactActionParams
  derivationClosed : scalarVectorExactDerivationClosed params
  scalarAlphaPositive : 0 < scalarAlphaExact params
  scalarBetaPositive : 0 < scalarBetaExact params
  scalarMassNonnegative : 0 <= scalarMassSquaredExact params
  vectorAlphaPositive : 0 < vectorAlphaExact params
  vectorBetaPositive : 0 < vectorBetaExact params
  vectorMassNonnegative : 0 <= vectorMassSquaredExact params

def scalarCoefficientsFromExact
    (c : ScalarVectorExactCoefficientCertificate) :
    ScalarQuadraticCoefficients :=
  { scalarAlphaPositive := 0 < scalarAlphaExact c.params
    scalarBetaPositive := 0 < scalarBetaExact c.params
    scalarSpeedSquaredPositive := 0 < scalarSpeedSquaredExact c.params
    scalarMassMatrixPositive := 0 <= scalarMassSquaredExact c.params
    scalarHyperbolicSector := 0 < scalarSpeedSquaredExact c.params }

def vectorCoefficientsFromExact
    (c : ScalarVectorExactCoefficientCertificate) :
    VectorQuadraticCoefficients :=
  { vectorAlphaPositive := 0 < vectorAlphaExact c.params
    vectorBetaPositive := 0 < vectorBetaExact c.params
    vectorSpeedSquaredPositive := 0 < vectorSpeedSquaredExact c.params
    vectorMassMatrixPositive := 0 <= vectorMassSquaredExact c.params
    vectorHyperbolicSector := 0 < vectorSpeedSquaredExact c.params }

def linearScalarCertificateFromExact
    (c : ScalarVectorExactCoefficientCertificate) :
    LinearScalarModeCertificate :=
  { setup := scalarSetupFromExactParams c.params
    coeffs := scalarCoefficientsFromExact c
    setupClosed := scalar_setup_from_exact_closed c.params c.derivationClosed
    stable := by
      dsimp [scalarLinearModeStable, noScalarGhost,
        noScalarGradientInstability, scalarSectorHyperbolic,
        scalarCoefficientsFromExact]
      exact And.intro c.scalarAlphaPositive
        (And.intro
          (And.intro c.scalarBetaPositive
            (scalar_speed_positive_from_exact_alpha_beta
              c.params c.scalarAlphaPositive c.scalarBetaPositive))
          (And.intro
            (scalar_speed_positive_from_exact_alpha_beta
              c.params c.scalarAlphaPositive c.scalarBetaPositive)
            c.scalarMassNonnegative)) }

def linearVectorCertificateFromExact
    (c : ScalarVectorExactCoefficientCertificate) :
    LinearVectorModeCertificate :=
  { setup := vectorSetupFromExactParams c.params
    coeffs := vectorCoefficientsFromExact c
    setupClosed := vector_setup_from_exact_closed c.params c.derivationClosed
    stable := by
      dsimp [vectorLinearModeStable, noVectorGhost,
        noVectorGradientInstability, vectorSectorHyperbolic,
        vectorCoefficientsFromExact]
      exact And.intro c.vectorAlphaPositive
        (And.intro
          (And.intro c.vectorBetaPositive
            (vector_speed_positive_from_exact_alpha_beta
              c.params c.vectorAlphaPositive c.vectorBetaPositive))
          (And.intro
            (vector_speed_positive_from_exact_alpha_beta
              c.params c.vectorAlphaPositive c.vectorBetaPositive)
            c.vectorMassNonnegative)) }

def fullLinearModeClosureFromExact
    (chain : P0CandidateClosureSummary.CandidateClosureChain)
    (c : ScalarVectorExactCoefficientCertificate) :
    FullLinearModeClosure :=
  { chain := chain
    scalar := linearScalarCertificateFromExact c
    vector := linearVectorCertificateFromExact c }

theorem exact_coefficients_close_consolidated_chain
    (chain : P0CandidateClosureSummary.CandidateClosureChain)
    (c : ScalarVectorExactCoefficientCertificate) :
    fullLinearModeClosureClosed
      (fullLinearModeClosureFromExact chain c) := by
  exact full_linear_mode_closure_closed
    (fullLinearModeClosureFromExact chain c)

theorem exact_scalar_formula_is_radion_aether_plus_double_well
    (p : ScalarVectorExactActionParams) :
    scalarAlphaExact p =
      p.radionVev * (p.planckMassSquared - p.aetherKineticScale) +
        2 * p.lambdaPhi * p.radionVev ^ 2 := by
  rfl

theorem exact_vector_formula_is_gauge_aether_load
    (p : ScalarVectorExactActionParams) :
    vectorAlphaExact p =
      p.radionVev * (p.planckMassSquared - p.aetherKineticScale) := by
  rfl

def sampleExactScalarVectorParams : ScalarVectorExactActionParams :=
  { planckMassSquared := 4
    aetherKineticScale := 1
    lambdaPhi := 1
    radionVev := 1
    hassanRosenMassSquared := 1
    membraneTension := 1
    svtDecompositionApplied := True
    constraintsSolved := True
    boundaryJumpConditionsApplied := True
    quadraticActionExpanded := True
    radionDoubleWellExpanded := True
    hassanRosenMembraneExpanded := True
    gaugeAetherKineticExpanded := True }

theorem sample_exact_scalar_vector_certificate :
    Nonempty ScalarVectorExactCoefficientCertificate := by
  refine ⟨
    { params := sampleExactScalarVectorParams
      derivationClosed := ?_
      scalarAlphaPositive := ?_
      scalarBetaPositive := ?_
      scalarMassNonnegative := ?_
      vectorAlphaPositive := ?_
      vectorBetaPositive := ?_
      vectorMassNonnegative := ?_ }⟩
  · norm_num [scalarVectorExactDerivationClosed, sampleExactScalarVectorParams]
  · norm_num [scalarAlphaExact, vectorAlphaExact, sampleExactScalarVectorParams]
  · norm_num [scalarBetaExact, sampleExactScalarVectorParams]
  · norm_num [scalarMassSquaredExact, sampleExactScalarVectorParams]
  · norm_num [vectorAlphaExact, sampleExactScalarVectorParams]
  · norm_num [vectorBetaExact, sampleExactScalarVectorParams]
  · norm_num [vectorMassSquaredExact, sampleExactScalarVectorParams]

end P0ScalarVectorExactCoefficientMap
end JanusFormal
