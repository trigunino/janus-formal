import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompatibilityBridgeHierarchy
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFourierSaintVenantExactness

/-!
# Finite-Fourier compatibility/Helmholtz bridge

This gate instantiates the compatibility-ideal mechanism with the actual
coefficientwise Saint-Venant symbol.  It is only a finite-mode symbol result;
it does not construct the global differential `K/J` complex on Janus bundles.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFourierCompatibilityHelmholtzBridge

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness
open P0EFTJanusGaussCodazziHelmholtzBridge

variable {Mode : Type*} [Fintype Mode]

/-- Euclidean coefficient pairing on finite Fourier curvature families. -/
def finiteFourierCurvaturePairing
    (first second : FourierCurvatureCoefficient Mode) : Real :=
  ∑ mode, ∑ i, ∑ j, ∑ k, ∑ l,
    first mode i j k l * second mode i j k l

theorem finiteFourierCurvaturePairing_symmetric
    (first second : FourierCurvatureCoefficient Mode) :
    finiteFourierCurvaturePairing first second =
      finiteFourierCurvaturePairing second first := by
  simp only [finiteFourierCurvaturePairing, mul_comm]

/-- The concrete finite-mode Saint-Venant map equipped with its pullback
quadratic pairing.  Boundary and transgression terms vanish at symbol level. -/
def finiteFourierSaintVenantBridge
    (frequency : FrequencyFamily Mode) :
    ConstraintGeneratedHelmholtzBridge
      (FourierMetricCoefficient Mode) (FourierCurvatureCoefficient Mode) where
  compatibility := finiteFourierSaintVenant frequency
  pairedLinearization := fun first second =>
    finiteFourierCurvaturePairing
      (finiteFourierSaintVenant frequency first)
      (finiteFourierSaintVenant frequency second)
  constraintTransgression := fun _ _ => 0
  boundaryFlux := fun _ _ => 0
  transgressionAtZero := by
    intro variation
    rfl
  defectFactorization := by
    intro first second
    rw [finiteFourierCurvaturePairing_symmetric]
    ring

/-- Every Lorentz--Gram gauge symbol is a compatible variation for this
concrete finite-mode bridge. -/
theorem finiteFourierLorentzGram_is_compatible
    (frequency : FrequencyFamily Mode)
    (potential : FourierPotential Mode) :
    IsCompatibleVariation
      (finiteFourierSaintVenantBridge frequency)
      (finiteFourierLorentzGram frequency potential) := by
  exact finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero
    frequency potential

/-- The pullback pairing is Helmholtz-symmetric on the concrete
Saint-Venant-compatible coefficient locus. -/
theorem finiteFourierSaintVenant_restricted_helmholtz
    (frequency : FrequencyFamily Mode) :
    RestrictedHelmholtz (finiteFourierSaintVenantBridge frequency) :=
  compatibility_generated_defect_implies_restricted_helmholtz
    (finiteFourierSaintVenantBridge frequency)

/-- In particular, two genuine Lorentz--Gram gauge symbols have symmetric
pulled-back Saint-Venant response (both compatibility images are zero). -/
theorem finiteFourierGaugePairing_helmholtz
    (frequency : FrequencyFamily Mode)
    (first second : FourierPotential Mode) :
    (finiteFourierSaintVenantBridge frequency).pairedLinearization
        (finiteFourierLorentzGram frequency first)
        (finiteFourierLorentzGram frequency second) =
      (finiteFourierSaintVenantBridge frequency).pairedLinearization
        (finiteFourierLorentzGram frequency second)
        (finiteFourierLorentzGram frequency first) := by
  apply finiteFourierSaintVenant_restricted_helmholtz
  · exact finiteFourierLorentzGram_is_compatible frequency first
  · exact finiteFourierLorentzGram_is_compatible frequency second
  · rfl

end


end P0EFTJanusFiniteFourierCompatibilityHelmholtzBridge
end JanusFormal
