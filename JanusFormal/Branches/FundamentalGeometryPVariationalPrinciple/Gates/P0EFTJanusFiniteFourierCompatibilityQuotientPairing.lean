import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFourierCompatibilityHelmholtzBridge

/-!
# Finite-Fourier compatibility-fibre quotient

This is the algebraic finite-mode quotient defined by equality of the concrete
Saint-Venant symbol.  It is not identified with the global Janus gauge-orbit
or Sobolev quotient.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFourierCompatibilityQuotientPairing

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness
open P0EFTJanusFiniteFourierCompatibilityHelmholtzBridge

variable {Mode : Type*} [Fintype Mode]

/-- Two finite Fourier metric coefficients are equivalent exactly when their
concrete Saint-Venant compatibility coefficients agree. -/
def finiteFourierCompatibilitySetoid
    (frequency : FrequencyFamily Mode) :
    Setoid (FourierMetricCoefficient Mode) where
  r first second :=
    finiteFourierSaintVenant frequency first =
      finiteFourierSaintVenant frequency second
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun hFirst hSecond => hFirst.trans hSecond }

abbrev FiniteFourierCompatibilityQuotient
    (frequency : FrequencyFamily Mode) :=
  Quotient (finiteFourierCompatibilitySetoid frequency)

/-- The concrete compatibility map descends to its fibre quotient. -/
def quotientSaintVenant
    (frequency : FrequencyFamily Mode) :
    FiniteFourierCompatibilityQuotient frequency ->
      FourierCurvatureCoefficient Mode :=
  Quotient.lift (finiteFourierSaintVenant frequency) (by
    intro first second hEquivalent
    exact hEquivalent)

@[simp] theorem quotientSaintVenant_mk
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) :
    quotientSaintVenant frequency
        (Quotient.mk (finiteFourierCompatibilitySetoid frequency) tensor) =
      finiteFourierSaintVenant frequency tensor :=
  rfl

/-- Equality of descended compatibility coefficients detects equality in the
compatibility-fibre quotient. -/
theorem quotientSaintVenant_injective
    (frequency : FrequencyFamily Mode) :
    Function.Injective (quotientSaintVenant frequency) := by
  intro first second hEqual
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second =>
          apply Quotient.sound
          exact hEqual

/-- The finite curvature pairing descends without representative choices. -/
def quotientCompatibilityPairing
    (frequency : FrequencyFamily Mode)
    (first second : FiniteFourierCompatibilityQuotient frequency) : Real :=
  finiteFourierCurvaturePairing
    (quotientSaintVenant frequency first)
    (quotientSaintVenant frequency second)

theorem quotientCompatibilityPairing_mk
    (frequency : FrequencyFamily Mode)
    (first second : FourierMetricCoefficient Mode) :
    quotientCompatibilityPairing frequency
        (Quotient.mk (finiteFourierCompatibilitySetoid frequency) first)
        (Quotient.mk (finiteFourierCompatibilitySetoid frequency) second) =
      finiteFourierCurvaturePairing
        (finiteFourierSaintVenant frequency first)
        (finiteFourierSaintVenant frequency second) :=
  rfl

theorem quotientCompatibilityPairing_symmetric
    (frequency : FrequencyFamily Mode)
    (first second : FiniteFourierCompatibilityQuotient frequency) :
    quotientCompatibilityPairing frequency first second =
      quotientCompatibilityPairing frequency second first :=
  finiteFourierCurvaturePairing_symmetric _ _

/-- Every genuine Lorentz--Gram gauge symbol represents the zero
compatibility class. -/
theorem quotient_mk_lorentzGram_eq_zero
    (frequency : FrequencyFamily Mode)
    (potential : FourierPotential Mode) :
    Quotient.mk (finiteFourierCompatibilitySetoid frequency)
        (finiteFourierLorentzGram frequency potential) =
      Quotient.mk (finiteFourierCompatibilitySetoid frequency) 0 := by
  apply Quotient.sound
  change finiteFourierSaintVenant frequency
      (finiteFourierLorentzGram frequency potential) =
    finiteFourierSaintVenant frequency 0
  rw [finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero]
  funext mode i j k l
  simp [finiteFourierSaintVenant, saintVenantSymbol]

end


end P0EFTJanusFiniteFourierCompatibilityQuotientPairing
end JanusFormal
