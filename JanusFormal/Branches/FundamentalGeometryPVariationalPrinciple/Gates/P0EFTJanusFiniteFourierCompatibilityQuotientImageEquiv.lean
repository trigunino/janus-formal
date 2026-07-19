import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFourierCompatibilityQuotientSeparation

/-!
# Finite-Fourier compatibility quotient as the Saint--Venant image

This identifies only the finite-mode fibre quotient with the concrete image
of its Saint--Venant symbol.  No global gauge or Sobolev quotient is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFourierCompatibilityQuotientImageEquiv

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness
open P0EFTJanusFiniteFourierCompatibilityQuotientPairing

variable {Mode : Type*} [Fintype Mode]

/-- The actual finite-mode image of the Saint--Venant symbol. -/
abbrev FiniteFourierSaintVenantImage (frequency : FrequencyFamily Mode) :=
  Set.range (finiteFourierSaintVenant frequency)

/-- The descended quotient map, with codomain restricted to its exact image. -/
def quotientSaintVenantToImage
    (frequency : FrequencyFamily Mode) :
    FiniteFourierCompatibilityQuotient frequency →
      FiniteFourierSaintVenantImage frequency := fun qclass =>
  ⟨quotientSaintVenant frequency qclass, by
    induction qclass using Quotient.inductionOn with
    | _ tensor => exact ⟨tensor, quotientSaintVenant_mk frequency tensor⟩⟩

@[simp]
theorem quotientSaintVenantToImage_mk
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) :
    (quotientSaintVenantToImage frequency
      (Quotient.mk (finiteFourierCompatibilitySetoid frequency) tensor) :
        FourierCurvatureCoefficient Mode) =
      finiteFourierSaintVenant frequency tensor :=
  rfl

/-- The image of the descended map is exactly the original Saint--Venant
image, not merely contained in it. -/
theorem range_quotientSaintVenant_eq_range_saintVenant
    (frequency : FrequencyFamily Mode) :
    Set.range (quotientSaintVenant frequency) =
      Set.range (finiteFourierSaintVenant frequency) := by
  ext curvature
  constructor
  · rintro ⟨qclass, rfl⟩
    induction qclass using Quotient.inductionOn with
    | _ tensor => exact ⟨tensor, quotientSaintVenant_mk frequency tensor⟩
  · rintro ⟨tensor, rfl⟩
    exact ⟨Quotient.mk (finiteFourierCompatibilitySetoid frequency) tensor,
      quotientSaintVenant_mk frequency tensor⟩

theorem quotientSaintVenantToImage_bijective
    (frequency : FrequencyFamily Mode) :
    Function.Bijective (quotientSaintVenantToImage frequency) := by
  constructor
  · intro first second h
    apply quotientSaintVenant_injective frequency
    exact Subtype.ext_iff.mp h
  · rintro ⟨curvature, tensor, rfl⟩
    exact ⟨Quotient.mk (finiteFourierCompatibilitySetoid frequency) tensor, rfl⟩

/-- Canonical equivalence between the finite fibre quotient and the concrete
Saint--Venant image. -/
def quotientSaintVenantImageEquiv
    (frequency : FrequencyFamily Mode) :
    FiniteFourierCompatibilityQuotient frequency ≃
      FiniteFourierSaintVenantImage frequency :=
  Equiv.ofBijective (quotientSaintVenantToImage frequency)
    (quotientSaintVenantToImage_bijective frequency)

@[simp]
theorem quotientSaintVenantImageEquiv_apply
    (frequency : FrequencyFamily Mode)
    (qclass : FiniteFourierCompatibilityQuotient frequency) :
    (quotientSaintVenantImageEquiv frequency qclass :
      FourierCurvatureCoefficient Mode) =
        quotientSaintVenant frequency qclass :=
  rfl

end

end P0EFTJanusFiniteFourierCompatibilityQuotientImageEquiv
end JanusFormal
