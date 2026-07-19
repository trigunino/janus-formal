import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFourierCompatibilityQuotientImageEquiv

/-!
# Pairing on the finite-Fourier Saint--Venant image

The quotient pairing is transported through the canonical equivalence with
the concrete Saint--Venant image.  This is finite-mode only.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFourierCompatibilityImagePairing

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness
open P0EFTJanusFiniteFourierCompatibilityHelmholtzBridge
open P0EFTJanusFiniteFourierCompatibilityQuotientPairing
open P0EFTJanusFiniteFourierCompatibilityQuotientSeparation
open P0EFTJanusFiniteFourierCompatibilityQuotientImageEquiv

variable {Mode : Type*} [Fintype Mode]

/-- Pairing transported from the compatibility quotient to its exact image. -/
def saintVenantImagePairing
    (frequency : FrequencyFamily Mode)
    (first second : FiniteFourierSaintVenantImage frequency) : Real :=
  quotientCompatibilityPairing frequency
    ((quotientSaintVenantImageEquiv frequency).symm first)
    ((quotientSaintVenantImageEquiv frequency).symm second)

/-- Transport agrees with the ambient curvature pairing. -/
theorem saintVenantImagePairing_eq_curvaturePairing
    (frequency : FrequencyFamily Mode)
    (first second : FiniteFourierSaintVenantImage frequency) :
    saintVenantImagePairing frequency first second =
      finiteFourierCurvaturePairing first.1 second.1 := by
  unfold saintVenantImagePairing quotientCompatibilityPairing
  have hFirst := congrArg Subtype.val
    ((quotientSaintVenantImageEquiv frequency).apply_symm_apply first)
  have hSecond := congrArg Subtype.val
    ((quotientSaintVenantImageEquiv frequency).apply_symm_apply second)
  change quotientSaintVenant frequency
      ((quotientSaintVenantImageEquiv frequency).symm first) = first.1 at hFirst
  change quotientSaintVenant frequency
      ((quotientSaintVenantImageEquiv frequency).symm second) = second.1 at hSecond
  change finiteFourierCurvaturePairing
      (quotientSaintVenant frequency
        ((quotientSaintVenantImageEquiv frequency).symm first))
      (quotientSaintVenant frequency
        ((quotientSaintVenantImageEquiv frequency).symm second)) = _
  rw [hFirst, hSecond]

@[simp]
theorem saintVenantImagePairing_mk
    (frequency : FrequencyFamily Mode)
    (first second : FourierMetricCoefficient Mode) :
    saintVenantImagePairing frequency
        ⟨finiteFourierSaintVenant frequency first, ⟨first, rfl⟩⟩
        ⟨finiteFourierSaintVenant frequency second, ⟨second, rfl⟩⟩ =
      finiteFourierCurvaturePairing
        (finiteFourierSaintVenant frequency first)
        (finiteFourierSaintVenant frequency second) := by
  apply saintVenantImagePairing_eq_curvaturePairing

theorem saintVenantImagePairing_symmetric
    (frequency : FrequencyFamily Mode)
    (first second : FiniteFourierSaintVenantImage frequency) :
    saintVenantImagePairing frequency first second =
      saintVenantImagePairing frequency second first := by
  rw [saintVenantImagePairing_eq_curvaturePairing,
    saintVenantImagePairing_eq_curvaturePairing]
  exact finiteFourierCurvaturePairing_symmetric _ _

/-- Under the same explicit pointwise nondegeneracy hypothesis on the actual
image, the transported pairing separates image elements. -/
theorem saintVenantImagePairing_separates
    (frequency : FrequencyFamily Mode)
    (hNondegenerate :
      ∀ curvature : FourierCurvatureCoefficient Mode,
        curvature ∈ Set.range (finiteFourierSaintVenant frequency) →
        (∀ test : FourierCurvatureCoefficient Mode,
          test ∈ Set.range (finiteFourierSaintVenant frequency) →
          finiteFourierCurvaturePairing curvature test = 0) →
        curvature = 0)
    (first second : FiniteFourierSaintVenantImage frequency)
    (hPairing : ∀ test,
      saintVenantImagePairing frequency first test =
        saintVenantImagePairing frequency second test) :
    first = second := by
  let equiv := quotientSaintVenantImageEquiv frequency
  have hQuotient : equiv.symm first = equiv.symm second := by
    apply quotientCompatibilityPairing_separates frequency hNondegenerate
    intro test
    have h := hPairing (equiv test)
    simpa [saintVenantImagePairing, equiv] using h
  exact equiv.symm.injective hQuotient

end

end P0EFTJanusFiniteFourierCompatibilityImagePairing
end JanusFormal
