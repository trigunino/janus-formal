import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFourierCompatibilityQuotientPairing

/-!
# Separation of the finite-Fourier compatibility quotient

This remains the fibre quotient of the finite-mode Saint--Venant symbol.  It
is not a gauge-orbit or Sobolev quotient on the global Janus field space.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFourierCompatibilityQuotientSeparation

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness
open P0EFTJanusFiniteFourierCompatibilityHelmholtzBridge
open P0EFTJanusFiniteFourierCompatibilityQuotientPairing

variable {Mode : Type*} [Fintype Mode]

/-- Classes are equal exactly when their concrete compatibility images agree. -/
theorem quotient_eq_iff_saintVenant_eq
    (frequency : FrequencyFamily Mode)
    (first second : FiniteFourierCompatibilityQuotient frequency) :
    first = second ↔
      quotientSaintVenant frequency first =
        quotientSaintVenant frequency second := by
  constructor
  · exact fun h => congrArg (quotientSaintVenant frequency) h
  · intro h
    exact quotientSaintVenant_injective frequency h

/-- The kernel fibre of the descended compatibility map is the zero class. -/
theorem quotientSaintVenant_eq_zero_iff
    (frequency : FrequencyFamily Mode)
    (qclass : FiniteFourierCompatibilityQuotient frequency) :
    quotientSaintVenant frequency qclass = 0 ↔
      qclass = Quotient.mk (finiteFourierCompatibilitySetoid frequency) 0 := by
  rw [quotient_eq_iff_saintVenant_eq]
  have hZero : finiteFourierSaintVenant frequency 0 = 0 := by
    funext mode i j k l
    simp [finiteFourierSaintVenant, saintVenantSymbol]
  rw [quotientSaintVenant_mk, hZero]

/-- If the curvature pairing is nondegenerate on the actual Saint--Venant
image, its descended pairing separates compatibility classes.  The hypothesis
is stated pointwise on that concrete image, rather than stored as a status
field. -/
theorem quotientCompatibilityPairing_separates
    (frequency : FrequencyFamily Mode)
    (hNondegenerate :
      ∀ curvature : FourierCurvatureCoefficient Mode,
        curvature ∈ Set.range (finiteFourierSaintVenant frequency) →
        (∀ test : FourierCurvatureCoefficient Mode,
          test ∈ Set.range (finiteFourierSaintVenant frequency) →
          finiteFourierCurvaturePairing curvature test = 0) →
        curvature = 0)
    (first second : FiniteFourierCompatibilityQuotient frequency)
    (hPairing : ∀ test,
      quotientCompatibilityPairing frequency first test =
        quotientCompatibilityPairing frequency second test) :
    first = second := by
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second =>
          apply (quotient_eq_iff_saintVenant_eq frequency _ _).2
          simp only [quotientSaintVenant_mk]
          have hDifference :
              finiteFourierSaintVenant frequency first -
                  finiteFourierSaintVenant frequency second = 0 := by
            apply hNondegenerate
            · refine ⟨first - second, ?_⟩
              funext mode i j k l
              simp [finiteFourierSaintVenant, saintVenantSymbol]
              ring
            · intro test hTest
              obtain ⟨tensor, rfl⟩ := hTest
              have h := hPairing
                (Quotient.mk (finiteFourierCompatibilitySetoid frequency)
                  tensor)
              simp only [quotientCompatibilityPairing_mk] at h
              simpa [finiteFourierCurvaturePairing, Finset.sum_sub_distrib,
                sub_mul] using sub_eq_zero.mpr h
          exact sub_eq_zero.mp hDifference

end

end P0EFTJanusFiniteFourierCompatibilityQuotientSeparation
end JanusFormal
