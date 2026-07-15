import Mathlib

namespace JanusFormal
namespace P0EFTJanusPTBoundaryFluxIntegrability

set_option autoImplicit false

theorem pt_paired_symplectic_flux_cancels
    (plusFlux minusFlux : ℝ) (hPT : minusFlux = -plusFlux) :
    plusFlux + minusFlux = 0 := by
  linarith

theorem vanishing_flux_is_antisymmetric_variation_closure
    (deltaOneDeltaTwo deltaTwoDeltaOne : ℝ)
    (hFlux : deltaOneDeltaTwo - deltaTwoDeltaOne = 0) :
    deltaOneDeltaTwo = deltaTwoDeltaOne := by
  linarith

end P0EFTJanusPTBoundaryFluxIntegrability
end JanusFormal
