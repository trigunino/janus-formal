import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusArbitraryFrequencySaintVenantExactness
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLinearizedEinsteinBianchiSymbol

/-!
# Saint--Venant / Einstein--Bianchi symbol bridge

At one real covector, the strain symbol used by the Saint--Venant complex is
literally the pure-gauge perturbation used by the linearized Einstein symbol.
This gate also separates the raised divergence from its composite with the
Einstein symbol.  The existing calculations then give the concrete symbol
relations `K_SV ∘ R = 0`, `G ∘ R = 0`, and `B ∘ G = 0` on the same
`Fin 4` coefficient spaces.

This remains a flat pointwise principal-symbol statement.  It constructs no
global differential operator, Sobolev domain, boundary condition, exact
global complex, or Janus-bundle cohomology.
-/

namespace JanusFormal
namespace P0EFTJanusSaintVenantEinsteinBianchiSymbolBridge

set_option autoImplicit false

noncomputable section

abbrev Covector4 :=
  P0EFTJanusArbitraryFrequencySaintVenantExactness.Covector4
abbrev Vector4 :=
  P0EFTJanusArbitraryFrequencySaintVenantExactness.Vector4
abbrev Tensor2 :=
  P0EFTJanusArbitraryFrequencySaintVenantExactness.CovariantTwoTensor
abbrev SymmetricPerturbation :=
  P0EFTJanusLinearizedEinsteinBianchiSymbol.SymmetricPerturbation

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusLinearizedEinsteinBianchiSymbol

/-- The Saint--Venant strain, bundled as the symmetric perturbation expected
by the linearized Einstein symbol. -/
def symmetricStrainSymbol
    (covector : Covector4) (variation : Vector4) :
    SymmetricPerturbation :=
  pureGaugePerturbation covector variation

@[simp]
theorem symmetricStrainSymbol_tensor
    (covector : Covector4) (variation : Vector4) :
    (symmetricStrainSymbol covector variation).tensor =
      strainSymbol covector variation := by
  rfl

/-- Raised principal-symbol divergence on an arbitrary covariant two-tensor. -/
def raisedTensorDivergenceSymbol
    (covector : Covector4) (tensor : Tensor2) : Covector4 :=
  fun index => ∑ contracted,
    raiseCovector covector contracted * tensor contracted index

/-- The Saint--Venant compatibility symbol kills the same bundled gauge
direction used below by the Einstein symbol. -/
theorem saintVenantSymbol_comp_symmetricStrain_eq_zero
    (covector : Covector4) (variation : Vector4) :
    saintVenantSymbol covector
        (symmetricStrainSymbol covector variation).tensor = 0 := by
  rw [symmetricStrainSymbol_tensor]
  exact saintVenantSymbol_strainSymbol_eq_zero covector variation

/-- The flat linearized Einstein symbol kills that exact same strain
direction: the concrete symbol relation `G ∘ R = 0`. -/
theorem linearizedEinsteinSymbol_comp_symmetricStrain_eq_zero
    (covector : Covector4) (variation : Vector4) :
    linearizedEinsteinSymbol covector
        (symmetricStrainSymbol covector variation) = 0 := by
  simpa only [symmetricStrainSymbol] using
    linearizedEinsteinSymbol_pureGauge_eq_zero covector variation

/-- The separately exposed divergence kills every linearized Einstein output:
the concrete symbol relation `B ∘ G = 0`. -/
theorem raisedTensorDivergenceSymbol_comp_linearizedEinstein_eq_zero
    (covector : Covector4)
    (perturbation : SymmetricPerturbation) :
    raisedTensorDivergenceSymbol covector
        (linearizedEinsteinSymbol covector perturbation) = 0 := by
  funext index
  change einsteinSymbolDivergence covector perturbation index = 0
  exact linearizedEinsteinSymbol_bianchi covector perturbation index

/-- All three consecutive symbol relations on the shared real `Fin 4`
coefficient spaces. -/
theorem saintVenant_einstein_bianchi_symbol_bridge
    (covector : Covector4) (variation : Vector4)
    (perturbation : SymmetricPerturbation) :
    saintVenantSymbol covector
          (symmetricStrainSymbol covector variation).tensor = 0 ∧
      linearizedEinsteinSymbol covector
          (symmetricStrainSymbol covector variation) = 0 ∧
      raisedTensorDivergenceSymbol covector
          (linearizedEinsteinSymbol covector perturbation) = 0 := by
  exact ⟨saintVenantSymbol_comp_symmetricStrain_eq_zero covector variation,
    linearizedEinsteinSymbol_comp_symmetricStrain_eq_zero covector variation,
    raisedTensorDivergenceSymbol_comp_linearizedEinstein_eq_zero
      covector perturbation⟩

end

end P0EFTJanusSaintVenantEinsteinBianchiSymbolBridge
end JanusFormal
