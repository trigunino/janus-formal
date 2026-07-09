import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4FullActionWardClosure
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4BackgroundBianchiIdentity

namespace JanusFormal
namespace P0EFTJanusZ4BackgroundActionDerivation

set_option autoImplicit false

structure BackgroundActionDerivation where
  einsteinPalatiniNormalizationDeclared : Prop
  z4MasterDensityProjected : Prop
  friedmannCoefficientDerived : Prop
  accelerationCoefficientDerived : Prop
  continuityFromWardCurrent : Prop
  bianchiResidualVanishes : Prop
  noExtraBackgroundFluidIntroduced : Prop

def backgroundActionDerivedReady (b : BackgroundActionDerivation) : Prop :=
  b.einsteinPalatiniNormalizationDeclared /\
  b.z4MasterDensityProjected /\
  b.friedmannCoefficientDerived /\
  b.accelerationCoefficientDerived /\
  b.continuityFromWardCurrent /\
  b.bianchiResidualVanishes /\
  b.noExtraBackgroundFluidIntroduced

theorem background_action_derivation_gives_friedmann_coefficient
    (b : BackgroundActionDerivation)
    (h : backgroundActionDerivedReady b) :
    b.friedmannCoefficientDerived := by
  exact h.right.right.left

theorem background_action_derivation_preserves_no_extra_fluid
    (b : BackgroundActionDerivation)
    (h : backgroundActionDerivedReady b) :
    b.noExtraBackgroundFluidIntroduced := by
  exact h.right.right.right.right.right.right

end P0EFTJanusZ4BackgroundActionDerivation
end JanusFormal
