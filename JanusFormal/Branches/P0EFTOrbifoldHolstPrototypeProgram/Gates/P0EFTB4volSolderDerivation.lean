import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTMassShellB4volMeasure

namespace JanusFormal
namespace P0EFTB4volSolderDerivation

set_option autoImplicit false

structure B4volSolderDerivation where
  tetradSolderingDefined : Prop
  determinantRatioComputed : Prop
  b4volLinkedToLogDetLambda : Prop
  detLSolderKnown : Prop
  massShellLapseFactorKnown : Prop
  activeSourceMeasureClosed : Prop

def b4volDerived (b : B4volSolderDerivation) : Prop :=
  b.tetradSolderingDefined /\
  b.determinantRatioComputed /\
  b.b4volLinkedToLogDetLambda

def b4volActiveMeasureClosed (b : B4volSolderDerivation) : Prop :=
  b4volDerived b /\
  b.detLSolderKnown /\
  b.massShellLapseFactorKnown /\
  b.activeSourceMeasureClosed

theorem tetrad_soldering_derives_b4vol
    (b : B4volSolderDerivation)
    (hSolder : b.tetradSolderingDefined)
    (hDet : b.determinantRatioComputed)
    (hLog : b.b4volLinkedToLogDetLambda) :
    b4volDerived b := by
  exact And.intro hSolder (And.intro hDet hLog)

theorem missing_lapse_factor_blocks_active_measure
    (b : B4volSolderDerivation)
    (hMissing : Not b.massShellLapseFactorKnown) :
    Not (b4volActiveMeasureClosed b) := by
  intro h
  exact hMissing h.right.right.left

theorem b4vol_and_lapse_close_active_measure
    (b : B4volSolderDerivation)
    (hB4 : b4volDerived b)
    (hDetL : b.detLSolderKnown)
    (hLapse : b.massShellLapseFactorKnown)
    (hActive : b.activeSourceMeasureClosed) :
    b4volActiveMeasureClosed b := by
  exact And.intro hB4 (And.intro hDetL (And.intro hLapse hActive))

end P0EFTB4volSolderDerivation
end JanusFormal
