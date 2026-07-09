import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTRadionBoundarySourceKick

namespace JanusFormal
namespace P0EFTRadionPotentialDerivation

set_option autoImplicit false

structure RadionPotentialDerivation where
  minimalECDerivativeTorsionOnly : Prop
  minimalECGeneratesDerivativeFreePotential : Prop
  janusVolumeHolonomySectorPresent : Prop
  z2EvenVolumePairGivesCoshShape : Prop
  canonicalGammaFixed : Prop
  lambdaJFixedByBackgroundEquation : Prop
  potentialShapeFixedNoFit : Prop
  potentialFullyFixedNoFit : Prop
  amplitudeFixedByBackgroundEquation : Prop

def minimalECNoPotential (p : RadionPotentialDerivation) : Prop :=
  p.minimalECDerivativeTorsionOnly /\
  Not p.minimalECGeneratesDerivativeFreePotential

def coshShapeDerived (p : RadionPotentialDerivation) : Prop :=
  p.janusVolumeHolonomySectorPresent /\
  p.z2EvenVolumePairGivesCoshShape /\
  p.canonicalGammaFixed /\
  p.potentialShapeFixedNoFit

def radionPotentialNoFitClosed (p : RadionPotentialDerivation) : Prop :=
  coshShapeDerived p /\
  p.amplitudeFixedByBackgroundEquation /\
  p.lambdaJFixedByBackgroundEquation /\
  p.potentialFullyFixedNoFit

theorem derivative_torsion_only_does_not_close_bulk_potential
    (p : RadionPotentialDerivation)
    (hEC : p.minimalECDerivativeTorsionOnly)
    (hNoPot : Not p.minimalECGeneratesDerivativeFreePotential) :
    minimalECNoPotential p := by
  exact And.intro hEC hNoPot

theorem janus_volume_holonomy_fixes_cosh_shape
    (p : RadionPotentialDerivation)
    (hVol : p.janusVolumeHolonomySectorPresent)
    (hEven : p.z2EvenVolumePairGivesCoshShape)
    (hGamma : p.canonicalGammaFixed)
    (hShape : p.potentialShapeFixedNoFit) :
    coshShapeDerived p := by
  exact And.intro hVol (And.intro hEven (And.intro hGamma hShape))

theorem missing_lambdaJ_blocks_full_no_fit_potential
    (p : RadionPotentialDerivation)
    (hMissing : Not p.lambdaJFixedByBackgroundEquation) :
    Not (radionPotentialNoFitClosed p) := by
  intro h
  exact hMissing h.right.right.left

theorem potential_no_fit_closes_after_lambdaJ_background_fix
    (p : RadionPotentialDerivation)
    (hShape : coshShapeDerived p)
    (hAmp : p.amplitudeFixedByBackgroundEquation)
    (hLambda : p.lambdaJFixedByBackgroundEquation)
    (hFull : p.potentialFullyFixedNoFit) :
    radionPotentialNoFitClosed p := by
  exact And.intro hShape (And.intro hAmp (And.intro hLambda hFull))

end P0EFTRadionPotentialDerivation
end JanusFormal
