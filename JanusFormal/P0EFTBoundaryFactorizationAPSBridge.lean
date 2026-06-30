import JanusFormal.P0EFTBoundaryDiracProjectorEL

namespace JanusFormal
namespace P0EFTBoundaryFactorizationAPSBridge

set_option autoImplicit false

structure BoundaryFactorization where
  bulkFluxCoefficientKnown : Prop
  diracBoundaryCoefficientKnown : Prop
  janusPinCoefficientKnown : Prop
  coefficientMatching : Prop
  factorizesAsGammaNormalChiral : Prop
  chiralKernelHalfSpace : Prop

structure APSBridge where
  apsOperatorIsGammaNormalTangentialDirac : Prop
  apsOperatorCommutesWithGammaFive : Prop
  chiralHalfSpaceMatchesAPSSpectralHalfSpace : Prop
  zeroModesEvenOrAbsent : Prop

def factorizationProved (f : BoundaryFactorization) : Prop :=
  f.bulkFluxCoefficientKnown /\
  f.diracBoundaryCoefficientKnown /\
  f.janusPinCoefficientKnown /\
  f.coefficientMatching /\
  f.factorizesAsGammaNormalChiral /\
  f.chiralKernelHalfSpace

def apsBridgeProved (a : APSBridge) : Prop :=
  a.apsOperatorIsGammaNormalTangentialDirac /\
  a.apsOperatorCommutesWithGammaFive /\
  a.chiralHalfSpaceMatchesAPSSpectralHalfSpace /\
  a.zeroModesEvenOrAbsent

def finalBoundarySpectralClosure
    (f : BoundaryFactorization)
    (a : APSBridge) : Prop :=
  factorizationProved f /\ apsBridgeProved a

theorem coefficient_matching_gives_boundary_factorization
    (f : BoundaryFactorization)
    (hBulk : f.bulkFluxCoefficientKnown)
    (hBnd : f.diracBoundaryCoefficientKnown)
    (hJanus : f.janusPinCoefficientKnown)
    (hMatch : f.coefficientMatching)
    (hFactor : f.factorizesAsGammaNormalChiral)
    (hHalf : f.chiralKernelHalfSpace) :
    factorizationProved f := by
  exact And.intro hBulk
    (And.intro hBnd
      (And.intro hJanus
        (And.intro hMatch
          (And.intro hFactor hHalf))))

theorem aps_operator_bridge_gives_spectral_domain
    (a : APSBridge)
    (hOp : a.apsOperatorIsGammaNormalTangentialDirac)
    (hComm : a.apsOperatorCommutesWithGammaFive)
    (hHalf : a.chiralHalfSpaceMatchesAPSSpectralHalfSpace)
    (hZero : a.zeroModesEvenOrAbsent) :
    apsBridgeProved a := by
  exact And.intro hOp (And.intro hComm (And.intro hHalf hZero))

theorem missing_factorization_blocks_final_spectral_closure
    (f : BoundaryFactorization)
    (a : APSBridge)
    (hMissing : Not (factorizationProved f)) :
    Not (finalBoundarySpectralClosure f a) := by
  intro h
  exact hMissing h.left

theorem missing_aps_bridge_blocks_final_spectral_closure
    (f : BoundaryFactorization)
    (a : APSBridge)
    (hMissing : Not (apsBridgeProved a)) :
    Not (finalBoundarySpectralClosure f a) := by
  intro h
  exact hMissing h.right

theorem factorization_and_aps_bridge_close_conditionally
    (f : BoundaryFactorization)
    (a : APSBridge)
    (hFactor : factorizationProved f)
    (hAPS : apsBridgeProved a) :
    finalBoundarySpectralClosure f a := by
  exact And.intro hFactor hAPS

end P0EFTBoundaryFactorizationAPSBridge
end JanusFormal
