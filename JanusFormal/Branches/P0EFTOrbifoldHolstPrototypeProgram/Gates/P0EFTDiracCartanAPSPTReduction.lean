import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTPinAnomalySelection

namespace JanusFormal
namespace P0EFTDiracCartanAPSPTReduction

set_option autoImplicit false

structure DiracCartanAPSDomain where
  l2SpinorDomain : Prop
  apsProjectorBoundary : Prop
  fredholmProblem : Prop

structure PTSpectralAction where
  pinMinus : Prop
  ptSquaresToMinusOne : Prop
  preservesAPSDomain : Prop
  signReversesDiracSpectrum : Prop
  merelyCommutesWithDirac : Prop
  zeroModesEvenOrAbsent : Prop

structure PinMinusCliffordLift where
  pinMinus : Prop
  orbifoldTetradSignTransition : Prop
  cliffordGeneratorSignRule : Prop
  cartanTorsionTermsRespectPT : Prop
  traceTorsionSourcesBoundaryChirality : Prop
  boundaryChiralityProjection : Prop
  projectorSwapCompensatedByChirality : Prop
  apsDomainInvariantUnderPT : Prop
  zeroModesEvenOrAbsent : Prop

def janusGeometryForcesDomainInvariant
    (lift : PinMinusCliffordLift) : Prop :=
  lift.orbifoldTetradSignTransition /\
  lift.traceTorsionSourcesBoundaryChirality /\
  lift.boundaryChiralityProjection /\
  lift.projectorSwapCompensatedByChirality /\
  lift.apsDomainInvariantUnderPT

def etaCancelsConditionally
    (domain : DiracCartanAPSDomain)
    (pt : PTSpectralAction) : Prop :=
  domain.apsProjectorBoundary /\
  domain.fredholmProblem /\
  pt.pinMinus /\
  pt.preservesAPSDomain /\
  pt.signReversesDiracSpectrum /\
  pt.zeroModesEvenOrAbsent

def liftForcesPTReduction
    (lift : PinMinusCliffordLift)
    (pt : PTSpectralAction) : Prop :=
  lift.pinMinus /\
  lift.orbifoldTetradSignTransition /\
  lift.cliffordGeneratorSignRule /\
  lift.cartanTorsionTermsRespectPT /\
  lift.traceTorsionSourcesBoundaryChirality /\
  lift.boundaryChiralityProjection /\
  lift.projectorSwapCompensatedByChirality /\
  lift.apsDomainInvariantUnderPT /\
  lift.zeroModesEvenOrAbsent /\
  pt.pinMinus /\
  pt.preservesAPSDomain /\
  pt.signReversesDiracSpectrum /\
  pt.zeroModesEvenOrAbsent

theorem sign_reversing_pt_gives_conditional_eta_zero
    (domain : DiracCartanAPSDomain)
    (pt : PTSpectralAction)
    (hDomain : domain.apsProjectorBoundary)
    (hFredholm : domain.fredholmProblem)
    (hPin : pt.pinMinus)
    (hPreserves : pt.preservesAPSDomain)
    (hSign : pt.signReversesDiracSpectrum)
    (hZero : pt.zeroModesEvenOrAbsent) :
    etaCancelsConditionally domain pt := by
  exact And.intro hDomain
    (And.intro hFredholm
      (And.intro hPin
        (And.intro hPreserves
          (And.intro hSign hZero))))

theorem pin_minus_clifford_lift_yields_pt_reduction
    (lift : PinMinusCliffordLift)
    (pt : PTSpectralAction)
    (hPin : lift.pinMinus)
    (hTetrad : lift.orbifoldTetradSignTransition)
    (hClifford : lift.cliffordGeneratorSignRule)
    (hTorsion : lift.cartanTorsionTermsRespectPT)
    (hTrace : lift.traceTorsionSourcesBoundaryChirality)
    (hChiral : lift.boundaryChiralityProjection)
    (hProjector : lift.projectorSwapCompensatedByChirality)
    (hAPSDomain : lift.apsDomainInvariantUnderPT)
    (hZero : lift.zeroModesEvenOrAbsent)
    (hPTPin : pt.pinMinus)
    (hPTDomain : pt.preservesAPSDomain)
    (hPTSign : pt.signReversesDiracSpectrum)
    (hPTZero : pt.zeroModesEvenOrAbsent) :
    liftForcesPTReduction lift pt := by
  exact And.intro hPin
    (And.intro hTetrad
      (And.intro hClifford
        (And.intro hTorsion
          (And.intro hTrace
            (And.intro hChiral
              (And.intro hProjector
                (And.intro hAPSDomain
                  (And.intro hZero
                    (And.intro hPTPin
                      (And.intro hPTDomain
                        (And.intro hPTSign hPTZero)))))))))))

theorem tetrad_trace_torsion_and_projector_compensation_give_domain_invariance
    (lift : PinMinusCliffordLift)
    (hTetrad : lift.orbifoldTetradSignTransition)
    (hTrace : lift.traceTorsionSourcesBoundaryChirality)
    (hChiral : lift.boundaryChiralityProjection)
    (hProjector : lift.projectorSwapCompensatedByChirality)
    (hDomain : lift.apsDomainInvariantUnderPT) :
    janusGeometryForcesDomainInvariant lift := by
  exact And.intro hTetrad
    (And.intro hTrace
      (And.intro hChiral
        (And.intro hProjector hDomain)))

theorem pin_minus_lift_and_aps_domain_give_conditional_eta_zero
    (domain : DiracCartanAPSDomain)
    (pt : PTSpectralAction)
    (lift : PinMinusCliffordLift)
    (hAPS : domain.apsProjectorBoundary)
    (hFredholm : domain.fredholmProblem)
    (hReduction : liftForcesPTReduction lift pt) :
    etaCancelsConditionally domain pt := by
  exact And.intro hAPS
    (And.intro hFredholm
      (And.intro hReduction.right.right.right.right.right.right.right.right.right.left
        (And.intro hReduction.right.right.right.right.right.right.right.right.right.right.left
          (And.intro hReduction.right.right.right.right.right.right.right.right.right.right.right.left
            hReduction.right.right.right.right.right.right.right.right.right.right.right.right))))

theorem commutation_alone_does_not_prove_eta_cancellation
    (domain : DiracCartanAPSDomain)
    (pt : PTSpectralAction)
    (hMissingSign : Not pt.signReversesDiracSpectrum) :
    Not (etaCancelsConditionally domain pt) := by
  intro h
  exact hMissingSign h.right.right.right.right.left

theorem missing_aps_domain_blocks_spectral_reduction
    (domain : DiracCartanAPSDomain)
    (pt : PTSpectralAction)
    (hMissingAPS : Not domain.apsProjectorBoundary) :
    Not (etaCancelsConditionally domain pt) := by
  intro h
  exact hMissingAPS h.left

end P0EFTDiracCartanAPSPTReduction
end JanusFormal
