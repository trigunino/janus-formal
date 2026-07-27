import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyC3FredholmCertificate4D

/-!
# Exact frontier of the global Dirac problem

This module consolidates the strongest unconditional Dirac results without
identifying distinct models.  The actual doubled D9 bundle has an intrinsic
smooth elliptic first-order operator.  The corrected signed spectral model
has a complete self-adjoint Fredholm realization.  Their geometric
intertwining is proved on the zero/first-sphere packet, while the separated
product model supplies a `C³` common-domain Fredholm family.

`DIRAC-GLOBAL-01` still requires one geometric Fourier/unitary identification
covering every sphere level and the completed common domain.  No such bridge
is assumed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalDiracFrontier4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProductThroatHolonomyC3FredholmCertificate4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Unconditional certificate for every Dirac layer already tied down. -/
structure ProgramPGlobalDiracFrontierCertificate4D where
  intrinsicGeometric :
    ProgramPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D
      period hPeriod
  signedSpectral :
    ProgramPPrimitiveSpinCSignedSpectralCompletionCertificate4D
  lowEnergyGeometric : ∀ sector circleMode,
    Function.Injective
        (primitiveSpinCHopfLowEnergySignedSynthesis
          period hPeriod sector circleMode) ∧
      (∀ coefficients,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCHopfLowEnergySignedSynthesis
              period hPeriod sector circleMode coefficients) =
          primitiveSpinCHopfLowEnergySignedSynthesis
            period hPeriod sector circleMode
            (primitiveSpinCHopfLowEnergySignedCoefficientOperator
              period sector circleMode coefficients)) ∧
      primitiveSpinCHopfLowEnergySignedActualDirac
          period hPeriod sector circleMode =
        (primitiveSpinCHopfLowEnergySignedSynthesisEquiv
            period hPeriod sector circleMode).toLinearMap.comp
          ((primitiveSpinCHopfLowEnergySignedCoefficientOperator
              period sector circleMode).comp
            (primitiveSpinCHopfLowEnergySignedSynthesisEquiv
              period hPeriod sector circleMode).symm.toLinearMap)
  separatedC3Fredholm : ∀ data fold reference,
    ProductThroatHolonomyC3FredholmCertificate data fold reference

/-- The exact current frontier is inhabited without extra hypotheses. -/
def programPGlobalDiracFrontierCertificate4D :
    ProgramPGlobalDiracFrontierCertificate4D period hPeriod where
  intrinsicGeometric :=
    programPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D
      period hPeriod
  signedSpectral :=
    programPPrimitiveSpinCSignedSpectralCompletionCertificate4D
  lowEnergyGeometric :=
    primitiveSpinCHopfLowEnergySignedGeometricRealization_closed
      period hPeriod
  separatedC3Fredholm :=
    productThroatHolonomyC3FredholmCertificate

theorem global_dirac_frontier_gate :
    Nonempty (ProgramPGlobalDiracFrontierCertificate4D period hPeriod) :=
  ⟨programPGlobalDiracFrontierCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPGlobalDiracFrontier4D
end JanusFormal
