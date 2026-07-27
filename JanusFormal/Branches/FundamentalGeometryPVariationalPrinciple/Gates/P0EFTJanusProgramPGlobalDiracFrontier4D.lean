import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricDomainUnitary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyC3FredholmCertificate4D

/-!
# Exact frontier of the global Dirac problem

This module consolidates the strongest unconditional Dirac results without
identifying distinct models.  The actual doubled D9 bundle has an intrinsic
smooth elliptic first-order operator.  The complete all-level coefficient
tower, including the zero sphere mode and both normal-root sectors, has a
dense self-adjoint Fredholm realization.  Its geometric intertwining is
proved on the zero/first-sphere packet, while the separated product model
supplies a `C³` common-domain Fredholm family.  The complete coefficient
domain is now unitarily identified with the zero tower plus the positive D10
domain, with exact operator conjugacy and graph-energy preservation.  Any
all-level geometric Fourier realization now extends canonically and
unitarily to the completed coefficient domain, including its maximal graph
domain and squared operator.

`DIRAC-GLOBAL-01` still requires the geometric Fourier synthesis of every
sphere level.  Completion is no longer an independent assumption.
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
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricDomainUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Unconditional certificate for every Dirac layer already tied down. -/
structure ProgramPGlobalDiracFrontierCertificate4D where
  intrinsicGeometric :
    ProgramPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D
      period hPeriod
  signedSpectral :
    ProgramPPrimitiveSpinCSignedSpectralCompletionCertificate4D
  allLevelGeometricCoefficients :
    ProgramPPrimitiveSpinCGeometricSpectralCertificate4D period hPeriod
  coefficientDomainUnitary :
    ProgramPPrimitiveSpinCGeometricDomainUnitaryCertificate4D
      period hPeriod
  geometricFourierCompletion :
    ∀ realization :
        ProgramPD9PrimitiveSpinCGeometricFourierRealization4D
          period hPeriod,
      realization.GeometricFourierCompletionCertificate
        period hPeriod
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
  allLevelGeometricCoefficients :=
    programPPrimitiveSpinCGeometricSpectralCertificate4D period hPeriod
  coefficientDomainUnitary :=
    programPPrimitiveSpinCGeometricDomainUnitaryCertificate4D
      period hPeriod
  geometricFourierCompletion := fun realization =>
    realization.geometricFourierCompletionCertificate period hPeriod
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
