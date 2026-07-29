import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricDomainUnitary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCThirdPositiveSphereDirac4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointSpectralSynthesis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFiniteHilbertCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleCoreCompleteness4D
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

The SpinC-specific two-by-two Dirac diagonalization is now uniform at every
positive sphere level and agrees exactly with the complete coefficient
spectrum.  The global scalar Leibniz rule now constructs the first equation
from any genuine smooth scalar multiplier, and a scalar Lichnerowicz seed
promotes canonically to the complete signed block.  The `p = 1` coordinate
packet, the five independent trace-free quadratic `p = 2` smooth
eigensections and the seven independent trace-free cubic `p = 3` smooth
eigensections now inhabit this interface with their exact `D²` equations.
At arbitrary `p`, the same null-curve now supplies exactly `2p+1`
independent complex homogeneous solid harmonics and, directly on the
intrinsic complex SpinC bundle, genuine smooth null-power sections.  Their
uniform first-order recurrence proves the exact `D²` equation and generates
the complete signed seed tower.  The resulting finite complex synthesis is
injective simultaneously across the Hopf zero tower, all positive levels,
both sectors, all circle modes and all multiplicities.  It exactly
intertwines geometric `D²` with the canonical complete coefficient diagonal.
Its actual smooth geometric span now carries the coefficient-induced Hilbert
norm; that span is dense in the full coefficient `L²`, its completion is
unitarily equivalent to that space, and the transported maximal `H²`
operator is exactly conjugate, coercive and bijective.
Independently, the canonical throat volume and descended Hermitian fiber
pairing now define a positive-definite geometric `L²` product on the whole
smooth SpinC core. Its Hilbert completion contains that core densely.
Inside every fixed level/sector/circle eigenspace, geometric Gram--Schmidt
gives an exact Euclidean Parseval isometry without changing the `D²`
eigenvalue. Distinct circle modes in one normal-root sector are now exactly
orthogonal in this independent geometric product, uniformly across sphere
levels and multiplicities. The two opposite normal-root sectors are also
exactly orthogonal for arbitrary levels and circle modes. Distinct sphere
levels in one fixed sector and circle mode are exactly orthogonal by the
rotation Casimir and invariant sphere measure.
These three orthogonality axes now assemble into a single Hilbert-sum
isometry whose image is exactly the closed span of the explicit blocks.
For every positive signed branch, the actual geometric eigenspace span now
also has a canonical finite Parseval isometry, closed completed image and
exact first-order Dirac intertwining.  The sum of the two signs has the
corresponding finite Parseval realization and exact `D²` intertwining.
Thus no further level-by-level packet, inter-level linear-separation or
Lichnerowicz hypothesis is needed.
Radial parity now proves that each signed raw family is linearly independent,
so every sign has exactly the expected `2p+1` multiplicity and the full
two-sign block has dimension `2(2p+1)`. This gives real and
intrinsic-imaginary smooth `D²` eigensections for every complete coefficient
label. The gradient/Casimir identity now also proves that the two opposite
first-order signs are exactly orthogonal inside every fixed spectral block.
Signed orthogonality between distinct labels and the joint isometry are now
proved. Polynomial monopole approximation and temporal Fourier completeness
show that its closed range contains the dense smooth core. The synthesis is
therefore surjective and gives an unconditional unitary onto the independently
constructed geometric completion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalDiracFrontier4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProductThroatHolonomyC3FredholmCertificate4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCThirdPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointSpectralSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFiniteHilbertCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierMonopoleDensity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleCoreCompleteness4D
open P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedPacket4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricDomainUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

local instance globalDiracPrimitiveSpinCComplexSMul :
    SMul Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexSMul period hPeriod

local instance globalDiracPrimitiveSpinCComplexModule :
    Module Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexModule period hPeriod

/-- Unconditional certificate for every Dirac layer already tied down. -/
structure ProgramPGlobalDiracFrontierCertificate4D where
  intrinsicGeometric :
    ProgramPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D
      period hPeriod
  signedSpectral :
    ProgramPPrimitiveSpinCSignedSpectralCompletionCertificate4D
  allLevelGeometricCoefficients :
    ProgramPPrimitiveSpinCGeometricSpectralCertificate4D period hPeriod
  allLevelHarmonicDiagonalization :
    PrimitiveSpinCAllLevelHarmonicDiagonalizationCertificate4D
      period hPeriod
  allLevelSignedGeometricRealization :
    ProgramPD9PrimitiveSpinCAllLevelSignedGeometricCertificate4D
      period hPeriod
  secondPositiveSpherePacket :
    PrimitiveSpinCSecondPositiveSpherePacketCertificate4D
      period hPeriod
  thirdPositiveSpherePacket :
    PrimitiveSpinCThirdPositiveSpherePacketCertificate4D
      period hPeriod
  allLevelSolidHarmonicPacket :
    ∀ degree : Nat,
      PrimitiveSpinCAllLevelSolidHarmonicPacketCertificate4D degree
  allLevelNullHarmonicSquaredSeeds :
    PrimitiveSpinCAllPositiveHarmonicSquaredSeedTower4D period hPeriod
  allLevelNullHarmonicPacketIndependent :
    ∀ positiveLevel sector circleMode,
      LinearIndependent Complex
        (fun multiplicity :
            Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) =>
          (primitiveSpinCAllLevelNullHarmonicSquaredSeed
            period hPeriod positiveLevel multiplicity sector circleMode
          ).scalarSection)
  allLevelNullHarmonicFiniteSynthesis :
    ∀ positiveLevel sector circleMode,
      Function.Injective
        (primitiveSpinCAllLevelNullHarmonicPacketSynthesis
          period hPeriod positiveLevel sector circleMode) ∧
      ∀ coefficients,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (d9PrimitiveSpinCGeometricDiracOperator
              period hPeriod .positiveQuarter
              (primitiveSpinCAllLevelNullHarmonicPacketSynthesis
                period hPeriod positiveLevel sector circleMode
                coefficients)) =
          (normalRootLeviCivitaCorrectedFrequency
                period sector circleMode ^ 2 +
              primitiveSpinCHarmonicSphereEnergy positiveLevel) •
            primitiveSpinCAllLevelNullHarmonicPacketSynthesis
              period hPeriod positiveLevel sector circleMode coefficients
  allPositiveLevelNullHarmonicFiniteSynthesis :
    ∀ sector circleMode,
      Function.Injective
        (primitiveSpinCAllPositiveNullHarmonicSynthesis
          period hPeriod sector circleMode) ∧
      ∀ coefficients,
        primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod
            (primitiveSpinCAllPositiveNullHarmonicSynthesis
              period hPeriod sector circleMode coefficients) =
          primitiveSpinCAllPositiveNullHarmonicSynthesis
            period hPeriod sector circleMode
            (primitiveSpinCAllPositiveNullHarmonicSquaredCoefficientOperator
              period sector circleMode coefficients)
  fixedPositiveLevelJointFourierSynthesis :
    ∀ positiveLevel,
      Function.Injective
        (primitiveSpinCFixedPositiveJointSynthesis
          period hPeriod positiveLevel)
  allPositiveLevelJointSpectralSynthesis :
    Function.Injective
        (primitiveSpinCAllPositiveJointSynthesis period hPeriod) ∧
      ∀ coefficients,
        primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod
            (primitiveSpinCAllPositiveJointSynthesis
              period hPeriod coefficients) =
          primitiveSpinCAllPositiveJointSynthesis period hPeriod
            (primitiveSpinCAllPositiveJointSquaredCoefficientOperator
              period coefficients)
  allFullLevelJointSpectralSynthesis :
    Function.Injective
        (primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod) ∧
      ∀ coefficients,
        primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod
            (primitiveSpinCAllModeNullHarmonicSynthesis
              period hPeriod coefficients) =
          primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod
            (primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator
              period hPeriod coefficients)
  finiteGeometricHilbertCompletion :
    PrimitiveSpinCAllModeFiniteHilbertCompletionCertificate4D
      period hPeriod
  independentGeometricL2Completion :
    ProgramPD9PrimitiveSpinCGeometricL2PairingCertificate4D
      period hPeriod
  geometricL2SignedBranchCompletion :
    ProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletionCertificate4D
      period hPeriod
  geometricL2SignedMultiplicity :
    ProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicityCertificate4D
      period hPeriod
  geometricL2BlockOrthonormalization :
    ProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalizationCertificate4D
      period hPeriod
  geometricL2FourierOrthogonality :
    ProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonalityCertificate4D
      period hPeriod
  geometricL2LevelOrthogonality :
    ProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonalityCertificate4D
      period hPeriod
  geometricL2GradientCasimir :
    ProgramPD9PrimitiveSpinCGeometricL2GradientCasimirCertificate4D
      period hPeriod
  geometricL2JointIsometry :
    ProgramPD9PrimitiveSpinCGeometricL2JointIsometryCertificate4D
      period hPeriod
  geometricL2SignedJointIsometry :
    ProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometryCertificate4D
      period hPeriod
  geometricL2FourierMonopoleCoreComplete :
    PrimitiveSpinCFourierMonopoleCoreComplete period hPeriod
  geometricL2SignedGlobalDensity :
    PrimitiveSpinCGeometricL2SignedGlobalDensity period hPeriod
  geometricL2SignedGlobalUnitary :
    PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
        period hPeriod ≃ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter
  allModeNullHarmonicSquaredSections :
    ∀ mode : PrimitiveSpinCGeometricFullMode,
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCAllModeNullHarmonicRealSection
              period hPeriod mode)) =
        primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode •
          primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod mode ∧
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCAllModeNullHarmonicImaginarySection
              period hPeriod mode)) =
        primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode •
          primitiveSpinCAllModeNullHarmonicImaginarySection
            period hPeriod mode
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
  allLevelHarmonicDiagonalization :=
    primitiveSpinCAllLevelHarmonicDiagonalizationCertificate4D
      period hPeriod
  allLevelSignedGeometricRealization :=
    programPD9PrimitiveSpinCAllLevelSignedGeometricCertificate4D
      period hPeriod
  secondPositiveSpherePacket :=
    primitiveSpinCSecondPositiveSpherePacketCertificate4D
      period hPeriod
  thirdPositiveSpherePacket :=
    primitiveSpinCThirdPositiveSpherePacketCertificate4D
      period hPeriod
  allLevelSolidHarmonicPacket :=
    primitiveSpinCAllLevelSolidHarmonicPacketCertificate4D
  allLevelNullHarmonicSquaredSeeds :=
    primitiveSpinCAllLevelNullHarmonicSquaredSeedTower period hPeriod
  allLevelNullHarmonicPacketIndependent :=
    primitiveSpinCAllLevelNullHarmonicSquaredSeed_linearIndependent
      period hPeriod
  allLevelNullHarmonicFiniteSynthesis := by
    intro positiveLevel sector circleMode
    exact
      ⟨primitiveSpinCAllLevelNullHarmonicPacketSynthesis_injective
          period hPeriod positiveLevel sector circleMode,
        primitiveSpinCAllLevelNullHarmonicPacketSynthesis_dirac_sq
          period hPeriod positiveLevel sector circleMode⟩
  allPositiveLevelNullHarmonicFiniteSynthesis :=
    primitiveSpinCAllPositiveNullHarmonicSpectralRealization_closed
      period hPeriod
  fixedPositiveLevelJointFourierSynthesis :=
    primitiveSpinCFixedPositiveJointSynthesis_injective period hPeriod
  allPositiveLevelJointSpectralSynthesis :=
    ⟨primitiveSpinCAllPositiveJointSynthesis_injective period hPeriod,
      primitiveSpinCAllPositiveJointSynthesis_intertwines_dirac_sq
        period hPeriod⟩
  allFullLevelJointSpectralSynthesis :=
    ⟨primitiveSpinCAllModeNullHarmonicSynthesis_injective period hPeriod,
      primitiveSpinCAllModeNullHarmonicSynthesis_intertwines_dirac_sq
        period hPeriod⟩
  finiteGeometricHilbertCompletion :=
    primitiveSpinCAllModeFiniteHilbertCompletionCertificate4D
      period hPeriod
  independentGeometricL2Completion :=
    programPD9PrimitiveSpinCGeometricL2PairingCertificate4D
      period hPeriod
  geometricL2SignedBranchCompletion :=
    programPD9PrimitiveSpinCGeometricL2SignedBranchCompletionCertificate4D
      period hPeriod
  geometricL2SignedMultiplicity :=
    programPD9PrimitiveSpinCGeometricL2SignedMultiplicityCertificate4D
      period hPeriod
  geometricL2BlockOrthonormalization :=
    programPD9PrimitiveSpinCGeometricL2BlockOrthonormalizationCertificate4D
      period hPeriod
  geometricL2FourierOrthogonality :=
    programPD9PrimitiveSpinCGeometricL2FourierOrthogonalityCertificate4D
      period hPeriod
  geometricL2LevelOrthogonality :=
    programPD9PrimitiveSpinCGeometricL2LevelOrthogonalityCertificate4D
      period hPeriod
  geometricL2GradientCasimir :=
    programPD9PrimitiveSpinCGeometricL2GradientCasimirCertificate4D
      period hPeriod
  geometricL2JointIsometry :=
    programPD9PrimitiveSpinCGeometricL2JointIsometryCertificate4D
      period hPeriod
  geometricL2SignedJointIsometry :=
    programPD9PrimitiveSpinCGeometricL2SignedJointIsometryCertificate4D
      period hPeriod
  geometricL2FourierMonopoleCoreComplete :=
    primitiveSpinCFourierMonopoleCoreComplete_proved period hPeriod
  geometricL2SignedGlobalDensity :=
    primitiveSpinCGeometricL2SignedGlobalDensity_fourierMonopole
      period hPeriod
  geometricL2SignedGlobalUnitary :=
    primitiveSpinCGeometricL2SignedFourierMonopoleUnitary_proved
      period hPeriod
  allModeNullHarmonicSquaredSections := fun mode =>
    ⟨primitiveSpinCAllModeNullHarmonicRealSection_dirac_sq
        period hPeriod mode,
      primitiveSpinCAllModeNullHarmonicImaginarySection_dirac_sq
        period hPeriod mode⟩
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

theorem global_dirac_closed_gate :
    Nonempty (ProgramPGlobalDiracFrontierCertificate4D period hPeriod) :=
  global_dirac_frontier_gate period hPeriod

theorem global_dirac_all_level_harmonic_diagonalization_gate :
    Nonempty
      (PrimitiveSpinCAllLevelHarmonicDiagonalizationCertificate4D
        period hPeriod) :=
  ⟨primitiveSpinCAllLevelHarmonicDiagonalizationCertificate4D
    period hPeriod⟩

theorem global_dirac_all_level_signed_geometric_realization_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCAllLevelSignedGeometricCertificate4D
        period hPeriod) :=
  primitiveSpinCAllLevelSignedGeometric_gate period hPeriod

/-- One genuine scalar Lichnerowicz seed generates its complete signed
first-order Dirac block without any further geometric hypothesis. -/
theorem global_dirac_scalar_lichnerowicz_reduction_gate
    (positiveLevel : Nat)
    (harmonic :
      PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod positiveLevel) :
    Nonempty
      (∀ sector circleMode,
        PrimitiveSpinCHarmonicDiracSeed4D
          period hPeriod positiveLevel sector circleMode) :=
  ⟨fun sector circleMode => harmonic.toDiracSeed sector circleMode⟩

/-- The already constructed first sphere-coordinate packet is a concrete
scalar Lichnerowicz seed. -/
theorem global_dirac_first_positive_scalar_lichnerowicz_gate
    (coordinate : Fin 3) :
    Nonempty
      (PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod 0) :=
  ⟨primitiveSpinCFirstPositiveScalarHarmonicLichnerowiczSeed
    period hPeriod coordinate⟩

/-- The complete fivefold `p = 2` scalar packet is concrete, independent and
already promoted to signed first-order Dirac seeds. -/
theorem global_dirac_second_positive_scalar_packet_gate :
    Nonempty
      (PrimitiveSpinCSecondPositiveSpherePacketCertificate4D
        period hPeriod) :=
  primitiveSpinCSecondPositiveSpherePacket_gate period hPeriod

/-- The five concrete `p = 2` smooth squared-Dirac eigensections are
independent in every normal-root sector and circle mode. -/
theorem global_dirac_second_positive_section_packet_linearIndependent
    (sector : NormalRootChoice) (mode : Int) :
    LinearIndependent Real
      (fun multiplicity : Fin 5 =>
        primitiveSpinCHopfSecondSphereTraceFreeSection
          period hPeriod multiplicity sector mode) :=
  (primitiveSpinCSecondPositiveSpherePacketCertificate4D
    period hPeriod).section_linearIndependent sector mode

/-- The complete sevenfold `p = 3` scalar packet is concrete, independent and
already promoted to signed first-order Dirac seeds. -/
theorem global_dirac_third_positive_scalar_packet_gate :
    Nonempty
      (PrimitiveSpinCThirdPositiveSpherePacketCertificate4D
        period hPeriod) :=
  primitiveSpinCThirdPositiveSpherePacket_gate period hPeriod

/-- The seven concrete `p = 3` smooth squared-Dirac eigensections are
independent in every normal-root sector and circle mode. -/
theorem global_dirac_third_positive_section_packet_linearIndependent
    (sector : NormalRootChoice) (mode : Int) :
    LinearIndependent Real
      (fun multiplicity : Fin 7 =>
        primitiveSpinCHopfThirdSphereTraceFreeSection
          period hPeriod multiplicity sector mode) :=
  (primitiveSpinCThirdPositiveSpherePacketCertificate4D
    period hPeriod).section_linearIndependent sector mode

/-- A single construction now provides the exact algebraic harmonic packet
and spherical energy at every degree. -/
theorem global_dirac_all_level_solid_harmonic_packet_gate
    (degree : Nat) :
    Nonempty
      (PrimitiveSpinCAllLevelSolidHarmonicPacketCertificate4D degree) :=
  ⟨primitiveSpinCAllLevelSolidHarmonicPacketCertificate4D degree⟩

/-- The null-power recurrence realizes every positive level by genuine
smooth squared-Dirac eigensections on the intrinsic SpinC bundle. -/
theorem global_dirac_all_level_null_harmonic_squared_seed_gate :
    Nonempty
      (PrimitiveSpinCAllPositiveHarmonicSquaredSeedTower4D
        period hPeriod) :=
  ⟨primitiveSpinCAllLevelNullHarmonicSquaredSeedTower period hPeriod⟩

/-- The same tower canonically supplies both signed first-order branches. -/
theorem global_dirac_all_level_null_harmonic_dirac_seed_gate :
    Nonempty
      (PrimitiveSpinCAllPositiveHarmonicSeedTower4D period hPeriod) :=
  ⟨primitiveSpinCAllLevelNullHarmonicDiracSeedTower period hPeriod⟩

/-- At every positive sphere level the smooth scalar packet has the exact
physical complex multiplicity `2p+1`. -/
theorem global_dirac_all_level_null_harmonic_packet_linearIndependent
    (positiveLevel : Nat)
    (sector : NormalRootChoice) (circleMode : Int) :
    LinearIndependent Complex
      (fun multiplicity :
          Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)) =>
        (primitiveSpinCAllLevelNullHarmonicSquaredSeed
          period hPeriod positiveLevel multiplicity sector circleMode
        ).scalarSection) :=
  primitiveSpinCAllLevelNullHarmonicSquaredSeed_linearIndependent
    period hPeriod positiveLevel sector circleMode

/-- Every finite all-level packet has faithful complex coordinates and
intertwines the genuine squared geometric Dirac operator. -/
theorem global_dirac_all_level_null_harmonic_finite_synthesis_gate
    (positiveLevel : Nat)
    (sector : NormalRootChoice) (circleMode : Int) :
    Function.Injective
        (primitiveSpinCAllLevelNullHarmonicPacketSynthesis
          period hPeriod positiveLevel sector circleMode) ∧
      ∀ coefficients,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (d9PrimitiveSpinCGeometricDiracOperator
              period hPeriod .positiveQuarter
              (primitiveSpinCAllLevelNullHarmonicPacketSynthesis
                period hPeriod positiveLevel sector circleMode
                coefficients)) =
          (normalRootLeviCivitaCorrectedFrequency
                period sector circleMode ^ 2 +
              primitiveSpinCHarmonicSphereEnergy positiveLevel) •
            primitiveSpinCAllLevelNullHarmonicPacketSynthesis
              period hPeriod positiveLevel sector circleMode coefficients :=
  ⟨primitiveSpinCAllLevelNullHarmonicPacketSynthesis_injective
      period hPeriod positiveLevel sector circleMode,
    primitiveSpinCAllLevelNullHarmonicPacketSynthesis_dirac_sq
      period hPeriod positiveLevel sector circleMode⟩

/-- Finite packets are jointly faithful across every positive sphere level
at fixed sector/circle mode, with exact diagonal squared-Dirac action. -/
theorem global_dirac_all_positive_level_null_harmonic_synthesis_gate
    (sector : NormalRootChoice) (circleMode : Int) :
    Function.Injective
        (primitiveSpinCAllPositiveNullHarmonicSynthesis
          period hPeriod sector circleMode) ∧
      ∀ coefficients,
        primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod
            (primitiveSpinCAllPositiveNullHarmonicSynthesis
              period hPeriod sector circleMode coefficients) =
          primitiveSpinCAllPositiveNullHarmonicSynthesis
            period hPeriod sector circleMode
            (primitiveSpinCAllPositiveNullHarmonicSquaredCoefficientOperator
              period sector circleMode coefficients) :=
  primitiveSpinCAllPositiveNullHarmonicSpectralRealization_closed
    period hPeriod sector circleMode

/-- At every arbitrary fixed positive level, one finite synthesis is faithful
jointly in both sectors, every circle mode and every multiplicity. -/
theorem global_dirac_fixed_positive_level_joint_fourier_synthesis_gate
    (positiveLevel : Nat) :
    Function.Injective
      (primitiveSpinCFixedPositiveJointSynthesis
        period hPeriod positiveLevel) :=
  primitiveSpinCFixedPositiveJointSynthesis_injective
    period hPeriod positiveLevel

/-- All positive levels, both sectors, every circle mode and every
multiplicity now form one faithful diagonal geometric synthesis. -/
theorem global_dirac_all_positive_joint_spectral_synthesis_gate :
    Function.Injective
        (primitiveSpinCAllPositiveJointSynthesis period hPeriod) ∧
      ∀ coefficients,
        primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod
            (primitiveSpinCAllPositiveJointSynthesis
              period hPeriod coefficients) =
          primitiveSpinCAllPositiveJointSynthesis period hPeriod
            (primitiveSpinCAllPositiveJointSquaredCoefficientOperator
              period coefficients) :=
  ⟨primitiveSpinCAllPositiveJointSynthesis_injective period hPeriod,
    primitiveSpinCAllPositiveJointSynthesis_intertwines_dirac_sq
      period hPeriod⟩

/-- The canonical complete coefficient index, including the Hopf zero tower,
has one faithful smooth geometric synthesis with exact diagonal `D²`. -/
theorem global_dirac_all_full_joint_spectral_synthesis_gate :
    Function.Injective
        (primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod) ∧
      ∀ coefficients,
        primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod
            (primitiveSpinCAllModeNullHarmonicSynthesis
              period hPeriod coefficients) =
          primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod
            (primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator
              period hPeriod coefficients) :=
  ⟨primitiveSpinCAllModeNullHarmonicSynthesis_injective period hPeriod,
    primitiveSpinCAllModeNullHarmonicSynthesis_intertwines_dirac_sq
      period hPeriod⟩

/-- The complete smooth eigensection span has a canonical dense Hilbert
completion, maximal-domain conjugacy, coercivity and bijectivity. -/
theorem global_dirac_finite_geometric_hilbert_completion_gate :
    Nonempty
      (PrimitiveSpinCAllModeFiniteHilbertCompletionCertificate4D
        period hPeriod) :=
  primitiveSpinCAllModeFiniteHilbertCompletion_gate period hPeriod

/-- The whole smooth primitive SpinC core has its independently integrated
geometric `L²` Hilbert completion. -/
theorem global_dirac_independent_geometric_l2_completion_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2PairingCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2Pairing_gate period hPeriod

/-- Every positive-level first-order signed branch, and the full two-sign
block, has exact Parseval coordinates and closed image in the independently
integrated geometric completion. -/
theorem global_dirac_geometric_l2_signed_branch_completion_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletionCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2SignedBranchCompletion_gate period hPeriod

/-- Every positive signed branch has its exact `2p+1` multiplicity; the
complete two-sign block has dimension `2(2p+1)`. -/
theorem global_dirac_geometric_l2_signed_multiplicity_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicityCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2SignedMultiplicity_gate period hPeriod

/-- Every fixed level/sector/circle multiplicity block has exact geometric
Parseval coordinates preserving its intrinsic `D²` eigenvalue. -/
theorem global_dirac_geometric_l2_block_orthonormalization_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalizationCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2BlockOrthonormalization_gate period hPeriod

/-- Distinct same-sector circle modes and the two opposite sectors are
exactly orthogonal in the independently integrated geometric `L²` product. -/
theorem global_dirac_geometric_l2_fourier_orthogonality_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonalityCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2FourierOrthogonality_gate period hPeriod

/-- Distinct sphere levels in one sector and circle mode are exactly
orthogonal in the independently integrated geometric `L²` product. -/
theorem global_dirac_geometric_l2_level_orthogonality_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonalityCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2LevelOrthogonality_gate period hPeriod

/-- The gradient norm is the exact round-sphere Casimir energy, and the two
first-order signs are orthogonal inside every fixed spectral block. -/
theorem global_dirac_geometric_l2_gradient_casimir_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2GradientCasimirCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2GradientCasimir_gate period hPeriod

/-- All normalized finite blocks assemble into one isometric Hilbert-sum
synthesis whose range is their exact closed geometric span. -/
theorem global_dirac_geometric_l2_joint_isometry_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2JointIsometryCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2JointIsometry_gate period hPeriod

/-- The zero tower and all positive signed blocks form one orthogonal global
Hilbert-sum isometry. -/
theorem global_dirac_geometric_l2_signed_joint_isometry_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometryCertificate4D
        period hPeriod) :=
  primitiveSpinCGeometricL2SignedJointIsometry_gate period hPeriod

/-- Fourier--monopole packets approximate every genuine smooth SpinC section
in the independent geometric norm. -/
theorem global_dirac_fourier_monopole_core_complete_gate :
    PrimitiveSpinCFourierMonopoleCoreComplete period hPeriod :=
  primitiveSpinCFourierMonopoleCoreComplete_proved period hPeriod

/-- The signed spectral range is dense in the full geometric completion. -/
theorem global_dirac_geometric_l2_signed_density_gate :
    PrimitiveSpinCGeometricL2SignedGlobalDensity period hPeriod :=
  primitiveSpinCGeometricL2SignedGlobalDensity_fourierMonopole
    period hPeriod

/-- Global geometric DIRAC unitary from signed spectral coefficients. -/
def globalDiracGeometricL2SignedUnitary :
    PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
        period hPeriod ≃ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  primitiveSpinCGeometricL2SignedFourierMonopoleUnitary_proved
    period hPeriod

/-- Every label of the complete squared coefficient tower now has genuine
real and intrinsic-imaginary smooth geometric representatives. -/
theorem global_dirac_all_mode_null_harmonic_squared_sections_gate
    (mode : PrimitiveSpinCGeometricFullMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod mode)) =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode •
        primitiveSpinCAllModeNullHarmonicRealSection
          period hPeriod mode ∧
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCAllModeNullHarmonicImaginarySection
            period hPeriod mode)) =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode •
        primitiveSpinCAllModeNullHarmonicImaginarySection
          period hPeriod mode :=
  ⟨primitiveSpinCAllModeNullHarmonicRealSection_dirac_sq
      period hPeriod mode,
    primitiveSpinCAllModeNullHarmonicImaginarySection_dirac_sq
      period hPeriod mode⟩

end
end P0EFTJanusProgramPGlobalDiracFrontier4D
end JanusFormal
