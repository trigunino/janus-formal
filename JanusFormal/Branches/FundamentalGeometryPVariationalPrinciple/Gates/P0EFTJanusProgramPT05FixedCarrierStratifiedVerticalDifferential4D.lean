import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D

/-!
# Fixed-carrier stratified vertical differential

This module extends Gate 846's degree-four lift to a fixed-carrier density
cochain containing every Gate-830 component: bulk, non-null boundary, null
faces and joints.  The SpinC frontier is retained through its scalar action
coefficient.  A signed local generator differential is defined in every
horizontal degree and commutes with sectorwise integration.

Actual derivatives along a one-parameter family are kept in two separate
contracts: one records the pointwise derivative densities, while the other
records the still-missing differentiation-under-integration statements.  They
are not used to manufacture the algebraic generator differential.

The constructed local differential has square zero.  After integration it
anticommutes with Gate 819's horizontal differential, and this identity is
specialized to the completed conditional horizontal targets of Gate 851.  No
terminal T05 statement is made.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05FixedCarrierStratifiedVerticalDifferential4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05AvailableStratifiedHorizontalComplex4D
open P0EFTJanusProgramPT05StratifiedLocalVerticalDensityComplex4D
open P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Degree-zero density coefficients in a fibre with fixed null intervals. -/
structure ProgramPT05FixedCarrierStratifiedDensityCoefficient
    (period : Real) (hPeriod : period ≠ 0)
    (NullFace : Type*)
    (_nullFaceInterval : NullFace → OrientedNullInterval) where
  bulkDensity : C(EffectiveQuotient period hPeriod, Real)
  spinCCoefficient : Real
  llDensity : C(EffectiveThroat period hPeriod, Real)
  nonNullBoundaryDensity : CandidateANormalBoundaryScalarField period hPeriod
  nullBoundaryDensity : NullFace → Real → Real
  jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real

/-- Gate 830 mapped into the fixed-carrier coefficient fibre. -/
def programPT05FixedCarrierStratifiedDensityCoefficientOfGeometric
    {NullFace : Type*}
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    ProgramPT05FixedCarrierStratifiedDensityCoefficient period hPeriod
      NullFace density.nullFaceInterval where
  bulkDensity := density.bulkDensity
  spinCCoefficient := programPT05BulkSpinCFrontierAction period hPeriod
    couplings density.spinCFrontier
  llDensity := density.llDensity
  nonNullBoundaryDensity := density.nonNullBoundaryDensity
  nullBoundaryDensity := density.nullBoundaryDensity
  jointDensity := density.jointDensity

/-- Supplied pointwise derivatives of a fixed-carrier density curve.  This
contract does not claim that any integral may yet be differentiated. -/
structure ProgramPT05FixedCarrierPointwiseVerticalDerivativeContract
    {NullFace : Type*}
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (curve : Real → ProgramPT05FixedCarrierStratifiedDensityCoefficient
      period hPeriod NullFace nullFaceInterval)
    (baseParameter : Real)
    (derivative : ProgramPT05FixedCarrierStratifiedVerticalDensityCochain
      period hPeriod NullFace nullFaceInterval) : Prop where
  bulkDerivative : ∀ point : EffectiveQuotient period hPeriod,
    HasDerivAt (fun parameter ↦ (curve parameter).bulkDensity point)
      (derivative.bulkVerticalDensity point) baseParameter
  spinCDerivative :
    HasDerivAt (fun parameter ↦ (curve parameter).spinCCoefficient)
      derivative.spinCVerticalCoefficient baseParameter
  llDerivative : ∀ point : EffectiveThroat period hPeriod,
    HasDerivAt (fun parameter ↦ (curve parameter).llDensity point)
      (derivative.llVerticalDensity point) baseParameter
  nonNullDerivative : ∀ point : OrientationBoundary period hPeriod,
    HasDerivAt
      (fun parameter ↦ (curve parameter).nonNullBoundaryDensity point)
      (derivative.nonNullBoundaryVerticalDensity point) baseParameter
  nullDerivative : ∀ (face : NullFace) (point : Real),
    HasDerivAt
      (fun parameter ↦ (curve parameter).nullBoundaryDensity face point)
      (derivative.nullBoundaryVerticalDensity face point) baseParameter
  jointDerivative : ∀ (face : NullFace)
      (endpoint : ProgramPT05NullJointEndpoint),
    HasDerivAt
      (fun parameter ↦ (curve parameter).jointDensity face endpoint)
      (derivative.jointVerticalDensity face endpoint) baseParameter

/-- The analytic interchange statements not implied by pointwise derivative
data.  Each stratum is displayed independently. -/
structure ProgramPT05FixedCarrierVerticalIntegrationDerivativeContract
    {NullFace : Type*} [Fintype NullFace]
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (curve : Real → ProgramPT05FixedCarrierStratifiedDensityCoefficient
      period hPeriod NullFace nullFaceInterval)
    (baseParameter : Real)
    (derivative : ProgramPT05FixedCarrierStratifiedVerticalDensityCochain
      period hPeriod NullFace nullFaceInterval) : Prop where
  bulkDerivativeUnderIntegral :
    HasDerivAt
      (fun parameter ↦
        (programPT05GeometricBulkDensityIntegral period hPeriod
              (curve parameter).bulkDensity +
            (curve parameter).spinCCoefficient) +
          programPT05GeometricLLDensityIntegral period hPeriod
            (curve parameter).llDensity)
      ((programPT05GeometricBulkDensityIntegral period hPeriod
            derivative.bulkVerticalDensity +
          derivative.spinCVerticalCoefficient) +
        programPT05GeometricLLDensityIntegral period hPeriod
          derivative.llVerticalDensity) baseParameter
  nonNullDerivativeUnderIntegral :
    HasDerivAt
      (fun parameter ↦ programPT05GeometricGHYDensityIntegral period hPeriod
        (curve parameter).nonNullBoundaryDensity)
      (programPT05GeometricGHYDensityIntegral period hPeriod
        derivative.nonNullBoundaryVerticalDensity) baseParameter
  nullDerivativeUnderIntegral :
    HasDerivAt
      (fun parameter ↦ programPT05GeometricNullBoundaryDensityIntegral
        nullFaceInterval (curve parameter).nullBoundaryDensity)
      (programPT05GeometricNullBoundaryDensityIntegral nullFaceInterval
        derivative.nullBoundaryVerticalDensity) baseParameter
  jointDerivativeUnderFiniteSum :
    HasDerivAt
      (fun parameter ↦ programPT05GeometricJointDensityIntegral
        (curve parameter).jointDensity)
      (programPT05GeometricJointDensityIntegral
        derivative.jointVerticalDensity) baseParameter

/-- Zero contact-degree-two density in the same fixed carrier. -/
def programPT05FixedCarrierZeroVerticalDensity
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval) :
    ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period hPeriod
      NullFace nullFaceInterval where
  bulkVerticalDensity := 0
  spinCVerticalCoefficient := 0
  llVerticalDensity := 0
  nonNullBoundaryVerticalDensity := 0
  nullBoundaryVerticalDensity := 0
  jointVerticalDensity := 0

/-- Signed local generator differential in horizontal degree `p`. -/
def programPT05FixedCarrierStratifiedLocalDV
    {NullFace : Type*}
    (p : Nat)
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierStratifiedDensityCoefficient period
      hPeriod NullFace nullFaceInterval) :
    ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period hPeriod
      NullFace nullFaceInterval where
  bulkVerticalDensity := (-1 : Real) ^ p • density.bulkDensity
  spinCVerticalCoefficient := (-1 : Real) ^ p * density.spinCCoefficient
  llVerticalDensity := (-1 : Real) ^ p • density.llDensity
  nonNullBoundaryVerticalDensity :=
    (-1 : Real) ^ p • density.nonNullBoundaryDensity
  nullBoundaryVerticalDensity := fun face point ↦
    (-1 : Real) ^ p * density.nullBoundaryDensity face point
  jointVerticalDensity := fun face endpoint ↦
    (-1 : Real) ^ p * density.jointDensity face endpoint

/-- The next contact differential kills the vertical-generator slot. -/
def programPT05FixedCarrierStratifiedLocalDVNext
    {NullFace : Type*}
    (_p : Nat)
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (_density : ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period
      hPeriod NullFace nullFaceInterval) :
    ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period hPeriod
      NullFace nullFaceInterval :=
  programPT05FixedCarrierZeroVerticalDensity period hPeriod nullFaceInterval

/-- The constructed local generator differential squares to zero. -/
@[simp]
theorem programPT05FixedCarrierStratifiedLocalDV_squared
    {NullFace : Type*}
    (p : Nat)
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierStratifiedDensityCoefficient period
      hPeriod NullFace nullFaceInterval) :
    programPT05FixedCarrierStratifiedLocalDVNext period hPeriod p
        (programPT05FixedCarrierStratifiedLocalDV period hPeriod p density) =
      programPT05FixedCarrierZeroVerticalDensity period hPeriod
        nullFaceInterval := by
  rfl

/-- Sectorwise integration of a fixed-carrier degree-zero density. -/
def programPT05IntegrateFixedCarrierStratifiedDensityCoefficient
    {NullFace : Type*} [Fintype NullFace]
    (p : Nat)
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierStratifiedDensityCoefficient period
      hPeriod NullFace nullFaceInterval) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent p 0
  | .bulk =>
      ((programPT05GeometricBulkDensityIntegral period hPeriod
            density.bulkDensity + density.spinCCoefficient) +
        programPT05GeometricLLDensityIntegral period hPeriod density.llDensity,
        0)
  | .nonNullBoundary =>
      (programPT05GeometricGHYDensityIntegral period hPeriod
        density.nonNullBoundaryDensity, 0)
  | .nullBoundary =>
      (programPT05GeometricNullBoundaryDensityIntegral nullFaceInterval
        density.nullBoundaryDensity, 0)
  | .joint =>
      (programPT05GeometricJointDensityIntegral density.jointDensity, 0)

/-- Sectorwise integration of a fixed-carrier vertical density. -/
def programPT05IntegrateFixedCarrierStratifiedVerticalDensity
    {NullFace : Type*} [Fintype NullFace]
    (p : Nat)
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period
      hPeriod NullFace nullFaceInterval) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent p 1
  | .bulk =>
      (0, (programPT05GeometricBulkDensityIntegral period hPeriod
            density.bulkVerticalDensity + density.spinCVerticalCoefficient) +
        programPT05GeometricLLDensityIntegral period hPeriod
          density.llVerticalDensity)
  | .nonNullBoundary =>
      (0, programPT05GeometricGHYDensityIntegral period hPeriod
        density.nonNullBoundaryVerticalDensity)
  | .nullBoundary =>
      (0, programPT05GeometricNullBoundaryDensityIntegral nullFaceInterval
        density.nullBoundaryVerticalDensity)
  | .joint =>
      (0, programPT05GeometricJointDensityIntegral
        density.jointVerticalDensity)

/-- The signed local generator differential commutes with sectorwise
integration in every horizontal degree. -/
theorem programPT05FixedCarrierStratifiedLocalDV_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (p : Nat)
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierStratifiedDensityCoefficient period
      hPeriod NullFace nullFaceInterval) :
    programPT05IntegrateFixedCarrierStratifiedVerticalDensity period hPeriod p
        nullFaceInterval
        (programPT05FixedCarrierStratifiedLocalDV period hPeriod p density) =
      programPT05ExactT03RelativeBicomplex.dV p 0
        (programPT05IntegrateFixedCarrierStratifiedDensityCoefficient period
          hPeriod p nullFaceInterval density) := by
  funext stratum
  cases stratum <;>
    apply Prod.ext <;>
    simp [programPT05IntegrateFixedCarrierStratifiedVerticalDensity,
      programPT05FixedCarrierStratifiedLocalDV,
      programPT05IntegrateFixedCarrierStratifiedDensityCoefficient,
      programPT05GeometricBulkDensityIntegral,
      programPT05GeometricLLDensityIntegral,
      programPT05LLDensityIntegral,
      programPT05GeometricGHYDensityIntegral,
      programPT05GHYFirstSheetDensityIntegral,
      programPT05GeometricNullBoundaryDensityIntegral,
      programPT05GeometricJointDensityIntegral,
      programPT05ExactT03RelativeBicomplex,
      programPT05RelativeVerticalDifferential,
      Finset.mul_sum] <;>
    ring

/-- After integration, the local vertical differential anticommutes with the
whole Gate-819 horizontal differential. -/
theorem programPT05FixedCarrierStratifiedLocalDV_mixed_anticommutes
    {NullFace : Type*} [Fintype NullFace]
    (p : Nat)
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierStratifiedDensityCoefficient period
      hPeriod NullFace nullFaceInterval) :
    programPT05ExactT03RelativeBicomplex.dV (p + 1) 0
          (programPT05ExactT03RelativeBicomplex.dH p 0
            (programPT05IntegrateFixedCarrierStratifiedDensityCoefficient
              period hPeriod p nullFaceInterval density)) +
        programPT05ExactT03RelativeBicomplex.dH p 1
          (programPT05IntegrateFixedCarrierStratifiedVerticalDensity period
            hPeriod p nullFaceInterval
            (programPT05FixedCarrierStratifiedLocalDV period hPeriod p
              density)) = 0 := by
  rw [programPT05FixedCarrierStratifiedLocalDV_integration_commutes]
  exact programPT05ExactT03RelativeBicomplex.mixed_anticommutes p 0
    (programPT05IntegrateFixedCarrierStratifiedDensityCoefficient period
      hPeriod p nullFaceInterval density)

/-- When Gate 851's two geometric contracts are supplied, the signed vertical
differential anticommutes with both completed horizontal targets. -/
theorem programPT05ContractCompletedHorizontal_dV_anticommutes
    {NullFace : Type*} [Fintype NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (nonNullBoundaryDensity :
      CandidateANormalBoundaryScalarField period hPeriod)
    (data : ProgramPT05MissingHorizontalDensityData NullFace)
    (contract : ProgramPT05MissingHorizontalGeometryContract period hPeriod
      field test faces nonNullBoundaryDensity data)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    let source := programPT05ContractCompletedHorizontalSource period hPeriod
      field test faces nonNullBoundaryDensity
    let target := programPT05ContractCompletedHorizontalTarget period hPeriod
      field test faces data
    programPT05ExactT03RelativeBicomplex.dV 5 0 target.1 +
          programPT05ExactT03RelativeBicomplex.dH 4 1
            (programPT05ExactT03RelativeBicomplex.dV 4 0 source.1) = 0 ∧
      programPT05ExactT03RelativeBicomplex.dV 4 0 target.2 +
          programPT05ExactT03RelativeBicomplex.dH 3 1
            (programPT05ExactT03RelativeBicomplex.dV 3 0 source.2) = 0 := by
  dsimp only
  have hIntegration :=
    programPT05ContractCompletedHorizontal_integration_commutes period hPeriod
      massSquared field test faces nonNullBoundaryDensity data contract
        contracts
  have hFirst := congrArg Prod.fst hIntegration
  have hSecond := congrArg Prod.snd hIntegration
  constructor
  · rw [← hFirst]
    exact programPT05ExactT03RelativeBicomplex.mixed_anticommutes 4 0
      (programPT05ContractCompletedHorizontalSource period hPeriod field test
        faces nonNullBoundaryDensity).1
  · rw [← hSecond]
    exact programPT05ExactT03RelativeBicomplex.mixed_anticommutes 3 0
      (programPT05ContractCompletedHorizontalSource period hPeriod field test
        faces nonNullBoundaryDensity).2

end
end P0EFTJanusProgramPT05FixedCarrierStratifiedVerticalDifferential4D
end JanusFormal
