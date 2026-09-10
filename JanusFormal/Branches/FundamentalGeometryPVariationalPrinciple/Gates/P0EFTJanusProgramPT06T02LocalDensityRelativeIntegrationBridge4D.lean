import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D

/-!
# T02 local-density integration into the T05 relative carrier

This gate gives the smallest direct local-to-integrated bridge presently
supported by the two carriers.  A continuous scalar function on the genuine
physical Finsupp second-jet fiber is evaluated along a continuous fixed-frame
jet section over the effective throat, integrated by T05's canonical throat
integral, and inserted into the bulk slot of the Gate-819 relative carrier.

The pulled-back T02 degree-four Lagrangian supplies such a continuous local
function through its proved Frechet derivative.  The construction is
fixed-frame and does not identify spatial total divergences with cellular
relative boundaries; that requires a separate Stokes/prolongation theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02LocalDensityRelativeIntegrationBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

private abbrev ThroatBase (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev FinsuppSecondJet :=
  ThroatSpatialMultiindexJet2 ActualPhysicalValueProductFiber

variable (period : Real) (hPeriod : period ≠ 0)

/-- A continuous fixed-frame physical second-jet section over the effective
throat. -/
abbrev ProgramPT06T02FinsuppSecondJetSection4D :=
  C(ThroatBase period hPeriod, FinsuppSecondJet)

/-- Evaluate a continuous local function on the physical Finsupp second-jet
fiber along a fixed-frame continuous jet section. -/
def programPT06FinsuppSecondJetLocalDensityAlongSection
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    C(ThroatBase period hPeriod, Real) :=
  density.comp jetSection

@[simp] theorem programPT06FinsuppSecondJetLocalDensityAlongSection_apply
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod)
    (base : ThroatBase period hPeriod) :
    programPT06FinsuppSecondJetLocalDensityAlongSection period hPeriod density
        jetSection base =
      density (jetSection base) := by
  rfl

/-- Genuine T05 throat integration of a local second-jet density evaluated
along a continuous section. -/
def programPT06FinsuppSecondJetLocalDensityIntegral
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    Real :=
  programPT05GeometricLLDensityIntegral period hPeriod
    (programPT06FinsuppSecondJetLocalDensityAlongSection period hPeriod density
      jetSection)

/-- Insert the integrated throat density into the bulk slot used for LL by
the concrete T05 relative carrier. -/
def programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    ProgramPT06RelativeDensity4D
  | .bulk =>
      (programPT06FinsuppSecondJetLocalDensityIntegral period hPeriod density
        jetSection, 0)
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint => 0

@[simp] theorem
    programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain_bulk
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain period
        hPeriod density jetSection .bulk =
      (programPT06FinsuppSecondJetLocalDensityIntegral period hPeriod density
        jetSection, 0) := by
  rfl

/-- The bridge lands in the horizontal-density subcarrier. -/
theorem programPT06FinsuppSecondJetLocalDensityIntegratedRelative_horizontal
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    IsHorizontalDensity
      (programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain period
        hPeriod density jetSection) := by
  intro stratum
  cases stratum <;> rfl

/-- Summing the four integrated relative slots recovers exactly the throat
integral used to define the bridge. -/
theorem programPT06FinsuppSecondJetLocalDensityIntegratedRelative_actionSum
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    programPT05IntegratedRelativeCochainActionSum
        (programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain
          period hPeriod density jetSection) =
      programPT06FinsuppSecondJetLocalDensityIntegral period hPeriod density
        jetSection := by
  simp [programPT05IntegratedRelativeCochainActionSum,
    programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain]

/-- Exact criterion supplied by the T05 relative differential for this
bulk-supported image: its integrated cochain is relatively null precisely
when the actual throat integral vanishes. -/
theorem
    programPT06FinsuppSecondJetLocalDensityIntegratedRelative_null_iff_integral_zero
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    IsRelativeNullLagrangian
        (programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain
          period hPeriod density jetSection) ↔
      programPT06FinsuppSecondJetLocalDensityIntegral period hPeriod density
          jetSection = 0 := by
  rw [isRelativeNullLagrangian_iff_components]
  simp [programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain]

/-- On the same bulk-supported image, being a relative boundary has the same
exact zero-integral criterion. -/
theorem
    programPT06FinsuppSecondJetLocalDensityIntegratedRelative_boundary_iff_integral_zero
    (density : C(FinsuppSecondJet, Real))
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    IsRelativeBoundaryTerm
        (programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain
          period hPeriod density jetSection) ↔
      programPT06FinsuppSecondJetLocalDensityIntegral period hPeriod density
          jetSection = 0 := by
  rw [isRelativeBoundaryTerm_iff_components]
  simp [programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain]

/-- Gate882's T02 local Lagrangian, bundled as a continuous function on the
genuine Finsupp second-jet fiber. -/
def programPT06T02FinsuppSecondJetContinuousLocalDensity
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    C(FinsuppSecondJet, Real) where
  toFun :=
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro jet
    exact
      (programPT06T02FinsuppSecondJetLocalLagrangian_hasFDerivAt period hPeriod
        functional jet).continuousAt

@[simp] theorem programPT06T02FinsuppSecondJetContinuousLocalDensity_apply
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetContinuousLocalDensity period hPeriod
        functional jet =
      programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
        jet := by
  rfl

/-- Concrete local-to-integrated image of a T02 admissible local functional
along a fixed-frame physical jet section. -/
def programPT06T02FinsuppSecondJetIntegratedRelativeCochain
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    ProgramPT06RelativeDensity4D :=
  programPT06FinsuppSecondJetLocalDensityIntegratedRelativeCochain period
    hPeriod
    (programPT06T02FinsuppSecondJetContinuousLocalDensity period hPeriod
      functional)
    jetSection

/-- Specialized relative-nullity criterion for the genuine T02 local
Lagrangian. -/
theorem programPT06T02FinsuppSecondJetIntegratedRelative_null_iff_integral_zero
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection : ProgramPT06T02FinsuppSecondJetSection4D period hPeriod) :
    IsRelativeNullLagrangian
        (programPT06T02FinsuppSecondJetIntegratedRelativeCochain period hPeriod
          functional jetSection) ↔
      programPT06FinsuppSecondJetLocalDensityIntegral period hPeriod
          (programPT06T02FinsuppSecondJetContinuousLocalDensity period hPeriod
            functional)
          jetSection = 0 := by
  exact
    programPT06FinsuppSecondJetLocalDensityIntegratedRelative_null_iff_integral_zero
      period hPeriod
      (programPT06T02FinsuppSecondJetContinuousLocalDensity period hPeriod
        functional)
      jetSection

end
end P0EFTJanusProgramPT06T02LocalDensityRelativeIntegrationBridge4D
end JanusFormal
