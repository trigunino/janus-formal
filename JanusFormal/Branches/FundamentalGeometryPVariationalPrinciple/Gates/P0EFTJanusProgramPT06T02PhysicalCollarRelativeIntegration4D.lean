import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourEulerKernelIff4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBulkMeasureTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D

/-!
# T02 radial current on the integrated physical collar

This gate isolates the remaining local geometric comparison between the
fixed-frame T02 fourth jet and the canonical physical collar.  Once a fourth-
jet section realizes the radial Cartan horizontal differential as the already
constructed physical bulk integrand, Gate 942 identifies `L - constant` with
that integrand and Gate 1075 integrates it to the physical boundary flux.

The resulting scalar is inserted as an actual horizontal boundary in the T05
relative carrier, with the T02 constant retained as a separate augmentation.
The repeated non-null/null carrier value is the algebraic Gate-819 incidence;
this statement does not construct a second physical null-face restriction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02PhysicalCollarRelativeIntegration4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D
open P0EFTJanusProgramPT06T02DegreeFourEulerKernelIff4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarRegionalStokes4D
open P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBoundaryMeasureTransport4D
open P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBulkMeasureTransport4D
open P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- A fixed-frame fourth-jet section on the physical image of the canonical
collar.  Its compatibility below is pointwise and precedes integration. -/
abbrev ProgramPT06T02PhysicalCollarFourthJetSection4D :=
  ProgramPT06EffectiveBulk period hPeriod → FourthJet

/-- The exact missing local prolongation datum: a physical-collar fourth-jet
section on which Gate 942's radial current is Gate 1075's bulk integrand.
Its compatibility is pointwise and assumes no equality of integrals or
boundary terms. -/
structure ProgramPT06T02RadialCurrentPhysicalCollarDatum
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity) where
  fourthJetSection :
    ProgramPT06T02PhysicalCollarFourthJetSection4D period hPeriod
  radialDH_eq_integrand : ∀ point,
    programPT06SecondOrderHorizontalCurrentDH
        (programPT06T02DegreeFourRadialCartanCurrent
          period hPeriod functional) (fourthJetSection point) =
      programPT06CanonicalFirstSheetPhysicalBulkIntegrand
        period hPeriod pole density point

/-- The T02 Lagrangian with its explicit constant augmentation removed,
evaluated on the physical-collar fourth-jet section. -/
def programPT06T02PhysicalCollarReducedDensity
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection :
      ProgramPT06T02PhysicalCollarFourthJetSection4D period hPeriod) :
    ProgramPT06EffectiveBulk period hPeriod → Real :=
  fun point =>
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4)
          (jetSection point)) -
      functional.lower.lower.constant

/-- Gate 942 identifies the constant-reduced local density with its radial
Cartan horizontal differential before any integration is performed. -/
theorem programPT06T02PhysicalCollarReducedDensity_eq_radialDH
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection :
      ProgramPT06T02PhysicalCollarFourthJetSection4D period hPeriod)
    (hEuler : ∀ jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0)
    (point : ProgramPT06EffectiveBulk period hPeriod) :
    programPT06T02PhysicalCollarReducedDensity period hPeriod functional
        jetSection point =
      programPT06SecondOrderHorizontalCurrentDH
        (programPT06T02DegreeFourRadialCartanCurrent
          period hPeriod functional) (jetSection point) := by
  have hExact :=
    (programPT06T02DegreeFour_euler_eq_zero_iff_radialCartanCurrent
      period hPeriod functional).1 hEuler (jetSection point)
  rw [programPT06T02PhysicalCollarReducedDensity, hExact]
  ring

/-- Local constant-plus-divergence normal form in the physical collar once
the supplied fourth-jet prolongation is compatible with Gate 1075. -/
theorem programPT06T02PhysicalCollarLocalDensity_eq_constant_add_integrand
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (datum : ProgramPT06T02RadialCurrentPhysicalCollarDatum
      period hPeriod functional pole density)
    (hEuler : ∀ jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0)
    (point : ProgramPT06EffectiveBulk period hPeriod) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4)
          (datum.fourthJetSection point)) =
      functional.lower.lower.constant +
        programPT06CanonicalFirstSheetPhysicalBulkIntegrand
          period hPeriod pole density point := by
  have hReduced :=
    programPT06T02PhysicalCollarReducedDensity_eq_radialDH
      period hPeriod functional datum.fourthJetSection hEuler point
  rw [programPT06T02PhysicalCollarReducedDensity] at hReduced
  calc
    _ = functional.lower.lower.constant +
        (programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4)
              (datum.fourthJetSection point)) -
          functional.lower.lower.constant) := by ring
    _ = functional.lower.lower.constant +
        programPT06SecondOrderHorizontalCurrentDH
          (programPT06T02DegreeFourRadialCartanCurrent
            period hPeriod functional) (datum.fourthJetSection point) := by
      rw [hReduced]
    _ = _ := by rw [datum.radialDH_eq_integrand point]

/-- Gate 1075 integrates the Gate-942 reduced local density to the genuine
physical first-sheet boundary image flux. -/
theorem programPT06T02PhysicalCollarReducedDensity_integral_eq_boundary
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (datum : ProgramPT06T02RadialCurrentPhysicalCollarDatum
      period hPeriod functional pole density)
    (hEuler : ∀ jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0) :
    (∫ point,
        programPT06T02PhysicalCollarReducedDensity period hPeriod functional
          datum.fourthJetSection point
      ∂programPT06CanonicalFirstSheetPhysicalBulkMeasure
        period hPeriod pole) =
      ∫ point,
        programPT06CanonicalFirstSheetPhysicalBoundaryFlux
          period hPeriod pole density point
        ∂programPT06CanonicalFirstSheetPhysicalBoundaryMeasure
          period hPeriod pole := by
  calc
    (∫ point,
        programPT06T02PhysicalCollarReducedDensity period hPeriod functional
          datum.fourthJetSection point
      ∂programPT06CanonicalFirstSheetPhysicalBulkMeasure
        period hPeriod pole) =
      ∫ point,
        programPT06CanonicalFirstSheetPhysicalBulkIntegrand
          period hPeriod pole density point
        ∂programPT06CanonicalFirstSheetPhysicalBulkMeasure
          period hPeriod pole := by
      apply integral_congr_ae
      filter_upwards with point
      rw [programPT06T02PhysicalCollarReducedDensity_eq_radialDH
        period hPeriod functional datum.fourthJetSection hEuler point,
        datum.radialDH_eq_integrand point]
    _ = _ :=
      programPT06CanonicalFirstSheetPhysicalImageMeasure_stokes
        period hPeriod contract pole metric

/-- Put one integrated boundary scalar in the degree-three bulk source of the
T05 relative carrier. -/
def programPT06T02PhysicalCollarRelativeBoundaryPrimitive
    (boundaryValue : Real) : ProgramPT06RelativeBoundaryPrimitive4D
  | .bulk => (boundaryValue, 0)
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint => 0

/-- The corresponding degree-four T05 horizontal boundary density. -/
def programPT06T02PhysicalCollarRelativeBoundaryDensity
    (boundaryValue : Real) : ProgramPT06RelativeDensity4D :=
  programPT05ExactT03RelativeBicomplex.dH 3 0
    (programPT06T02PhysicalCollarRelativeBoundaryPrimitive boundaryValue)

@[simp] theorem programPT06T02PhysicalCollarRelativeBoundaryDensity_bulk
    (boundaryValue : Real) :
    programPT06T02PhysicalCollarRelativeBoundaryDensity boundaryValue .bulk =
      0 := by
  rfl

@[simp] theorem programPT06T02PhysicalCollarRelativeBoundaryDensity_nonNull
    (boundaryValue : Real) :
    programPT06T02PhysicalCollarRelativeBoundaryDensity boundaryValue
        .nonNullBoundary = (boundaryValue, 0) := by
  rfl

@[simp] theorem programPT06T02PhysicalCollarRelativeBoundaryDensity_null
    (boundaryValue : Real) :
    programPT06T02PhysicalCollarRelativeBoundaryDensity boundaryValue
        .nullBoundary = (boundaryValue, 0) := by
  rfl

@[simp] theorem programPT06T02PhysicalCollarRelativeBoundaryDensity_joint
    (boundaryValue : Real) :
    programPT06T02PhysicalCollarRelativeBoundaryDensity boundaryValue .joint =
      0 := by
  simp [programPT06T02PhysicalCollarRelativeBoundaryDensity,
    programPT06T02PhysicalCollarRelativeBoundaryPrimitive,
    programPT05ExactT03RelativeBicomplex,
    programPT05RelativeHorizontalDifferential]

/-- Constant augmentation and the T05 relative boundary are kept as distinct
typed components. -/
structure ProgramPT06T02ConstantAugmentedRelativeBoundary4D where
  constant : Real
  relativeBoundary : ProgramPT06RelativeDensity4D

/-- The augmented integrated normal form determined by the T02 constant and
the physical first-sheet flux. -/
def programPT06T02PhysicalCollarConstantAugmentedBoundary
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    ProgramPT06T02ConstantAugmentedRelativeBoundary4D :=
  { constant := functional.lower.lower.constant
    relativeBoundary :=
      programPT06T02PhysicalCollarRelativeBoundaryDensity
        (∫ point,
          programPT06CanonicalFirstSheetPhysicalBoundaryFlux
            period hPeriod pole density point
          ∂programPT06CanonicalFirstSheetPhysicalBoundaryMeasure
            period hPeriod pole) }

@[simp] theorem programPT06T02PhysicalCollarConstantAugmentedBoundary_constant
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    (programPT06T02PhysicalCollarConstantAugmentedBoundary
      period hPeriod functional pole density).constant =
      functional.lower.lower.constant := by
  rfl

/-- The integrated physical flux component is an actual T05 relative
boundary and hence a relative null Lagrangian. -/
theorem programPT06T02PhysicalCollarConstantAugmentedBoundary_boundary_and_null
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    IsRelativeBoundaryTerm
        (programPT06T02PhysicalCollarConstantAugmentedBoundary
          period hPeriod functional pole density).relativeBoundary ∧
      IsRelativeNullLagrangian
        (programPT06T02PhysicalCollarConstantAugmentedBoundary
          period hPeriod functional pole density).relativeBoundary := by
  let boundaryValue :=
    ∫ point,
      programPT06CanonicalFirstSheetPhysicalBoundaryFlux
        period hPeriod pole density point
      ∂programPT06CanonicalFirstSheetPhysicalBoundaryMeasure
        period hPeriod pole
  have hBoundary : IsRelativeBoundaryTerm
      (programPT06T02PhysicalCollarRelativeBoundaryDensity boundaryValue) := by
    exact ⟨programPT06T02PhysicalCollarRelativeBoundaryPrimitive boundaryValue,
      rfl⟩
  have hHorizontal : IsHorizontalDensity
      (programPT06T02PhysicalCollarRelativeBoundaryDensity boundaryValue) := by
    intro stratum
    cases stratum <;>
      simp [programPT06T02PhysicalCollarRelativeBoundaryDensity,
        programPT06T02PhysicalCollarRelativeBoundaryPrimitive,
        programPT05ExactT03RelativeBicomplex,
        programPT05RelativeHorizontalDifferential]
  exact ⟨hBoundary,
    (horizontalDensity_null_iff_boundary _ hHorizontal).2 hBoundary⟩

/-- End-to-end local-to-integrated statement.  The reduced T02 bulk integral
is the non-null slot of an explicit T05 boundary density; the same value in
the null slot is only the fixed relative incidence. -/
theorem programPT06T02EulerKernel_integrates_to_augmentedRelativeBoundary
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (datum : ProgramPT06T02RadialCurrentPhysicalCollarDatum
      period hPeriod functional pole density)
    (hEuler : ∀ jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0) :
    let augmented :=
      programPT06T02PhysicalCollarConstantAugmentedBoundary
        period hPeriod functional pole density
    augmented.constant = functional.lower.lower.constant ∧
      augmented.relativeBoundary .nonNullBoundary =
        ((∫ point,
          programPT06T02PhysicalCollarReducedDensity period hPeriod functional
            datum.fourthJetSection point
          ∂programPT06CanonicalFirstSheetPhysicalBulkMeasure
            period hPeriod pole), 0) ∧
      augmented.relativeBoundary .nullBoundary =
        ((∫ point,
          programPT06T02PhysicalCollarReducedDensity period hPeriod functional
            datum.fourthJetSection point
          ∂programPT06CanonicalFirstSheetPhysicalBulkMeasure
            period hPeriod pole), 0) ∧
      IsRelativeBoundaryTerm augmented.relativeBoundary ∧
      IsRelativeNullLagrangian augmented.relativeBoundary := by
  dsimp only
  have hIntegral :=
    programPT06T02PhysicalCollarReducedDensity_integral_eq_boundary
      period hPeriod functional pole metric density contract datum hEuler
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [programPT06T02PhysicalCollarConstantAugmentedBoundary,
      programPT06T02PhysicalCollarRelativeBoundaryDensity_nonNull]
    rw [hIntegral]
  · simp only [programPT06T02PhysicalCollarConstantAugmentedBoundary,
      programPT06T02PhysicalCollarRelativeBoundaryDensity_null]
    rw [hIntegral]
  · exact
      programPT06T02PhysicalCollarConstantAugmentedBoundary_boundary_and_null
        period hPeriod functional pole density

end
end P0EFTJanusProgramPT06T02PhysicalCollarRelativeIntegration4D
end JanusFormal
