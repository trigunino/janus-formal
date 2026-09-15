import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D

/-!
# Euler-relative radial normal form for T06

The genuine T02 Euler residual at each physical formal fourth jet is inserted
in the bulk component of the concrete T05 relative carrier.  Thus one common
family, rather than an independent product of predicates, detects Euler
vanishing by relative nullity.  Gate942 then supplies the canonical physical
third-jet radial vector density, while Gate866 supplies the unique normalized
relative primitive of every null residual member.

This is a logical common carrier.  It does not identify the formal residual
family with an integrated physical bulk measure or prove a global Stokes map.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06EulerRelativeRadialNormalForm4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D
open P0EFTJanusProgramPT06T02DegreeFourEulerKernelIff4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

local notation "Bicomplex" => programPT05ExactT03RelativeBicomplex

variable (period : Real) (hPeriod : period ≠ 0)

/-- Put one genuine Gate942 Euler residual in the bulk slot of Gate866's
relative carrier. -/
def programPT06EulerResidualRelativeDensity
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FourthJet) (variation : Fiber) : ProgramPT06RelativeDensity4D
  | .bulk =>
      (programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional)
          jet variation, 0)
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint => 0

/-- Every Euler-residual member is a horizontal relative density. -/
theorem programPT06EulerResidualRelativeDensity_horizontal
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FourthJet) (variation : Fiber) :
    IsHorizontalDensity
      (programPT06EulerResidualRelativeDensity
        period hPeriod functional jet variation) := by
  intro stratum
  cases stratum <;> rfl

/-- Relative nullity of one residual member is exactly pointwise Euler
vanishing; no comparison hypothesis is supplied. -/
theorem programPT06EulerResidualRelativeDensity_null_iff_euler_zero
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FourthJet) (variation : Fiber) :
    IsRelativeNullLagrangian
        (programPT06EulerResidualRelativeDensity
          period hPeriod functional jet variation) ↔
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet variation = 0 := by
  rw [isRelativeNullLagrangian_iff_components]
  simp [programPT06EulerResidualRelativeDensity]

/-- The common logical nullity predicate: the family of genuine Euler
residuals is null in the concrete relative complex. -/
def IsProgramPT06EulerRelativeNull
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) : Prop :=
  ∀ jet : FourthJet,
    ∀ variation : Fiber,
      IsRelativeNullLagrangian
        (programPT06EulerResidualRelativeDensity
          period hPeriod functional jet variation)

/-- The common predicate detects exactly the genuine Gate942 Euler kernel. -/
theorem isProgramPT06EulerRelativeNull_iff_euler_zero
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    IsProgramPT06EulerRelativeNull period hPeriod functional ↔
      ∀ jet : FourthJet,
        programPT06SecondOrderLocalEuler
          (programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional) jet = 0 := by
  constructor
  · intro hNull jet
    apply ContinuousLinearMap.ext
    intro variation
    exact
      (programPT06EulerResidualRelativeDensity_null_iff_euler_zero
        period hPeriod functional jet variation).1 (hNull jet variation)
  · intro hEuler jet variation
    exact
      (programPT06EulerResidualRelativeDensity_null_iff_euler_zero
        period hPeriod functional jet variation).2 (by
          rw [hEuler jet]
          rfl)

/-- Common relative nullity is equivalent to the explicit constant plus the
chartwise differential of the canonical physical J3 radial vector density. -/
theorem isProgramPT06EulerRelativeNull_iff_physicalRadialNormalForm
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    IsProgramPT06EulerRelativeNull period hPeriod functional ↔
      ∀ jet : FourthJet,
        programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
          functional.lower.lower.constant +
            programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH
              (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
                period hPeriod functional) jet := by
  rw [isProgramPT06EulerRelativeNull_iff_euler_zero]
  constructor
  · intro hEuler jet
    exact
      programPT06T02DegreeFourLocalLagrangian_eq_constant_add_actualPhysicalVectorDensityChartwiseDH
        period hPeriod functional hEuler jet
  · intro hFactor
    apply
      (programPT06T02DegreeFour_euler_eq_zero_iff_radialCartanCurrent
        period hPeriod functional).2
    intro jet
    rw [←
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_chartwiseDH
        period hPeriod functional]
    exact hFactor jet

/-- Gate866's canonical primitive realizes every actual boundary density. -/
theorem canonicalRelativeBoundaryPrimitive_dH
    (density : ProgramPT06RelativeDensity4D)
    (hBoundary : IsRelativeBoundaryTerm density) :
    (Bicomplex).dH 3 0 (canonicalRelativeBoundaryPrimitive density) = density := by
  have hComponents :=
    (isRelativeBoundaryTerm_iff_components density).1 hBoundary
  funext stratum
  cases stratum <;>
    simp [canonicalRelativeBoundaryPrimitive,
      programPT05ExactT03RelativeBicomplex,
      programPT05RelativeHorizontalDifferential,
      hComponents.1, hComponents.2]

/-- A normal form records the explicit constant, the canonical physical J3
radial density and one normalized relative primitive for every Euler residual. -/
abbrev ProgramPT06EulerRelativeRadialNormalForm4D :=
  Real × ProgramPT06ActualPhysicalThirdJetVectorDensity4D ×
    (FourthJet → Fiber → ProgramPT06RelativeBoundaryPrimitive4D)

/-- The canonical normal-form candidate. -/
def programPT06CanonicalEulerRelativeRadialNormalForm
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ProgramPT06EulerRelativeRadialNormalForm4D :=
  (functional.lower.lower.constant,
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
      period hPeriod functional,
    fun jet variation ↦ canonicalRelativeBoundaryPrimitive
      (programPT06EulerResidualRelativeDensity
        period hPeriod functional jet variation))

/-- A normal form simultaneously reconstructs the local density and every
member of its relative Euler-residual family. -/
def IsProgramPT06EulerRelativeRadialNormalForm
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (normalForm : ProgramPT06EulerRelativeRadialNormalForm4D) : Prop :=
  normalForm.1 = functional.lower.lower.constant ∧
    normalForm.2.1 =
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional ∧
    (∀ jet : FourthJet,
      programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
        normalForm.1 +
          programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH
            normalForm.2.1 jet) ∧
    ∀ (jet : FourthJet) (variation : Fiber),
      IsNormalizedRelativeBoundaryPrimitive
          (normalForm.2.2 jet variation) ∧
        (Bicomplex).dH 3 0 (normalForm.2.2 jet variation) =
          programPT06EulerResidualRelativeDensity
            period hPeriod functional jet variation

/-- Terminal logical normal form: common Euler-relative nullity is equivalent
to existence of one unique explicit radial/relative normal form. -/
theorem isProgramPT06EulerRelativeNull_iff_existsUnique_radialNormalForm
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    IsProgramPT06EulerRelativeNull period hPeriod functional ↔
      ∃! normalForm : ProgramPT06EulerRelativeRadialNormalForm4D,
        IsProgramPT06EulerRelativeRadialNormalForm
          period hPeriod functional normalForm := by
  constructor
  · intro hNull
    let canonical :=
      programPT06CanonicalEulerRelativeRadialNormalForm
        period hPeriod functional
    have hRadial :=
      (isProgramPT06EulerRelativeNull_iff_physicalRadialNormalForm
        period hPeriod functional).1 hNull
    have hCanonical : IsProgramPT06EulerRelativeRadialNormalForm
        period hPeriod functional canonical := by
      refine ⟨rfl, rfl, hRadial, ?_⟩
      intro jet variation
      have hHorizontal :=
        programPT06EulerResidualRelativeDensity_horizontal
          period hPeriod functional jet variation
      have hBoundary : IsRelativeBoundaryTerm
          (programPT06EulerResidualRelativeDensity
            period hPeriod functional jet variation) :=
        (horizontalDensity_null_iff_boundary _ hHorizontal).1
          (hNull jet variation)
      exact ⟨canonicalRelativeBoundaryPrimitive_normalized _,
        canonicalRelativeBoundaryPrimitive_dH _ hBoundary⟩
    refine ⟨canonical, hCanonical, ?_⟩
    intro other hOther
    apply Prod.ext
    · exact hOther.1.trans hCanonical.1.symm
    · apply Prod.ext
      · exact hOther.2.1.trans hCanonical.2.1.symm
      · funext jet variation
        let density :=
          programPT06EulerResidualRelativeDensity
            period hPeriod functional jet variation
        have hHorizontal :=
          programPT06EulerResidualRelativeDensity_horizontal
            period hPeriod functional jet variation
        have hBoundary : IsRelativeBoundaryTerm density :=
          (horizontalDensity_null_iff_boundary density hHorizontal).1
            (hNull jet variation)
        obtain ⟨primitive, hPrimitive, hUnique⟩ :=
          relativeBoundaryTerm_existsUnique_normalizedPrimitive
            density hBoundary
        have hOtherPrimitive :
            IsNormalizedRelativeBoundaryPrimitive
                (other.2.2 jet variation) ∧
              (Bicomplex).dH 3 0 (other.2.2 jet variation) = density :=
          hOther.2.2.2 jet variation
        have hCanonicalPrimitive :
            IsNormalizedRelativeBoundaryPrimitive
                (canonical.2.2 jet variation) ∧
              (Bicomplex).dH 3 0 (canonical.2.2 jet variation) = density :=
          hCanonical.2.2.2 jet variation
        exact (hUnique _ hOtherPrimitive).trans
          (hUnique _ hCanonicalPrimitive).symm
  · rintro ⟨normalForm, hNormal, -⟩
    intro jet variation
    have hBoundary : IsRelativeBoundaryTerm
        (programPT06EulerResidualRelativeDensity
          period hPeriod functional jet variation) :=
      ⟨normalForm.2.2 jet variation,
        (hNormal.2.2.2 jet variation).2⟩
    exact
      (horizontalDensity_null_iff_boundary _
        (programPT06EulerResidualRelativeDensity_horizontal
          period hPeriod functional jet variation)).2 hBoundary

end

end P0EFTJanusProgramPT06EulerRelativeRadialNormalForm4D
end JanusFormal
