import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8BackgroundCategory4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusMappingTorusStructuredJetGroupoid
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusCechCoherenceClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCActualPrincipalBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalOperatorClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPEInvariantPairings

/-!
# Global naturality package for Program P

This gate only assembles constructions already proved on the actual Janus
quotient: the effective-D8 category, descended holonomic structured jets,
the canonical Pin-minus/PinC bundles and the finite natural local-term
classifier.  No additional naturality or existence hypothesis is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalNaturalClassification4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusMappingTorusStructuredJetGroupoid
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientPinMinusCechCoherenceClosure4D
open P0EFTJanusProgramPAmbientPinCActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
open P0EFTJanusProgramPNaturalOperatorClassification4D
open P0EFTJanusNaturalLowerOrderFreedom
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- The already constructed category of all nonzero-period effective-D8
backgrounds. -/
def janusNaturalCategory :=
  effectiveD8BackgroundCategory

/-- Actual holonomic structured jets on the reflected-sphere cover. -/
abbrev JanusHolonomicJetFamily
    (period : Real) (hPeriod : period ≠ 0) :=
  SmoothDeckHolonomicStructuredJetFamily
    (Tangent := EuclideanR4) (Normal := Real)
    coverModelWithCorners (⊤ : ℕ∞) (reflectedSphereData period hPeriod)

/-- Holonomicity survives the genuine quotient descent. -/
theorem janusHolonomicJet_descends
    (family : JanusHolonomicJetFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ∃ localData : ActualJanusLocalJetData
          (Tangent := EuclideanR4) (Normal := Real),
      localData.toStructuredJet =
        (family.toInvariantMap coverModelWithCorners (⊤ : ℕ∞)
          (reflectedSphereData period hPeriod)).descended
            coverModelWithCorners _ (⊤ : ℕ∞)
              (reflectedSphereData period hPeriod) point :=
  SmoothDeckHolonomicStructuredJetFamily.descended_is_holonomic
      coverModelWithCorners (⊤ : ℕ∞) (reflectedSphereData period hPeriod)
        family point

/-- Canonical genuine Pin-minus principal bundle. -/
def janusPinMinusPrincipalBundle :=
  canonicalAmbientPinMinusActualPrincipalBundle period hPeriod

/-- Canonical genuine PinC principal-bundle core. -/
def janusPinCPrincipalBundleCore :=
  canonicalAmbientPinCPrincipalBundleCore period hPeriod

/-- Canonical genuine associated PinC spinor-bundle core. -/
def janusPinCSpinorBundleCore (choice : NormalRootChoice) :=
  canonicalAmbientPinCSpinorBundleCore period hPeriod choice

/-- Finite coefficient family for every classified Program-P local sector. -/
abbrev JanusNaturalLocalCoefficients :=
  ProgramPLowerOrderCoefficients

/-- The concrete six-invariant, sectorwise local evaluator. -/
def janusNaturalLocalEvaluator :
    JanusNaturalLocalCoefficients →
      P0EFTJanusNaturalOperatorBlueprint.NaturalOperatorSector →
        P0EFTJanusNaturalLowerOrderFreedom.ImmersionInvariantJet → Real :=
  programPLowerOrderEvaluator

/-- The finite natural evaluator loses no local coefficient. -/
theorem janusNaturalLocalEvaluator_injective :
    Function.Injective janusNaturalLocalEvaluator :=
  programPLowerOrderEvaluator_injective

/-- Exact coefficient classification in the retained six-invariant EFT
truncation, for every scalar natural potential in that truncation. -/
theorem janusSixInvariantEFTPotential_existsUnique_coefficients
    (potential :
      P0EFTJanusNaturalLowerOrderFreedom.ImmersionInvariantJet → Real)
    (hEFT : IsSixInvariantEFTPotential potential) :
    ∃! couplings : NaturalPotentialCouplings,
      potential = naturalPotential couplings :=
  sixInvariantEFTPotential_existsUnique_coefficients potential hEFT

/-- Concrete closure certificate: all three genuine bundle constructions
exist and the finite natural-term classifier is exact and faithful. -/
theorem global_natural_classification_gate :
    Nonempty
        (CanonicalAmbientPinMinusActualPrincipalBundle period hPeriod) ∧
      Nonempty
        (ProgramPAmbientPinCActualPrincipalBundleCertificate4D
          period hPeriod) ∧
      Nonempty
        (ProgramPAmbientPinCActualSpinorBundleCertificate4D
          period hPeriod) ∧
      Function.Injective janusNaturalLocalEvaluator ∧
      (∀ potential :
          P0EFTJanusNaturalLowerOrderFreedom.ImmersionInvariantJet → Real,
        IsSixInvariantEFTPotential potential →
          ∃! couplings : NaturalPotentialCouplings,
            potential = naturalPotential couplings) := by
  exact ⟨canonicalAmbientPinMinusActualPrincipalBundle_nonempty
      period hPeriod,
    programPAmbientPinCActualPrincipalBundleCertificate4D_nonempty
      period hPeriod,
    programPAmbientPinCActualSpinorBundleCertificate4D_nonempty
      period hPeriod,
    janusNaturalLocalEvaluator_injective,
    janusSixInvariantEFTPotential_existsUnique_coefficients⟩

end
end P0EFTJanusProgramPGlobalNaturalClassification4D
end JanusFormal
