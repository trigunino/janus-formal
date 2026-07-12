import Mathlib
import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalEllipticFamilyExistence
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusQuillenFamilyCanonicity

namespace JanusFormal
namespace P0EFTJanusNaturalFamilyQuillenBridge

set_option autoImplicit false

open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusQuillenFamilyCanonicity

/-- Analytic upgrade from a categorical natural family to a smooth Fredholm family. -/
structure NaturalFamilyAnalyticUpgrade where
  parameterSpaceOrStackConstructed : Prop
  universalImmersionFamilyConstructed : Prop
  smoothFiberMetricsChosen : Prop
  naturalBundleMetricsChosen : Prop
  naturalConnectionsConstructed : Prop
  naturalFamilyOperatorConstructed : Prop
  principalSymbolElliptic : Prop
  selfAdjointOrFredholmDomainsConstructed : Prop
  smoothFamilyDependenceProved : Prop
  normalRootBoundaryDomainsIncluded : Prop
  gaugeEquivariantFamilyConstructed : Prop

/-- Forget the extra naturality/boundary data to the Quillen input interface. -/
def toEllipticFamilyInputStatus
    (s : NaturalFamilyAnalyticUpgrade) : EllipticFamilyInputStatus :=
  { parameterSpaceOrStackConstructed :=
      s.parameterSpaceOrStackConstructed
    universalFamilyConstructed :=
      s.universalImmersionFamilyConstructed
    smoothFiberMetricsChosen := s.smoothFiberMetricsChosen
    bundleMetricsChosen := s.naturalBundleMetricsChosen
    compatibleConnectionsChosen := s.naturalConnectionsConstructed
    familyOperatorConstructed := s.naturalFamilyOperatorConstructed
    ellipticityProved := s.principalSymbolElliptic
    fredholmDomainsConstructed :=
      s.selfAdjointOrFredholmDomainsConstructed
    smoothFamilyDependenceProved := s.smoothFamilyDependenceProved }

/-- Closing the stronger natural-family upgrade closes the ordinary Quillen input contract. -/
theorem natural_family_upgrade_closes_quillen_input
    (s : NaturalFamilyAnalyticUpgrade)
    (hClosed :
      s.parameterSpaceOrStackConstructed /\
      s.universalImmersionFamilyConstructed /\
      s.smoothFiberMetricsChosen /\
      s.naturalBundleMetricsChosen /\
      s.naturalConnectionsConstructed /\
      s.naturalFamilyOperatorConstructed /\
      s.principalSymbolElliptic /\
      s.selfAdjointOrFredholmDomainsConstructed /\
      s.smoothFamilyDependenceProved) :
    ellipticFamilyInputClosed (toEllipticFamilyInputStatus s) := by
  exact hClosed

/-- Complete relative determinant package. -/
structure NaturalQuillenPackage where
  analyticFamily : NaturalFamilyAnalyticUpgrade
  analyticFamilyClosed :
    ellipticFamilyInputClosed
      (toEllipticFamilyInputStatus analyticFamily)
  quillen : QuillenBismutFreedStatus
  quillenClosed : quillenBismutFreedClosed quillen
  normalRootPhaseDerivedBeforeQuantization : Prop
  primitiveMonopoleTwistDerivedBeforeQuantization : Prop
  anomalyCancellationDerived : Prop

/-- A Quillen package is canonical only relative to a fully specified family. -/
def relativeQuillenClosure
    (s : NaturalQuillenPackage) : Prop :=
  s.analyticFamilyClosed /\
  s.quillenClosed /\
  s.normalRootPhaseDerivedBeforeQuantization /\
  s.primitiveMonopoleTwistDerivedBeforeQuantization /\
  s.anomalyCancellationDerived

/-- Missing the normal-root boundary family blocks the Janus determinant package. -/
theorem missing_normal_root_boundary_blocks_relative_quillen
    (s : NaturalQuillenPackage)
    (hMissing : Not s.normalRootPhaseDerivedBeforeQuantization) :
    Not (relativeQuillenClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

/-- Missing the primitive monopole twist also blocks the intended family. -/
theorem missing_monopole_twist_blocks_relative_quillen
    (s : NaturalQuillenPackage)
    (hMissing : Not s.primitiveMonopoleTwistDerivedBeforeQuantization) :
    Not (relativeQuillenClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.1

/-- The Quillen construction does not create the Z4 phase; it transports a phase already present in the operator domain. -/
structure Z4OriginAudit where
  normalLineHolonomyMinusOneDerived : Prop
  squareRootLineConstructed : Prop
  quarterBoundaryConditionsDerived : Prop
  familyDomainUsesQuarterBoundaryConditions : Prop
  determinantHolonomyComputed : Prop
  determinantHolonomyMatchesInputZ4 : Prop

/-- Correct causal order of the phase construction. -/
def z4OriginAuditClosed
    (s : Z4OriginAudit) : Prop :=
  s.normalLineHolonomyMinusOneDerived /\
  s.squareRootLineConstructed /\
  s.quarterBoundaryConditionsDerived /\
  s.familyDomainUsesQuarterBoundaryConditions /\
  s.determinantHolonomyComputed /\
  s.determinantHolonomyMatchesInputZ4

/-- A determinant computation without a square-root line is not a derivation of Janus Z4. -/
theorem missing_square_root_blocks_z4_origin
    (s : Z4OriginAudit)
    (hMissing : Not s.squareRootLineConstructed) :
    Not (z4OriginAuditClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.1

/-- Same Quillen family still admits inequivalent finite scalar actions. -/
theorem natural_quillen_family_does_not_fix_renormalized_scalar_action :
    ∃ first second : RenormalizedSectionChoices,
      first ≠ second /\
      renormalizedActionValue 1 first ≠
        renormalizedActionValue 1 second :=
  quillen_line_does_not_fix_renormalized_action

/--
Quillen/Bismut--Freed is the canonical quantization layer of a chosen smooth
Fredholm family.  It does not choose the natural operator family, the Z4 domain,
the field representation, or the finite renormalized action.
-/
structure NaturalQuillenPhysicalStatus where
  naturalFredholmFamilyDerived : Prop
  determinantLineConstructed : Prop
  quillenMetricConstructed : Prop
  bismutFreedConnectionConstructed : Prop
  familiesIndexCurvatureProved : Prop
  globalHolonomyFormulaProved : Prop
  normalRootZ4Matched : Prop
  anomalyCancelled : Prop
  partitionSectionTrivialized : Prop
  finiteRenormalizationFixed : Prop
  physicalPotentialDerived : Prop


def naturalQuillenPhysicalClosure
    (s : NaturalQuillenPhysicalStatus) : Prop :=
  s.naturalFredholmFamilyDerived /\
  s.determinantLineConstructed /\
  s.quillenMetricConstructed /\
  s.bismutFreedConnectionConstructed /\
  s.familiesIndexCurvatureProved /\
  s.globalHolonomyFormulaProved /\
  s.normalRootZ4Matched /\
  s.anomalyCancelled /\
  s.partitionSectionTrivialized /\
  s.finiteRenormalizationFixed /\
  s.physicalPotentialDerived

end P0EFTJanusNaturalFamilyQuillenBridge
end JanusFormal
