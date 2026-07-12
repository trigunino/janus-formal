import Mathlib
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusAnomalyObjectDimensionParity
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusPartitionFunctionSectionNoGo
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusQuillenFamilyCanonicity
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalPinLiftBoundaryConditions

namespace JanusFormal
namespace P0EFTJanusQuillenAnomalySynthesis

set_option autoImplicit false

open P0EFTJanusAnomalyObjectDimensionParity
open P0EFTJanusPartitionFunctionSectionNoGo
open P0EFTJanusQuillenFamilyCanonicity
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusNormalOrientationZ4Lift

/-- Three mathematically distinct ways of organizing the Janus fermion family. -/
inductive JanusFermionFamilyRoute where
  | intrinsicClosedThreeDimensional
  | sphereFiberedEvenDimensional
  | fourDimensionalBulkWithBoundary
  deriving DecidableEq, Repr

/-- Primary anomaly object expected from each route. -/
def routeAnomalyObject :
    JanusFermionFamilyRoute → AnomalyObjectKind
  | JanusFermionFamilyRoute.intrinsicClosedThreeDimensional =>
      AnomalyObjectKind.indexGerbe
  | JanusFermionFamilyRoute.sphereFiberedEvenDimensional =>
      AnomalyObjectKind.determinantLine
  | JanusFermionFamilyRoute.fourDimensionalBulkWithBoundary =>
      AnomalyObjectKind.determinantLine

@[simp] theorem intrinsic_three_route_has_index_gerbe :
    routeAnomalyObject
        JanusFermionFamilyRoute.intrinsicClosedThreeDimensional =
      AnomalyObjectKind.indexGerbe := by
  rfl

@[simp] theorem sphere_fibered_route_has_determinant_line :
    routeAnomalyObject
        JanusFermionFamilyRoute.sphereFiberedEvenDimensional =
      AnomalyObjectKind.determinantLine := by
  rfl

@[simp] theorem bulk_boundary_route_has_determinant_line :
    routeAnomalyObject
        JanusFermionFamilyRoute.fourDimensionalBulkWithBoundary =
      AnomalyObjectKind.determinantLine := by
  rfl

/--
The direct closed-three-dimensional route agrees with the odd families-index
classification.
-/
theorem intrinsic_route_matches_dimension_parity :
    routeAnomalyObject
        JanusFermionFamilyRoute.intrinsicClosedThreeDimensional =
      canonicalAnomalyObject 3 := by
  rw [intrinsic_three_route_has_index_gerbe,
    three_dimensional_family_has_index_gerbe]

/--
The normal square-root geometry supplies two PT-conjugate quarter phases, not a
single selected phase.
-/
theorem normal_root_geometry_supplies_pair_not_choice :
    IsNormalSquareRoot
        (normalRootPhase NormalRootChoice.positiveQuarter) /\
    IsNormalSquareRoot
        (normalRootPhase NormalRootChoice.negativeQuarter) /\
    normalRootPhase NormalRootChoice.positiveQuarter ≠
      normalRootPhase NormalRootChoice.negativeQuarter := by
  exact ⟨normal_root_phase_is_square_root _,
    normal_root_phase_is_square_root _,
    by native_decide⟩

/-- The two root multipliers square to the same normal sign. -/
theorem normal_root_pair_has_common_square :
    normalRootMultiplier NormalRootChoice.positiveQuarter *
        normalRootMultiplier NormalRootChoice.positiveQuarter = -1 /\
    normalRootMultiplier NormalRootChoice.negativeQuarter *
        normalRootMultiplier NormalRootChoice.negativeQuarter = -1 := by
  exact ⟨normal_root_multiplier_square _,
    normal_root_multiplier_square _⟩

/--
Even if a determinant line exists, its bare existence does not determine a
renormalized scalar action.
-/
theorem determinant_line_does_not_fix_effective_potential :
    ∃ first second : RenormalizedSectionChoices,
      first ≠ second /\
      renormalizedActionValue 1 first ≠
        renormalizedActionValue 1 second :=
  quillen_line_does_not_fix_renormalized_action

/-- The same anomaly section admits arbitrary scalar representatives after changing trivialization. -/
theorem anomaly_section_does_not_fix_scalar_action
    (sectionLog targetAction : ℝ) :
    scalarEffectiveAction
      (trivializationForTarget sectionLog targetAction) =
      targetAction :=
  every_target_action_can_be_realized sectionLog targetAction

/--
Data required for the precise affirmative statement: a canonical anomaly object
exists only after the universal elliptic family has been specified.
-/
structure JanusCanonicalAnomalyStatus where
  moduliStackConstructed : Prop
  universalImmersionFamilyConstructed : Prop
  spinOrPinCBundleFamilyConstructed : Prop
  normalRootFlatLineFamilyConstructed : Prop
  primitiveMonopoleTwistFamilyConstructed : Prop
  gaugeFixedEllipticComplexFamilyConstructed : Prop
  smoothFredholmFamilyProved : Prop
  bosonicGhostDeterminantLineConstructed : Prop
  oddFermionIndexGerbeConstructed : Prop
  etaSectionConstructed : Prop
  anomalyCancellationOrBulkTrivializationDerived : Prop


def janusCanonicalAnomalyObjectClosed
    (s : JanusCanonicalAnomalyStatus) : Prop :=
  s.moduliStackConstructed /\
  s.universalImmersionFamilyConstructed /\
  s.spinOrPinCBundleFamilyConstructed /\
  s.normalRootFlatLineFamilyConstructed /\
  s.primitiveMonopoleTwistFamilyConstructed /\
  s.gaugeFixedEllipticComplexFamilyConstructed /\
  s.smoothFredholmFamilyProved /\
  s.bosonicGhostDeterminantLineConstructed /\
  s.oddFermionIndexGerbeConstructed /\
  s.etaSectionConstructed /\
  s.anomalyCancellationOrBulkTrivializationDerived

/-- Additional data needed before the anomaly package becomes a predictive scalar potential. -/
structure JanusPredictivePotentialStatus extends JanusCanonicalAnomalyStatus where
  fieldMultiplicitiesDerived : Prop
  actionAndHessianDerived : Prop
  rootChoiceOrPTPairSelected : Prop
  globalTrivializationDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop
  referenceScaleDerived : Prop
  sectorNormalizationsDerived : Prop
  scalarEffectivePotentialDerived : Prop
  stableVacuumSchemeIndependent : Prop


def janusPredictivePotentialClosed
    (s : JanusPredictivePotentialStatus) : Prop :=
  janusCanonicalAnomalyObjectClosed s.toJanusCanonicalAnomalyStatus /\
  s.fieldMultiplicitiesDerived /\
  s.actionAndHessianDerived /\
  s.rootChoiceOrPTPairSelected /\
  s.globalTrivializationDerived /\
  s.finiteCountertermsFixedMicroscopically /\
  s.referenceScaleDerived /\
  s.sectorNormalizationsDerived /\
  s.scalarEffectivePotentialDerived /\
  s.stableVacuumSchemeIndependent

/-- A canonical anomaly object without the action/Hessian does not determine the elliptic complex dynamically. -/
theorem missing_action_blocks_predictive_potential
    (s : JanusPredictivePotentialStatus)
    (hMissing : Not s.actionAndHessianDerived) :
    Not (janusPredictivePotentialClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

/-- A canonical anomaly object without microscopic finite parts does not determine a vacuum. -/
theorem missing_finite_parts_blocks_predictive_potential
    (s : JanusPredictivePotentialStatus)
    (hMissing : Not s.finiteCountertermsFixedMicroscopically) :
    Not (janusPredictivePotentialClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

/-- A canonical anomaly object does not choose between the two normal-root phases. -/
theorem missing_root_selection_blocks_predictive_potential
    (s : JanusPredictivePotentialStatus)
    (hMissing : Not s.rootChoiceOrPTPairSelected) :
    Not (janusPredictivePotentialClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.1

/--
Final mathematical verdict encoded by the branch:

* a canonical anomaly package is available relative to a constructed universal
  elliptic family;
* the intrinsic closed 3D fermionic component is naturally gerbe/K1-valued;
* a determinant line appears for the boson/ghost Fredholm complex, for a chosen
  even-dimensional `S2` fibration, or through 4D bulk/boundary transgression;
* none of these objects alone selects the action, the Z4 root, field
  multiplicities, finite counterterms or sector normalization.
-/
structure JanusQuillenVerdict where
  canonicalRelativeAnomalyObjectExists : Prop
  directIntrinsicFermionObjectIsIndexGerbe : Prop
  determinantLineRoutesRequireExtraStructure : Prop
  normalGeometrySuppliesTwoZ4Roots : Prop
  anomalyObjectDoesNotSelectRoot : Prop
  anomalyObjectDoesNotGenerateEllipticFamily : Prop
  anomalyObjectDoesNotFixFinitePotential : Prop
  anomalyObjectDoesNotFixSectorNormalization : Prop
  bulkInflowCanTrivializeRelativeAnomaly : Prop
  predictiveClosureRequiresMicroscopicInput : Prop


def janusQuillenVerdictClosed
    (s : JanusQuillenVerdict) : Prop :=
  s.canonicalRelativeAnomalyObjectExists /\
  s.directIntrinsicFermionObjectIsIndexGerbe /\
  s.determinantLineRoutesRequireExtraStructure /\
  s.normalGeometrySuppliesTwoZ4Roots /\
  s.anomalyObjectDoesNotSelectRoot /\
  s.anomalyObjectDoesNotGenerateEllipticFamily /\
  s.anomalyObjectDoesNotFixFinitePotential /\
  s.anomalyObjectDoesNotFixSectorNormalization /\
  s.bulkInflowCanTrivializeRelativeAnomaly /\
  s.predictiveClosureRequiresMicroscopicInput

end P0EFTJanusQuillenAnomalySynthesis
end JanusFormal
