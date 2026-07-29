import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalPTPairedConformalGeneralLorentzFieldPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFieldSpace4D

/-!
# Canonical conformal global-field time orbit

The complete mapping-torus time action preserves positivity of scalar fields.
It therefore transports the explicit positive PT-paired conformal scales into
an actual real-parameter family of `GlobalFieldConfiguration`s through the
intrinsic Candidate-A geometry and the canonical zero-field constructor.

This gate proves the identity and composition laws inherited from scalar
pullback.  It does not claim a time action on arbitrary global configurations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCanonicalConformalGlobalFieldTimeOrbit4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
open P0EFTJanusCanonicalPTPairedConformalGeneralLorentzFieldPacket4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Pullback by a time slice preserves strict positivity. -/
theorem smoothSpacetimeTimeAction_pos
    (field : SmoothScalarField period hPeriod)
    (hField : ∀ point, 0 < field point)
    (shift : Real) (point) :
    0 <
      smoothSpacetimeTimeAction period hPeriod Real shift field point := by
  rw [smoothSpacetimeTimeAction_apply]
  exact hField _

/-- A smooth scalar field bundled with its strict positivity. -/
abbrev PositiveSmoothScalarField :=
  { field : SmoothScalarField period hPeriod //
    ∀ point, 0 < field point }

/-- The complete pullback time action restricted to positive scalar fields. -/
def positiveSmoothScalarTimeAction
    (shift : Real)
    (field : PositiveSmoothScalarField period hPeriod) :
    PositiveSmoothScalarField period hPeriod :=
  ⟨smoothSpacetimeTimeAction period hPeriod Real shift field.1,
    smoothSpacetimeTimeAction_pos period hPeriod field.1 field.2 shift⟩

@[simp]
theorem positiveSmoothScalarTimeAction_zero
    (field : PositiveSmoothScalarField period hPeriod) :
    positiveSmoothScalarTimeAction period hPeriod 0 field = field := by
  apply Subtype.ext
  exact smoothSpacetimeTimeAction_zero period hPeriod Real field.1

theorem positiveSmoothScalarTimeAction_add
    (first second : Real)
    (field : PositiveSmoothScalarField period hPeriod) :
    positiveSmoothScalarTimeAction period hPeriod (first + second) field =
      positiveSmoothScalarTimeAction period hPeriod second
        (positiveSmoothScalarTimeAction period hPeriod first field) := by
  apply Subtype.ext
  exact smoothSpacetimeTimeAction_add period hPeriod Real first second field.1

/-- Lift a positive conformal pair to the canonical zero-field global
configuration. -/
def positiveConformalGlobalFieldConfiguration
    (plus minus : PositiveSmoothScalarField period hPeriod) :
    GlobalFieldConfiguration period hPeriod :=
  zeroGlobalFieldConfiguration period hPeriod
    (conformalGlobalCandidateAGeometry period hPeriod
      plus.1 minus.1 plus.2 minus.2)

/-- The conformal global configuration obtained by translating both positive
scales. -/
def positiveConformalGlobalFieldTimeOrbit
    (plus minus : PositiveSmoothScalarField period hPeriod)
    (shift : Real) :
    GlobalFieldConfiguration period hPeriod :=
  positiveConformalGlobalFieldConfiguration period hPeriod
    (positiveSmoothScalarTimeAction period hPeriod shift plus)
    (positiveSmoothScalarTimeAction period hPeriod shift minus)

@[simp]
theorem positiveConformalGlobalFieldTimeOrbit_zero
    (plus minus : PositiveSmoothScalarField period hPeriod) :
    positiveConformalGlobalFieldTimeOrbit period hPeriod plus minus 0 =
      positiveConformalGlobalFieldConfiguration period hPeriod plus minus := by
  unfold positiveConformalGlobalFieldTimeOrbit
  rw [positiveSmoothScalarTimeAction_zero,
    positiveSmoothScalarTimeAction_zero]

theorem positiveConformalGlobalFieldTimeOrbit_add
    (first second : Real)
    (plus minus : PositiveSmoothScalarField period hPeriod) :
    positiveConformalGlobalFieldTimeOrbit period hPeriod
        plus minus (first + second) =
      positiveConformalGlobalFieldTimeOrbit period hPeriod
        (positiveSmoothScalarTimeAction period hPeriod first plus)
        (positiveSmoothScalarTimeAction period hPeriod first minus)
        second := by
  unfold positiveConformalGlobalFieldTimeOrbit
  rw [positiveSmoothScalarTimeAction_add,
    positiveSmoothScalarTimeAction_add]

/-- The explicit positive conformal scale as a bundled field. -/
def explicitPositiveScale :
    PositiveSmoothScalarField period hPeriod :=
  ⟨explicitPositivePTScale period hPeriod,
    explicitPositivePTScale_pos period hPeriod⟩

/-- The bundled positive PT partner of the explicit scale. -/
def explicitPositivePTPartnerScale :
    PositiveSmoothScalarField period hPeriod :=
  ⟨ptPairedConformalScale period hPeriod
      (explicitPositivePTScale period hPeriod),
    ptPairedConformalScale_pos period hPeriod
      (explicitPositivePTScale period hPeriod)
      (explicitPositivePTScale_pos period hPeriod)⟩

/-- The base point of the canonical conformal time orbit. -/
def canonicalConformalGlobalField :
    GlobalFieldConfiguration period hPeriod :=
  positiveConformalGlobalFieldConfiguration period hPeriod
    (explicitPositiveScale period hPeriod)
    (explicitPositivePTPartnerScale period hPeriod)

/-- The explicit positive scale and its PT partner, translated together and
lifted to the unified Program-P global field space. -/
def canonicalConformalGlobalFieldTimeOrbit (shift : Real) :
    GlobalFieldConfiguration period hPeriod :=
  positiveConformalGlobalFieldTimeOrbit period hPeriod
    (explicitPositiveScale period hPeriod)
    (explicitPositivePTPartnerScale period hPeriod)
    shift

@[simp]
theorem canonicalConformalGlobalFieldTimeOrbit_zero :
    canonicalConformalGlobalFieldTimeOrbit period hPeriod 0 =
      canonicalConformalGlobalField period hPeriod := by
  exact positiveConformalGlobalFieldTimeOrbit_zero period hPeriod
    (explicitPositiveScale period hPeriod)
    (explicitPositivePTPartnerScale period hPeriod)

theorem canonicalConformalGlobalFieldTimeOrbit_add
    (first second : Real) :
    canonicalConformalGlobalFieldTimeOrbit period hPeriod (first + second) =
      positiveConformalGlobalFieldTimeOrbit period hPeriod
        (positiveSmoothScalarTimeAction period hPeriod first
          (explicitPositiveScale period hPeriod))
        (positiveSmoothScalarTimeAction period hPeriod first
          (explicitPositivePTPartnerScale period hPeriod))
        second := by
  exact positiveConformalGlobalFieldTimeOrbit_add period hPeriod
    first second
    (explicitPositiveScale period hPeriod)
    (explicitPositivePTPartnerScale period hPeriod)

end
end P0EFTJanusProgramPCanonicalConformalGlobalFieldTimeOrbit4D
end JanusFormal
