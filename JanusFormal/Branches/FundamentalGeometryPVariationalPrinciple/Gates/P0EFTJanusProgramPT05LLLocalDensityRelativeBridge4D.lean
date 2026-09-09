import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D

/-!
# T05 LL local-density relative bridge

This module packages the existing polynomial LL first-jet density, its compact
throat integral and the exact raw, smooth and PT-symmetric LL actions.  The
integrated LL coefficient is inserted into Gate 819's bulk stratum, because
that four-stratum complex has no separate `ll` constructor.

No horizontal incidence theorem is asserted: the available LL density lives
on the effective throat and has not been identified with a boundary or joint
Stokes term in the relative complex.  A full local jet first-variation
realization of T05 remains open.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance llEffectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance llEffectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- A genuine continuous LL density on the effective throat.  The field name
records the LL sector without adding a nonexistent fifth relative stratum. -/
structure ProgramPT05LLLocalDensityCochain
    (period : Real) (hPeriod : period ≠ 0) where
  llDensity : C(EffectiveThroat period hPeriod, Real)

/-- The existing polynomial density on one strong C⁰ LL first-jet packet. -/
def programPT05CanonicalRawLLLocalDensityCochain
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (packet :
      GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame) :
    ProgramPT05LLLocalDensityCochain period hPeriod where
  llDensity := regularGeneralMetricC0LLDensity period hPeriod frame packet

/-- The averaged direct/PT density on the paired first-jet packet. -/
def programPT05CanonicalPTLLLocalDensityCochain
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (packet : GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame) :
    ProgramPT05LLLocalDensityCochain period hPeriod where
  llDensity := (1 / 2 : Real) •
    (regularGeneralMetricC0LLDensity period hPeriod frame packet.1 +
      regularGeneralMetricC0LLDensity period hPeriod frame packet.2)

/-- Continuous integration of the typed LL density against a finite throat
measure. -/
def programPT05LLDensityIntegral
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (density : ProgramPT05LLLocalDensityCochain period hPeriod) : Real :=
  continuousThroatIntegralCLM period hPeriod measure density.llDensity

/-- The wrapper is the actual Bochner integral of its LL density. -/
theorem programPT05LLDensityIntegral_eq_integral
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (density : ProgramPT05LLLocalDensityCochain period hPeriod) :
    programPT05LLDensityIntegral period hPeriod measure density =
      ∫ point, density.llDensity point ∂measure := by
  exact continuousThroatIntegralCLM_apply period hPeriod measure density.llDensity

/-- Integrating the canonical raw density is exactly the existing raw LL
action. -/
theorem programPT05CanonicalRawLLDensityIntegral_eq_action
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (packet :
      GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame) :
    programPT05LLDensityIntegral period hPeriod measure
        (programPT05CanonicalRawLLLocalDensityCochain period hPeriod
          frame packet) =
      regularGeneralMetricC0LLRawAction period hPeriod frame measure packet := by
  rfl

/-- On a smooth first jet, the packaged density is the original differential
LL density pointwise. -/
theorem programPT05CanonicalRawLLLocalDensity_smooth_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (programPT05CanonicalRawLLLocalDensityCochain period hPeriod frame
      (smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame
        (fields.llAuxMetric, (fields.llMeasure, fields.llField)))).llDensity point =
      differentialLLDensity period hPeriod frame fields point := by
  exact regularGeneralMetricC0LLDensity_smooth_apply
    period hPeriod frame fields point

/-- The smooth specialization of the integral is the genuine LL action. -/
theorem programPT05CanonicalRawLLDensityIntegral_smooth
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (fields : IndependentFields period hPeriod) :
    programPT05LLDensityIntegral period hPeriod measure
        (programPT05CanonicalRawLLLocalDensityCochain period hPeriod frame
          (smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame
            (fields.llAuxMetric, (fields.llMeasure, fields.llField)))) =
      globalDifferentialLLAction period hPeriod frame fields measure := by
  exact
    (programPT05CanonicalRawLLDensityIntegral_eq_action period hPeriod frame
      measure
      (smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame
        (fields.llAuxMetric, (fields.llMeasure, fields.llField)))).trans
      (regularGeneralMetricC0LLRawAction_smooth period hPeriod frame measure fields)

/-- Integrating the averaged local density is the existing PT-symmetric packet
action. -/
theorem programPT05CanonicalPTLLDensityIntegral_eq_action
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (packet : GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame) :
    programPT05LLDensityIntegral period hPeriod measure
        (programPT05CanonicalPTLLLocalDensityCochain period hPeriod
          frame packet) =
      regularGeneralMetricC0LLPTAction period hPeriod frame measure packet := by
  simp [programPT05LLDensityIntegral,
    programPT05CanonicalPTLLLocalDensityCochain,
    regularGeneralMetricC0LLPTAction, regularGeneralMetricC0LLRawAction]
  ring

/-- The smooth paired specialization is the genuine PT-symmetric LL action. -/
theorem programPT05CanonicalPTLLDensityIntegral_smooth
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (fields : IndependentFields period hPeriod) :
    programPT05LLDensityIntegral period hPeriod measure
        (programPT05CanonicalPTLLLocalDensityCochain period hPeriod frame
          (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
            (fields.llAuxMetric, (fields.llMeasure, fields.llField)))) =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields measure := by
  exact
    (programPT05CanonicalPTLLDensityIntegral_eq_action period hPeriod frame
      measure
      (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
        (fields.llAuxMetric, (fields.llMeasure, fields.llField)))).trans
      (regularGeneralMetricC0LLPTAction_smooth period hPeriod frame measure fields)

/-- Support extension of the integrated LL action to Gate 819.  LL is part of
the total action coefficient, so it is stored on `.bulk`; no `.ll` stratum
exists in the relative carrier. -/
def programPT05LLDensityIntegratedRelativeCochain
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (density : ProgramPT05LLLocalDensityCochain period hPeriod) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0
  | .bulk => (programPT05LLDensityIntegral period hPeriod measure density, 0)
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint => 0

@[simp]
theorem programPT05LLDensityIntegratedRelativeCochain_bulk
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (density : ProgramPT05LLLocalDensityCochain period hPeriod) :
    programPT05LLDensityIntegratedRelativeCochain period hPeriod measure density
        .bulk =
      (programPT05LLDensityIntegral period hPeriod measure density, 0) := by
  rfl

/-- The bulk coefficient obtained from a canonical raw LL density is its exact
existing action. -/
theorem programPT05CanonicalRawLLIntegratedRelativeCochain_bulk_eq_action
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure measure]
    (packet :
      GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame) :
    programPT05LLDensityIntegratedRelativeCochain period hPeriod measure
        (programPT05CanonicalRawLLLocalDensityCochain period hPeriod
          frame packet) .bulk =
      (regularGeneralMetricC0LLRawAction period hPeriod frame measure packet, 0) := by
  rw [programPT05LLDensityIntegratedRelativeCochain_bulk,
    programPT05CanonicalRawLLDensityIntegral_eq_action]

end
end P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D
end JanusFormal
