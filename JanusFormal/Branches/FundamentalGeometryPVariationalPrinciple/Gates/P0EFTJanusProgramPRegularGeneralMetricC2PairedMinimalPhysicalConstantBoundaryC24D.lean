import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D

/-!
# Constant boundary blocks in the paired minimal-physical family

The paired target construction rebases only the dependent boundary variation
packet.  Its non-null boundary source and finite null-face ledger are inherited
verbatim from the base action datum.  Consequently the Robin and finite-BV
action blocks are constant on the exact paired domain and hence C² for every
compatible norm on the minimal physical tangent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The exact nine blocks of the canonical paired family, totalized at its
certified zero direction. -/
noncomputable def regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    FullCoupledActionBlocks (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :=
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  let hZero :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  globalCandidateAActionBlocks period hPeriod
    (family.toActionFamily period hPeriod 0 hZero) measure

/-- The Robin/GHY block agrees with the base boundary action throughout the
exact paired domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_robin_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure).robin direction =
      globalCandidateAGHYAction period hPeriod data := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  have hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ family.domain :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change globalCandidateAGHYAction period hPeriod
      (family.datumAtTotal period hPeriod 0 hZero direction).2 =
    globalCandidateAGHYAction period hPeriod data
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  rfl

/-- The finite null-face/BV block agrees with the base finite action throughout
the exact paired domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_finiteBV_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure).finiteBV direction =
      globalCandidateANullBoundaryAction period hPeriod data := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  have hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ family.domain :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change globalCandidateANullBoundaryAction period hPeriod
      (family.datumAtTotal period hPeriod 0 hZero direction).2 =
    globalCandidateANullBoundaryAction period hPeriod data
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  rfl

/-- The five nonconstant physical blocks left after eliminating Robin and
finite BV. -/
structure GlobalCandidateAFiveVariablePhysicalC2WithinAt
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (domain : Set Model) (point : Model) : Prop where
  candidateA : ContDiffWithinAt Real 2 blocks.candidateA domain point
  einsteinHilbertPlus :
    ContDiffWithinAt Real 2 blocks.einsteinHilbertPlus domain point
  einsteinHilbertMinus :
    ContDiffWithinAt Real 2 blocks.einsteinHilbertMinus domain point
  maxwellPlus : ContDiffWithinAt Real 2 blocks.maxwellPlus domain point
  maxwellMinus : ContDiffWithinAt Real 2 blocks.maxwellMinus domain point

/-- The constant Robin block is C² within the exact paired domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_robin_contDiffWithinAt
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)]
    [NormedSpace Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration couplings data plusBase minusBase hBase
          measure).robin
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) point := by
  exact contDiffWithinAt_const.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_robin_eq
        period hPeriod configuration couplings data plusBase minusBase hBase
          measure direction hDirection)
    hPoint

/-- The constant finite-BV block is C² within the exact paired domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_finiteBV_contDiffWithinAt
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)]
    [NormedSpace Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration couplings data plusBase minusBase hBase
          measure).finiteBV
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) point := by
  exact contDiffWithinAt_const.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_finiteBV_eq
        period hPeriod configuration couplings data plusBase minusBase hBase
          measure direction hDirection)
    hPoint

/-- Five variable certificates reconstruct the established seven-physical
packet because the two boundary blocks are constant. -/
def regularGeneralMetricC2PairedMinimalPhysicalFiveVariableC2ToSevenPhysical
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)]
    [NormedSpace Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (hVariable : GlobalCandidateAFiveVariablePhysicalC2WithinAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration couplings data plusBase minusBase hBase
          measure)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) point) :
    GlobalCandidateASevenPhysicalC2WithinAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration couplings data plusBase minusBase hBase
          measure)
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) point where
  candidateA := hVariable.candidateA
  robin :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_robin_contDiffWithinAt
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure point hPoint
  einsteinHilbertPlus := hVariable.einsteinHilbertPlus
  einsteinHilbertMinus := hVariable.einsteinHilbertMinus
  maxwellPlus := hVariable.maxwellPlus
  maxwellMinus := hVariable.maxwellMinus
  finiteBV :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_finiteBV_contDiffWithinAt
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure point hPoint

/-- Gate marker: only five variable physical C² blocks remain after the exact
paired family eliminates its two constant boundary blocks. -/
theorem regular_general_metric_c2_paired_minimal_physical_constant_boundary_c2_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)]
    [NormedSpace Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration couplings data plusBase minusBase hBase
            measure).robin
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration plusBase minusBase) point ∧
      ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration couplings data plusBase minusBase hBase
            measure).finiteBV
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration plusBase minusBase) point :=
  ⟨regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_robin_contDiffWithinAt
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure point hPoint,
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_finiteBV_contDiffWithinAt
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure point hPoint⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
end JanusFormal
