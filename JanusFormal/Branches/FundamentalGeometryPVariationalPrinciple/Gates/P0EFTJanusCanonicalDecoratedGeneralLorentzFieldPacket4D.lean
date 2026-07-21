import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalDecoratedProgramPFieldDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D

/-! # Canonical decorated general-Lorentz field packet -/

namespace JanusFormal
namespace P0EFTJanusCanonicalDecoratedGeneralLorentzFieldPacket4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusCanonicalEffectiveDecoratedMappingTorus4D
open P0EFTJanusCanonicalDecoratedProgramPFieldDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The canonical common core with its diagonal metric scaffold replaced by
two genuine intrinsic general Lorentz metrics on the same D8 base. -/
structure CanonicalDecoratedGeneralLorentzFieldPacket where
  core : CanonicalDecoratedProgramPFieldDomain period hPeriod
  generalFields : GeneralLorentzIndependentFields period hPeriod
  generalBoundary : GeneralLorentzIndependentBoundaryData period hPeriod

def canonicalDecoratedGeneralLorentzFields :
    GeneralLorentzIndependentFields period hPeriod :=
  let fields := canonicalPositiveOperatorFields period hPeriod
  { metrics :=
      (intrinsicSmoothGeneralLorentzMetric period hPeriod,
        intrinsicSmoothGeneralLorentzMetric period hPeriod)
    matter := fields.matter
    gauge := fields.gauge
    ghosts := fields.ghosts
    auxiliaries := fields.auxiliaries
    llAuxMetric := fields.llAuxMetric
    llMeasure := fields.llMeasure
    llField := fields.llField }

def canonicalDecoratedGeneralLorentzFieldPacket :
    CanonicalDecoratedGeneralLorentzFieldPacket period hPeriod :=
  let fields := canonicalDecoratedGeneralLorentzFields period hPeriod
  { core := canonicalDecoratedProgramPFieldDomain period hPeriod
    generalFields := fields
    generalBoundary :=
      generalLorentzIndependentBoundaryTrace period hPeriod fields }

/-- Only the metric representation changes: every non-metric field is exactly
the field already stored in the common domain. -/
theorem canonicalDecoratedGeneralLorentzFields_scaffold :
    diagonalScaffold period hPeriod
        (canonicalDecoratedGeneralLorentzFields period hPeriod) =
      canonicalPositiveOperatorFields period hPeriod :=
  rfl

@[simp] theorem canonicalDecoratedGeneralLorentzFieldPacket_metrics :
    (canonicalDecoratedGeneralLorentzFieldPacket period hPeriod).generalFields.metrics =
      ((canonicalDecoratedGeneralLorentzFieldPacket period hPeriod).core.decorations.lorentzMetric,
        (canonicalDecoratedGeneralLorentzFieldPacket period hPeriod).core.decorations.lorentzMetric) := by
  change
    (intrinsicSmoothGeneralLorentzMetric period hPeriod,
      intrinsicSmoothGeneralLorentzMetric period hPeriod) =
    ((canonicalEffectiveDecoratedMappingTorus period hPeriod).lorentzMetric,
      (canonicalEffectiveDecoratedMappingTorus period hPeriod).lorentzMetric)
  rw [canonicalEffectiveDecoratedMappingTorus_lorentzMetric]

/-- The actual general-metric packet is fixed by simultaneous analytic PT and
sector exchange. -/
theorem canonicalDecoratedGeneralLorentzFields_pt_fixed :
    generalLorentzIndependentExchange period hPeriod
        (canonicalDecoratedGeneralLorentzFields period hPeriod) =
      canonicalDecoratedGeneralLorentzFields period hPeriod := by
  have hNonmetric :
      independentExchange period hPeriod
          (canonicalPositiveOperatorFields period hPeriod) =
        canonicalPositiveOperatorFields period hPeriod :=
    (ptMatchedIndependent_iff_fixed_exchange period hPeriod _).1
      (canonicalPositiveOperatorFields_ptMatched period hPeriod)
  apply GeneralLorentzIndependentFields.ext
  · change
      smoothGeneralLorentzMetricPTExchange period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod,
            intrinsicSmoothGeneralLorentzMetric period hPeriod) =
        (intrinsicSmoothGeneralLorentzMetric period hPeriod,
          intrinsicSmoothGeneralLorentzMetric period hPeriod)
    exact intrinsicSmoothGeneralLorentzMetric_pair_ptExchange_fixed
      period hPeriod
  · exact congrArg IndependentFields.matter hNonmetric
  · exact congrArg IndependentFields.gauge hNonmetric
  · exact congrArg IndependentFields.ghosts hNonmetric
  · exact congrArg IndependentFields.auxiliaries hNonmetric
  · exact congrArg IndependentFields.llAuxMetric hNonmetric
  · exact congrArg IndependentFields.llMeasure hNonmetric
  · exact congrArg IndependentFields.llField hNonmetric

theorem canonicalDecoratedGeneralLorentzFieldPacket_satisfies_boundary :
    let package := canonicalDecoratedGeneralLorentzFieldPacket period hPeriod
    SatisfiesGeneralLorentzIndependentBoundary period hPeriod
      package.generalBoundary package.generalFields :=
  rfl

theorem canonicalDecoratedGeneralLorentzBoundary_pt_fixed :
    let package := canonicalDecoratedGeneralLorentzFieldPacket period hPeriod
    generalLorentzIndependentBoundaryExchange period hPeriod
        package.generalBoundary =
      package.generalBoundary := by
  change generalLorentzIndependentBoundaryExchange period hPeriod
      (generalLorentzIndependentBoundaryTrace period hPeriod
        (canonicalDecoratedGeneralLorentzFields period hPeriod)) =
    generalLorentzIndependentBoundaryTrace period hPeriod
      (canonicalDecoratedGeneralLorentzFields period hPeriod)
  rw [← generalLorentzIndependentBoundaryTrace_exchange,
    canonicalDecoratedGeneralLorentzFields_pt_fixed]

end
end P0EFTJanusCanonicalDecoratedGeneralLorentzFieldPacket4D
end JanusFormal
