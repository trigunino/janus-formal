import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D

/-!
# Global compatible physical third-jet vector-density representatives

The already established base/fiber covariance law is packaged as a family of
smooth-in-the-fiber representatives over every valid chart at a base point.
The canonical radial Cartan density supplies such a compatible family by using
the base point and the bundle core's preferred index as reference data.

No base regularity, integration, or Stokes statement is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (Base period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (Base period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev Chart :=
  ActualPhysicalThirdOrderJetProductBundleIndex period hPeriod

private abbrev PhysicalThirdJetCore :=
  actualPhysicalThirdOrderJetProductVectorBundleCore
    period hPeriod .positiveQuarter

/-- A simultaneous valid base chart and physical J³ fiber chart at one base
point. -/
structure ProgramPT06PhysicalThirdJetVectorDensityChartAt4D
    (base : Base period hPeriod) where
  center : Base period hPeriod
  center_mem : base ∈
    (extChartAt throatCoverModelWithCorners center).source
  fiberChart : Chart period hPeriod
  fiber_mem : base ∈
    (PhysicalThirdJetCore period hPeriod).baseSet fiberChart

/-- Preferred valid chart at a base point: the centered manifold chart and the
bundle core's selected index. -/
def programPT06PhysicalThirdJetVectorDensityCanonicalChartAt
    (base : Base period hPeriod) :
    ProgramPT06PhysicalThirdJetVectorDensityChartAt4D period hPeriod base where
  center := base
  center_mem := mem_extChartAt_source base
  fiberChart := (PhysicalThirdJetCore period hPeriod).indexAt base
  fiber_mem := (PhysicalThirdJetCore period hPeriod).mem_baseSet_at base

/-- A global physical J³ vector density presented by compatible local chart
representatives.  The regularity recorded here is exactly fixed-base
smoothness in the physical J³ fiber. -/
structure ProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D where
  representative : (base : Base period hPeriod) →
    ProgramPT06PhysicalThirdJetVectorDensityChartAt4D period hPeriod base →
      ProgramPT06ActualPhysicalThirdJetVectorDensity4D
  representative_contDiff : ∀ (base : Base period hPeriod)
    (chart :
      ProgramPT06PhysicalThirdJetVectorDensityChartAt4D period hPeriod base),
      ContDiff Real ∞ (representative base chart)
  transition : ∀ (base : Base period hPeriod)
    (first second :
      ProgramPT06PhysicalThirdJetVectorDensityChartAt4D period hPeriod base),
      programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
          first.center second.center base first.center_mem second.center_mem
          first.fiberChart second.fiberChart (representative base second) =
        representative base first

/-- The representative selected in the preferred centered chart. -/
def ProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D.canonicalValue
    (densitySection :
      ProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D period hPeriod)
    (base : Base period hPeriod) :
    ProgramPT06ActualPhysicalThirdJetVectorDensity4D :=
  densitySection.representative base
    (programPT06PhysicalThirdJetVectorDensityCanonicalChartAt
      period hPeriod base)

/-- Every valid representative is the exact pullback of the preferred chart
value. -/
theorem
    ProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D.pullback_canonicalValue
    (densitySection :
      ProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D period hPeriod)
    (base : Base period hPeriod)
    (chart :
      ProgramPT06PhysicalThirdJetVectorDensityChartAt4D period hPeriod base) :
    programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
        chart.center base base chart.center_mem (mem_extChartAt_source base)
        chart.fiberChart ((PhysicalThirdJetCore period hPeriod).indexAt base)
        (ProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D.canonicalValue
          period hPeriod densitySection base) =
      densitySection.representative base chart := by
  exact densitySection.transition base chart
    (programPT06PhysicalThirdJetVectorDensityCanonicalChartAt
      period hPeriod base)

/-- Gate 942's radial Cartan vector density, glued over all valid simultaneous
base/fiber charts. -/
def programPT06T02DegreeFourRadialCartanGlobalPhysicalThirdJetVectorDensitySection
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D period hPeriod where
  representative := fun base chart =>
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
      period hPeriod functional base chart.center base
      (mem_extChartAt_source base) chart.center_mem
      ((PhysicalThirdJetCore period hPeriod).indexAt base) chart.fiberChart
  representative_contDiff := by
    intro base chart
    exact
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative_contDiff
        period hPeriod functional base chart.center base
        (mem_extChartAt_source base) chart.center_mem
        ((PhysicalThirdJetCore period hPeriod).indexAt base) chart.fiberChart
  transition := by
    intro base first second
    exact
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_chartChange
        period hPeriod functional base first.center second.center base
        (mem_extChartAt_source base) first.center_mem second.center_mem
        ((PhysicalThirdJetCore period hPeriod).indexAt base)
        first.fiberChart second.fiberChart
        ⟨⟨first.fiber_mem, second.fiber_mem⟩,
          (PhysicalThirdJetCore period hPeriod).mem_baseSet_at base⟩

/-- In its preferred chart, the glued radial section is the original Gate 942
physical vector density. -/
@[simp]
theorem
    programPT06T02DegreeFourRadialCartanGlobalPhysicalThirdJetVectorDensitySection_canonicalValue
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (base : Base period hPeriod) :
    ProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D.canonicalValue
        period hPeriod
        (programPT06T02DegreeFourRadialCartanGlobalPhysicalThirdJetVectorDensitySection
          period hPeriod functional) base =
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional := by
  apply
    programPT06ActualPhysicalThirdJetVectorDensityPullback_self
      period hPeriod base base (mem_extChartAt_source base)
      ((PhysicalThirdJetCore period hPeriod).indexAt base)
      ((PhysicalThirdJetCore period hPeriod).mem_baseSet_at base)

end
end P0EFTJanusProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D
end JanusFormal
