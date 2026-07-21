import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D

/-! # Global covariant derivative on the doubled smooth D9 spinor bundle -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledGlobalCovariantDerivative4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Bundle
open Bundle Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance coreIsContMDiff (choice : NormalRootChoice) :
    (smoothThroatDoubledMatterSpinorVectorBundleCore period hPeriod choice)
      |>.IsContMDiff throatCoverModelWithCorners ω :=
  smoothThroatDoubledMatterSpinorVectorBundleCore_isContMDiff
    period hPeriod choice

local instance totalSpaceTopology (choice : NormalRootChoice) :
    TopologicalSpace (Bundle.TotalSpace D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice)) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).toTopologicalSpace

local instance fiberBundle (choice : NormalRootChoice) :
    FiberBundle D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).fiberBundle

local instance vectorBundle (choice : NormalRootChoice) :
    VectorBundle Real D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatDoubledMatterSpinorVectorBundleCore
    period hPeriod choice).vectorBundle

local instance fiberIsTopologicalAddGroup (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    IsTopologicalAddGroup
      (D9DoubledMatterSpinorFiber period hPeriod choice base) := by
  change IsTopologicalAddGroup D9DoubledMatterFiber
  infer_instance

local instance fiberContinuousSMul (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    ContinuousSMul Real
      (D9DoubledMatterSpinorFiber period hPeriod choice base) := by
  change ContinuousSMul Real D9DoubledMatterFiber
  infer_instance

def d9DoubledMatterSpinorGlobalCovariantDerivativeAt
    (choice : NormalRootChoice)
    (spinorSection : ∀ base : ThroatBase period hPeriod,
      D9DoubledMatterSpinorFiber period hPeriod choice base)
    (base : ThroatBase period hPeriod) :
    TangentSpace throatCoverModelWithCorners base →L[Real]
      D9DoubledMatterSpinorFiber period hPeriod choice base := by
  let e := trivializationAt D9DoubledMatterFiber
    (D9DoubledMatterSpinorFiber period hPeriod choice) base
  let hb : base ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' base
  exact ((e.continuousLinearEquivAt Real base hb).symm :
      D9DoubledMatterFiber →L[Real]
        D9DoubledMatterSpinorFiber period hPeriod choice base).comp
    (mvfderiv throatCoverModelWithCorners
      (fun current : ThroatBase period hPeriod =>
        (e ⟨current, spinorSection current⟩).2) base)

theorem d9DoubledMatterSpinorGlobalCovariantDerivativeAt_isCovariant
    (choice : NormalRootChoice) :
    IsCovariantDerivativeOn D9DoubledMatterFiber
      (d9DoubledMatterSpinorGlobalCovariantDerivativeAt
        period hPeriod choice) := by
  constructor
  · intro first second base hFirst hSecond _
    let e := trivializationAt D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) base
    let hb : base ∈ e.baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' base
    let firstCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, first current⟩).2
    let secondCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, second current⟩).2
    let addCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, (first + second) current⟩).2
    have hFirstCoord : MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) firstCoord base :=
      (mdifferentiableAt_section throatCoverModelWithCorners first).mp hFirst
    have hSecondCoord : MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) secondCoord base :=
      (mdifferentiableAt_section throatCoverModelWithCorners second).mp hSecond
    have hEq : addCoord =ᶠ[nhds base] (firstCoord + secondCoord) := by
      filter_upwards [e.open_baseSet.mem_nhds hb] with current hCurrent
      exact (e.linear Real hCurrent).map_add (first current) (second current)
    have hDerivative :
        mvfderiv throatCoverModelWithCorners addCoord base =
          mvfderiv throatCoverModelWithCorners firstCoord base +
            mvfderiv throatCoverModelWithCorners secondCoord base := by
      unfold mvfderiv
      rw [hEq.mfderiv_eq]
      exact mfderiv_add hFirstCoord hSecondCoord
    change
      ((e.continuousLinearEquivAt Real base hb).symm :
          D9DoubledMatterFiber →L[Real]
            D9DoubledMatterSpinorFiber period hPeriod choice base).comp
          (mvfderiv throatCoverModelWithCorners addCoord base) = _
    rw [hDerivative]
    ext tangent
    simp [d9DoubledMatterSpinorGlobalCovariantDerivativeAt, e,
      firstCoord, secondCoord]
  · intro spinorSection scalar base hSection hScalar _
    let e := trivializationAt D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) base
    let hb : base ∈ e.baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' base
    let sectionCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, spinorSection current⟩).2
    let smulCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, (scalar • spinorSection) current⟩).2
    have hSectionCoord : MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) sectionCoord base :=
      (mdifferentiableAt_section throatCoverModelWithCorners spinorSection).mp
        hSection
    have hEq : smulCoord =ᶠ[nhds base] (scalar • sectionCoord) := by
      filter_upwards [e.open_baseSet.mem_nhds hb] with current hCurrent
      exact (e.linear Real hCurrent).map_smul
        (scalar current) (spinorSection current)
    have hDerivative :
        mvfderiv throatCoverModelWithCorners smulCoord base =
          scalar base •
              mvfderiv throatCoverModelWithCorners sectionCoord base +
            (mvfderiv throatCoverModelWithCorners scalar base).smulRight
              (sectionCoord base) := by
      unfold mvfderiv
      rw [hEq.mfderiv_eq]
      exact mvfderiv_smul hScalar hSectionCoord
    change
      ((e.continuousLinearEquivAt Real base hb).symm :
          D9DoubledMatterFiber →L[Real]
            D9DoubledMatterSpinorFiber period hPeriod choice base).comp
          (mvfderiv throatCoverModelWithCorners smulCoord base) = _
    rw [hDerivative]
    ext tangent
    simp [d9DoubledMatterSpinorGlobalCovariantDerivativeAt, e, hb,
      sectionCoord]

def d9DoubledMatterSpinorGlobalCovariantDerivative
    (choice : NormalRootChoice) :
    CovariantDerivative throatCoverModelWithCorners D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice) where
  toFun := d9DoubledMatterSpinorGlobalCovariantDerivativeAt
    period hPeriod choice
  isCovariantDerivativeOnUniv :=
    d9DoubledMatterSpinorGlobalCovariantDerivativeAt_isCovariant
      period hPeriod choice

structure ProgramPD9MatterSpinorDoubledGlobalCovariantDerivativeCertificate4D
    where
  choice : NormalRootChoice
  covariantDerivative :
    CovariantDerivative throatCoverModelWithCorners D9DoubledMatterFiber
      (D9DoubledMatterSpinorFiber period hPeriod choice)
  covariantDerivativeCanonical : covariantDerivative =
    d9DoubledMatterSpinorGlobalCovariantDerivative period hPeriod choice

def programPD9MatterSpinorDoubledGlobalCovariantDerivativeCertificate4D :
    ProgramPD9MatterSpinorDoubledGlobalCovariantDerivativeCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  covariantDerivative :=
    d9DoubledMatterSpinorGlobalCovariantDerivative
      period hPeriod .positiveQuarter
  covariantDerivativeCanonical := rfl

theorem programPD9MatterSpinorDoubledGlobalCovariantDerivativeCertificate4D_nonempty :
    Nonempty
      (ProgramPD9MatterSpinorDoubledGlobalCovariantDerivativeCertificate4D
        period hPeriod) :=
  ⟨programPD9MatterSpinorDoubledGlobalCovariantDerivativeCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledGlobalCovariantDerivative4D
end JanusFormal
