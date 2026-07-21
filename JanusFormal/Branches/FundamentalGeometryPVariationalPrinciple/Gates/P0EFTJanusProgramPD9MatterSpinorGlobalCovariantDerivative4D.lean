import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D

/-!
# Global covariant derivative on the smooth D9 spinor bundle

A preferred local trivialization at each base point packages the ordinary
coordinate derivative as a genuine Mathlib `CovariantDerivative`.  Its
regularity and its identification with the flat cover derivative remain open.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorGlobalCovariantDerivative4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Bundle
open Bundle Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
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
    (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ω :=
  smoothThroatMatterSpinorVectorBundleCore_isContMDiff period hPeriod choice

local instance totalSpaceTopology (choice : NormalRootChoice) :
    TopologicalSpace (Bundle.TotalSpace MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice)) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).toTopologicalSpace

local instance fiberBundle (choice : NormalRootChoice) :
    FiberBundle MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).fiberBundle

local instance vectorBundle (choice : NormalRootChoice) :
    VectorBundle Real MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) :=
  (smoothThroatMatterSpinorVectorBundleCore period hPeriod choice).vectorBundle

local instance fiberIsTopologicalAddGroup (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    IsTopologicalAddGroup
      (SmoothThroatMatterSpinorFiber period hPeriod choice base) := by
  change IsTopologicalAddGroup MatterFiber
  infer_instance

local instance fiberContinuousSMul (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    ContinuousSMul Real
      (SmoothThroatMatterSpinorFiber period hPeriod choice base) := by
  change ContinuousSMul Real MatterFiber
  infer_instance

def d9MatterSpinorGlobalCovariantDerivativeAt
    (choice : NormalRootChoice)
    (spinorSection : ∀ base : ThroatBase period hPeriod,
      SmoothThroatMatterSpinorFiber period hPeriod choice base)
    (base : ThroatBase period hPeriod) :
    TangentSpace throatCoverModelWithCorners base →L[Real]
      SmoothThroatMatterSpinorFiber period hPeriod choice base := by
  let e := trivializationAt MatterFiber
    (SmoothThroatMatterSpinorFiber period hPeriod choice) base
  let hb : base ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' base
  exact ((e.continuousLinearEquivAt Real base hb).symm :
      MatterFiber →L[Real]
        SmoothThroatMatterSpinorFiber period hPeriod choice base).comp
    (mvfderiv throatCoverModelWithCorners
      (fun current : ThroatBase period hPeriod =>
        (e ⟨current, spinorSection current⟩).2) base)

theorem d9MatterSpinorGlobalCovariantDerivativeAt_isCovariant
    (choice : NormalRootChoice) :
    IsCovariantDerivativeOn MatterFiber
      (d9MatterSpinorGlobalCovariantDerivativeAt period hPeriod choice) := by
  constructor
  · intro first second base hFirst hSecond _
    let e := trivializationAt MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) base
    let hb : base ∈ e.baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' base
    let firstCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, first current⟩).2
    let secondCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, second current⟩).2
    let addCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, (first + second) current⟩).2
    have hFirstCoord : MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) firstCoord base :=
      (mdifferentiableAt_section throatCoverModelWithCorners first).mp hFirst
    have hSecondCoord : MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) secondCoord base :=
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
          MatterFiber →L[Real]
            SmoothThroatMatterSpinorFiber period hPeriod choice base).comp
          (mvfderiv throatCoverModelWithCorners addCoord base) = _
    rw [hDerivative]
    ext tangent
    simp [d9MatterSpinorGlobalCovariantDerivativeAt, e,
      firstCoord, secondCoord]
  · intro spinorSection scalar base hSection hScalar _
    let e := trivializationAt MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) base
    let hb : base ∈ e.baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' base
    let sectionCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, spinorSection current⟩).2
    let smulCoord := fun current : ThroatBase period hPeriod =>
      (e ⟨current, (scalar • spinorSection) current⟩).2
    have hSectionCoord : MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, MatterFiber) sectionCoord base :=
      (mdifferentiableAt_section throatCoverModelWithCorners spinorSection).mp
        hSection
    have hEq : smulCoord =ᶠ[nhds base] (scalar • sectionCoord) := by
      filter_upwards [e.open_baseSet.mem_nhds hb] with current hCurrent
      exact (e.linear Real hCurrent).map_smul
        (scalar current) (spinorSection current)
    have hDerivative :
        mvfderiv throatCoverModelWithCorners smulCoord base =
          scalar base • mvfderiv throatCoverModelWithCorners sectionCoord base +
            (mvfderiv throatCoverModelWithCorners scalar base).smulRight
              (sectionCoord base) := by
      unfold mvfderiv
      rw [hEq.mfderiv_eq]
      exact mvfderiv_smul hScalar hSectionCoord
    change
      ((e.continuousLinearEquivAt Real base hb).symm :
          MatterFiber →L[Real]
            SmoothThroatMatterSpinorFiber period hPeriod choice base).comp
          (mvfderiv throatCoverModelWithCorners smulCoord base) = _
    rw [hDerivative]
    ext tangent
    simp [d9MatterSpinorGlobalCovariantDerivativeAt, e, hb, sectionCoord]

def d9MatterSpinorGlobalCovariantDerivative
    (choice : NormalRootChoice) :
    CovariantDerivative throatCoverModelWithCorners MatterFiber
      (SmoothThroatMatterSpinorFiber period hPeriod choice) where
  toFun := d9MatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
  isCovariantDerivativeOnUniv :=
    d9MatterSpinorGlobalCovariantDerivativeAt_isCovariant
      period hPeriod choice

structure ProgramPD9MatterSpinorGlobalCovariantDerivativeCertificate4D where
  choice : NormalRootChoice
  covariantDerivative : CovariantDerivative throatCoverModelWithCorners
    MatterFiber (SmoothThroatMatterSpinorFiber period hPeriod choice)
  covariantDerivativeCanonical : covariantDerivative =
    d9MatterSpinorGlobalCovariantDerivative period hPeriod choice

def programPD9MatterSpinorGlobalCovariantDerivativeCertificate4D :
    ProgramPD9MatterSpinorGlobalCovariantDerivativeCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  covariantDerivative :=
    d9MatterSpinorGlobalCovariantDerivative period hPeriod .positiveQuarter
  covariantDerivativeCanonical := rfl

theorem programPD9MatterSpinorGlobalCovariantDerivativeCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorGlobalCovariantDerivativeCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorGlobalCovariantDerivativeCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorGlobalCovariantDerivative4D
end JanusFormal
