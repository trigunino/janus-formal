import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D

/-!
# Smooth section core of the primitive D9 SpinC bundle

This gate exposes the genuine `C∞` section module of the charge-one SpinC
bundle constructed on the quotient throat.  It does not choose a
trivialization and therefore remains valid for the nontrivial monopole
clutching.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Fiber of the primitive SpinC bundle over one D9 point. -/
abbrev D9PrimitiveSpinCFiber
    (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).Fiber base

local instance primitiveSpinCCoreIsContMDiff
    (choice : NormalRootChoice) :
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ∞ :=
  d9PrimitiveSpinCVectorBundleCore_isContMDiff
    period hPeriod choice

local instance primitiveSpinCTotalSpaceTopology
    (choice : NormalRootChoice) :
    TopologicalSpace
      (Bundle.TotalSpace D9DoubledMatterFiber
        (D9PrimitiveSpinCFiber period hPeriod choice)) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).toTopologicalSpace

local instance primitiveSpinCFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle D9DoubledMatterFiber
      (D9PrimitiveSpinCFiber period hPeriod choice) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).fiberBundle

local instance primitiveSpinCVectorBundle
    (choice : NormalRootChoice) :
    VectorBundle Real D9DoubledMatterFiber
      (D9PrimitiveSpinCFiber period hPeriod choice) :=
  (d9PrimitiveSpinCVectorBundleCore
    period hPeriod choice).vectorBundle

/-- Genuine smooth sections of the nontrivial primitive SpinC bundle. -/
abbrev D9PrimitiveSpinCSmoothSection
    (choice : NormalRootChoice) :=
  ContMDiffSection throatCoverModelWithCorners
    D9DoubledMatterFiber ∞
      (D9PrimitiveSpinCFiber period hPeriod choice)

/-- The section core is nonempty without selecting a gauge. -/
def d9PrimitiveSpinCZeroSection
    (choice : NormalRootChoice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  0

@[simp]
theorem d9PrimitiveSpinCZeroSection_apply
    (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCZeroSection period hPeriod choice base = 0 :=
  rfl

/-- Evaluation at one D9 point is a real-linear map on the smooth core. -/
def d9PrimitiveSpinCSectionEvaluation
    (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice →ₗ[Real]
      D9PrimitiveSpinCFiber period hPeriod choice base where
  toFun state := state base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem d9PrimitiveSpinCSectionEvaluation_apply
    (choice : NormalRootChoice)
    (base : ThroatBase period hPeriod)
    (state : D9PrimitiveSpinCSmoothSection
      period hPeriod choice) :
    d9PrimitiveSpinCSectionEvaluation
        period hPeriod choice base state =
      state base :=
  rfl

/-- Assumption-free certificate for the geometric smooth section core. -/
structure ProgramPD9PrimitiveSpinCSmoothSectionCoreCertificate4D where
  choice : NormalRootChoice
  core :
    Type
  core_eq :
    core =
      D9PrimitiveSpinCSmoothSection period hPeriod choice
  coreNonempty : Nonempty core

def programPD9PrimitiveSpinCSmoothSectionCoreCertificate4D :
    ProgramPD9PrimitiveSpinCSmoothSectionCoreCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  core :=
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter
  core_eq := rfl
  coreNonempty :=
    ⟨d9PrimitiveSpinCZeroSection
      period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
end JanusFormal
