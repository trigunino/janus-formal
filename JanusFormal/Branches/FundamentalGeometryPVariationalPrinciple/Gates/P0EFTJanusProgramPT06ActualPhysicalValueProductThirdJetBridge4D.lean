import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppThirdJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D

/-!
# Actual physical value-product third-jet bridge

The genuine spatial multi-index third jet of the complete physical value
fiber is distributed over its eleven components and identified componentwise
with the corresponding framed third jets.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualLLThirdOrderJetProductCoordChange4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetCoordChange4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppThirdJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

attribute [local instance 1001]
  AddCommGroup.toAddCommMonoid

local instance actualMetricValueNormedAddCommGroup :
    NormedAddCommGroup ActualMetricValueFiber :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance actualMetricValueNormedSpace :
    NormedSpace Real ActualMetricValueFiber :=
  ContinuousLinearMap.toNormedSpace

local instance actualMetricValueFiniteDimensional :
    FiniteDimensional Real ActualMetricValueFiber :=
  ContinuousLinearMap.finiteDimensional

private abbrev RawActualPhysicalValueProductFiber :=
  ((ActualGaugeValueProductFiber × ActualLLValueProductFiber) ×
      ActualMetricValueProductFiber) × ActualSpinCValueProductFiber

local instance actualPhysicalValueProductNormedAddCommGroup :
    NormedAddCommGroup ActualPhysicalValueProductFiber :=
  inferInstanceAs (NormedAddCommGroup RawActualPhysicalValueProductFiber)

local instance actualPhysicalValueProductNormedSpace :
    NormedSpace Real ActualPhysicalValueProductFiber :=
  inferInstanceAs (NormedSpace Real RawActualPhysicalValueProductFiber)

/-- A third jet of a product is exactly a pair of third jets, coefficient by
coefficient. -/
def programPT06ThroatSpatialThirdJetProdLinearEquiv
    {First Second : Type*}
    [AddCommMonoid First] [Module Real First]
    [AddCommMonoid Second] [Module Real Second] :
    ThroatSpatialMultiindexJet3 (First × Second) ≃ₗ[Real]
      ThroatSpatialMultiindexJet3 First ×
        ThroatSpatialMultiindexJet3 Second where
  toFun jet :=
    (fun index ↦ (jet index).1, fun index ↦ (jet index).2)
  invFun jets index := (jets.1 index, jets.2 index)
  left_inv jet := by
    funext index
    rfl
  right_inv jets := by
    apply Prod.ext
    · funext index
      rfl
    · funext index
      rfl
  map_add' first second := by
    apply Prod.ext
    · funext index
      rfl
    · funext index
      rfl
  map_smul' scalar jet := by
    apply Prod.ext
    · funext index
      rfl
    · funext index
      rfl

private abbrev SpatialJet (Fiber : Type*) :=
  ThroatSpatialMultiindexJet3 Fiber

/-- Four gauge spatial third jets. -/
abbrev ActualGaugeSpatialThirdJetProductFiber :=
  (SpatialJet ActualGaugeValueFiber × SpatialJet ActualGaugeValueFiber) ×
    (SpatialJet ActualGaugeValueFiber × SpatialJet ActualGaugeValueFiber)

/-- Three LL spatial third jets. -/
abbrev ActualLLSpatialThirdJetProductFiber :=
  (SpatialJet LLMetricFiber × SpatialJet Real) ×
    SpatialJet LLFieldFiber

/-- Two metric spatial third jets. -/
abbrev ActualMetricSpatialThirdJetProductFiber :=
  SpatialJet ActualMetricValueFiber × SpatialJet ActualMetricValueFiber

/-- Two doubled SpinC spatial third jets. -/
abbrev ActualSpinCSpatialThirdJetProductFiber :=
  SpatialJet D9DoubledMatterFiber × SpatialJet D9DoubledMatterFiber

/-- The exact physical nesting after distributing over all eleven value
components. -/
abbrev ActualPhysicalSpatialThirdJetProductFiber :=
  PhysicalSecondJetFiber
    (GaugeFiber := ActualGaugeSpatialThirdJetProductFiber)
    (LLFiber := ActualLLSpatialThirdJetProductFiber)
    (MetricFiber := ActualMetricSpatialThirdJetProductFiber)
    (SpinCFiber := ActualSpinCSpatialThirdJetProductFiber)

private abbrev GaugeLLSpatialJetProduct :=
  SpatialJet ActualGaugeValueProductFiber ×
    SpatialJet ActualLLValueProductFiber

private abbrev GaugeLLMetricSpatialJetProduct :=
  GaugeLLSpatialJetProduct × SpatialJet ActualMetricValueProductFiber

private abbrev PhysicalSectorSpatialJetProduct :=
  GaugeLLMetricSpatialJetProduct ×
    SpatialJet ActualSpinCValueProductFiber

local instance actualMetricValueProductModule :
    Module Real ActualMetricValueProductFiber :=
  Prod.instModule

local instance gaugeLLSpatialJetProductModule :
    Module Real GaugeLLSpatialJetProduct :=
  Prod.instModule

local instance gaugeLLMetricSpatialJetProductModule :
    Module Real GaugeLLMetricSpatialJetProduct :=
  Prod.instModule

local instance physicalSectorSpatialJetProductAddCommMonoid :
    AddCommMonoid PhysicalSectorSpatialJetProduct :=
  Prod.instAddCommMonoid

local instance physicalSectorSpatialJetProductModule :
    Module Real PhysicalSectorSpatialJetProduct :=
  Prod.instModule

local instance actualMetricSpatialThirdJetProductModule :
    Module Real ActualMetricSpatialThirdJetProductFiber :=
  Prod.instModule

local instance actualPhysicalSpatialThirdJetProductAddCommMonoid :
    AddCommMonoid ActualPhysicalSpatialThirdJetProductFiber :=
  Prod.instAddCommMonoid

local instance actualPhysicalSpatialThirdJetProductModule :
    Module Real ActualPhysicalSpatialThirdJetProductFiber :=
  Prod.instModule

private def gaugeSpatialSplitLinearEquiv :
    SpatialJet ActualGaugeValueProductFiber ≃ₗ[Real]
      ActualGaugeSpatialThirdJetProductFiber :=
  (programPT06ThroatSpatialThirdJetProdLinearEquiv
      (First := ActualGaugeValueFiber × ActualGaugeValueFiber)
      (Second := ActualGaugeValueFiber × ActualGaugeValueFiber)).trans
    ((programPT06ThroatSpatialThirdJetProdLinearEquiv
        (First := ActualGaugeValueFiber)
        (Second := ActualGaugeValueFiber)).prodCongr
      (programPT06ThroatSpatialThirdJetProdLinearEquiv
        (First := ActualGaugeValueFiber)
        (Second := ActualGaugeValueFiber)))

private def llSpatialSplitLinearEquiv :
    SpatialJet ActualLLValueProductFiber ≃ₗ[Real]
      ActualLLSpatialThirdJetProductFiber :=
  (programPT06ThroatSpatialThirdJetProdLinearEquiv
      (First := LLMetricFiber × Real) (Second := LLFieldFiber)).trans
    ((programPT06ThroatSpatialThirdJetProdLinearEquiv
        (First := LLMetricFiber) (Second := Real)).prodCongr
      (LinearEquiv.refl Real (SpatialJet LLFieldFiber)))

private def metricSpatialSplitLinearEquiv :
    SpatialJet ActualMetricValueProductFiber ≃ₗ[Real]
      ActualMetricSpatialThirdJetProductFiber :=
  programPT06ThroatSpatialThirdJetProdLinearEquiv
    (First := ActualMetricValueFiber) (Second := ActualMetricValueFiber)

private def spinCSpatialSplitLinearEquiv :
    SpatialJet ActualSpinCValueProductFiber ≃ₗ[Real]
      ActualSpinCSpatialThirdJetProductFiber :=
  programPT06ThroatSpatialThirdJetProdLinearEquiv
    (First := D9DoubledMatterFiber) (Second := D9DoubledMatterFiber)

private def physicalSectorSpatialSplitLinearEquiv :
    SpatialJet ActualPhysicalValueProductFiber ≃ₗ[Real]
      PhysicalSectorSpatialJetProduct :=
  (programPT06ThroatSpatialThirdJetProdLinearEquiv
      (First :=
        (ActualGaugeValueProductFiber × ActualLLValueProductFiber) ×
          ActualMetricValueProductFiber)
      (Second := ActualSpinCValueProductFiber)).trans
    (((programPT06ThroatSpatialThirdJetProdLinearEquiv
        (First := ActualGaugeValueProductFiber × ActualLLValueProductFiber)
        (Second := ActualMetricValueProductFiber)).trans
      ((programPT06ThroatSpatialThirdJetProdLinearEquiv
          (First := ActualGaugeValueProductFiber)
          (Second := ActualLLValueProductFiber)).prodCongr
        (LinearEquiv.refl Real
          (SpatialJet ActualMetricValueProductFiber)))).prodCongr
      (LinearEquiv.refl Real
        (SpatialJet ActualSpinCValueProductFiber)))

/-- Linear distribution of one spatial J3 value-product jet into the exact
product of eleven component spatial jets. -/
def programPT06ActualPhysicalValueProductSpatialThirdJetSplitLinearEquiv :
    SpatialJet ActualPhysicalValueProductFiber ≃ₗ[Real]
      ActualPhysicalSpatialThirdJetProductFiber :=
  physicalSectorSpatialSplitLinearEquiv.trans
    (((gaugeSpatialSplitLinearEquiv.prodCongr
      llSpatialSplitLinearEquiv).prodCongr
      metricSpatialSplitLinearEquiv).prodCongr
      spinCSpatialSplitLinearEquiv)

private def gaugeSpatialFramedLinearEquiv :
    ActualGaugeSpatialThirdJetProductFiber ≃ₗ[Real]
      ActualGaugeThirdOrderJetProductFiber :=
  ((programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)).prodCongr
    (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber))).prodCongr
  ((programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)).prodCongr
    (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)))

private def llSpatialFramedLinearEquiv :
    ActualLLSpatialThirdJetProductFiber ≃ₗ[Real]
      ActualLLThirdOrderJetFiber :=
  ((programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
      (Fiber := LLMetricFiber)).prodCongr
    (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
      (Fiber := Real))).prodCongr
  (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
    (Fiber := LLFieldFiber))

private def metricSpatialFramedLinearEquiv :
    ActualMetricSpatialThirdJetProductFiber ≃ₗ[Real]
      ActualMetricThirdOrderJetProductFiber :=
  (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
    (Fiber := ActualMetricValueFiber)).prodCongr
  (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
    (Fiber := ActualMetricValueFiber))

private def spinCSpatialFramedLinearEquiv :
    ActualSpinCSpatialThirdJetProductFiber ≃ₗ[Real]
      ActualSpinCThirdOrderJetProductFiber :=
  (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
    (Fiber := D9DoubledMatterFiber)).prodCongr
  (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
    (Fiber := D9DoubledMatterFiber))

/-- Componentwise Gate959 equivalence from the eleven spatial third jets to
the actual physical product of framed third jets. -/
def programPT06ActualPhysicalSpatialThirdJetProductFramedLinearEquiv :
    ActualPhysicalSpatialThirdJetProductFiber ≃ₗ[Real]
      ActualPhysicalThirdOrderJetProductFiber :=
  (((gaugeSpatialFramedLinearEquiv.prodCongr
      llSpatialFramedLinearEquiv).prodCongr
    metricSpatialFramedLinearEquiv).prodCongr
  spinCSpatialFramedLinearEquiv)

/-- Exact linear identification of the spatial J3 jet of the complete value
product with the product of all eleven actual framed third jets. -/
def programPT06ActualPhysicalValueProductThirdJetLinearEquiv :
    ThroatSpatialMultiindexJet3 ActualPhysicalValueProductFiber ≃ₗ[Real]
      ActualPhysicalThirdOrderJetProductFiber :=
  programPT06ActualPhysicalValueProductSpatialThirdJetSplitLinearEquiv.trans
    programPT06ActualPhysicalSpatialThirdJetProductFramedLinearEquiv

/-! ## Truncation -/

private def gaugeThirdOrderJetProductTruncate :
    ActualGaugeThirdOrderJetProductFiber →ₗ[Real]
      ActualGaugeSecondOrderJetProductFiber :=
  ((framedThirdOrderJetTruncateLinearMap
      (Base := ThroatCoverCoordinates)
      (Fiber := ActualGaugeValueFiber)).prodMap
    (framedThirdOrderJetTruncateLinearMap
      (Base := ThroatCoverCoordinates)
      (Fiber := ActualGaugeValueFiber))).prodMap
  ((framedThirdOrderJetTruncateLinearMap
      (Base := ThroatCoverCoordinates)
      (Fiber := ActualGaugeValueFiber)).prodMap
    (framedThirdOrderJetTruncateLinearMap
      (Base := ThroatCoverCoordinates)
      (Fiber := ActualGaugeValueFiber)))

private def metricThirdOrderJetProductTruncate :
    ActualMetricThirdOrderJetProductFiber →ₗ[Real]
      ActualMetricSecondOrderJetProductFiber :=
  (framedThirdOrderJetTruncateLinearMap
    (Base := ThroatCoverCoordinates)
    (Fiber := ActualMetricValueFiber)).prodMap
  (framedThirdOrderJetTruncateLinearMap
    (Base := ThroatCoverCoordinates)
    (Fiber := ActualMetricValueFiber))

private def spinCThirdOrderJetProductTruncate :
    ActualSpinCThirdOrderJetProductFiber →ₗ[Real]
      ActualSpinCSecondOrderJetProductFiber :=
  (framedThirdOrderJetTruncateLinearMap
    (Base := ThroatCoverCoordinates)
    (Fiber := D9DoubledMatterFiber)).prodMap
  (framedThirdOrderJetTruncateLinearMap
    (Base := ThroatCoverCoordinates)
    (Fiber := D9DoubledMatterFiber))

/-- Componentwise truncation from the eleven framed third jets to the exact
physical second-jet product. -/
def programPT06ActualPhysicalThirdOrderJetProductTruncate :
    ActualPhysicalThirdOrderJetProductFiber →ₗ[Real]
      ActualPhysicalSecondOrderJetProductFiber :=
  (((gaugeThirdOrderJetProductTruncate.prodMap
      actualLLThirdOrderJetProductTruncate).prodMap
    metricThirdOrderJetProductTruncate).prodMap
  spinCThirdOrderJetProductTruncate)

private abbrev RawLLThirdOrderJetFiber :=
  ((FramedThirdOrderJet ThroatCoverCoordinates LLMetricFiber ×
      FramedThirdOrderJet ThroatCoverCoordinates Real) ×
    FramedThirdOrderJet ThroatCoverCoordinates LLFieldFiber)

local instance actualLLThirdOrderJetNormedAddCommGroup :
    NormedAddCommGroup ActualLLThirdOrderJetFiber :=
  inferInstanceAs (NormedAddCommGroup RawLLThirdOrderJetFiber)

local instance actualLLThirdOrderJetNormedSpace :
    NormedSpace Real ActualLLThirdOrderJetFiber :=
  inferInstanceAs (NormedSpace Real RawLLThirdOrderJetFiber)

local instance actualLLThirdOrderJetFiniteDimensional :
    FiniteDimensional Real ActualLLThirdOrderJetFiber :=
  inferInstanceAs (FiniteDimensional Real RawLLThirdOrderJetFiber)

private abbrev RawActualPhysicalThirdOrderJetProductFiber :=
  ((ActualGaugeThirdOrderJetProductFiber × ActualLLThirdOrderJetFiber) ×
      ActualMetricThirdOrderJetProductFiber) ×
    ActualSpinCThirdOrderJetProductFiber

local instance actualPhysicalThirdOrderJetProductNormedAddCommGroup :
    NormedAddCommGroup ActualPhysicalThirdOrderJetProductFiber :=
  inferInstanceAs
    (NormedAddCommGroup RawActualPhysicalThirdOrderJetProductFiber)

local instance actualPhysicalThirdOrderJetProductNormedSpace :
    NormedSpace Real ActualPhysicalThirdOrderJetProductFiber :=
  inferInstanceAs (NormedSpace Real RawActualPhysicalThirdOrderJetProductFiber)

local instance actualPhysicalValueProductFiniteDimensional :
    FiniteDimensional Real ActualPhysicalValueProductFiber :=
  inferInstanceAs
    (FiniteDimensional Real RawActualPhysicalValueProductFiber)

local instance actualPhysicalValueProductSpatialThirdJetContinuousSMul :
    ContinuousSMul Real
      (ThroatSpatialMultiindexJet3 ActualPhysicalValueProductFiber) :=
  IsBoundedSMul.continuousSMul

local instance actualPhysicalValueProductSpatialThirdJetFiniteDimensional :
    FiniteDimensional Real
      (ThroatSpatialMultiindexJet3 ActualPhysicalValueProductFiber) :=
  inferInstance

local instance actualPhysicalThirdOrderJetProductFiniteDimensional :
    FiniteDimensional Real ActualPhysicalThirdOrderJetProductFiber :=
  FiniteDimensional.of_injective
    programPT06ActualPhysicalValueProductThirdJetLinearEquiv.symm.toLinearMap
    programPT06ActualPhysicalValueProductThirdJetLinearEquiv.symm.injective

/-- Continuous-linear form of the complete physical J3 carrier bridge. -/
def programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv :
    ThroatSpatialMultiindexJet3 ActualPhysicalValueProductFiber ≃L[Real]
      ActualPhysicalThirdOrderJetProductFiber :=
  programPT06ActualPhysicalValueProductThirdJetLinearEquiv.toContinuousLinearEquiv

end
end P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
end JanusFormal
