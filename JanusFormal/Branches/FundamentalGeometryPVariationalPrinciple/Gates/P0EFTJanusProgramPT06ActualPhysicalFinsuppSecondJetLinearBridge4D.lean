import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppSecondJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D

/-!
# Linear physical bridge for genuine spatial second jets

This gate upgrades the exact Gate877 reindexing to a linear equivalence and
composes it with the Gate874 eleven-component physical bridge.  The result
identifies the genuine order-two spatial jet of the complete value product
with the actual physical second-order jet product used by T02.

This is an identification of fixed model fibers.  No naturality under chart,
frame, deck or BRST transformations is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D

private abbrev RawLLSecondOrderJetFiber :=
  ((FramedSecondOrderJet ThroatCoverCoordinates LLMetricFiber ×
      FramedSecondOrderJet ThroatCoverCoordinates Real) ×
    FramedSecondOrderJet ThroatCoverCoordinates LLFieldFiber)

local instance actualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  inferInstanceAs (NormedAddCommGroup RawLLSecondOrderJetFiber)

local instance actualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  inferInstanceAs (NormedSpace Real RawLLSecondOrderJetFiber)

private abbrev RawActualPhysicalValueProductFiber :=
  ((ActualGaugeValueProductFiber × ActualLLValueProductFiber) ×
      ActualMetricValueProductFiber) × ActualSpinCValueProductFiber

local instance actualPhysicalValueProductNormedAddCommGroup :
    NormedAddCommGroup ActualPhysicalValueProductFiber :=
  inferInstanceAs (NormedAddCommGroup RawActualPhysicalValueProductFiber)

local instance actualPhysicalValueProductNormedSpace :
    NormedSpace Real ActualPhysicalValueProductFiber :=
  inferInstanceAs (NormedSpace Real RawActualPhysicalValueProductFiber)

universe v

private abbrev SpatialJet (Fiber : Type*) :=
  ThroatSpatialMultiindexSecondJet Fiber

private abbrev GaugeLLSpatialJetProduct :=
  SpatialJet ActualGaugeValueProductFiber ×
    SpatialJet ActualLLValueProductFiber

private abbrev GaugeLLMetricSpatialJetProduct :=
  GaugeLLSpatialJetProduct × SpatialJet ActualMetricValueProductFiber

private abbrev PhysicalSectorSpatialJetProduct :=
  GaugeLLMetricSpatialJetProduct × SpatialJet ActualSpinCValueProductFiber

private abbrev GaugeLLComponentSpatialJetProduct :=
  ActualGaugeSpatialSecondJetProductFiber ×
    ActualLLSpatialSecondJetProductFiber

private abbrev GaugeLLMetricComponentSpatialJetProduct :=
  GaugeLLComponentSpatialJetProduct ×
    ActualMetricSpatialSecondJetProductFiber

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

local instance gaugeLLComponentSpatialJetProductModule :
    Module Real GaugeLLComponentSpatialJetProduct :=
  Prod.instModule

local instance gaugeLLMetricComponentSpatialJetProductModule :
    Module Real GaugeLLMetricComponentSpatialJetProduct :=
  Prod.instModule

local instance actualPhysicalSpatialSecondJetProductAddCommMonoid :
    AddCommMonoid ActualPhysicalSpatialSecondJetProductFiber :=
  Prod.instAddCommMonoid

local instance actualPhysicalSpatialSecondJetProductModule :
    Module Real ActualPhysicalSpatialSecondJetProductFiber :=
  Prod.instModule

/-- Gate877 reindexing is linear for every real module fiber. -/
noncomputable def throatSpatialFinsuppSecondJetLinearEquiv
    (Fiber : Type v) [AddCommMonoid Fiber] [Module Real Fiber] :
    ThroatSpatialMultiindexJet2 Fiber ≃ₗ[Real]
      ThroatSpatialMultiindexSecondJet Fiber where
  toEquiv := throatSpatialFinsuppSecondJetEquiv Fiber
  map_add' first second := by
    funext index
    rfl
  map_smul' scalar jet := by
    funext index
    rfl

private def gaugeSpatialSplitLinearEquiv :
    SpatialJet ActualGaugeValueProductFiber ≃ₗ[Real]
      ActualGaugeSpatialSecondJetProductFiber :=
  (programPT06ThroatSpatialSecondJetProdLinearEquiv
      (First := ActualGaugeValueFiber × ActualGaugeValueFiber)
      (Second := ActualGaugeValueFiber × ActualGaugeValueFiber)).trans
    ((programPT06ThroatSpatialSecondJetProdLinearEquiv
        (First := ActualGaugeValueFiber)
        (Second := ActualGaugeValueFiber)).prodCongr
      (programPT06ThroatSpatialSecondJetProdLinearEquiv
        (First := ActualGaugeValueFiber)
        (Second := ActualGaugeValueFiber)))

private def llSpatialSplitLinearEquiv :
    SpatialJet ActualLLValueProductFiber ≃ₗ[Real]
      ActualLLSpatialSecondJetProductFiber :=
  (programPT06ThroatSpatialSecondJetProdLinearEquiv
      (First := LLMetricFiber × Real) (Second := LLFieldFiber)).trans
    ((programPT06ThroatSpatialSecondJetProdLinearEquiv
        (First := LLMetricFiber) (Second := Real)).prodCongr
      (LinearEquiv.refl Real (SpatialJet LLFieldFiber)))

private def metricSpatialSplitLinearEquiv :
    SpatialJet ActualMetricValueProductFiber ≃ₗ[Real]
      ActualMetricSpatialSecondJetProductFiber :=
  programPT06ThroatSpatialSecondJetProdLinearEquiv
    (First := ActualMetricValueFiber) (Second := ActualMetricValueFiber)

private def spinCSpatialSplitLinearEquiv :
    SpatialJet ActualSpinCValueProductFiber ≃ₗ[Real]
      ActualSpinCSpatialSecondJetProductFiber :=
  programPT06ThroatSpatialSecondJetProdLinearEquiv
    (First := D9DoubledMatterFiber) (Second := D9DoubledMatterFiber)

private def physicalSectorSpatialSplitLinearEquiv :
    SpatialJet ActualPhysicalValueProductFiber ≃ₗ[Real]
      PhysicalSectorSpatialJetProduct :=
  (programPT06ThroatSpatialSecondJetProdLinearEquiv
      (First :=
        (ActualGaugeValueProductFiber × ActualLLValueProductFiber) ×
          ActualMetricValueProductFiber)
      (Second := ActualSpinCValueProductFiber)).trans
    (((programPT06ThroatSpatialSecondJetProdLinearEquiv
        (First := ActualGaugeValueProductFiber × ActualLLValueProductFiber)
        (Second := ActualMetricValueProductFiber)).trans
      ((programPT06ThroatSpatialSecondJetProdLinearEquiv
          (First := ActualGaugeValueProductFiber)
          (Second := ActualLLValueProductFiber)).prodCongr
        (LinearEquiv.refl Real
          (SpatialJet ActualMetricValueProductFiber)))).prodCongr
      (LinearEquiv.refl Real
        (SpatialJet ActualSpinCValueProductFiber)))

private def physicalSpatialSplitLinearEquiv :
    SpatialJet ActualPhysicalValueProductFiber ≃ₗ[Real]
      ActualPhysicalSpatialSecondJetProductFiber :=
  physicalSectorSpatialSplitLinearEquiv.trans
    (((gaugeSpatialSplitLinearEquiv.prodCongr
      llSpatialSplitLinearEquiv).prodCongr
      metricSpatialSplitLinearEquiv).prodCongr
      spinCSpatialSplitLinearEquiv)

private def gaugeSpatialFramedLinearEquiv :
    ActualGaugeSpatialSecondJetProductFiber ≃ₗ[Real]
      ActualGaugeSecondOrderJetProductFiber :=
  ((programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)).prodCongr
    (programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber))).prodCongr
  ((programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)).prodCongr
    (programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)))

private def llSpatialFramedLinearEquiv :
    ActualLLSpatialSecondJetProductFiber ≃ₗ[Real]
      ActualLLSecondOrderJetFiber :=
  ((programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := LLMetricFiber)).prodCongr
    (programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := Real))).prodCongr
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := LLFieldFiber))

private def metricSpatialFramedLinearEquiv :
    ActualMetricSpatialSecondJetProductFiber ≃ₗ[Real]
      ActualMetricSecondOrderJetProductFiber :=
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := ActualMetricValueFiber)).prodCongr
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := ActualMetricValueFiber))

private def spinCSpatialFramedLinearEquiv :
    ActualSpinCSpatialSecondJetProductFiber ≃ₗ[Real]
      ActualSpinCSecondOrderJetProductFiber :=
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := D9DoubledMatterFiber)).prodCongr
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := D9DoubledMatterFiber))

private def physicalSpatialFramedLinearEquiv :
    ActualPhysicalSpatialSecondJetProductFiber ≃ₗ[Real]
      ActualPhysicalSecondOrderJetProductFiber :=
  (((gaugeSpatialFramedLinearEquiv.prodCongr
      llSpatialFramedLinearEquiv).prodCongr
    metricSpatialFramedLinearEquiv).prodCongr
  spinCSpatialFramedLinearEquiv)

/-- Linear form of Gate874's assembled componentwise second-jet bridge. -/
noncomputable def programPT06ActualPhysicalValueProductSecondJetLinearEquiv :
    ThroatSpatialMultiindexSecondJet ActualPhysicalValueProductFiber ≃ₗ[Real]
      ActualPhysicalSecondOrderJetProductFiber :=
  physicalSpatialSplitLinearEquiv.trans physicalSpatialFramedLinearEquiv

/-- Linear identification of the genuine physical value-product second jet
with the assembled T02 physical second-jet product. -/
noncomputable def programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv :
    ThroatSpatialMultiindexJet2 ActualPhysicalValueProductFiber ≃ₗ[Real]
      ActualPhysicalSecondOrderJetProductFiber :=
  (throatSpatialFinsuppSecondJetLinearEquiv
      ActualPhysicalValueProductFiber).trans
    programPT06ActualPhysicalValueProductSecondJetLinearEquiv

local instance actualPhysicalSecondOrderJetProductFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

local instance actualPhysicalValueProductFinsuppSecondJetFiniteDimensional :
    FiniteDimensional Real
      (ThroatSpatialMultiindexJet2 ActualPhysicalValueProductFiber) :=
  FiniteDimensional.of_injective
    programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv.toLinearMap
    programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv.injective

/-- Continuous form of the physical linear bridge.  Continuity follows from
finite dimensionality of the genuine order-two source jet. -/
noncomputable def programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv :
    ThroatSpatialMultiindexJet2 ActualPhysicalValueProductFiber ≃L[Real]
      ActualPhysicalSecondOrderJetProductFiber :=
  programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv.toContinuousLinearEquiv

end
end P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
end JanusFormal
