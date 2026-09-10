import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D

/-!
# Actual physical value-product second-jet bridge

This gate distributes the throat spatial second-jet carrier over the exact
eleven-component physical value product and then applies the componentwise
Gate870 equivalence to the framed second jets used by T02.

It is an exact model-fiber equivalence assembled from componentwise linear
identifications.  It does not assert naturality under changes of throat frame
or identify the corresponding bundle transition maps.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore

/-- A second jet of a product is exactly a pair of second jets, coefficient by
coefficient. -/
def programPT06ThroatSpatialSecondJetProdLinearEquiv
    {First Second : Type*}
    [AddCommMonoid First] [Module Real First]
    [AddCommMonoid Second] [Module Real Second] :
    ThroatSpatialMultiindexSecondJet (First × Second) ≃ₗ[Real]
      ThroatSpatialMultiindexSecondJet First ×
        ThroatSpatialMultiindexSecondJet Second where
  toFun jet :=
    (fun index => (jet index).1, fun index => (jet index).2)
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

/-- Underlying value fiber of one actual throat gauge jet. -/
abbrev ActualGaugeValueFiber :=
  FramedCovector ThroatCoverCoordinates

/-- Four gauge value fibers, with the exact nesting of the T02 gauge product. -/
abbrev ActualGaugeValueProductFiber :=
  (ActualGaugeValueFiber × ActualGaugeValueFiber) ×
    (ActualGaugeValueFiber × ActualGaugeValueFiber)

/-- The three LL value fibers, with the exact nesting of the T02 LL product. -/
abbrev ActualLLValueProductFiber :=
  (LLMetricFiber × Real) × LLFieldFiber

/-- Underlying value fiber of one actual throat metric jet. -/
abbrev ActualMetricValueFiber :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

/-- Two metric value fibers, with the exact nesting of the T02 metric product. -/
abbrev ActualMetricValueProductFiber :=
  ActualMetricValueFiber × ActualMetricValueFiber

/-- Two doubled SpinC value fibers, with the exact nesting of the T02 SpinC
product. -/
abbrev ActualSpinCValueProductFiber :=
  D9DoubledMatterFiber × D9DoubledMatterFiber

/-- The exact eleven-component physical value fiber underlying the T02 second
jet product. -/
abbrev ActualPhysicalValueProductFiber :=
  PhysicalSecondJetFiber
    (GaugeFiber := ActualGaugeValueProductFiber)
    (LLFiber := ActualLLValueProductFiber)
    (MetricFiber := ActualMetricValueProductFiber)
    (SpinCFiber := ActualSpinCValueProductFiber)

private abbrev SpatialJet (Fiber : Type*) :=
  ThroatSpatialMultiindexSecondJet Fiber

/-- Four gauge spatial jets, one for each gauge value component. -/
abbrev ActualGaugeSpatialSecondJetProductFiber :=
  (SpatialJet ActualGaugeValueFiber × SpatialJet ActualGaugeValueFiber) ×
    (SpatialJet ActualGaugeValueFiber × SpatialJet ActualGaugeValueFiber)

/-- Three LL spatial jets, one for each LL value component. -/
abbrev ActualLLSpatialSecondJetProductFiber :=
  (SpatialJet LLMetricFiber × SpatialJet Real) ×
    SpatialJet LLFieldFiber

/-- Two metric spatial jets. -/
abbrev ActualMetricSpatialSecondJetProductFiber :=
  SpatialJet ActualMetricValueFiber × SpatialJet ActualMetricValueFiber

/-- Two doubled SpinC spatial jets. -/
abbrev ActualSpinCSpatialSecondJetProductFiber :=
  SpatialJet D9DoubledMatterFiber × SpatialJet D9DoubledMatterFiber

/-- The exact physical nesting after distributing the spatial jet over all
eleven value components. -/
abbrev ActualPhysicalSpatialSecondJetProductFiber :=
  PhysicalSecondJetFiber
    (GaugeFiber := ActualGaugeSpatialSecondJetProductFiber)
    (LLFiber := ActualLLSpatialSecondJetProductFiber)
    (MetricFiber := ActualMetricSpatialSecondJetProductFiber)
    (SpinCFiber := ActualSpinCSpatialSecondJetProductFiber)

private def gaugeSpatialSplitEquiv :
    SpatialJet ActualGaugeValueProductFiber ≃
      ActualGaugeSpatialSecondJetProductFiber :=
  (programPT06ThroatSpatialSecondJetProdLinearEquiv
      (First := ActualGaugeValueFiber × ActualGaugeValueFiber)
      (Second := ActualGaugeValueFiber × ActualGaugeValueFiber)).toEquiv.trans
    (Equiv.prodCongr
      (programPT06ThroatSpatialSecondJetProdLinearEquiv
        (First := ActualGaugeValueFiber)
        (Second := ActualGaugeValueFiber)).toEquiv
      (programPT06ThroatSpatialSecondJetProdLinearEquiv
        (First := ActualGaugeValueFiber)
        (Second := ActualGaugeValueFiber)).toEquiv)

private def llSpatialSplitEquiv :
    SpatialJet ActualLLValueProductFiber ≃
      ActualLLSpatialSecondJetProductFiber :=
  (programPT06ThroatSpatialSecondJetProdLinearEquiv
      (First := LLMetricFiber × Real) (Second := LLFieldFiber)).toEquiv.trans
    (Equiv.prodCongr
      (programPT06ThroatSpatialSecondJetProdLinearEquiv
        (First := LLMetricFiber) (Second := Real)).toEquiv
      (Equiv.refl (SpatialJet LLFieldFiber)))

private def metricSpatialSplitEquiv :
    SpatialJet ActualMetricValueProductFiber ≃
      ActualMetricSpatialSecondJetProductFiber :=
  (programPT06ThroatSpatialSecondJetProdLinearEquiv
    (First := ActualMetricValueFiber) (Second := ActualMetricValueFiber)).toEquiv

private def spinCSpatialSplitEquiv :
    SpatialJet ActualSpinCValueProductFiber ≃
      ActualSpinCSpatialSecondJetProductFiber :=
  (programPT06ThroatSpatialSecondJetProdLinearEquiv
    (First := D9DoubledMatterFiber) (Second := D9DoubledMatterFiber)).toEquiv

private def physicalSectorSpatialSplitEquiv :
    SpatialJet ActualPhysicalValueProductFiber ≃
      (((SpatialJet ActualGaugeValueProductFiber ×
          SpatialJet ActualLLValueProductFiber) ×
        SpatialJet ActualMetricValueProductFiber) ×
        SpatialJet ActualSpinCValueProductFiber) :=
  (programPT06ThroatSpatialSecondJetProdLinearEquiv
      (First :=
        (ActualGaugeValueProductFiber × ActualLLValueProductFiber) ×
          ActualMetricValueProductFiber)
      (Second := ActualSpinCValueProductFiber)).toEquiv.trans
    (((programPT06ThroatSpatialSecondJetProdLinearEquiv
        (First := ActualGaugeValueProductFiber × ActualLLValueProductFiber)
        (Second := ActualMetricValueProductFiber)).toEquiv.trans
      ((programPT06ThroatSpatialSecondJetProdLinearEquiv
          (First := ActualGaugeValueProductFiber)
          (Second := ActualLLValueProductFiber)).toEquiv.prodCongr
        (Equiv.refl
          (SpatialJet ActualMetricValueProductFiber)))).prodCongr
      (Equiv.refl
        (SpatialJet ActualSpinCValueProductFiber)))

/-- Distribution of one spatial jet of the complete value product into the
exact product of eleven component spatial jets. -/
def programPT06ActualPhysicalValueProductSpatialSecondJetSplitEquiv :
    SpatialJet ActualPhysicalValueProductFiber ≃
      ActualPhysicalSpatialSecondJetProductFiber :=
  physicalSectorSpatialSplitEquiv.trans
    (((gaugeSpatialSplitEquiv.prodCongr llSpatialSplitEquiv).prodCongr
        metricSpatialSplitEquiv).prodCongr spinCSpatialSplitEquiv)

private def gaugeSpatialFramedEquiv :
    ActualGaugeSpatialSecondJetProductFiber ≃
      ActualGaugeSecondOrderJetProductFiber :=
  ((programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)).toEquiv.prodCongr
    (programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)).toEquiv).prodCongr
  ((programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)).toEquiv.prodCongr
    (programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := ActualGaugeValueFiber)).toEquiv)

private def llSpatialFramedEquiv :
    ActualLLSpatialSecondJetProductFiber ≃
      ActualLLSecondOrderJetFiber :=
  ((programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := LLMetricFiber)).toEquiv.prodCongr
    (programPT06ThroatSpatialSecondJetFramedLinearEquiv
      (Fiber := Real)).toEquiv).prodCongr
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := LLFieldFiber)).toEquiv

private def metricSpatialFramedEquiv :
    ActualMetricSpatialSecondJetProductFiber ≃
      ActualMetricSecondOrderJetProductFiber :=
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := ActualMetricValueFiber)).toEquiv.prodCongr
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := ActualMetricValueFiber)).toEquiv

private def spinCSpatialFramedEquiv :
    ActualSpinCSpatialSecondJetProductFiber ≃
      ActualSpinCSecondOrderJetProductFiber :=
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := D9DoubledMatterFiber)).toEquiv.prodCongr
  (programPT06ThroatSpatialSecondJetFramedLinearEquiv
    (Fiber := D9DoubledMatterFiber)).toEquiv

/-- Componentwise Gate870 equivalence from the eleven spatial jets to the
exact T02 physical second-jet product. -/
def programPT06ActualPhysicalSpatialSecondJetProductFramedEquiv :
    ActualPhysicalSpatialSecondJetProductFiber ≃
      ActualPhysicalSecondOrderJetProductFiber :=
  (((gaugeSpatialFramedEquiv.prodCongr
      llSpatialFramedEquiv).prodCongr
    metricSpatialFramedEquiv).prodCongr
  spinCSpatialFramedEquiv)

/-- Exact equivalence between one spatial second jet of the complete
eleven-component physical value fiber and the assembled T02 product of framed
second jets.  Every component map comes from Gate870's linear equivalence. -/
def programPT06ActualPhysicalValueProductSecondJetEquiv :
    ThroatSpatialMultiindexSecondJet ActualPhysicalValueProductFiber ≃
      ActualPhysicalSecondOrderJetProductFiber :=
  programPT06ActualPhysicalValueProductSpatialSecondJetSplitEquiv.trans
    programPT06ActualPhysicalSpatialSecondJetProductFramedEquiv

end
end P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
end JanusFormal
