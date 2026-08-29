import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Chartwise extraction of physical second-order jets

This gate constructs the framed carrier from an ordinary coordinate
representative which is `C^2` at the selected chart point.  The second slot is
the derivative of the first Frechet derivative; its symmetry is the Mathlib
Schwarz theorem.

The throat wrappers below are deliberately local: their inputs are already
written in a fixed tangent chart and fixed fiber trivialization.  No global
section trivialization, overlap law, or global-field extraction is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D

variable {Domain Fiber : Type*}
  [NormedAddCommGroup Domain] [NormedSpace Real Domain]
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- The actual value, first Frechet derivative and iterated second Frechet
derivative of a `C^2` coordinate representative at one chart point. -/
def chartwiseSecondOrderJetAt
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 2 field point) :
    FramedSecondOrderJet Domain Fiber where
  value := field point
  firstDerivative := fderiv Real field point
  secondDerivative := fderiv Real (fderiv Real field) point
  secondDerivative_symmetric := fun first second =>
    (regularity.isSymmSndFDerivAt (by simp)).eq first second

@[simp]
theorem chartwiseSecondOrderJetAt_value
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 2 field point) :
    (chartwiseSecondOrderJetAt field point regularity).value = field point :=
  rfl

@[simp]
theorem chartwiseSecondOrderJetAt_firstDerivative
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 2 field point) :
    (chartwiseSecondOrderJetAt field point regularity).firstDerivative =
      fderiv Real field point :=
  rfl

@[simp]
theorem chartwiseSecondOrderJetAt_secondDerivative
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 2 field point) :
    (chartwiseSecondOrderJetAt field point regularity).secondDerivative =
      fderiv Real (fderiv Real field) point :=
  rfl

/-- Global `C^2` regularity supplies the pointwise chartwise constructor. -/
def chartwiseSecondOrderJet
    (field : Domain → Fiber) (regularity : ContDiff Real 2 field)
    (point : Domain) :
    FramedSecondOrderJet Domain Fiber :=
  chartwiseSecondOrderJetAt field point regularity.contDiffAt

@[simp]
theorem chartwiseSecondOrderJet_value
    (field : Domain → Fiber) (regularity : ContDiff Real 2 field)
    (point : Domain) :
    (chartwiseSecondOrderJet field regularity point).value = field point :=
  rfl

@[simp]
theorem chartwiseSecondOrderJet_firstDerivative
    (field : Domain → Fiber) (regularity : ContDiff Real 2 field)
    (point : Domain) :
    (chartwiseSecondOrderJet field regularity point).firstDerivative =
      fderiv Real field point :=
  rfl

@[simp]
theorem chartwiseSecondOrderJet_secondDerivative
    (field : Domain → Fiber) (regularity : ContDiff Real 2 field)
    (point : Domain) :
    (chartwiseSecondOrderJet field regularity point).secondDerivative =
      fderiv Real (fderiv Real field) point :=
  rfl

/-- SpinC matter jet in a selected throat chart and selected bundle
trivialization. -/
def fixedTrivializationSpinCMatterJetAt
    (field : ThroatCoverCoordinates → D9DoubledMatterFiber)
    (point : ThroatCoverCoordinates)
    (regularity : ContDiffAt Real 2 field point) :
    FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber :=
  chartwiseSecondOrderJetAt field point regularity

/-- LL auxiliary-metric jet in a selected throat chart and trivialization. -/
def fixedTrivializationLLAuxMetricJetAt
    (field : ThroatCoverCoordinates → LLMetricFiber)
    (point : ThroatCoverCoordinates)
    (regularity : ContDiffAt Real 2 field point) :
    FramedSecondOrderJet ThroatCoverCoordinates LLMetricFiber :=
  chartwiseSecondOrderJetAt field point regularity

/-- LL measure-coefficient jet in a selected throat chart. -/
def fixedTrivializationLLMeasureJetAt
    (field : ThroatCoverCoordinates → Real)
    (point : ThroatCoverCoordinates)
    (regularity : ContDiffAt Real 2 field point) :
    FramedSecondOrderJet ThroatCoverCoordinates Real :=
  chartwiseSecondOrderJetAt field point regularity

/-- LL field jet in a selected throat chart and trivialization. -/
def fixedTrivializationLLFieldJetAt
    (field : ThroatCoverCoordinates → LLFieldFiber)
    (point : ThroatCoverCoordinates)
    (regularity : ContDiffAt Real 2 field point) :
    FramedSecondOrderJet ThroatCoverCoordinates LLFieldFiber :=
  chartwiseSecondOrderJetAt field point regularity

/-- The local coordinate representatives of all primitive throat matter/LL
fields.  The SpinC sector index agrees with the physical carrier. -/
structure FixedTrivializationThroatFields where
  spinCMatter : Sector → ThroatCoverCoordinates → D9DoubledMatterFiber
  llAuxMetric : ThroatCoverCoordinates → LLMetricFiber
  llMeasure : ThroatCoverCoordinates → Real
  llField : ThroatCoverCoordinates → LLFieldFiber

/-- Pointwise `C^2` evidence for a fixed-trivialization throat packet. -/
structure FixedTrivializationThroatFieldsContDiffAtTwo
    (fields : FixedTrivializationThroatFields)
    (point : ThroatCoverCoordinates) : Prop where
  spinCMatter : ∀ sector, ContDiffAt Real 2 (fields.spinCMatter sector) point
  llAuxMetric : ContDiffAt Real 2 fields.llAuxMetric point
  llMeasure : ContDiffAt Real 2 fields.llMeasure point
  llField : ContDiffAt Real 2 fields.llField point

/-- Exactly the throat matter/LL part of the physical second-order carrier,
without inventing its background or metric components. -/
structure FixedTrivializationThroatSecondOrderJets where
  spinCMatter : Sector → FramedSecondOrderJet ThroatCoverCoordinates
    D9DoubledMatterFiber
  llAuxMetric : FramedSecondOrderJet ThroatCoverCoordinates LLMetricFiber
  llMeasure : FramedSecondOrderJet ThroatCoverCoordinates Real
  llField : FramedSecondOrderJet ThroatCoverCoordinates LLFieldFiber

/-- Simultaneous pointwise extraction for the primitive throat packet in one
fixed chart and fixed fiber trivializations. -/
def FixedTrivializationThroatFields.secondOrderJetsAt
    (fields : FixedTrivializationThroatFields)
    (point : ThroatCoverCoordinates)
    (regularity :
      FixedTrivializationThroatFieldsContDiffAtTwo fields point) :
    FixedTrivializationThroatSecondOrderJets where
  spinCMatter := fun sector =>
    fixedTrivializationSpinCMatterJetAt
      (fields.spinCMatter sector) point (regularity.spinCMatter sector)
  llAuxMetric :=
    fixedTrivializationLLAuxMetricJetAt
      fields.llAuxMetric point regularity.llAuxMetric
  llMeasure :=
    fixedTrivializationLLMeasureJetAt
      fields.llMeasure point regularity.llMeasure
  llField :=
    fixedTrivializationLLFieldJetAt
      fields.llField point regularity.llField

@[simp]
theorem FixedTrivializationThroatFields.secondOrderJetsAt_spinCMatter_value
    (fields : FixedTrivializationThroatFields)
    (point : ThroatCoverCoordinates)
    (regularity :
      FixedTrivializationThroatFieldsContDiffAtTwo fields point)
    (sector : Sector) :
    ((fields.secondOrderJetsAt point regularity).spinCMatter sector).value =
      fields.spinCMatter sector point :=
  rfl

@[simp]
theorem FixedTrivializationThroatFields.secondOrderJetsAt_llAuxMetric_value
    (fields : FixedTrivializationThroatFields)
    (point : ThroatCoverCoordinates)
    (regularity :
      FixedTrivializationThroatFieldsContDiffAtTwo fields point) :
    (fields.secondOrderJetsAt point regularity).llAuxMetric.value =
      fields.llAuxMetric point :=
  rfl

@[simp]
theorem FixedTrivializationThroatFields.secondOrderJetsAt_llMeasure_value
    (fields : FixedTrivializationThroatFields)
    (point : ThroatCoverCoordinates)
    (regularity :
      FixedTrivializationThroatFieldsContDiffAtTwo fields point) :
    (fields.secondOrderJetsAt point regularity).llMeasure.value =
      fields.llMeasure point :=
  rfl

@[simp]
theorem FixedTrivializationThroatFields.secondOrderJetsAt_llField_value
    (fields : FixedTrivializationThroatFields)
    (point : ThroatCoverCoordinates)
    (regularity :
      FixedTrivializationThroatFieldsContDiffAtTwo fields point) :
    (fields.secondOrderJetsAt point regularity).llField.value =
      fields.llField point :=
  rfl

end
end P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
end JanusFormal
