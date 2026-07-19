import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationD9FieldAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterLLVisibleQuotientGeneralMetricBVD9Bridge4D

/-!
# Normal Pin-minus covariance on the complete Program-P variation

This gate puts three already genuine pieces on one
`ProgramPCompleteVariation4D`: an arbitrary smooth section of the constructed
normal line, the full general-metric BV tensor, and the exact D9 field readout.
The local normal D9 coordinate transforms by the orientation reduction of the
actual principal `Pin⁻(1)` transition.  The matter--LL action, Hessian and
current boundary domain still read the same independent direction.

This is a normal `Pin⁻(1)` statement.  It neither constructs the ambient
`Pin⁻(4)` tangent identification nor a physical `PinC` spinor bundle, and it
does not add EH, Maxwell or D10-mode dynamics.
-/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationNormalPinMinusGeneralMetricD9Bridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusCompleteVariationBoundaryDomainBridge4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusIndependentMatterLLActionVisibleQuotient4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
open P0EFTJanusMatterLLVisibleQuotientGeneralMetricBVD9Bridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Real action obtained by reducing a normal `Pin⁻(1)` phase to orientation. -/
def normalPinMinusOrientationAction
    (phase : NormalPinMinusOne) (coordinate : Real) : Real :=
  if normalPinMinusOrientationReduction phase = 0 then coordinate else -coordinate

@[simp]
theorem normalPinMinusOrientationAction_one (coordinate : Real) :
    normalPinMinusOrientationAction (1 : NormalPinMinusOne) coordinate =
      -coordinate := by
  simp [normalPinMinusOrientationAction, normalPinMinusOrientationReduction]

/-- Add an arbitrary genuine normal displacement to the same complete
variation whose full tensor slot is supplied by the general-metric BV field. -/
def completeVariationWithGeneralMetricBVAndNormal
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (normalDisplacement : Sector → SmoothNormalDisplacement period hPeriod) :
    ProgramPCompleteVariation4D period hPeriod :=
  { completeVariationWithGeneralMetricBV period hPeriod variation phase with
      normalDisplacement := normalDisplacement }

@[simp]
theorem completeVariationWithGeneralMetricBVAndNormal_independent
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (normalDisplacement : Sector → SmoothNormalDisplacement period hPeriod) :
    (completeVariationWithGeneralMetricBVAndNormal period hPeriod variation
      phase normalDisplacement).independent = variation :=
  rfl

@[simp]
theorem completeVariationWithGeneralMetricBVAndNormal_normalDisplacement
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (normalDisplacement : Sector → SmoothNormalDisplacement period hPeriod)
    (sector : Sector) :
    (completeVariationWithGeneralMetricBVAndNormal period hPeriod variation
      phase normalDisplacement).normalDisplacement sector =
        normalDisplacement sector :=
  rfl

/-- The same complete tangent retains all six D9 spatial coefficients of the
general metric, including the three off-diagonal entries. -/
theorem completeVariationWithGeneralMetricBVAndNormal_metricPerturbationAt
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (normalDisplacement : Sector → SmoothNormalDisplacement period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    (completeVariationWithGeneralMetricBVAndNormal period hPeriod variation
        phase normalDisplacement).metricPerturbationAt period hPeriod sector point =
      (completeVariationWithGeneralMetricBV period hPeriod variation phase
        ).metricPerturbationAt period hPeriod sector point :=
  rfl

/-- D9 field readout in an explicitly selected normal-bundle chart. -/
def completeVariationD9FieldInNormalChart
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor) :
    CompleteLocalField Spinor where
  bosonic :=
    { normalMode := localNormalMode period hPeriod
        (variation.normalDisplacement sector) anchor point hPoint
      gaugeOneForm :=
        d9GaugeOneForm period hPeriod variation.independent sector column point
      metricPerturbation :=
        variation.metricPerturbationAt period hPeriod sector point }
  ghosts :=
    { u1Ghost :=
        d9U1Ghost period hPeriod variation.independent sector column point
      diffeomorphismGhost :=
        variation.diffeomorphismGhostAt period hPeriod sector point }
  spinor := matterSpinorIdentification
    (d9MatterCoefficient period hPeriod variation.independent sector point)

@[simp]
theorem completeVariationD9FieldInNormalChart_metricPerturbation
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor) :
    (completeVariationD9FieldInNormalChart period hPeriod
      matterSpinorIdentification variation sector column point anchor hPoint
      ).bosonic.metricPerturbation =
        variation.metricPerturbationAt period hPeriod sector point :=
  rfl

/-- One deck circuit acts on the local D9 normal coordinate exactly through
the orientation reduction of the genuine principal `Pin⁻(1)` transition. -/
theorem completeVariationD9FieldInNormalChart_oneLoop_pinMinus
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (column : Fin 2)
    (anchor : ThroatCover period hPeriod)
    (hAnchor : mappingTorusMk (fixedEquatorData period hPeriod) anchor ∈
      normalBundleBaseSet period hPeriod anchor)
    (hShifted : mappingTorusMk (fixedEquatorData period hPeriod) anchor ∈
      normalBundleBaseSet period hPeriod ((1 : Int) +ᵥ anchor)) :
    let point := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    (completeVariationD9FieldInNormalChart period hPeriod
        matterSpinorIdentification variation sector column point
        ((1 : Int) +ᵥ anchor) hShifted).bosonic.normalMode =
      normalPinMinusOrientationAction
        ((fixedThroatNormalPinMinusPrincipalBundle period hPeriod).core.coordChange
          anchor ((1 : Int) +ᵥ anchor) point 0)
        ((completeVariationD9FieldInNormalChart period hPeriod
          matterSpinorIdentification variation sector column point anchor hAnchor
          ).bosonic.normalMode) := by
  dsimp only [completeVariationD9FieldInNormalChart, localNormalMode]
  have hPin :
      (fixedThroatNormalPinMinusPrincipalBundle period hPeriod).core.coordChange
          anchor ((1 : Int) +ᵥ anchor)
          (mappingTorusMk (fixedEquatorData period hPeriod) anchor) 0 = 1 := by
    simpa [fixedThroatNormalPinMinusPrincipalBundle] using
      one_loop_pinMinus_coordChange period hPeriod anchor (0 : NormalPinMinusOne)
  rw [hPin, normalPinMinusOrientationAction_one]
  exact localNormalCoordinate_oneLoop period hPeriod anchor
    ((variation.normalDisplacement sector)
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor))

/-- Adding the genuine normal section does not change the already proved
matter--LL action quotient agreement. -/
theorem visibleQuotientActionCurve_withGeneralMetricBVAndNormal
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (normalDisplacement : Sector → SmoothNormalDisplacement period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : Real) :
    matterLLVisibleQuotientActionCurve period hPeriod data frame fields mu
        parameter ((matterLLActionInvisibleSubmodule period hPeriod).mkQ variation) =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationWithGeneralMetricBVAndNormal period hPeriod variation
          phase normalDisplacement) mu parameter := by
  rw [visibleQuotientActionCurve_withGeneralMetricBV period hPeriod data frame
    fields variation phase mu parameter]
  rfl

/-- The analogous equality holds for the actual symmetric matter--LL Hessian
on two independently chosen normal sections. -/
theorem visibleQuotientHessian_withGeneralMetricBVAndNormal
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : IndependentFieldVariation period hPeriod)
    (firstPhase secondPhase : SmoothGeneralMetricBVField period hPeriod)
    (firstNormal secondNormal :
      Sector → SmoothNormalDisplacement period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    matterLLActionVisibleQuotientHessian period hPeriod data frame fields mu
        ((matterLLActionInvisibleSubmodule period hPeriod).mkQ first)
        ((matterLLActionInvisibleSubmodule period hPeriod).mkQ second) =
      completeVariationMatterLLHessian period hPeriod data frame fields
        (completeVariationWithGeneralMetricBVAndNormal period hPeriod first
          firstPhase firstNormal)
        (completeVariationWithGeneralMetricBVAndNormal period hPeriod second
          secondPhase secondNormal) mu := by
  rw [visibleQuotientHessian_withGeneralMetricBV period hPeriod data frame fields
    first second firstPhase secondPhase mu]
  rfl

/-- The current boundary domain still tests precisely the unchanged
independent-field direction. -/
theorem completeVariationWithGeneralMetricBVAndNormal_mem_boundaryDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (normalDisplacement : Sector → SmoothNormalDisplacement period hPeriod) :
    completeVariationWithGeneralMetricBVAndNormal period hPeriod variation phase
        normalDisplacement ∈
      programPBoundaryTangentDomain4D period hPeriod domain ↔
    variation ∈ independentBoundaryTangentDomain4D period hPeriod domain :=
  Iff.rfl

end

end P0EFTJanusCompleteVariationNormalPinMinusGeneralMetricD9Bridge4D
end JanusFormal
