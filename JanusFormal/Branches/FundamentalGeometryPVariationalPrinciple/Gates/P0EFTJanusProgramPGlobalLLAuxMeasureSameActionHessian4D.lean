import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLVariationalAPI4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D

/-!
# Global LL auxiliary-metric/measure same-action Hessian

This gate restricts the existing full LL variational API to the two slots
`llAuxMetric` and `llMeasure` of the unchanged global Candidate-A LL summand.
It is only a smooth directional Hessian gate: no Hilbert completion or
Fredholm operator is asserted for these two slots.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalLLAuxMeasureSameActionHessian4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- Inclusion of the two residual LL slots, with every other direction zero. -/
def globalCandidateALLAuxMeasureDirection
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    FullMatterRobinLLDirections period hPeriod :=
  { fullRobinLLDirection period hPeriod 0 0 with
    llAuxMetric := dAux
    llMeasure := dMeasure }

@[simp]
theorem globalCandidateALLAuxMeasureDirection_llAuxMetric
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    (globalCandidateALLAuxMeasureDirection period hPeriod dAux dMeasure).llAuxMetric =
      dAux := rfl

@[simp]
theorem globalCandidateALLAuxMeasureDirection_llMeasure
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    (globalCandidateALLAuxMeasureDirection period hPeriod dAux dMeasure).llMeasure =
      dMeasure := rfl

@[simp]
theorem globalCandidateALLAuxMeasureDirection_llField
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    (globalCandidateALLAuxMeasureDirection period hPeriod dAux dMeasure).common.ll =
      0 := rfl

/-- The actual global LL summand along its auxiliary-metric/measure curve. -/
def globalCandidateALLAuxMeasureCurveAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real)
    (t : Real) : Real :=
  globalPTSymmetricDifferentialLLAction period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (differentialLLFullCurve period hPeriod
      (data.boundary.llFields period hPeriod) dAux dMeasure 0 t)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- At the base point the curve is exactly the unchanged global LL summand. -/
theorem globalCandidateALLAuxMeasureCurveAction_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    globalCandidateALLAuxMeasureCurveAction period hPeriod data dAux dMeasure 0 =
      globalCandidateALLAction period hPeriod data := by
  simp [globalCandidateALLAuxMeasureCurveAction, globalCandidateALLAction,
    differentialLLFullCurve]

/-- First variation of the same global LL summand in the two-slot direction. -/
def globalCandidateALLAuxMeasureEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) : Real :=
  fullLLEuler period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateALLAuxMeasureDirection period hPeriod dAux dMeasure)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The existing first-variation theorem applied to the unchanged global LL
summand and the two residual LL slots. -/
theorem globalCandidateALLAuxMeasureCurveAction_hasDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dMeasure : SmoothThroatField period hPeriod Real) :
    HasDerivAt
      (globalCandidateALLAuxMeasureCurveAction period hPeriod data dAux dMeasure)
      (globalCandidateALLAuxMeasureEuler period hPeriod data dAux dMeasure) 0 := by
  change HasDerivAt
    (fun t : Real =>
      globalPTSymmetricDifferentialLLAction period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (differentialLLFullCurve period hPeriod
          (data.boundary.llFields period hPeriod) dAux dMeasure 0 t)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    (fullLLEuler period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (data.boundary.llFields period hPeriod)
      (globalCandidateALLAuxMeasureDirection period hPeriod dAux dMeasure)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) 0
  simpa using
    (truePTAction_fullCurve_hasDerivAt_fullLLEuler period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (data.boundary.llFields period hPeriod)
      (globalCandidateALLAuxMeasureDirection period hPeriod dAux dMeasure)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))

/-- The genuine mixed Hessian of the same LL summand on the two-slot slice. -/
def globalCandidateALLAuxMeasureHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (firstAux secondAux : SmoothThroatField period hPeriod LLMetricFiber)
    (firstMeasure secondMeasure : SmoothThroatField period hPeriod Real) : Real :=
  fullLLHessian period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateALLAuxMeasureDirection period hPeriod firstAux firstMeasure)
    (globalCandidateALLAuxMeasureDirection period hPeriod secondAux secondMeasure)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- First variation in the first direction, evaluated along the second. -/
def globalCandidateALLAuxMeasureEulerAlong
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (firstAux secondAux : SmoothThroatField period hPeriod LLMetricFiber)
    (firstMeasure secondMeasure : SmoothThroatField period hPeriod Real)
    (t : Real) : Real :=
  fullLLEulerAlong period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateALLAuxMeasureDirection period hPeriod firstAux firstMeasure)
    (globalCandidateALLAuxMeasureDirection period hPeriod secondAux secondMeasure)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) t

/-- The two-slot form is the derivative of the same-action Euler functional. -/
theorem globalCandidateALLAuxMeasureEulerAlong_hasDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (firstAux secondAux : SmoothThroatField period hPeriod LLMetricFiber)
    (firstMeasure secondMeasure : SmoothThroatField period hPeriod Real) :
    HasDerivAt
      (globalCandidateALLAuxMeasureEulerAlong period hPeriod data
        firstAux secondAux firstMeasure secondMeasure)
      (globalCandidateALLAuxMeasureHessian period hPeriod data
        firstAux secondAux firstMeasure secondMeasure) 0 := by
  exact fullLLEuler_second_direction_hasDerivAt period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateALLAuxMeasureDirection period hPeriod firstAux firstMeasure)
    (globalCandidateALLAuxMeasureDirection period hPeriod secondAux secondMeasure)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Symmetry inherited from the full Hessian of the unchanged LL action. -/
theorem globalCandidateALLAuxMeasureHessian_symmetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (firstAux secondAux : SmoothThroatField period hPeriod LLMetricFiber)
    (firstMeasure secondMeasure : SmoothThroatField period hPeriod Real) :
    globalCandidateALLAuxMeasureHessian period hPeriod data
        firstAux secondAux firstMeasure secondMeasure =
      globalCandidateALLAuxMeasureHessian period hPeriod data
        secondAux firstAux secondMeasure firstMeasure := by
  exact fullLLHessian_symmetric period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateALLAuxMeasureDirection period hPeriod firstAux firstMeasure)
    (globalCandidateALLAuxMeasureDirection period hPeriod secondAux secondMeasure)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

end
end P0EFTJanusProgramPGlobalLLAuxMeasureSameActionHessian4D
end JanusFormal
