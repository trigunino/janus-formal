import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinLLActualActionEulerHessian4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- One actual action containing all eight matter coordinates, the Robin
junction field, and the PT-averaged differential LL field. -/
def matterRobinLLAction
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod) : Real :=
  globalMatterMultipletAction period hPeriod matterData matter +
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      robinMeasure +
    globalPTSymmetricDifferentialLLAction period hPeriod frame llFields llMeasure

/-- The exact Euler pairing of the assembled matter + Robin + LL action. -/
def matterRobinLLEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matter matterDirection : MatterComponentFamily period hPeriod)
    (junction junctionDirection : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llDirection : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  globalMatterMultipletEuler period hPeriod matterData matter matterDirection +
    robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      junctionDirection robinMeasure +
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
      llFields llDirection llMeasure

/-- The displayed Euler pairing is the genuine simultaneous derivative of
the single assembled action. -/
theorem matterRobinLLAction_hasDerivAt
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (matter matterDirection : MatterComponentFamily period hPeriod)
    (junction junctionDirection : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llDirection : SmoothThroatField period hPeriod LLFieldFiber) :
    HasDerivAt
      (fun epsilon : Real => matterRobinLLAction period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        (matterMultipletAffineCurve period hPeriod matter matterDirection epsilon)
        (junctionAffineCurve period hPeriod junction junctionDirection epsilon)
        (differentialLLFluxCurve period hPeriod llFields llDirection epsilon))
      (matterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure matter matterDirection junction
        junctionDirection llFields llDirection) 0 := by
  unfold matterRobinLLAction matterRobinLLEuler
  exact ((globalMatterMultipletAction_hasDerivAt period hPeriod matterData
      matter matterDirection).add
    (robinJunctionAction_affine_hasDerivAt period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction junctionDirection robinMeasure)).add
    (globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt period hPeriod
      frame llFields llDirection llMeasure)

/-- Genuine Hessian of the assembled matter + Robin + LL action. -/
def matterRobinLLHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matterFirst matterSecond : MatterComponentFamily period hPeriod)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llFirst llSecond : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  globalMatterMultipletHessian period hPeriod matterData matterFirst matterSecond +
    robinHessian period hPeriod kPlus kMinus robinFirst robinSecond robinMeasure +
    globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame llFields
      llFirst llSecond llMeasure

/-- The Euler of the assembled action is genuinely differentiable, with the
preceding Hessian as derivative. -/
theorem matterRobinLLEuler_hasDerivAt
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (matter matterFirst matterSecond : MatterComponentFamily period hPeriod)
    (junction robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llFirst llSecond : SmoothThroatField period hPeriod LLFieldFiber) :
    HasDerivAt
      (fun epsilon : Real => matterRobinLLEuler period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        (matterMultipletAffineCurve period hPeriod matter matterFirst epsilon)
        matterSecond
        (junctionAffineCurve period hPeriod junction robinFirst epsilon)
        robinSecond
        (differentialLLFluxCurve period hPeriod llFields llFirst epsilon) llSecond)
      (matterRobinLLHessian period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure matterFirst matterSecond robinFirst robinSecond llFields
        llFirst llSecond) 0 := by
  unfold matterRobinLLEuler matterRobinLLHessian
  exact ((globalMatterMultipletEuler_hasDerivAt period hPeriod matterData
      matter matterFirst matterSecond).add
    (robinWeakBalance_linearized_hasDerivAt period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction robinFirst robinSecond robinMeasure)).add
    (globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
      period hPeriod frame llFields llFirst llSecond llMeasure)

/-- Helmholtz symmetry of the same assembled Hessian. -/
theorem matterRobinLLHessian_symmetric
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matterFirst matterSecond : MatterComponentFamily period hPeriod)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llFirst llSecond : SmoothThroatField period hPeriod LLFieldFiber) :
    matterRobinLLHessian period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure matterFirst matterSecond robinFirst robinSecond llFields
        llFirst llSecond =
      matterRobinLLHessian period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure matterSecond matterFirst robinSecond robinFirst llFields
        llSecond llFirst := by
  unfold matterRobinLLHessian
  rw [globalMatterMultipletHessian_symmetric period hPeriod matterData
      matterFirst matterSecond,
    robinHessian_symmetric period hPeriod kPlus kMinus robinFirst robinSecond
      robinMeasure,
    globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod frame
      llFields llFirst llSecond llMeasure]

end

end P0EFTJanusMatterRobinLLActualActionEulerHessian4D
end JanusFormal
