import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff InnerProduct ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D

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

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Actual directional derivative of the unchanged Robin junction action. -/
def robinJunctionActionDirectionalDerivative
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  deriv (fun epsilon : Real =>
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
      (junctionAffineCurve period hPeriod junction direction epsilon) mu) 0

theorem robinJunctionActionDirectionalDerivative_eq_firstVariation
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    robinJunctionActionDirectionalDerivative period hPeriod kPlus kMinus
        bulkPlus bulkMinus junction direction mu =
      robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
        junction direction mu := by
  exact (robinJunctionAction_affine_hasDerivAt period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction direction mu).deriv

/-- Actual mixed Hessian of the unchanged Robin junction action. -/
def robinJunctionActionMixedHessian
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction first second : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  deriv (fun epsilon : Real =>
    robinJunctionActionDirectionalDerivative period hPeriod kPlus kMinus
      bulkPlus bulkMinus
      (junctionAffineCurve period hPeriod junction first epsilon) second mu) 0

theorem robinJunctionActionMixedHessian_eq_robinHessian
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction first second : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    robinJunctionActionMixedHessian period hPeriod kPlus kMinus bulkPlus
        bulkMinus junction first second mu =
      robinHessian period hPeriod kPlus kMinus first second mu := by
  unfold robinJunctionActionMixedHessian
  rw [show (fun epsilon : Real =>
      robinJunctionActionDirectionalDerivative period hPeriod kPlus kMinus
        bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction first epsilon) second mu) =
      (fun epsilon : Real =>
        robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          (junctionAffineCurve period hPeriod junction first epsilon) second mu) from by
    funext epsilon
    exact robinJunctionActionDirectionalDerivative_eq_firstVariation period
      hPeriod kPlus kMinus bulkPlus bulkMinus
      (junctionAffineCurve period hPeriod junction first epsilon) second mu]
  exact (robinWeakBalance_linearized_hasDerivAt period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction first second mu).deriv

/-- Actual directional derivative of the unchanged PT-averaged LL action. -/
def globalPTSymmetricDifferentialLLActionDirectionalDerivative
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  deriv (fun epsilon : Real =>
    globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFluxCurve period hPeriod fields direction epsilon) mu) 0

theorem globalPTSymmetricDifferentialLLActionDirectionalDerivative_eq_firstVariation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLActionDirectionalDerivative period hPeriod
        frame fields direction mu =
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        fields direction mu := by
  exact (globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt period
    hPeriod frame fields direction mu).deriv

/-- Actual mixed Hessian of the unchanged PT-averaged LL action. -/
def globalPTSymmetricDifferentialLLActionMixedHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  deriv (fun epsilon : Real =>
    globalPTSymmetricDifferentialLLActionDirectionalDerivative period hPeriod
      frame (differentialLLFluxCurve period hPeriod fields first epsilon)
      second mu) 0

theorem globalPTSymmetricDifferentialLLActionMixedHessian_eq_fluxHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLActionMixedHessian period hPeriod frame
        fields first second mu =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
        first second mu := by
  unfold globalPTSymmetricDifferentialLLActionMixedHessian
  rw [show (fun epsilon : Real =>
      globalPTSymmetricDifferentialLLActionDirectionalDerivative period hPeriod
        frame (differentialLLFluxCurve period hPeriod fields first epsilon)
        second mu) =
      (fun epsilon : Real =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields first epsilon)
          second mu) from by
    funext epsilon
    exact
      globalPTSymmetricDifferentialLLActionDirectionalDerivative_eq_firstVariation
        period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields first epsilon) second mu]
  exact
    (globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
      period hPeriod frame fields first second mu).deriv

/-- One actual smooth action assembling exactly the three reduced bosonic
blocks, with no metric, gauge, or ghost sector. -/
def reducedBosonicSmoothAction
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (scalar : GlobalScalarTestSpace period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod) : Real :=
  globalHolonomicScalarAction period hPeriod scalarData.formData.massSquared
      scalarData.formData.magnitude scalar scalarData.formData.measure +
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      robinMeasure +
    globalPTSymmetricDifferentialLLAction period hPeriod frame llFields llMeasure

/-- Actual simultaneous directional derivative of the assembled action. -/
def reducedBosonicSmoothActionDirectionalDerivative
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (scalar scalarDirection : GlobalScalarTestSpace period hPeriod)
    (junction junctionDirection : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llDirection : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  deriv (fun epsilon : Real =>
    reducedBosonicSmoothAction period hPeriod scalarData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure
      (scalarAffineCurve period hPeriod scalar scalarDirection epsilon)
      (junctionAffineCurve period hPeriod junction junctionDirection epsilon)
      (differentialLLFluxCurve period hPeriod llFields llDirection epsilon)) 0

theorem reducedBosonicSmoothActionDirectionalDerivative_eq
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (scalar scalarDirection : GlobalScalarTestSpace period hPeriod)
    (junction junctionDirection : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llDirection : SmoothThroatField period hPeriod LLFieldFiber) :
    reducedBosonicSmoothActionDirectionalDerivative period hPeriod scalarData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar
        scalarDirection junction junctionDirection llFields llDirection =
      weakGlobalHolonomicScalarEulerOperator period hPeriod scalarData.formData
          scalar scalarDirection +
        robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction junctionDirection robinMeasure +
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
          llFields llDirection llMeasure := by
  unfold reducedBosonicSmoothActionDirectionalDerivative reducedBosonicSmoothAction
  exact (((globalHolonomicScalarAction_hasDerivAt_weakEuler period hPeriod
      scalarData.formData scalar scalarDirection).add
    (robinJunctionAction_affine_hasDerivAt period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction junctionDirection robinMeasure)).add
    (globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt period hPeriod
      frame llFields llDirection llMeasure)).deriv

/-- Actual mixed Hessian of the single assembled reduced action. -/
def reducedBosonicSmoothActionMixedHessian
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (scalar scalarFirst scalarSecond : GlobalScalarTestSpace period hPeriod)
    (junction robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llFirst llSecond : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  deriv (fun epsilon : Real =>
    reducedBosonicSmoothActionDirectionalDerivative period hPeriod scalarData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
      (scalarAffineCurve period hPeriod scalar scalarFirst epsilon) scalarSecond
      (junctionAffineCurve period hPeriod junction robinFirst epsilon) robinSecond
      (differentialLLFluxCurve period hPeriod llFields llFirst epsilon) llSecond) 0

theorem reducedBosonicSmoothActionMixedHessian_eq
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (scalar scalarFirst scalarSecond : GlobalScalarTestSpace period hPeriod)
    (junction robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llFirst llSecond : SmoothThroatField period hPeriod LLFieldFiber) :
    reducedBosonicSmoothActionMixedHessian period hPeriod scalarData kPlus
        kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar scalarFirst
        scalarSecond junction robinFirst robinSecond llFields llFirst llSecond =
      weakGlobalHolonomicScalarJacobiOperator period hPeriod scalarData.formData
          scalarFirst scalarSecond +
        robinHessian period hPeriod kPlus kMinus robinFirst robinSecond
          robinMeasure +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame llFields
          llFirst llSecond llMeasure := by
  unfold reducedBosonicSmoothActionMixedHessian
  rw [show (fun epsilon : Real =>
      reducedBosonicSmoothActionDirectionalDerivative period hPeriod scalarData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        (scalarAffineCurve period hPeriod scalar scalarFirst epsilon) scalarSecond
        (junctionAffineCurve period hPeriod junction robinFirst epsilon) robinSecond
        (differentialLLFluxCurve period hPeriod llFields llFirst epsilon) llSecond) =
      (fun epsilon : Real =>
        weakGlobalHolonomicScalarEulerOperator period hPeriod scalarData.formData
            (scalarAffineCurve period hPeriod scalar scalarFirst epsilon)
            scalarSecond +
          robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
            (junctionAffineCurve period hPeriod junction robinFirst epsilon)
            robinSecond robinMeasure +
          globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
            (differentialLLFluxCurve period hPeriod llFields llFirst epsilon)
            llSecond llMeasure) from by
    funext epsilon
    exact reducedBosonicSmoothActionDirectionalDerivative_eq period hPeriod
      scalarData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
      (scalarAffineCurve period hPeriod scalar scalarFirst epsilon) scalarSecond
      (junctionAffineCurve period hPeriod junction robinFirst epsilon) robinSecond
      (differentialLLFluxCurve period hPeriod llFields llFirst epsilon) llSecond]
  exact (((weakGlobalHolonomicScalarEulerOperator_hasDerivAt period hPeriod
      scalarData.formData scalar scalarFirst scalarSecond).add
    (robinWeakBalance_linearized_hasDerivAt period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction robinFirst robinSecond robinMeasure)).add
    (globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
      period hPeriod frame llFields llFirst llSecond llMeasure)).deriv

/-- On the smooth reduced bosonic sector, the scalar block of the assembled
Fredholm pairing is the actual mixed Hessian of the unchanged global D8 scalar
action.  The Robin and LL blocks remain their already proved natural action
Hessians; no metric, gauge, ghost, or full Candidate-A block is asserted. -/
theorem reducedBosonicNaturalHessian_smooth_eq_actualScalarActionHessian
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (scalarBase : GlobalScalarTestSpace period hPeriod)
    (scalarFirst scalarSecond :
      StaticGlobalScalarTest period hPeriod scalarData)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarFirst,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarSecond,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) =
      globalHolonomicScalarActionMixedHessian period hPeriod
          scalarData.formData scalarBase scalarFirst.toField scalarSecond.toField +
        robinHessian period hPeriod kPlus kMinus robinFirst robinSecond
          robinMeasure +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
          llFirst.toTest llSecond.toTest llData.mu := by
  rw [reducedBosonicNaturalHessian_smooth_eq period hPeriod scalarData
    kPlus kMinus robinMeasure llData scalarFirst scalarSecond robinFirst
    robinSecond llFirst llSecond]
  rw [globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod
    scalarData.formData scalarBase scalarFirst.toField scalarSecond.toField]
  rw [weakGlobalHolonomicScalarJacobiOperator_apply]

/-- On the smooth reduced bosonic sector, every block pairing is an actual
mixed second derivative of its unchanged action. -/
theorem reducedBosonicNaturalHessian_smooth_eq_actualActionHessians
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (scalarBase : GlobalScalarTestSpace period hPeriod)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (scalarFirst scalarSecond :
      StaticGlobalScalarTest period hPeriod scalarData)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarFirst,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarSecond,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) =
      globalHolonomicScalarActionMixedHessian period hPeriod
          scalarData.formData scalarBase scalarFirst.toField scalarSecond.toField +
        robinJunctionActionMixedHessian period hPeriod kPlus kMinus bulkPlus
          bulkMinus junction robinFirst robinSecond robinMeasure +
        globalPTSymmetricDifferentialLLActionMixedHessian period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
          llFirst.toTest llSecond.toTest llData.mu := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [reducedBosonicNaturalHessian_smooth_eq_actualScalarActionHessian period
    hPeriod scalarData kPlus kMinus robinMeasure llData scalarBase scalarFirst
    scalarSecond robinFirst robinSecond llFirst llSecond]
  rw [robinJunctionActionMixedHessian_eq_robinHessian period hPeriod kPlus
    kMinus bulkPlus bulkMinus junction robinFirst robinSecond robinMeasure]
  rw [globalPTSymmetricDifferentialLLActionMixedHessian_eq_fluxHessian period
    hPeriod (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
    llFirst.toTest llSecond.toTest llData.mu]

/-- The completed reduced Fredholm pairing, restricted to its smooth dense
sector, is the actual mixed Hessian of one assembled reduced bosonic action. -/
theorem reducedBosonicNaturalHessian_smooth_eq_assembledActionMixedHessian
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (scalarBase : GlobalScalarTestSpace period hPeriod)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (scalarFirst scalarSecond :
      StaticGlobalScalarTest period hPeriod scalarData)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarFirst,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarSecond,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) =
      reducedBosonicSmoothActionMixedHessian period hPeriod scalarData kPlus
        kMinus bulkPlus bulkMinus robinMeasure
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu scalarBase
        scalarFirst.toField scalarSecond.toField junction robinFirst robinSecond
        llData.fields llFirst.toTest llSecond.toTest := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [reducedBosonicNaturalHessian_smooth_eq period hPeriod scalarData
    kPlus kMinus robinMeasure llData scalarFirst scalarSecond robinFirst
    robinSecond llFirst llSecond]
  rw [reducedBosonicSmoothActionMixedHessian_eq period hPeriod scalarData
    kPlus kMinus bulkPlus bulkMinus robinMeasure
    (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu scalarBase
    scalarFirst.toField scalarSecond.toField junction robinFirst robinSecond
    llData.fields llFirst.toTest llSecond.toTest]
  rw [weakGlobalHolonomicScalarJacobiOperator_apply]

end

end P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D
end JanusFormal
