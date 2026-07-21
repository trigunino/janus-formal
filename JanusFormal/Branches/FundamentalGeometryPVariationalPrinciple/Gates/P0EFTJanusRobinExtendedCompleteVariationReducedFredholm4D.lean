import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationBoundaryDomainBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D

/-!
# Robin extension of the complete Program-P variation

`ProgramPCompleteVariation4D` contains the genuine independent, normal,
diffeomorphism-ghost and full-metric directions, but no Robin junction
direction.  This gate adds exactly that missing smooth field without changing
the existing record.  The old complete tangent embeds injectively at zero
Robin direction, and the current boundary domain pulls back through the
complete component because its boundary curve does not yet constrain Robin.

The same extended type below is used by the actual matter + Robin + three-slot
LL action curve, its Euler derivative and its Hessian.  Its comparison with
the natural Fredholm pairing is deliberately restricted to the smooth reduced
Robin + LL sector: the reduced scalar entry is zero, and matter, EH, Maxwell,
ghost, auxiliary-bulk and the three geometric completion blocks are absent.
-/

namespace JanusFormal
namespace P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D

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
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationBoundaryDomainBridge4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Minimal Robin extension of the genuine complete Program-P tangent. -/
structure ProgramPRobinCompleteVariation4D where
  complete : ProgramPCompleteVariation4D period hPeriod
  robin : SmoothThroatField period hPeriod Real

/-- Every existing complete tangent is retained, with zero Robin velocity. -/
def includeCompleteVariation
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    ProgramPRobinCompleteVariation4D period hPeriod where
  complete := variation
  robin := 0

@[simp]
theorem includeCompleteVariation_complete
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    (includeCompleteVariation period hPeriod variation).complete = variation :=
  rfl

@[simp]
theorem includeCompleteVariation_robin
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    (includeCompleteVariation period hPeriod variation).robin = 0 :=
  rfl

theorem includeCompleteVariation_injective :
    Function.Injective (includeCompleteVariation period hPeriod) := by
  intro first second hEqual
  exact congrArg ProgramPRobinCompleteVariation4D.complete hEqual

/-- Exact pullback of the current independent-field boundary domain.  This
does not assert a new Robin boundary equation. -/
def programPRobinBoundaryTangentDomain4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    Set (ProgramPRobinCompleteVariation4D period hPeriod) :=
  { variation |
      variation.complete ∈
        programPBoundaryTangentDomain4D period hPeriod domain }

theorem mem_robinBoundaryTangentDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : ProgramPRobinCompleteVariation4D period hPeriod) :
    variation ∈ programPRobinBoundaryTangentDomain4D period hPeriod domain ↔
      variation.complete ∈
        programPBoundaryTangentDomain4D period hPeriod domain :=
  Iff.rfl

theorem includeCompleteVariation_mem_boundaryDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    includeCompleteVariation period hPeriod variation ∈
        programPRobinBoundaryTangentDomain4D period hPeriod domain ↔
      variation ∈ programPBoundaryTangentDomain4D period hPeriod domain :=
  Iff.rfl

/-- Replacing only the Robin velocity leaves the current boundary domain
unchanged, because that domain is defined by the stored independent curve. -/
theorem boundaryDomain_congr_robin
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : ProgramPRobinCompleteVariation4D period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) :
    ({ complete := variation.complete, robin := robin } :
        ProgramPRobinCompleteVariation4D period hPeriod) ∈
          programPRobinBoundaryTangentDomain4D period hPeriod domain ↔
      variation ∈ programPRobinBoundaryTangentDomain4D period hPeriod domain :=
  Iff.rfl

/-- Exact action-visible projection.  It retains every independent-field slot
and Robin; only the normal, tangent-ghost and full-metric completion fields are
inactive in the present matter + Robin + LL action. -/
def toFullMatterRobinLLDirections
    (variation : ProgramPRobinCompleteVariation4D period hPeriod) :
    FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := variation.complete.independent.metrics
      matter := variation.complete.independent.matter
      gauge := variation.complete.independent.gauge
      ghost := variation.complete.independent.ghosts
      auxiliary := variation.complete.independent.auxiliaries
      ll := variation.complete.independent.llField }
  robin := variation.robin
  llAuxMetric := variation.complete.independent.llAuxMetric
  llMeasure := variation.complete.independent.llMeasure

@[simp]
theorem fullMatterRobinLLVariation_toFull_independent
    (variation : ProgramPRobinCompleteVariation4D period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod
      (toFullMatterRobinLLDirections period hPeriod variation)).1 =
        variation.complete.independent :=
  rfl

@[simp]
theorem fullMatterRobinLLVariation_toFull_robin
    (variation : ProgramPRobinCompleteVariation4D period hPeriod) :
    (fullMatterRobinLLVariation period hPeriod
      (toFullMatterRobinLLDirections period hPeriod variation)).2 =
        variation.robin :=
  rfl

/-- The earlier common + Robin packet embeds in the new wrapper with its
three geometric completion slots and the two extra LL slots set to zero. -/
def enrichedCommonCompleteVariation
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    ProgramPRobinCompleteVariation4D period hPeriod where
  complete := independentCompleteVariation period hPeriod
    (combinedIndependentVariation period hPeriod direction.common)
  robin := direction.robin

theorem enrichedCommonCompleteVariation_injective :
    Function.Injective (enrichedCommonCompleteVariation period hPeriod) := by
  intro first second hEqual
  apply enrichedCommonVariation_injective period hPeriod
  apply Prod.ext
  · exact congrArg
      (fun variation : ProgramPRobinCompleteVariation4D period hPeriod =>
        variation.complete.independent) hEqual
  · exact congrArg ProgramPRobinCompleteVariation4D.robin hEqual

theorem toFull_enrichedCommonCompleteVariation
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    toFullMatterRobinLLDirections period hPeriod
        (enrichedCommonCompleteVariation period hPeriod direction) =
      { common := direction.common
        robin := direction.robin
        llAuxMetric := 0
        llMeasure := 0 } := by
  cases direction
  rfl

/-- The unchanged matter + Robin + true three-slot LL action along an
extended complete direction. -/
def robinCompleteMatterTrueLLActionCurve
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  let fullDirection :=
    toFullMatterRobinLLDirections period hPeriod direction
  globalMatterMultipletAction period hPeriod matterData
      (matterMultipletAffineCurve period hPeriod
        (independentMatterComponentFamily period hPeriod fields)
        (matterVariationComponentFamily period hPeriod
          fullDirection.common.matter) parameter) +
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
      (junctionAffineCurve period hPeriod junction fullDirection.robin parameter)
      robinMeasure +
    globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields fullDirection.llAuxMetric
        fullDirection.llMeasure fullDirection.common.ll parameter) llMeasure

/-- Euler coefficient of that exact action curve on the same wrapper. -/
def robinCompleteMatterTrueLLEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
    bulkMinus robinMeasure frame llMeasure fields junction
    (toFullMatterRobinLLDirections period hPeriod direction)

theorem robinCompleteMatterTrueLLAction_hasDerivAt
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod) :
    HasDerivAt
      (robinCompleteMatterTrueLLActionCurve period hPeriod matterData kPlus
        kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        direction)
      (robinCompleteMatterTrueLLEuler period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction)
      0 := by
  unfold robinCompleteMatterTrueLLActionCurve robinCompleteMatterTrueLLEuler
  exact fullMatterRobinTrueLLAction_hasDerivAt period hPeriod matterData kPlus
    kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    (toFullMatterRobinLLDirections period hPeriod direction)

/-- Genuine assembled Hessian, pulled back to two values of the same extended
complete type used by the action curve. -/
def robinCompleteMatterTrueLLHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields
    (toFullMatterRobinLLDirections period hPeriod first)
    (toFullMatterRobinLLDirections period hPeriod second)

theorem robinCompleteMatterTrueLLHessian_symmetric
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) :
    robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields second first := by
  exact globalMatterRobinFullLLHessian_symmetric period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure fields
    (toFullMatterRobinLLDirections period hPeriod first)
    (toFullMatterRobinLLDirections period hPeriod second)

/-- Euler curve used to differentiate in `varied`, while `test` remains the
first-variation test direction. -/
def robinCompleteMatterTrueLLEulerCurve
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (test varied : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  let fullTest := toFullMatterRobinLLDirections period hPeriod test
  let fullVaried := toFullMatterRobinLLDirections period hPeriod varied
  globalMatterRobinFullLLFirstVariation period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure
    (matterMultipletAffineCurve period hPeriod matter
      (matterVariationComponentFamily period hPeriod fullVaried.common.matter)
      parameter)
    (junctionAffineCurve period hPeriod junction fullVaried.robin parameter)
    (fullLLCurve period hPeriod fields
      (fullDirectionLLVariation period hPeriod fullVaried)
      fullVaried.llAuxMetric parameter)
    fullTest

theorem robinCompleteMatterTrueLLEuler_hasDerivAt
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (test varied : ProgramPRobinCompleteVariation4D period hPeriod) :
    HasDerivAt
      (robinCompleteMatterTrueLLEulerCurve period hPeriod matterData kPlus
        kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction
        fields test varied)
      (robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields test varied) 0 := by
  unfold robinCompleteMatterTrueLLEulerCurve
    robinCompleteMatterTrueLLHessian
  exact globalMatterRobinFullLLFirstVariation_second_direction_hasDerivAt
    period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure matter junction fields
    (toFullMatterRobinLLDirections period hPeriod test)
    (toFullMatterRobinLLDirections period hPeriod varied)

/-- Smooth LL direction read from the same extended complete type. -/
def reducedLLSmoothDirection
    (llData : PositiveLLH1Data period hPeriod)
    (variation : ProgramPRobinCompleteVariation4D period hPeriod) :
    LLH1Smooth period hPeriod llData :=
  ⟨variation.complete.independent.llField⟩

/-- Canonical sectorial projection retaining only Robin and the LL field.
Matter, auxiliary-metric and measure LL directions, all other independent
sectors, and all three geometric completion slots become exactly zero. -/
def reducedRobinLLSector
    (variation : ProgramPRobinCompleteVariation4D period hPeriod) :
    ProgramPRobinCompleteVariation4D period hPeriod where
  complete := independentCompleteVariation period hPeriod
    { metrics := { plusLogDirection := 0, minusLogDirection := 0 }
      matter := 0
      gauge := 0
      ghosts := 0
      auxiliaries := 0
      llAuxMetric := 0
      llMeasure := 0
      llField := variation.complete.independent.llField }
  robin := variation.robin

/-- Smooth reduced Fredholm vector read from the same wrapper.  Its scalar
component is explicitly zero. -/
def reducedRobinLLFredholmVector
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (variation : ProgramPRobinCompleteVariation4D period hPeriod) :
    ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData :=
  (staticScalarEnergyEmbedding period hPeriod scalarData 0,
    smoothThroatFieldToL2 period hPeriod robinMeasure variation.robin,
    llH1SmoothEmbedding period hPeriod llData
      (reducedLLSmoothDirection period hPeriod llData variation))

/-- Natural reduced Fredholm pairing pulled back to the same extended type.
Only its zero-scalar Robin + LL projection is read. -/
def reducedRobinLLFredholmPairing
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
    robinMeasure llData
    (reducedRobinLLFredholmVector period hPeriod scalarData robinMeasure llData
      first)
    (reducedRobinLLFredholmVector period hPeriod scalarData robinMeasure llData
      second)

/-- On the canonical smooth Robin + LL sector, the Hessian of the actual
matter + Robin + full LL action equals the pairing of the true reduced
Fredholm Jacobi operator.  This is sectorial, not a full Program-P Hessian. -/
theorem robinCompleteHessian_reducedRobinLL_eq_fredholmPairing
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    [IsFiniteMeasure llData.mu]
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) :
    robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields
        (reducedRobinLLSector period hPeriod first)
        (reducedRobinLLSector period hPeriod second) =
      reducedRobinLLFredholmPairing period hPeriod scalarData kPlus kMinus
        robinMeasure llData first second := by
  simpa [robinCompleteMatterTrueLLHessian,
    toFullMatterRobinLLDirections, reducedRobinLLSector,
    reducedRobinLLFredholmPairing, reducedRobinLLFredholmVector,
    reducedLLSmoothDirection, independentCompleteVariation,
    fullRobinLLDirection, commonRobinLLDirection] using
    (globalMatterRobinFullLLHessian_eq_reducedNatural_robinLL_block
      period hPeriod matterData scalarData kPlus kMinus robinMeasure llData
      first.robin second.robin
      (reducedLLSmoothDirection period hPeriod llData first)
      (reducedLLSmoothDirection period hPeriod llData second))

end
end P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
end JanusFormal
