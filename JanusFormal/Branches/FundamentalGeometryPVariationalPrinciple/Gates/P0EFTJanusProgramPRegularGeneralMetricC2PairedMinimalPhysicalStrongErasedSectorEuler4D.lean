import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D

/-! # Euler equations in the configuration-erased strong sectors -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedSectorEuler4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartTargetLocalActionDatum4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance globalMinimalPhysicalBulkTangentAddCommGroup :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroup
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModule
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Normal-coordinate test retained by the strong tangent but not by the
physical configuration projection. -/
abbrev RegularGeneralMetricC2PairedMinimalPhysicalStrongNormalTest :=
  Sector → SmoothNormalDisplacement period hPeriod

/-- Diffeomorphism-ghost test retained by the strong tangent but not by the
physical configuration projection. -/
abbrev RegularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostTest :=
  Sector → CInfinityThroatGhost period hPeriod

/-- Both coordinates erased by the current physical-configuration target. -/
abbrev RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest :=
  RegularGeneralMetricC2PairedMinimalPhysicalStrongNormalTest period hPeriod ×
    RegularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostTest
      period hPeriod

def regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection period
    hPeriod configuration (0, (0, (test.1, (test.2, (0, (0, 0))))))

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection_fullMetricPerturbation
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
      hPeriod configuration test).1.completeVariation.fullMetricPerturbation =
        0 :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection_independent
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
      hPeriod configuration test).1.completeVariation.independent = 0 :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection_spinC
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
      hPeriod configuration test).1.2 = 0 :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_fullMetricPerturbation
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) (t : Real) :
    (point + t •
      regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
        hPeriod configuration test).1.completeVariation.fullMetricPerturbation =
      point.1.completeVariation.fullMetricPerturbation := by
  change point.1.completeVariation.fullMetricPerturbation + t •
    (0 : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod) = _
  simp

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_independent
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) (t : Real) :
    (point + t •
      regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
        hPeriod configuration test).1.completeVariation.independent =
      point.1.completeVariation.independent := by
  change point.1.completeVariation.independent + t • 0 = _
  simp

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_spinC
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) (t : Real) :
    (point + t •
      regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
        hPeriod configuration test).1.2 = point.1.2 := by
  change point.1.2 + t • 0 = _
  simp

def regularGeneralMetricC2PairedMinimalPhysicalStrongNormalDirection
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongNormalTest
      period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
    hPeriod configuration (test, 0)

def regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostDirection
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test :
      RegularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostTest
        period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
    hPeriod configuration (0, test)

theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) (t : Real) :
    point + t •
        regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
          hPeriod configuration test ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase := by
  change GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
    plusBase minusBase
      ((point + t •
        regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
          hPeriod configuration test).1.completeVariation.fullMetricPerturbation)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_fullMetricPerturbation]
  exact hPoint

theorem regularGeneralMetricC2PairedMinimalPhysicalStrongNormalLine_mem
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongNormalTest
      period hPeriod) (t : Real) :
    point + t •
        regularGeneralMetricC2PairedMinimalPhysicalStrongNormalDirection period
          hPeriod configuration test ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase := by
  exact regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period
    hPeriod configuration plusBase minusBase point hPoint (test, 0) t

theorem regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostLine_mem
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (test :
      RegularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostTest
        period hPeriod) (t : Real) :
    point + t •
        regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostDirection
          period hPeriod configuration test ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase := by
  exact regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period
    hPeriod configuration plusBase minusBase point hPoint (0, test) t

private theorem globalMetricPerturbationPairLorentzChartGeometry_congr
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (first second : GlobalMetricPerturbationPair period hPeriod)
    (hFirst : GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
      plusBase minusBase first)
    (hSecond : GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
      plusBase minusBase second)
    (h : first = second) :
    globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
        minusBase first hFirst =
      globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
        minusBase second hSecond := by
  subst second
  rfl

/-- The projected physical configuration is constant along both erased
coordinate directions. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedTarget_line
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) (t : Real) :
    regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase
        (point + t •
          regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection
            period hPeriod configuration test)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period
          hPeriod configuration plusBase minusBase point hPoint test t) =
      regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase point hPoint := by
  change GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
    plusBase minusBase point.1.completeVariation.fullMetricPerturbation at hPoint
  unfold regularGeneralMetricC2PairedMinimalPhysicalTarget
  rw [globalMetricPerturbationPairLorentzChartGeometry_congr period hPeriod
    plusBase minusBase _ _
      (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period
        hPeriod configuration plusBase minusBase point hPoint test t) hPoint
      (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_fullMetricPerturbation
        period hPeriod configuration point test t)]
  unfold globalMinimalPhysicalConfigurationAt
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_independent,
    regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_spinC]

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

private theorem regularGeneralMetricC2PairedGravity_congr
    (firstPlus firstMinus secondPlus secondMinus :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hFirst : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase firstPlus firstMinus)
    (hSecond : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase secondPlus secondMinus)
    (hPlus : firstPlus = secondPlus) (hMinus : firstMinus = secondMinus) :
    regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase minusBase
        firstPlus firstMinus hFirst =
      regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase minusBase
        secondPlus secondMinus hSecond ∧
    regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase minusBase
        firstPlus firstMinus hFirst =
      regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase minusBase
        secondPlus secondMinus hSecond := by
  subst secondPlus
  subst secondMinus
  exact ⟨rfl, rfl⟩

private theorem regularGeneralMetricC2PairedTargetLocalActionDatum_congr
    (firstTarget secondTarget : GlobalFieldConfiguration period hPeriod)
    (firstPlus firstMinus secondPlus secondMinus :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hFirst : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase firstPlus firstMinus)
    (hSecond : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase secondPlus secondMinus)
    (hFirstGeometry : firstTarget.geometry =
      regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod plusBase
        minusBase firstPlus firstMinus hFirst)
    (hSecondGeometry : secondTarget.geometry =
      regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod plusBase
        minusBase secondPlus secondMinus hSecond)
    (firstVariation secondVariation :
      Sector → SmoothAbelianGaugePotential period hPeriod)
    (hTarget : firstTarget = secondTarget)
    (hPlus : firstPlus = secondPlus) (hMinus : firstMinus = secondMinus)
    (hVariation : firstVariation = secondVariation) :
    regularGeneralMetricC2PairedTargetLocalActionDatum period hPeriod
        configuration.physical firstTarget couplings data plusBase minusBase
          firstPlus firstMinus hFirst hFirstGeometry firstVariation =
      regularGeneralMetricC2PairedTargetLocalActionDatum period hPeriod
        configuration.physical secondTarget couplings data plusBase minusBase
          secondPlus secondMinus hSecond hSecondGeometry secondVariation := by
  subst secondTarget
  subst secondPlus
  subst secondMinus
  subst secondVariation
  rfl

private theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDatum_line
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) (t : Real) :
    let line := point + t •
      regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
        hPeriod configuration.physical test
    let hLine :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period
        hPeriod configuration.physical plusBase minusBase point hPoint test t
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration.physical couplings data plusBase minusBase).datumAt
        line hLine =
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
        period hPeriod configuration.physical couplings data plusBase minusBase).datumAt
          point hPoint := by
  dsimp only
  unfold regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
  unfold regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn
  dsimp only
  unfold regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum
  apply regularGeneralMetricC2PairedTargetLocalActionDatum_congr period hPeriod
    configuration data plusBase minusBase
  · exact regularGeneralMetricC2PairedMinimalPhysicalStrongErasedTarget_line
      period hPeriod configuration.physical plusBase minusBase point hPoint test t
  · exact congrFun
      (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_fullMetricPerturbation
        period hPeriod configuration.physical point test t) .plus
  · exact congrFun
      (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_fullMetricPerturbation
        period hPeriod configuration.physical point test t) .minus
  · have hFullMetric :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_fullMetricPerturbation
        period hPeriod configuration.physical point test t
    have hGravity := regularGeneralMetricC2PairedGravity_congr period hPeriod
      plusBase minusBase _ _ _ _
        (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period
          hPeriod configuration.physical plusBase minusBase point hPoint test t)
        hPoint (congrFun hFullMetric .plus) (congrFun hFullMetric .minus)
    have hIndependent :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_independent
        period hPeriod configuration.physical point test t
    funext sector
    cases sector
    · simp only [regularGeneralMetricC2PairedMinimalPhysicalGaugeVariation]
      apply congrArg₂ _
      · exact congrArg (fun gravity => gravity.metric) hGravity.1
      · exact congrArg (fun fields => fields.gauge.1) hIndependent
    · simp only [regularGeneralMetricC2PairedMinimalPhysicalGaugeVariation]
      apply congrArg₂ _
      · exact congrArg (fun gravity => gravity.metric) hGravity.2
      · exact congrArg (fun fields => fields.gauge.2) hIndependent

/-- The authentic total action is constant along the two tangent coordinates
erased by the current physical-configuration projection. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedAction_line
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) (t : Real) :
    globalCandidateALocalActionPullback period hPeriod
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        (point + t •
          regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection
            period hPeriod configuration.physical test) =
      globalCandidateALocalActionPullback period hPeriod
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure) point := by
  let hLine :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period
      hPeriod configuration.physical plusBase minusBase point hPoint test t
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongLocalAction_eq_CandidateA
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure _ hLine,
    regularGeneralMetricC2PairedMinimalPhysicalStrongLocalAction_eq_CandidateA
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint]
  exact congrArg
    (fun datum : GlobalCandidateALocalActionDatum period hPeriod couplings
        NonNullFace NullFace =>
      globalCandidateACovariantAction period hPeriod datum.2 measure)
    (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDatum_line period
      hPeriod configuration data plusBase minusBase point hPoint test t)

/-- The total strong Euler covector annihilates every erased direction. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongErasedEuler_apply
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
      period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let chart :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure
  letI chartNormedAddCommGroup : NormedAddCommGroup chart.Model :=
    chart.normedAddCommGroup
  letI chartNormedSpace : NormedSpace Real chart.Model := chart.normedSpace
  let action := globalCandidateALocalActionPullback period hPeriod chart
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection period
      hPeriod configuration.physical test
  have hPoint' : point ∈ chart.family.domain := hPoint
  have hAction := globalCandidateALocalAction_hasFDerivAt period hPeriod chart
    point hPoint'
  have hLine : HasDerivAt (fun t : Real => point + t • direction) direction 0 := by
    have hConstant : HasDerivAt (fun _ : Real => point) 0 0 :=
      hasDerivAt_const (x := (0 : Real)) (c := point)
    have hLinear := (hasDerivAt_id (0 : Real)).smul_const direction
    exact (hConstant.add hLinear).congr_deriv (by simp)
  have hFrechet := hAction.comp_hasDerivAt_of_eq 0 hLine (by simp)
  have hFrechet' :
      HasDerivAt (fun t : Real => action (point + t • direction))
        (globalCandidateALocalEulerLagrangeOperator period hPeriod chart point
          direction) 0 := by
    simpa [Function.comp_def] using hFrechet
  have hFunctions :
      (fun t : Real => action (point + t • direction)) =
        (fun _ : Real => action point) := by
    funext t
    simpa [action, chart] using
      (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedAction_line
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point hPoint test t)
  rw [hFunctions] at hFrechet'
  have hZero := hFrechet'.unique
    (hasDerivAt_const (x := (0 : Real)) (c := action point))
  have hEulerEq :
      globalCandidateALocalEulerLagrangeOperator period hPeriod chart point
          direction =
        regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point
          (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection
            period hPeriod configuration.physical test) := by
    rfl
  exact hEulerEq ▸ hZero

/-- Gate: the current physical target erases the normal and diffeomorphism-
ghost coordinates, so both authentic strong Euler components vanish.  This is
an architectural degeneracy statement, not a new physical field equation. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_erased_sector_euler_gate
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongNormalEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ∧
      regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  constructor
  · apply LinearMap.ext
    intro test
    simp only [LinearMap.zero_apply]
    change regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongNormalDirection period
          hPeriod configuration.physical test) = 0
    exact regularGeneralMetricC2PairedMinimalPhysicalStrongErasedEuler_apply
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint (test, 0)
  · apply LinearMap.ext
    intro test
    simp only [LinearMap.zero_apply]
    change regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostDirection
          period hPeriod configuration.physical test) = 0
    exact regularGeneralMetricC2PairedMinimalPhysicalStrongErasedEuler_apply
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint (0, test)

end
end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedSectorEuler4D
end JanusFormal
