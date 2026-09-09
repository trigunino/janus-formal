import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

/-!
# T05 smooth SpinC matter local-density bridge

The primitive SpinC action already pairs a smooth field with its genuine
first-order expression `2D + m²` and integrates that pairing over the effective
throat.  This module packages the pointwise real part as a continuous local
density and proves that its integral is the existing smooth action.  The
unconditional geometric-Green realization then identifies the same integral
with the closed-graph action used by Gate 828.

The final refinement is deliberately restricted to graph states in the image
of smooth SpinC fields.  No inverse or surjectivity statement for the maximal
coefficient graph is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterSmoothLocalDensityBridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance spinCMatterEffectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance spinCMatterEffectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance spinCMatterCanonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The real pointwise pairing of one smooth SpinC sector with its exact
first-order action Hessian. -/
def programPT05SpinCMatterSmoothSectorLocalDensity
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod)
    (sector : Sector) : C(EffectiveThroat period hPeriod, Real) where
  toFun := fun base =>
    (d9PrimitiveSpinCPointwiseHermitianPairing
      period hPeriod .positiveQuarter
      (state sector)
      (primitiveSpinCGeometricSignedActionHessianSmoothCore
        period hPeriod massSquared (state sector)) base).re
  continuous_toFun :=
    Complex.reCLM.continuous.comp
      (d9PrimitiveSpinCPointwiseHermitianPairing_continuous
        period hPeriod .positiveQuarter
        (state sector)
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared (state sector)))

@[simp]
theorem programPT05SpinCMatterSmoothSectorLocalDensity_apply
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod)
    (sector : Sector) (base : EffectiveThroat period hPeriod) :
    programPT05SpinCMatterSmoothSectorLocalDensity period hPeriod
        massSquared state sector base =
      (d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (state sector)
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared (state sector)) base).re :=
  rfl

/-- The genuine two-sector SpinC matter density on the effective throat. -/
def programPT05SpinCMatterSmoothLocalDensity
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    C(EffectiveThroat period hPeriod, Real) :=
  ContinuousMap.const (EffectiveThroat period hPeriod) (1 / 2 : Real) *
    ∑ sector : Sector,
      programPT05SpinCMatterSmoothSectorLocalDensity period hPeriod
        massSquared state sector

@[simp]
theorem programPT05SpinCMatterSmoothLocalDensity_apply
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod)
    (base : EffectiveThroat period hPeriod) :
    programPT05SpinCMatterSmoothLocalDensity period hPeriod massSquared state
        base =
      (1 / 2 : Real) *
        ∑ sector : Sector,
          (d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            (state sector)
            (primitiveSpinCGeometricSignedActionHessianSmoothCore
              period hPeriod massSquared (state sector)) base).re := by
  simp [programPT05SpinCMatterSmoothLocalDensity]

/-- Canonical throat integral of the smooth SpinC matter density. -/
def programPT05SpinCMatterSmoothLocalDensityIntegral
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) : Real :=
  ∫ base,
    programPT05SpinCMatterSmoothLocalDensity period hPeriod massSquared state
      base
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The local density integrates to the pre-existing smooth SpinC action. -/
theorem programPT05SpinCMatterSmoothLocalDensityIntegral_eq_smoothAction
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
        massSquared state =
      programPPrimitiveSpinCMatterSmoothAction period hPeriod massSquared
        state := by
  unfold programPT05SpinCMatterSmoothLocalDensityIntegral
    programPPrimitiveSpinCMatterSmoothAction
  simp_rw [programPT05SpinCMatterSmoothLocalDensity_apply]
  rw [integral_const_mul, integral_finsetSum Finset.univ]
  · congr 1
    apply Finset.sum_congr rfl
    intro sector _
    unfold d9PrimitiveSpinCGeometricL2Pairing
    exact
      (integral_re
        (d9PrimitiveSpinCPointwiseHermitianPairing_integrable
          period hPeriod .positiveQuarter
          (state sector)
          (primitiveSpinCGeometricSignedActionHessianSmoothCore
            period hPeriod massSquared (state sector))))
  · intro sector _
    exact
      (d9PrimitiveSpinCPointwiseHermitianPairing_integrable
        period hPeriod .positiveQuarter
        (state sector)
        (primitiveSpinCGeometricSignedActionHessianSmoothCore
          period hPeriod massSquared (state sector))).re

/-- On every smooth field, the same local integral is exactly the graph action
selected by the unconditional geometric Green identity. -/
theorem programPT05SpinCMatterSmoothLocalDensityIntegral_eq_graphAction_geometricGreen
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
        massSquared state =
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        ((programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
          period hPeriod massSquared).toGraph state) := by
  rw [programPT05SpinCMatterSmoothLocalDensityIntegral_eq_smoothAction]
  exact
    ((programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
      period hPeriod massSquared).action_agreement state).symm

/-- Evidence that a Gate-828 SpinC frontier is represented by one genuine
smooth field.  This is an image restriction, not a claim about every point of
the maximal graph. -/
structure ProgramPT05BulkSpinCSmoothLocalDensityRefinement
    (couplings : GlobalCandidateAActionCouplings)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared) where
  smoothState : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod
  frontier_eq_toGraph :
    frontier.graphState =
      (programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
        period hPeriod couplings.matterMassSquared).toGraph smoothState

/-- The local density carried by a smooth refinement of a Gate-828 frontier. -/
def ProgramPT05BulkSpinCSmoothLocalDensityRefinement.localDensity
    (couplings : GlobalCandidateAActionCouplings)
    {frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared}
    (refinement : ProgramPT05BulkSpinCSmoothLocalDensityRefinement period
      hPeriod couplings frontier) : C(EffectiveThroat period hPeriod, Real) :=
  programPT05SpinCMatterSmoothLocalDensity period hPeriod
    couplings.matterMassSquared refinement.smoothState

/-- Integrating a smooth refinement recovers the exact Gate-828 frontier
action. -/
theorem ProgramPT05BulkSpinCSmoothLocalDensityRefinement.integral_eq_frontierAction
    (couplings : GlobalCandidateAActionCouplings)
    {frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared}
    (refinement : ProgramPT05BulkSpinCSmoothLocalDensityRefinement period
      hPeriod couplings frontier) :
    programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
        couplings.matterMassSquared refinement.smoothState =
      programPT05BulkSpinCFrontierAction period hPeriod couplings frontier := by
  rw [programPT05SpinCMatterSmoothLocalDensityIntegral_eq_graphAction_geometricGreen]
  unfold programPT05BulkSpinCFrontierAction
  rw [refinement.frontier_eq_toGraph]

/-- Gate 828's mixed evaluation becomes a sum of three actual density
integrals whenever its SpinC frontier carries a smooth refinement. -/
theorem programPT05BulkActionLocalDensityEvaluation_eq_smoothSpinCDensity
    (couplings : GlobalCandidateAActionCouplings)
    (packet : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (refinement : ProgramPT05BulkSpinCSmoothLocalDensityRefinement period
      hPeriod couplings packet.spinCFrontier) :
    programPT05BulkActionLocalDensityEvaluation period hPeriod couplings
        packet =
      (finiteFrameBRSTCanonicalIntegralCLM period hPeriod
          (programPT05BulkSpacetimeDensity period hPeriod couplings packet) +
        programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
          couplings.matterMassSquared refinement.smoothState) +
        programPT05LLDensityIntegral period hPeriod
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
          packet.llDensity := by
  unfold programPT05BulkActionLocalDensityEvaluation
  rw [refinement.integral_eq_frontierAction]

end
end P0EFTJanusProgramPT05SpinCMatterSmoothLocalDensityBridge4D
end JanusFormal
