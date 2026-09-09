import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Completion4D

/-!
# T05 intrinsic SpinC L1 first variation

The completed intrinsic pairing of Gate 857 gives a continuous bilinear L1
pairing on the maximal graph domain.  Its diagonal is the maximal local
density.  Differentiating that diagonal gives an actual L1-valued local
variation, and integrating it recovers the graph-action Euler covector and
the already proved Frechet derivative of the SpinC action.

This is only the SpinC maximal-graph sector.  It does not assert a full local
jet differential or a terminal T05 result.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Variation4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal lp
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Completion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCMatterL1 :=
  Lp Real 1 (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

local instance spinCMatterIntrinsicL1VariationMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance spinCMatterIntrinsicL1VariationBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance spinCMatterIntrinsicL1VariationFiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance spinCMatterIntrinsicL1VariationHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

/-- Gate 857's intrinsic L1 pairing pulled back to both components of the
maximal SpinC graph. -/
def programPT05SpinCMatterMaximalIntrinsicGraphPairingL1
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared →L[Real]
        SpinCMatterL1 period hPeriod :=
  (programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod).bilinearComp
    (programPPrimitiveSpinCMatterGraphFstRealCLM period hPeriod massSquared)
    (programPPrimitiveSpinCMatterGraphOperatorRealCLM period hPeriod
      massSquared)

@[simp]
theorem programPT05SpinCMatterMaximalIntrinsicGraphPairingL1_apply
    (massSquared : Real)
    (first second : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    programPT05SpinCMatterMaximalIntrinsicGraphPairingL1 period hPeriod
        massSquared first second =
      programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
        first.1.1 second.1.2 := by
  rfl

/-- The genuine L1-valued first variation of the maximal intrinsic density.
It is the polarized derivative of the quadratic diagonal. -/
def programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared →L[Real]
      SpinCMatterL1 period hPeriod :=
  (1 / 2 : Real) •
    (programPT05SpinCMatterMaximalIntrinsicGraphPairingL1 period hPeriod
        massSquared state +
      (programPT05SpinCMatterMaximalIntrinsicGraphPairingL1 period hPeriod
        massSquared).flip state)

@[simp]
theorem programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_apply
    (massSquared : Real)
    (state direction : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
        period hPeriod massSquared state direction =
      (1 / 2 : Real) •
        (programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
            state.1.1 direction.1.2 +
          programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
            direction.1.1 state.1.2) := by
  simp only [programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential,
    smul_apply, add_apply,
    ContinuousLinearMap.flip_apply,
    programPT05SpinCMatterMaximalIntrinsicGraphPairingL1_apply]

/-- The displayed L1 variation is the Frechet derivative of Gate 857's
maximal intrinsic local density map. -/
theorem programPT05SpinCMatterMaximalIntrinsicLocalDensityL1_hasFDerivAt
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    HasFDerivAt
      (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1 period hPeriod
        massSquared)
      (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
        period hPeriod massSquared state)
      state := by
  let pairing := programPT05SpinCMatterMaximalIntrinsicGraphPairingL1
    period hPeriod massSquared
  have hDiagonal :=
    (pairing.hasFDerivAt (x := state)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) state)
  have hScaled := hDiagonal.const_smul (1 / 2 : Real)
  change HasFDerivAt
    (fun current => (1 / 2 : Real) • pairing current current)
    ((1 / 2 : Real) • (pairing state + pairing.flip state)) state
  apply hScaled.congr_fderiv
  ext direction
  simp

/-- Frechet derivative formula for the L1-valued density map. -/
theorem programPT05SpinCMatterMaximalIntrinsicLocalDensityL1_fderiv
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    fderiv Real
        (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1 period hPeriod
          massSquared)
        state =
      programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
        period hPeriod massSquared state :=
  (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1_hasFDerivAt
    period hPeriod massSquared state).fderiv

/-- Integration of the local L1 variation is exactly the graph Euler
covector evaluated on the chosen direction. -/
theorem programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_integralCLM
    (massSquared : Real)
    (state direction : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    L1.integralCLM
        (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
          period hPeriod massSquared state direction) =
      programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
        state direction := by
  rw [programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_apply]
  simp only [map_smul, map_add, smul_eq_mul,
    programPT05SpinCMatterMaximalIntrinsicPairingL1_integral]
  change (1 / 2 : Real) *
      (programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
          state direction +
        programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
          direction state) =
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
      state direction
  rw [programPPrimitiveSpinCMatterGraphForm_comm period hPeriod massSquared
    direction state]
  ring

/-- Integrating the L1 differential gives the same continuous covector as
the already proved Frechet derivative of the graph action. -/
theorem programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_integral_eq_action_fderiv
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    (L1.integralCLM
      (α := EffectiveThroat period hPeriod) (E := Real)
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)).comp
        (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
          period hPeriod massSquared state) =
      fderiv Real
        (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared)
        state := by
  rw [programPPrimitiveSpinCMatterGraphAction_fderiv]
  apply ContinuousLinearMap.ext
  intro direction
  rw [ContinuousLinearMap.comp_apply]
  exact
    programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_integralCLM
      period hPeriod massSquared state direction

/-- Pointwise directional form using the actual integral of the L1 class. -/
theorem programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_integral
    (massSquared : Real)
    (state direction : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    (∫ base,
      programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
        period hPeriod massSquared state direction base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      fderiv Real
          (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared)
          state direction := by
  calc
    (∫ base,
      programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
        period hPeriod massSquared state direction base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        L1.integral
          (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
            period hPeriod massSquared state direction) :=
      (L1.integral_eq_integral _).symm
    _ = L1.integralCLM
          (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
            period hPeriod massSquared state direction) :=
      L1.integral_eq _
    _ = programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
          state direction :=
      programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_integralCLM
        period hPeriod massSquared state direction
    _ = fderiv Real
          (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared)
          state direction := by
      rw [programPPrimitiveSpinCMatterGraphAction_fderiv]

end
end P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Variation4D
end JanusFormal
