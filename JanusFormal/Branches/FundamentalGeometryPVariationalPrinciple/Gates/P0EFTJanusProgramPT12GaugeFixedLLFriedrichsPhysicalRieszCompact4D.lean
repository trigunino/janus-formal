import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusDiagonalCompactResolvent
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatRellichCompactness4D

/-!
# Compact transported physical Riesz perturbation

A proper diagonal weight makes the graph-to-`L2` inclusion compact.  Applied
to the signed matter multiplier, this combines with LL Rellich compactness to
make the actual matter--LL readout compact.  Hence the transported physical
Riesz perturbation is compact on the spectral--LL Friedrichs carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszCompact4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalProperShiftFredholm4D
open P0EFTJanusInfiniteL2DiracDomain
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalThroatRellichCompactness4D

/-! ## A reusable proper diagonal graph inclusion -/

section Diagonal

variable {Mode : Type*} [DecidableEq Mode]

private def diagonalMultiplierLinearMap
    (multiplier : Mode → Complex)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1) :
    ComplexDiagonalHilbert Mode →ₗ[Complex] ComplexDiagonalHilbert Mode where
  toFun state := ⟨fun mode => multiplier mode * state mode, by
    refine state.2.mono' ?_
    intro mode
    simpa using
      mul_le_mul_of_nonneg_right (hBound mode) (norm_nonneg (state mode))⟩
  map_add' := by
    intro first second
    ext mode
    simp [mul_add]
  map_smul' := by
    intro scalar state
    ext mode
    simp [mul_left_comm]

private def diagonalMultiplierCLM
    (multiplier : Mode → Complex)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1) :
    ComplexDiagonalHilbert Mode →L[Complex] ComplexDiagonalHilbert Mode :=
  (diagonalMultiplierLinearMap multiplier hBound).mkContinuous 1 (by
    intro state
    rw [one_mul]
    apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
    intro mode
    change ‖multiplier mode * state mode‖ ≤ ‖state mode‖
    rw [norm_mul]
    simpa using
      mul_le_mul_of_nonneg_right (hBound mode) (norm_nonneg (state mode)))

omit [DecidableEq Mode] in
@[simp]
private theorem diagonalMultiplierCLM_apply
    (multiplier : Mode → Complex)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (state : ComplexDiagonalHilbert Mode) (mode : Mode) :
    diagonalMultiplierCLM multiplier hBound state mode =
      multiplier mode * state mode :=
  rfl

private def coordinateRankOne (mode : Mode) :
    ComplexDiagonalHilbert Mode →L[Complex] ComplexDiagonalHilbert Mode :=
  (lp.singleContinuousLinearMap Complex (fun _ : Mode => Complex) 2 mode).comp
    (lp.evalCLM Complex (fun _ : Mode => Complex) 2 mode)

private theorem coordinateRankOne_compact (mode : Mode) :
    IsCompactOperator (coordinateRankOne mode) := by
  exact
    (isCompactOperator_of_locallyCompactSpace_dom
      (lp.evalCLM Complex (fun _ : Mode => Complex) 2 mode)).clm_comp
        (lp.singleContinuousLinearMap Complex
          (fun _ : Mode => Complex) 2 mode)

private def finiteDiagonalTruncation
    (multiplier : Mode → Complex) (modes : Finset Mode) :
    ComplexDiagonalHilbert Mode →L[Complex] ComplexDiagonalHilbert Mode :=
  ∑ mode ∈ modes, multiplier mode • coordinateRankOne mode

@[simp]
private theorem finiteDiagonalTruncation_apply
    (multiplier : Mode → Complex) (modes : Finset Mode)
    (state : ComplexDiagonalHilbert Mode) (mode : Mode) :
    finiteDiagonalTruncation multiplier modes state mode =
      if mode ∈ modes then multiplier mode * state mode else 0 := by
  classical
  induction modes using Finset.induction_on with
  | empty => simp [finiteDiagonalTruncation]
  | @insert inserted modes hInserted hInduction =>
      rw [finiteDiagonalTruncation, Finset.sum_insert hInserted]
      change multiplier inserted *
          (lp.single 2 inserted (state inserted) :
            ComplexDiagonalHilbert Mode) mode +
          finiteDiagonalTruncation multiplier modes state mode = _
      by_cases hMode : mode = inserted
      · subst mode
        rw [hInduction]
        simp [hInserted]
      · rw [lp.single_apply_ne (E := fun _ : Mode => Complex)
            2 inserted (state inserted) hMode,
          mul_zero, zero_add, hInduction]
        simp [hMode]

private theorem finiteDiagonalTruncation_compact
    (multiplier : Mode → Complex) (modes : Finset Mode) :
    IsCompactOperator (finiteDiagonalTruncation multiplier modes) := by
  induction modes using Finset.induction_on with
  | empty =>
      simp [finiteDiagonalTruncation]
      exact isCompactOperator_zero
  | @insert mode modes hMode hInduction =>
      rw [finiteDiagonalTruncation, Finset.sum_insert hMode]
      exact
        ((coordinateRankOne_compact mode).smul (multiplier mode)).add
          hInduction

private theorem diagonal_sub_finiteDiagonalTruncation_norm_le
    (multiplier : Mode → Complex)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (modes : Finset Mode) (ε : Real) (hε : 0 ≤ ε)
    (hTail : ∀ mode, mode ∉ modes → ‖multiplier mode‖ ≤ ε) :
    ‖diagonalMultiplierCLM multiplier hBound -
        finiteDiagonalTruncation multiplier modes‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro state
  rw [← show ‖(ε : Complex) • state‖ = ε * ‖state‖ by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε] using
      (norm_smul (ε : Complex) state)]
  apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
  intro mode
  change ‖multiplier mode * state mode -
      finiteDiagonalTruncation multiplier modes state mode‖ ≤
        ‖(ε : Complex) • state mode‖
  by_cases hMode : mode ∈ modes
  · simp [hMode]
    positivity
  · rw [finiteDiagonalTruncation_apply, if_neg hMode, sub_zero,
      norm_mul, norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
    exact
      mul_le_mul_of_nonneg_right (hTail mode hMode)
        (norm_nonneg (state mode))

private def diagonalMultiplierVanishesAtInfinity
    (multiplier : Mode → Complex) : Prop :=
  ∀ ε : Real, 0 < ε → Set.Finite {mode | ε ≤ ‖multiplier mode‖}

private def decayTruncationModes
    (multiplier : Mode → Complex)
    (hDecay : diagonalMultiplierVanishesAtInfinity multiplier)
    (n : Nat) : Finset Mode :=
  (hDecay (1 / ((n : Real) + 1)) (by positivity)).toFinset

private theorem norm_finiteDecayTruncation_sub_diagonal_le
    (multiplier : Mode → Complex)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (hDecay : diagonalMultiplierVanishesAtInfinity multiplier)
    (n : Nat) :
    ‖finiteDiagonalTruncation multiplier
          (decayTruncationModes multiplier hDecay n) -
        diagonalMultiplierCLM multiplier hBound‖ ≤
      1 / ((n : Real) + 1) := by
  rw [norm_sub_rev]
  apply diagonal_sub_finiteDiagonalTruncation_norm_le
  · positivity
  · intro mode hMode
    have hNotSuperlevel :
        mode ∉ {mode | 1 / ((n : Real) + 1) ≤ ‖multiplier mode‖} := by
      simpa [decayTruncationModes] using hMode
    exact le_of_lt (not_le.mp hNotSuperlevel)

private theorem diagonalMultiplier_compact_of_vanishesAtInfinity
    (multiplier : Mode → Complex)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (hDecay : diagonalMultiplierVanishesAtInfinity multiplier) :
    IsCompactOperator (diagonalMultiplierCLM multiplier hBound) := by
  apply isCompactOperator_of_tendsto
    (l := Filter.atTop)
    (F := fun n : Nat =>
      finiteDiagonalTruncation multiplier
        (decayTruncationModes multiplier hDecay n))
    (f := diagonalMultiplierCLM multiplier hBound)
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero
      (fun n => norm_nonneg _)
      (norm_finiteDecayTruncation_sub_diagonal_le
        multiplier hBound hDecay)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Filter.Eventually.of_forall fun n =>
      finiteDiagonalTruncation_compact multiplier
        (decayTruncationModes multiplier hDecay n)

private def shiftIResolventMultiplier
    (weight : Mode → Real) (mode : Mode) : Complex :=
  1 / ((weight mode : Complex) - Complex.I)

omit [DecidableEq Mode] in
private theorem shiftIResolventMultiplier_norm_le_one
    (weight : Mode → Real) (mode : Mode) :
    ‖shiftIResolventMultiplier weight mode‖ ≤ 1 := by
  unfold shiftIResolventMultiplier
  rw [norm_div, norm_one]
  have hDenPos : 0 < ‖(weight mode : Complex) - Complex.I‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_real_sub_I (weight mode))
  apply (div_le_iff₀ hDenPos).mpr
  simpa using one_le_norm_real_sub_I (weight mode)

omit [DecidableEq Mode] in
private theorem shiftIResolventMultiplier_vanishesAtInfinity
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight) :
    diagonalMultiplierVanishesAtInfinity
      (shiftIResolventMultiplier weight) := by
  intro ε hε
  refine (proper.finite_sublevel (1 / ε)).subset ?_
  intro mode hMode
  change ε ≤ ‖1 / ((weight mode : Complex) - Complex.I)‖ at hMode
  rw [norm_div, norm_one] at hMode
  have hDenPos : 0 < ‖(weight mode : Complex) - Complex.I‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_real_sub_I (weight mode))
  have hMul : ε * ‖(weight mode : Complex) - Complex.I‖ ≤ 1 :=
    (le_div_iff₀ hDenPos).mp hMode
  have hDen : ‖(weight mode : Complex) - Complex.I‖ ≤ 1 / ε := by
    apply (le_div_iff₀ hε).mpr
    simpa [mul_comm] using hMul
  change |weight mode| ≤ 1 / ε
  simpa [Complex.norm_real, Real.norm_eq_abs] using
    (norm_real_le_norm_real_sub_I (weight mode)).trans hDen

private def shiftIResolventCLM (weight : Mode → Real) :
    ComplexDiagonalHilbert Mode →L[Complex] ComplexDiagonalHilbert Mode :=
  diagonalMultiplierCLM (shiftIResolventMultiplier weight)
    (shiftIResolventMultiplier_norm_le_one weight)

private theorem shiftIResolventCLM_compact
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight) :
    IsCompactOperator (shiftIResolventCLM weight) :=
  diagonalMultiplier_compact_of_vanishesAtInfinity
    (shiftIResolventMultiplier weight)
    (shiftIResolventMultiplier_norm_le_one weight)
    (shiftIResolventMultiplier_vanishesAtInfinity weight proper)

private def complexDiagonalGraphShiftICLM (weight : Mode → Real) :
    ComplexDiagonalGraphDomain Mode weight →L[Complex]
      ComplexDiagonalHilbert Mode :=
  complexDiagonalGraphOperatorCLM Mode weight -
    Complex.I • complexDiagonalGraphFstCLM Mode weight

private theorem shiftIResolventCLM_comp_graphShiftI
    (weight : Mode → Real) :
    (shiftIResolventCLM weight).comp
        (complexDiagonalGraphShiftICLM weight) =
      complexDiagonalGraphFstCLM Mode weight := by
  ext state mode
  rw [ContinuousLinearMap.comp_apply]
  simp only [shiftIResolventCLM, diagonalMultiplierCLM_apply,
    complexDiagonalGraphFstCLM_apply]
  have hRelation :
      state.1.2 mode =
        (weight mode : Complex) * state.1.1 mode :=
    complexDiagonalGraphDomain_relation Mode weight state mode
  change
    shiftIResolventMultiplier weight mode *
        (state.1.2 mode - Complex.I * state.1.1 mode) =
      state.1.1 mode
  rw [hRelation]
  rw [show
      (weight mode : Complex) * state.1.1 mode -
          Complex.I * state.1.1 mode =
        ((weight mode : Complex) - Complex.I) * state.1.1 mode by
          exact (sub_mul _ _ _).symm]
  unfold shiftIResolventMultiplier
  rw [one_div, ← mul_assoc,
    inv_mul_cancel₀ (real_sub_I_ne_zero (weight mode)), one_mul]

/-- A proper diagonal multiplier has compact graph-to-ambient inclusion. -/
theorem complexDiagonalGraphFstCLM_compact_of_proper
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight) :
    IsCompactOperator (complexDiagonalGraphFstCLM Mode weight) := by
  rw [← shiftIResolventCLM_comp_graphShiftI weight]
  exact (shiftIResolventCLM_compact weight proper).comp_clm
    (complexDiagonalGraphShiftICLM weight)

def complexDiagonalProperWeight_addConst
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight)
    (constant : Real) :
    ComplexDiagonalProperWeight Mode (fun mode => weight mode + constant) where
  finite_sublevel := by
    intro bound
    apply (proper.finite_sublevel (bound + |constant|)).subset
    intro mode hMode
    calc
      |weight mode| = |(weight mode + constant) - constant| := by
        rw [add_sub_cancel_right]
      _ ≤ |weight mode + constant| + |constant| := abs_sub _ _
      _ ≤ bound + |constant| := add_le_add hMode (le_refl _)

def complexDiagonalProperWeight_finiteProduct
    {Index : Type*} [Finite Index]
    (weight : Mode → Real)
    (proper : ComplexDiagonalProperWeight Mode weight) :
    ComplexDiagonalProperWeight (Index × Mode) (fun mode => weight mode.2) where
  finite_sublevel := by
    intro bound
    apply (Set.finite_univ.prod (proper.finite_sublevel bound)).subset
    rintro ⟨index, mode⟩ hMode
    exact ⟨Set.mem_univ index, hMode⟩

end Diagonal

/-! ## Matter graph and transported physical residual -/

variable (period : Real) (hPeriod : period ≠ 0)

/-- Properness of the exact two-sector matter Hessian multiplier. -/
def programPPrimitiveSpinCMatterHessianWeight_proper
    (massSquared : Real) :
    ComplexDiagonalProperWeight ProgramPPrimitiveSpinCMatterMode
      (programPPrimitiveSpinCMatterHessianWeight
        period hPeriod massSquared) :=
  complexDiagonalProperWeight_finiteProduct
    (fun mode =>
      primitiveSpinCGeometricSignedKineticHessianWeight period hPeriod mode +
        massSquared)
    (complexDiagonalProperWeight_addConst
      (primitiveSpinCGeometricSignedKineticHessianWeight period hPeriod)
      (primitiveSpinCGeometricSignedKineticHessianWeight_proper
        period hPeriod)
      massSquared)

/-- Compact graph-to-`L2` inclusion for the exact signed matter Hessian. -/
theorem programPPrimitiveSpinCMatterGraphFstRealCLM_compact
    (massSquared : Real) :
    IsCompactOperator
      (programPPrimitiveSpinCMatterGraphFstRealCLM
        period hPeriod massSquared) := by
  change IsCompactOperator
    (complexDiagonalGraphFstCLM ProgramPPrimitiveSpinCMatterMode
      (programPPrimitiveSpinCMatterHessianWeight
        period hPeriod massSquared))
  exact complexDiagonalGraphFstCLM_compact_of_proper
    (programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared)
    (programPPrimitiveSpinCMatterHessianWeight_proper
      period hPeriod massSquared)

private theorem isCompactOperator_prod
    {Source First Second : Type*}
    [NormedAddCommGroup Source] [NormedSpace Real Source]
    [NormedAddCommGroup First] [NormedSpace Real First]
    [NormedAddCommGroup Second] [NormedSpace Real Second]
    {first : Source →L[Real] First}
    {second : Source →L[Real] Second}
    (hFirst : IsCompactOperator first)
    (hSecond : IsCompactOperator second) :
    IsCompactOperator (first.prod second) := by
  rw [show first.prod second =
      (ContinuousLinearMap.inl Real First Second).comp first +
        (ContinuousLinearMap.inr Real First Second).comp second by
    ext source <;> simp]
  exact
    (hFirst.clm_comp (ContinuousLinearMap.inl Real First Second)).add
      (hSecond.clm_comp (ContinuousLinearMap.inr Real First Second))

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

section Physical

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

/-- The matter readout from the actual graph is compact. -/
theorem programPT12ActualMatterReadout_compact :
    IsCompactOperator
      (programPT12ActualMatterReadout
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod) := by
  exact
    (programPPrimitiveSpinCMatterGraphFstRealCLM_compact period hPeriod
      couplings.matterMassSquared).comp_clm _

/-- The LL readout from the actual graph is compact by LL Rellich. -/
theorem programPT12ActualLLReadout_compact :
    IsCompactOperator
      (programPT12ActualLLReadout
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod) := by
  exact
    (canonicalLLH1ToFluxL2_isCompact period hPeriod analysis).comp_clm _

/-- The joint actual-to-matter--LL Friedrichs readout is compact. -/
theorem programPT12ActualToFriedrichsMatterLLReadout_compact :
    IsCompactOperator
      (programPT12ActualToFriedrichsMatterLLReadout
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod) := by
  have hProd : IsCompactOperator
      ((programPT12ActualMatterReadout
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod).prod
        (programPT12ActualLLReadout
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod)) :=
    isCompactOperator_prod
      (first := programPT12ActualMatterReadout
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod)
      (second := programPT12ActualLLReadout
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod)
      (programPT12ActualMatterReadout_compact
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod)
      (programPT12ActualLLReadout_compact
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod)
  exact hProd.clm_comp
    (WithLp.prodContinuousLinearEquiv 2 Real
      ProgramPPrimitiveSpinCMatterHilbert
      (CanonicalLLL2 period hPeriod analysis)).symm.toContinuousLinearMap

/-- Pulling the bounded seven-block Riesz operator through the compact
actual readout gives a compact matter--LL residual. -/
theorem programPT12FriedrichsMatterLLPhysicalRieszOperator_compact :
    IsCompactOperator
      (programPT12FriedrichsMatterLLPhysicalRieszOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod) := by
  exact
    (programPT12ActualToFriedrichsMatterLLReadout_compact
      (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod).comp_clm _

/-- The transported physical perturbation is compact on the full
spectral--LL Friedrichs carrier. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_compact
    {iota : Type*} [DecidableEq iota] :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod) := by
  have hMiddle :=
    (programPT12FriedrichsMatterLLPhysicalRieszOperator_compact
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod).comp_clm
      (programPT12GaugeFixedLLFriedrichsMatterLLReadout
        (configuration := configuration) (iota := iota)
          period hPeriod analysis)
  exact hMiddle.clm_comp
    (programPT12GaugeFixedLLFriedrichsMatterLLReadout
      (configuration := configuration) (iota := iota)
        period hPeriod analysis).adjoint

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszCompact4D
end JanusFormal
