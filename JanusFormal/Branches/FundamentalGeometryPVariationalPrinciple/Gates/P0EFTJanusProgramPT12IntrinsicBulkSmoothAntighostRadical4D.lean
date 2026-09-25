import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkGlobalBRSTHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PureAntighostBRSTIsotropic4D

/-! The genuine shared smooth antighost gives a null column of the native
BRST Hessian at the intrinsic base, under the same opposite-weight equation
as the ghost radical. The state differential kills this smooth sector. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostRadical4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkGlobalBRSTHessian4D
open P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismDeDonderOperatorFamily4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPOperatorFamily4D
open P0EFTJanusProgramPT12PureAntighostBRSTIsotropic4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

private theorem scalar_weighted_sum_zero (plus minus value : Real)
    (hWeights : plus + minus = 0) : plus * value + minus * value = 0 := by
  rw [← add_mul, hWeights, zero_mul]

private theorem bilinear_left_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (pairing : E →L[Real] E →L[Real] Real) (test : E) : pairing 0 test = 0 :=
  congrArg (fun functional : E →L[Real] Real => functional test) pairing.map_zero

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Throat period hPeriod) := borel _
local instance : BorelSpace (Throat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) := canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)
local notation "Ghost" => FiniteFrameDiffeomorphismC2Core period hPeriod frame
local notation "Packet" => FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame
local notation "Metric" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "Fields" => FrameFreeDiffeomorphismBRSTFields period hPeriod frame metric
private abbrev AntighostIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "Index" => AntighostIndex period hPeriod
local notation "C0" => C(Q period hPeriod, Real)
local notation "mono" => frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric
local notation "abelian" => frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric
local notation "transition" => finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod frame frame metric
local notation "vectorTransition" => finiteFrameDiffeomorphismC2Transition period hPeriod frame frame metric
local instance : NormedAddCommGroup Metric := inferInstance
local instance : NormedSpace Real Metric := Submodule.normedSpace (GeneralMetricRelativeC2Core period hPeriod frame metric)
local instance : NormedAddCommGroup Ghost := inferInstance
local instance : NormedSpace Real Ghost := inferInstance
local instance : NormedAddCommGroup Packet := inferInstance
local instance : NormedSpace Real Packet := inferInstance
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := inferInstance

private theorem mono_apply (variation : Metric) (first second : Fields) :
    mono variation first second = finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (finiteFrameCanonicalVolumeC0 period hPeriod frame metric variation *
        ((∑ i : Index,
          frameFreeDiffeomorphismDeDonderOperatorFamily period hPeriod frame metric variation
            (finiteFrameTensorC0FirstJetCLM period hPeriod frame metric first.1) i *
              finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame second.2.1 i) -
          (1 / 2 : Real) • (∑ i : Index, ∑ j : Index,
            (finiteFrameMetricC0Coefficient period hPeriod frame metric i j variation *
              finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame first.2.1 i) *
                finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame second.2.1 j) -
          ∑ i : Index,
            frameFreeDiffeomorphismFPOperatorFamily period hPeriod frame metric variation first.2.2.2 i *
              finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame second.2.2.1 i)) := by
  change finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameCanonicalVolumeC0 period hPeriod frame metric variation *
      frameFreeDiffeomorphismBRSTBilinearPolynomial period hPeriod frame metric variation first second) = _
  simp only [frameFreeDiffeomorphismBRSTBilinearPolynomial, sum_apply, sub_apply, smul_apply,
    ContinuousLinearMap.bilinearComp_apply]
  rfl

private theorem mono_antighost_left (variation : Metric) (antighost : Ghost) (test : Fields) :
    mono variation (0, (0, (antighost, 0))) test = 0 := by
  have hTensorZero := (finiteFrameTensorC0FirstJetCLM period hPeriod frame metric).map_zero
  have hDeDonderZero := (frameFreeDiffeomorphismDeDonderOperatorFamily period hPeriod frame metric variation).map_zero
  have hFPZero := (frameFreeDiffeomorphismFPOperatorFamily period hPeriod frame metric variation).map_zero
  have hReadoutZero := (finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).map_zero
  have hIntegralZero := (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).map_zero
  have hFormula := mono_apply period hPeriod variation (0, (0, (antighost, 0))) test
  simp only [hTensorZero, hDeDonderZero, hFPZero, hReadoutZero, Pi.zero_apply,
    zero_mul, mul_zero, Finset.sum_const_zero, smul_zero, sub_zero, hIntegralZero] at hFormula
  exact hFormula

private def antighostPairing (variation : Metric) (ghost antighost : Ghost) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameCanonicalVolumeC0 period hPeriod frame metric variation *
      -(∑ i : Index, frameFreeDiffeomorphismFPOperatorFamily period hPeriod frame metric variation ghost i *
        finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame antighost i))

private theorem mono_antighost_right (variation : Metric) (antighost : Ghost) (test : Fields) :
    mono variation test (0, (0, (antighost, 0))) =
      antighostPairing period hPeriod variation test.2.2.2 antighost := by
  have hReadoutZero := (finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).map_zero
  have hFormula := mono_apply period hPeriod variation test (0, (0, (antighost, 0)))
  simp only [hReadoutZero, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    smul_zero, sub_zero, zero_sub] at hFormula
  exact hFormula

private theorem transition_antighost (antighost : Ghost) :
    transition (0, (antighost, 0)) = (0, (vectorTransition antighost, 0)) := by
  change (vectorTransition 0, (vectorTransition antighost, vectorTransition 0)) = _
  have hZero := (finiteFrameDiffeomorphismC2Transition period hPeriod frame frame metric).map_zero
  rw [hZero]

private theorem mono_transition_antighost_left (variation : Metric) (antighost : Ghost) (test : Fields) :
    mono variation (0, transition (0, (antighost, 0))) test = 0 := by
  have hTransition := congrArg (fun fields : Packet => mono variation (0, fields) test)
    (transition_antighost period hPeriod antighost)
  exact hTransition.trans (mono_antighost_left period hPeriod variation (vectorTransition antighost) test)

private theorem mono_transition_antighost_right (variation : Metric) (antighost : Ghost) (test : Fields) :
    mono variation test (0, transition (0, (antighost, 0))) =
      antighostPairing period hPeriod variation test.2.2.2 (vectorTransition antighost) := by
  have hTransition := congrArg (fun fields : Packet => mono variation test (0, fields))
    (transition_antighost period hPeriod antighost)
  exact hTransition.trans (mono_antighost_right period hPeriod variation (vectorTransition antighost) test)

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance : AddZeroClass Bulk := (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings

private theorem globalBilinear_antighost_left (antighost : Ghost) (test : Bulk) :
    intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings 0
      (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings (0, (antighost, 0))) test = 0 := by
  change abelian 0 0 (intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings test).2 +
    abelian 0 0 (intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings test).2 +
    (candidateAPlusEinsteinKineticWeight couplings *
      mono 0 (0, transition (0, (antighost, 0))) (test.1.1.1.1, transition test.1.1.2.2) +
    candidateAMinusEinsteinKineticWeight couplings *
      mono 0 (0, transition (0, (antighost, 0))) (test.1.1.1.2, transition test.1.1.2.2)) = 0
  have hAbelian := congrArg₂ (fun x y : Real => x + y)
    (bilinear_left_zero (abelian (0 : Metric))
      (intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings test).2)
    (bilinear_left_zero (abelian (0 : Metric))
      (intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings test).2)
  have hDiffeomorphism := congrArg₂ (fun x y : Real =>
    candidateAPlusEinsteinKineticWeight couplings * x + candidateAMinusEinsteinKineticWeight couplings * y)
    (mono_transition_antighost_left period hPeriod 0 antighost (test.1.1.1.1, transition test.1.1.2.2))
    (mono_transition_antighost_left period hPeriod 0 antighost (test.1.1.1.2, transition test.1.1.2.2))
  exact (congrArg₂ (fun x y : Real => x + y) hAbelian hDiffeomorphism).trans (by ring)

private theorem globalBilinear_antighost_right
    (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)
    (antighost : Ghost) (test : Bulk) :
    intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings 0 test
      (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings (0, (antighost, 0))) = 0 := by
  change abelian 0 (intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings test).2 0 +
    abelian 0 (intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings test).2 0 +
    (candidateAPlusEinsteinKineticWeight couplings *
      mono 0 (test.1.1.1.1, transition test.1.1.2.2) (0, transition (0, (antighost, 0))) +
    candidateAMinusEinsteinKineticWeight couplings *
      mono 0 (test.1.1.1.2, transition test.1.1.2.2) (0, transition (0, (antighost, 0)))) = 0
  have hAbelian := congrArg₂ (fun x y : Real => x + y)
    ((abelian (0 : Metric) (intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings test).2).map_zero)
    ((abelian (0 : Metric) (intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings test).2).map_zero)
  have hDiffeomorphism := congrArg₂ (fun x y : Real =>
    candidateAPlusEinsteinKineticWeight couplings * x + candidateAMinusEinsteinKineticWeight couplings * y)
    (mono_transition_antighost_right period hPeriod 0 antighost (test.1.1.1.1, transition test.1.1.2.2))
    (mono_transition_antighost_right period hPeriod 0 antighost (test.1.1.1.2, transition test.1.1.2.2))
  have hZero := hDiffeomorphism.trans
    (scalar_weighted_sum_zero (candidateAPlusEinsteinKineticWeight couplings)
      (candidateAMinusEinsteinKineticWeight couplings) _ hWeights)
  exact (congrArg₂ (fun x y : Real => x + y) hAbelian hZero).trans (by ring)

/-- The full native BRST column vanishes against every bulk test. The
opposite-weight hypothesis is exactly the one used for the ghost radical. -/
theorem intrinsicBulkBRSTHessian_antighost_column_zero
    (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)
    (antighost : Ghost) (test : Bulk) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings (0, (antighost, 0))) test = 0 := by
  have h := intrinsicBulkBRSTHessian_eq_globalBilinear period hPeriod couplings
    (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings (0, (antighost, 0))) test
  have hSum := congrArg₂ (fun x y : Real => x + y)
    (globalBilinear_antighost_left period hPeriod couplings antighost test)
    (globalBilinear_antighost_right period hPeriod couplings hWeights antighost test)
  exact h.trans (hSum.trans (zero_add 0))

def intrinsicBulkPureAntighostBRSTState (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  metricPerturbation := 0
  nonminimal := pureAntighostNonminimal period hPeriod antighost

theorem globalCandidateADiagonalDiffeomorphismBRST_pureAntighost
    (metrics : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    globalCandidateADiagonalDiffeomorphismBRST period hPeriod metrics
      (intrinsicBulkPureAntighostBRSTState period hPeriod antighost) = 0 := by
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · exact (globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap period hPeriod metrics).map_zero
  · rfl

def intrinsicBulkSmoothAntighostInsertion (antighost : GlobalDiffeomorphismAntighostField period hPeriod) : Bulk :=
  intrinsicBulkSmoothBRSTInsertion period hPeriod couplings (intrinsicBulkPureAntighostBRSTState period hPeriod antighost)

theorem intrinsicBulkSmoothAntighostInsertion_injective :
    Function.Injective (intrinsicBulkSmoothAntighostInsertion period hPeriod couplings) := by
  intro first second hEqual
  have h := intrinsicBulkSmoothBRSTInsertion_injective period hPeriod couplings hEqual
  exact congrArg (fun state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod => state.nonminimal.antighost) h

private theorem smoothAntighostInsertion_eq_coefficients
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    intrinsicBulkSmoothAntighostInsertion period hPeriod couplings antighost =
      intrinsicBulkDiffeomorphismInsertion period hPeriod couplings
        (0, (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod ⟨antighost.field⟩, 0)) := by
  have hZero := (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod).map_zero
  change (((
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric 0,
      smoothToGeneralMetricRelativeC2Core period hPeriod frame metric 0),
    (0, (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod 0,
      (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod ⟨antighost.field⟩,
        intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod 0)))), 0), 0) = _
  rw [map_zero, hZero]
  rfl

theorem intrinsicBulkBRSTHessian_smoothAntighost_column_zero
    (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) (test : Bulk) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkSmoothAntighostInsertion period hPeriod couplings antighost) test = 0 := by
  have hInsertion := congrArg (fun input : Bulk => intrinsicBulkBRSTHessian period hPeriod couplings input test)
    (smoothAntighostInsertion_eq_coefficients period hPeriod couplings antighost)
  exact hInsertion.trans (intrinsicBulkBRSTHessian_antighost_column_zero period hPeriod couplings hWeights _ test)

/-- This is the differential on states: a pure antighost has B=0 and hence
zero BRST image. No coordinate/tangent interchange is used. -/
theorem intrinsicBulkSmoothBRST_pureAntighost
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    intrinsicBulkSmoothBRST period hPeriod (intrinsicBulkPureAntighostBRSTState period hPeriod antighost) = 0 :=
  globalCandidateADiagonalDiffeomorphismBRST_pureAntighost period hPeriod _ antighost

theorem intrinsicBulkSmoothBRST_preserves_pureAntighost
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    intrinsicBulkSmoothBRST period hPeriod (intrinsicBulkPureAntighostBRSTState period hPeriod antighost) ∈
      Set.range (intrinsicBulkPureAntighostBRSTState period hPeriod) := by
  refine ⟨0, ?_⟩
  rw [intrinsicBulkSmoothBRST_pureAntighost]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostRadical4D
