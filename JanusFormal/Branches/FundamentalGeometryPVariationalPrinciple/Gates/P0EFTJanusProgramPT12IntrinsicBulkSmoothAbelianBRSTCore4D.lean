import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkActionCore4D

/-! Faithful realization of the existing paired smooth Abelian BRST fields in
the intrinsic bulk core. The native sign convention is `sA = -dc`. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothAbelianBRSTCore4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameMetricContraction4D P0EFTJanusFiniteFrameLorenzCovariantTrace4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
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
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)

private theorem smoothPotentialCoefficients_injective :
    Function.Injective (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame) := by
  intro first second hEqual
  have hCoefficient (component : Fin 2) (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
      finiteFramePotentialCoefficient period hPeriod frame first component index =
        finiteFramePotentialCoefficient period hPeriod frame second component index :=
    smoothToCanonicalPhysicalScalarC2JetCore_injective period hPeriod
      (congrFun (congrFun hEqual component) index)
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  have hForms : first.toFun component point = second.toFun component point := by
    rw [finiteFrameCovector_reconstructs period hPeriod frame base point (first.toFun component point),
      finiteFrameCovector_reconstructs period hPeriod frame base point (second.toFun component point)]
    apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun coefficient : Real => coefficient •
      P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D.generalMetricFiniteFrameCoefficientAt
        period hPeriod frame base point index)
      (congrArg (fun field : SmoothQuotientField period hPeriod Real => field point)
        (hCoefficient component index))
  exact congrArg (fun covector => covector tangent) hForms

private theorem smoothGhostCoefficients_injective :
    Function.Injective (finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod) := by
  intro first second hEqual
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply PiLp.ext
  intro component
  exact congrArg (fun field : SmoothQuotientField period hPeriod Real => field point)
    (smoothToCanonicalPhysicalScalarC2JetCore_injective period hPeriod (congrFun hEqual component))

private theorem smoothPotentialCoefficients_zero :
    finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame 0 = 0 := by
  funext component index
  have hCoefficient : finiteFramePotentialCoefficient period hPeriod frame 0 component index = 0 := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod _ = 0
  rw [hCoefficient]
  exact (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_zero

private theorem smoothGhostCoefficients_zero :
    finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod 0 = 0 := by
  funext component
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (ghostComponent period hPeriod 0 component) = 0
  rw [ghostComponent_zero]
  exact (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_zero

variable (couplings : GlobalCandidateAActionCouplings)
local instance coreNormedAddCommGroup : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : AddZeroClass (IntrinsicBulkCore period hPeriod couplings) :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass

/-- Native smooth Abelian core builders, with the other bulk fields set to zero. -/
def intrinsicBulkSmoothAbelianBRSTInsertion
    (state : GlobalPairedAbelianBRSTState period hPeriod) : IntrinsicBulkCore period hPeriod couplings :=
  let plus := finiteFrameSmoothAbelianBRSTCore period hPeriod frame base 0
    (state.potential .plus) (state.nonminimal .plus)
  let minus := finiteFrameSmoothAbelianBRSTCore period hPeriod frame base 0
    (state.potential .minus) (state.nonminimal .minus)
  ((((plus.1, minus.1), ((plus.2, minus.2), 0)), 0), 0)

theorem intrinsicBulkSmoothAbelianBRSTInsertion_metric
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings state).1.1.1 = 0 := by
  change (smoothToGeneralMetricRelativeC2Core period hPeriod frame base 0,
    smoothToGeneralMetricRelativeC2Core period hPeriod frame base 0) = 0
  simp only [(smoothToGeneralMetricRelativeC2Core period hPeriod frame base).map_zero]
  rfl

theorem intrinsicBulkSmoothAbelianBRSTInsertion_other_fields
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    ((intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings state).1.1.2.2,
      ((intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings state).1.2,
       (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings state).2)) = 0 := rfl

theorem intrinsicBulkSmoothAbelianBRSTInsertion_injective :
    Function.Injective (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings) := by
  intro first second hEqual
  have hFields (sector : Sector) :
      (finiteFrameSmoothAbelianBRSTCore period hPeriod frame base 0
        (first.potential sector) (first.nonminimal sector)).2 =
      (finiteFrameSmoothAbelianBRSTCore period hPeriod frame base 0
        (second.potential sector) (second.nonminimal sector)).2 := by
    cases sector with
    | plus => exact congrArg (fun input : IntrinsicBulkCore period hPeriod couplings => input.1.1.2.1.1) hEqual
    | minus => exact congrArg (fun input : IntrinsicBulkCore period hPeriod couplings => input.1.1.2.1.2) hEqual
  apply GlobalPairedAbelianBRSTState.ext
  · funext sector
    exact smoothPotentialCoefficients_injective period hPeriod (congrArg Prod.fst (hFields sector))
  · funext sector
    apply GlobalAbelianNonminimalFields.ext
    · apply GlobalAbelianGhostField.ext
      exact smoothGhostCoefficients_injective period hPeriod (congrArg (fun fields => fields.2.2.2) (hFields sector))
    · apply GlobalAbelianAntighostField.ext
      exact smoothGhostCoefficients_injective period hPeriod (congrArg (fun fields => fields.2.2.1) (hFields sector))
    · apply GlobalAbelianNakanishiLautrupField.ext
      exact smoothGhostCoefficients_injective period hPeriod (congrArg (fun fields => fields.2.1) (hFields sector))

/-- Exact physical column of the existing differential, with its native minus sign. -/
theorem intrinsicBulkSmoothAbelianBRSTInsertion_BRST_potential
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    ((intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
        (globalPairedAbelianBRST period hPeriod state)).1.1.2.1.1.1,
      (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
        (globalPairedAbelianBRST period hPeriod state)).1.1.2.1.2.1) =
      (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame
        (-exactGaugePotential period hPeriod (state.nonminimal .plus).ghost.field),
       finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame
        (-exactGaugePotential period hPeriod (state.nonminimal .minus).ghost.field)) := rfl

theorem intrinsicBulkSmoothAbelianBRSTInsertion_BRST_nonminimal
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    ((intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
        (globalPairedAbelianBRST period hPeriod state)).1.1.2.1.1.2,
      (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
        (globalPairedAbelianBRST period hPeriod state)).1.1.2.1.2.2) =
      ((0, (finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod
          (state.nonminimal .plus).nakanishiLautrup.field, 0)),
       (0, (finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod
          (state.nonminimal .minus).nakanishiLautrup.field, 0))) := by
  dsimp only [intrinsicBulkSmoothAbelianBRSTInsertion, finiteFrameSmoothAbelianBRSTCore,
    globalPairedAbelianBRST, globalAbelianNonminimalBRST,
    zeroGlobalAbelianGhostField, zeroGlobalAbelianNakanishiLautrupField]
  simp only [smoothGhostCoefficients_zero]

theorem intrinsicBulkSmoothAbelianBRSTInsertion_zero :
    intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
      (zeroGlobalPairedAbelianBRSTState period hPeriod) = 0 := by
  dsimp only [intrinsicBulkSmoothAbelianBRSTInsertion, finiteFrameSmoothAbelianBRSTCore,
    zeroGlobalPairedAbelianBRSTState, zeroGlobalAbelianNonminimalFields,
    zeroGlobalAbelianGhostField, zeroGlobalAbelianAntighostField, zeroGlobalAbelianNakanishiLautrupField]
  simp only [smoothPotentialCoefficients_zero, smoothGhostCoefficients_zero,
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame base).map_zero]
  rfl

theorem intrinsicBulkSmoothAbelianBRSTInsertion_BRST_square_zero
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
      (globalPairedAbelianBRST period hPeriod (globalPairedAbelianBRST period hPeriod state)) = 0 :=
  (congrArg (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings)
    (globalPairedAbelianBRST_square_zero period hPeriod state)).trans
      (intrinsicBulkSmoothAbelianBRSTInsertion_zero period hPeriod couplings)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothAbelianBRSTCore4D
