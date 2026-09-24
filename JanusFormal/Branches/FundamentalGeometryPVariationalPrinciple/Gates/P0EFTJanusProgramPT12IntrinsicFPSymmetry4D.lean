import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFPFormalAdjointCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D

/-! The genuine intrinsic FP has no canonical-volume adjoint correction or mixed signed ghost
defect. Equality of minimal closures below does not assert maximal self-adjointness. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicFPSymmetry4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
open P0EFTJanusProgramPT12FrameFreeFPClosed4D
open P0EFTJanusProgramPT12FrameFreeFPFormalAdjointCore4D
open P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

theorem intrinsicFPFormalAdjoint_eq
    (field : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    canonicalFPFormalAdjoint period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod) field =
      globalGeneralMetricAbelianFaddeevPopov period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) field := by
  have hWeight : smoothGaugeWeight period hPeriod
      (inverseSmoothMetricRatio period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod))
      field = field := by
    apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
    intro point
    change (globalMetricVolumeRatio period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) point)⁻¹ • field point = field point
    rw [globalMetricVolumeRatio_intrinsic, inv_one, one_smul]
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply PiLp.ext
  intro component
  rw [canonicalFPFormalAdjoint_apply, globalMetricVolumeRatio_intrinsic, hWeight, one_mul]

theorem intrinsicPairedFPFormalAdjointL2_eq :
    pairedFPCanonicalAdjointL2 period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) =
      globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) := by
  apply LinearMap.ext
  intro field
  change globalPairedGaugeLieL2LinearMap period hPeriod
      (fun sector => canonicalFPFormalAdjoint period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) (field sector)) = _
  simp_rw [intrinsicFPFormalAdjoint_eq]
  rfl

theorem intrinsicPairedFP_pairing_symmetric
    (field test : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real (globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) field)
      (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod field)
      (globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) test) := by
  have h := frameFreePairedFPCanonicalAdjoint_pairing period hPeriod
    (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) field test
  rw [intrinsicPairedFPFormalAdjointL2_eq] at h
  exact h

theorem intrinsicPairedFPSkewIntegral_zero
    (field test : GlobalPairedGaugeLieSmooth period hPeriod) :
    intrinsicPairedFPSkewIntegral period hPeriod field test = 0 :=
  (intrinsicPairedFP_symmetric_iff_skewIntegral_zero period hPeriod field test).mp
    (intrinsicPairedFP_pairing_symmetric period hPeriod field test)

theorem intrinsicFPFormalAdjointMinimal_eq :
    frameFreeFPFormalAdjointMinimal period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) =
      frameFreeFPCanonicalMinimal period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) := by
  unfold frameFreeFPFormalAdjointMinimal frameFreeFPCanonicalMinimal
  rw [intrinsicPairedFPFormalAdjointL2_eq]

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicFPSymmetry4D
