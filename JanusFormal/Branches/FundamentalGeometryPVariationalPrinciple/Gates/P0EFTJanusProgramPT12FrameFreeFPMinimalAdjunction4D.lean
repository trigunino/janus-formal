import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicFPSymmetry4D

/-! Extend actual smooth FP adjunction to both minimal graph domains. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeFPMinimalAdjunction4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
open P0EFTJanusProgramPT12FrameFreeFPClosed4D
open P0EFTJanusProgramPT12FrameFreeFPFormalAdjointCore4D
open P0EFTJanusProgramPT12IntrinsicFPSymmetry4D

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

variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

theorem frameFreeFPMinimal_adjunction :
    (frameFreeFPCanonicalMinimal period hPeriod metric).IsFormalAdjoint
      (frameFreeFPFormalAdjointMinimal period hPeriod metric) := by
  intro first second
  have hFirst := (frameFreeFPCanonicalMinimal period hPeriod metric).mem_graph first
  rw [frameFreeFPCanonicalMinimal_graph] at hFirst
  have hSecond := (frameFreeFPFormalAdjointMinimal period hPeriod metric).mem_graph second
  rw [frameFreeFPFormalAdjointMinimal_graph] at hSecond
  have hClosed : IsClosed {pair : GlobalPairedGaugeLieL2 period hPeriod ×
      GlobalPairedGaugeLieL2 period hPeriod |
      inner Real (frameFreeFPCanonicalMinimal period hPeriod metric first) pair.1 =
        inner Real (first : GlobalPairedGaugeLieL2 period hPeriod) pair.2} := by
    apply isClosed_eq <;> fun_prop
  apply closure_minimal (s := Set.range
    ((globalPairedGaugeLieL2LinearMap period hPeriod).prod
      (pairedFPCanonicalAdjointL2 period hPeriod metric))) ?_ hClosed hSecond
  rintro pair ⟨test, rfl⟩
  exact linearFeatureGraphClosure_pairing
    (globalPairedGaugeLieL2LinearMap period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod metric)
    (pairedFPCanonicalAdjointL2 period hPeriod metric)
    (frameFreePairedFPCanonicalAdjoint_pairing period hPeriod metric) ⟨_, hFirst⟩ test

theorem frameFreeFPFormalAdjointMinimal_le_adjoint :
    frameFreeFPFormalAdjointMinimal period hPeriod metric ≤
      (frameFreeFPCanonicalMinimal period hPeriod metric)† :=
  LinearPMap.IsFormalAdjoint.le_adjoint
    (frameFreeFPCanonicalMinimal_dense_domain period hPeriod metric)
    (frameFreeFPMinimal_adjunction period hPeriod metric)

theorem intrinsicFPMinimal_symmetric :
    (frameFreeFPCanonicalMinimal period hPeriod
      (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod)).IsFormalAdjoint
    (frameFreeFPCanonicalMinimal period hPeriod
      (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod)) := by
  have h := frameFreeFPMinimal_adjunction period hPeriod
    (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod)
  rw [intrinsicFPFormalAdjointMinimal_eq] at h
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeFPMinimalAdjunction4D
