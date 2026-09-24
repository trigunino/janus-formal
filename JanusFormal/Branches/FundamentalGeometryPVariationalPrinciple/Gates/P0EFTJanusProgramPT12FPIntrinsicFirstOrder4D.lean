import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FPVolumeFirstOrder4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorenzSmoothScalarLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothInverseMusical4D

/-! Intrinsic coefficients of the actual FP canonical-volume correction. -/
namespace JanusFormal.P0EFTJanusProgramPT12FPIntrinsicFirstOrder4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D
open P0EFTJanusLorenzSmoothScalarLeibniz4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12FPVolumeFirstOrder4D
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D
open P0EFTJanusScalarStressCovariantJetConservation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Duplicate a scalar in both abelian components to read the scalar FP operator. -/
def scalarDiagonalGhost (field : SmoothScalarField period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun := fun point => WithLp.toLp 2 fun _ : Fin 2 => field point
  contMDiff_toFun :=
    (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin 2 => Real)).symm.contDiff.contMDiff.comp
      (contMDiff_pi_space.mpr (fun _ => field.contMDiff_toFun))

@[simp] theorem ghostComponent_scalarDiagonalGhost
    (field : SmoothScalarField period hPeriod) (component : Fin 2) :
    ghostComponent period hPeriod (scalarDiagonalGhost period hPeriod field) component = field := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

def actualFPScalarWave (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod) : SmoothScalarField period hPeriod :=
  ghostComponent period hPeriod (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric
    (scalarDiagonalGhost period hPeriod field)) 0

theorem actualFPScalarWave_local (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    actualFPScalarWave period hPeriod metric field (patch.coordinateMap coordinate) =
      covariantScalarJetWave (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch field coordinate) := by
  change globalGeneralMetricAbelianFaddeevPopov period hPeriod metric
    (scalarDiagonalGhost period hPeriod field) (patch.coordinateMap coordinate) 0 = _
  rw [globalGeneralMetricAbelianFaddeevPopov_apply_local, ghostComponent_scalarDiagonalGhost]

def actualFPScalarGradient (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod) : SmoothTangentField period hPeriod :=
  effectiveD8SmoothInverseMusical ⟨period, hPeriod⟩ metric
    (effectiveD8SmoothScalarDifferential ⟨period, hPeriod⟩ field)

theorem actualFPScalarGradient_pairing_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    scalarDifferential period hPeriod first (patch.coordinateMap coordinate)
        (actualFPScalarGradient period hPeriod metric second (patch.coordinateMap coordinate)) =
      covariantScalarGradientPairing (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch first coordinate)
        (localCovariantScalarJet period hPeriod metric patch second coordinate) := by
  have h := scalarDifferential_inverseMetricSharp_eq_local period hPeriod metric first
    (exactGaugePotential period hPeriod (scalarDiagonalGhost period hPeriod second)) 0 patch coordinate
  have hDifferential :
      (exactGaugePotential period hPeriod (scalarDiagonalGhost period hPeriod second)).toFun
        0 (patch.coordinateMap coordinate) =
      scalarDifferential period hPeriod second (patch.coordinateMap coordinate) := by
    simp only [exactGaugePotential, ghostComponent_scalarDiagonalGhost]
    rfl
  rw [hDifferential] at h
  change scalarDifferential period hPeriod first (patch.coordinateMap coordinate)
    (inverseMetricSharp period hPeriod metric (patch.coordinateMap coordinate)
      (scalarDifferential period hPeriod second (patch.coordinateMap coordinate))) = _
  rw [h]
  simp only [localRaisedAbelianGaugePotential, Matrix.mulVec, dotProduct,
    localGaugeCoefficient_exact, ghostComponent_scalarDiagonalGhost]
  change (∑ i, localScalarGradient period hPeriod first patch coordinate i *
    ∑ j, (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ i j *
      localScalarGradient period hPeriod second patch coordinate j) = _
  unfold covariantScalarGradientPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change _ = (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ i j *
    localScalarGradient period hPeriod first patch coordinate i *
    localScalarGradient period hPeriod second patch coordinate j
  ring

/-- Global first-order formula with smooth coefficients fixed by the actual metric. -/
theorem canonicalFPFormalAdjoint_eq_intrinsic_firstOrder
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod) :
    canonicalFPFormalAdjoint period hPeriod metric ghost point component =
      globalGeneralMetricAbelianFaddeevPopov period hPeriod metric ghost point component +
        globalMetricVolumeRatio period hPeriod metric point *
          (ghost point component * actualFPScalarWave period hPeriod metric
            (inverseSmoothMetricRatio period hPeriod metric) point +
          2 * scalarDifferential period hPeriod (ghostComponent period hPeriod ghost component) point
            (actualFPScalarGradient period hPeriod metric
              (inverseSmoothMetricRatio period hPeriod metric) point)) := by
  obtain ⟨patch, coordinate, hPoint⟩ :=
    P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D.canonicalHolonomicChartThroughEveryPoint
      period hPeriod point
  rw [← hPoint, canonicalFPFormalAdjoint_eq_fp_add_firstOrder]
  unfold fpVolumeCorrectionLocal
  rw [actualFPScalarWave_local, actualFPScalarGradient_pairing_local,
    covariantScalarGradientPairing_symmetric]

end
end JanusFormal.P0EFTJanusProgramPT12FPIntrinsicFirstOrder4D
