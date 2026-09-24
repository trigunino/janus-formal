import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicTemporalGradient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicTemporalLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

/-! A genuine time-first stereographic holonomic patch and its intrinsic
metric density. The patch is a local diffeomorphism, not a global frame. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalHolonomicPatch4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusCanonicalHolonomicStereographicInverse4D
open P0EFTJanusCanonicalStereographicIntrinsicMetric4D
open P0EFTJanusProgramPT12IntrinsicTemporalLocalDivergence4D

private abbrev Vector4 := Fin 4 → Real
private abbrev Coordinates := EuclideanSpace Real (Fin 3) × Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev QuotientSpace := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (QuotientSpace period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (QuotientSpace period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem holonomicCoordinateEquiv_symm_time (coordinate : Vector4) :
    (holonomicCoordinateEquiv.symm coordinate).2 = coordinate 0 :=
  congrFun (holonomicCoordinateEquiv.apply_symm_apply coordinate) 0

theorem holonomicCoordinateEquiv_symm_spatial (coordinate : Vector4) (index : Fin 3) :
    (holonomicCoordinateEquiv.symm coordinate).1 index = coordinate index.succ :=
  congrFun (holonomicCoordinateEquiv.apply_symm_apply coordinate) index.succ

theorem holonomicCoordinateEquiv_symm_single (index : Fin 4) :
    holonomicCoordinateEquiv.symm (Pi.single index 1) = tangentCoordinate index := by
  apply holonomicCoordinateEquiv.injective
  rw [holonomicCoordinateEquiv.apply_symm_apply]
  ext coefficient
  simp [holonomicCoordinateEquiv_apply, holonomicVectorCoefficient_tangentCoordinate,
    Pi.single_apply, eq_comm]

private theorem holonomicCoordinateEquiv_symm_localDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf Real Vector4) coverModelWithCorners ∞
      holonomicCoordinateEquiv.symm := by
  have hSelf : IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Coordinates) ∞ holonomicCoordinateEquiv.symm :=
    holonomicCoordinateEquiv.symm.toDiffeomorph.isLocalDiffeomorph
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hSelf
  exact hSelf

private theorem holonomicCoordinateEquiv_symm_mfderiv (coordinate : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        holonomicCoordinateEquiv.symm coordinate =
      holonomicCoordinateEquiv.symm.toContinuousLinearMap := by
  have hSelf : mfderiv (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Coordinates) holonomicCoordinateEquiv.symm coordinate =
      holonomicCoordinateEquiv.symm.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact holonomicCoordinateEquiv.symm.hasFDerivAt.fderiv
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hSelf
  exact hSelf

/-- The actual stereographic physical map with time as coordinate zero. -/
def intrinsicTemporalHolonomicPatch (shift : Real) (pole : StandardSphere) :
    SmoothHolonomicFrameChart4 period hPeriod :=
  smoothHolonomicFrameChart4OfLocalDiffeomorph period hPeriod
    (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘
      holonomicCoordinateEquiv.symm) (by
    intro coordinate
    exact IsLocalDiffeomorphAt.comp
      (I := modelWithCornersSelf Real Vector4)
      (J := coverModelWithCorners) (K := coverModelWithCorners)
      (M := Vector4) (N := Coordinates) (P := QuotientSpace period hPeriod) (n := ∞)
      (holonomicCoordinateEquiv_symm_localDiffeomorph coordinate)
      (shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph_smooth
        period hPeriod shift pole (holonomicCoordinateEquiv.symm coordinate)))

@[simp] theorem intrinsicTemporalHolonomicPatch_coordinateMap
    (shift : Real) (pole : StandardSphere) (coordinate : Vector4) :
    (intrinsicTemporalHolonomicPatch period hPeriod shift pole).coordinateMap coordinate =
      shiftedStereographicPhysicalMapAmbient period hPeriod shift pole
        (holonomicCoordinateEquiv.symm coordinate) := rfl

theorem intrinsicTemporalHolonomicPatch_mfderiv
    (shift : Real) (pole : StandardSphere) (coordinate vector : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        (intrinsicTemporalHolonomicPatch period hPeriod shift pole).coordinateMap coordinate vector =
      mfderiv coverModelWithCorners coverModelWithCorners
        (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole)
        (holonomicCoordinateEquiv.symm coordinate) (holonomicCoordinateEquiv.symm vector) := by
  change mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
    (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘
      holonomicCoordinateEquiv.symm) coordinate vector = _
  rw [mfderiv_comp coordinate
    ((shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph_smooth
      period hPeriod shift pole).mdifferentiable (by simp) _)
    (holonomicCoordinateEquiv_symm_localDiffeomorph.mdifferentiable (by simp) coordinate),
    holonomicCoordinateEquiv_symm_mfderiv]
  rfl

theorem intrinsicTemporalHolonomicPatch_metricMatrix
    (shift : Real) (pole : StandardSphere) (coordinate : Vector4) :
    localMetricMatrix period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (intrinsicTemporalHolonomicPatch period hPeriod shift pole) coordinate =
      Matrix.diagonal (fun index : Fin 4 => if index = 0 then -1 else
        (4 / ((∑ index : Fin 3, coordinate index.succ ^ 2) + 4)) ^ 2) := by
  classical
  have hNorm : ‖(holonomicCoordinateEquiv.symm coordinate).1‖ ^ 2 =
      ∑ index : Fin 3, coordinate index.succ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [holonomicCoordinateEquiv_symm_spatial]
  ext first second
  change (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor _
    ((intrinsicTemporalHolonomicPatch period hPeriod shift pole).frame coordinate first)
    ((intrinsicTemporalHolonomicPatch period hPeriod shift pole).frame coordinate second) = _
  rw [(intrinsicTemporalHolonomicPatch period hPeriod shift pole).frame_eq_coordinateDerivative,
    (intrinsicTemporalHolonomicPatch period hPeriod shift pole).frame_eq_coordinateDerivative,
    intrinsicTemporalHolonomicPatch_mfderiv, intrinsicTemporalHolonomicPatch_mfderiv,
    holonomicCoordinateEquiv_symm_single, holonomicCoordinateEquiv_symm_single]
  change (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
    (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole
      (holonomicCoordinateEquiv.symm coordinate)) _ _ = _
  rw [shiftedStereographicPhysicalMapAmbient_intrinsic_metric, hNorm]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  fin_cases first <;> fin_cases second <;>
    norm_num [Matrix.diagonal, tangentCoordinate] <;>
    simp only [Fin.ext_iff] <;> norm_num

/-- The local density is computed from the same intrinsic tensor. -/
theorem intrinsicTemporalHolonomicPatch_volumeFactor
    (shift : Real) (pole : StandardSphere) (coordinate : Vector4) :
    localMetricVolumeFactor period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (intrinsicTemporalHolonomicPatch period hPeriod shift pole) coordinate =
      intrinsicTemporalCoordinateDensity coordinate := by
  let factor : Real := 4 / ((∑ index : Fin 3, coordinate index.succ ^ 2) + 4)
  have hDet : (localMetricMatrix period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (intrinsicTemporalHolonomicPatch period hPeriod shift pole) coordinate).det =
      -(factor ^ 6) := by
    rw [intrinsicTemporalHolonomicPatch_metricMatrix, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ, factor]
    ring
  rw [localMetricVolumeFactor, hDet, abs_neg, abs_of_nonneg (by positivity)]
  change Real.sqrt (factor ^ 6) = factor ^ 3
  have hFactor : 0 ≤ factor := by dsimp [factor]; positivity
  rw [show factor ^ 6 = (factor ^ 3) ^ 2 by ring, Real.sqrt_sq (pow_nonneg hFactor 3)]

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalHolonomicPatch4D
