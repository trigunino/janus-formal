import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalCovectorCollarDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D

/-!
# Adapted holonomic current component and the genuine normal flux
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeAdaptedHolonomicGreenCurrentFlux4D

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarStressEnergyCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D
open P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance cutBulkIsManifold :
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobal_isManifold period hPeriod

abbrev Vector4 := Fin 4 → Real

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem localMetricMatrix_adapted_zero_row
    (base : CanonicalLatitudeBase) (normal : Real)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (index : Fin 4) :
    localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) 0 0 index =
      if index = 0 then 1 else 0 := by
  by_cases hIndex : index = 0
  · subst index
    simp only [if_pos]
    unfold localMetricMatrix localMetricCoefficient
    change (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
      (chart.coordinateMap 0)
      ((chart.toSmoothHolonomicFrameChart4 period hPeriod).frame 0 0)
      ((chart.toSmoothHolonomicFrameChart4 period hPeriod).frame 0 0) = 1
    rw [chart.at_zero, chart.frame_zero_normal]
    exact intrinsicMetric_canonicalLatitudeNormalVector_self
      period hPeriod base normal
  · rw [if_neg hIndex]
    unfold localMetricMatrix localMetricCoefficient
    change (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
      (chart.coordinateMap 0)
      ((chart.toSmoothHolonomicFrameChart4 period hPeriod).frame 0 0)
      ((chart.toSmoothHolonomicFrameChart4 period hPeriod).frame 0 index) = 0
    rw [chart.at_zero, chart.frame_zero_normal]
    let tangent :=
      (chart.toSmoothHolonomicFrameChart4 period hPeriod).frame 0 index
    have hFlat := congrArg
      (fun linearMap =>
        linearMap (canonicalLatitudeNormalVector period hPeriod base normal))
      ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical_eq_tensor
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal))
    exact (DFunLike.congr_fun hFlat tangent).symm.trans
      (chart.frame_tangential period hPeriod index hIndex)

theorem localInverseMetricMatrix_adapted_zero_row
    (base : CanonicalLatitudeBase) (normal : Real)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (index : Fin 4) :
    Ring.inverse
        (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          (chart.toSmoothHolonomicFrameChart4 period hPeriod) 0) 0 index =
      if index = 0 then 1 else 0 := by
  let patch := chart.toSmoothHolonomicFrameChart4 period hPeriod
  let matrix := localMetricMatrix period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch 0
  have hDet : IsUnit matrix.det :=
    isUnit_iff_ne_zero.mpr
      (localMetricMatrix_det_ne_zero period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch 0)
  have hProduct := Matrix.mul_nonsing_inv matrix hDet
  rw [Matrix.nonsing_inv_eq_ringInverse] at hProduct
  have hEntry := congrArg (fun product => product 0 index) hProduct
  simpa [Matrix.mul_apply, Matrix.one_apply, eq_comm, matrix, patch,
    localMetricMatrix_adapted_zero_row] using hEntry

theorem localScalarRepresentative_adapted_zero
    (base : CanonicalLatitudeBase) (normal : Real)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (field : SmoothScalarField period hPeriod) :
    localScalarRepresentative period hPeriod field
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) 0 =
      canonicalLatitudeValue period hPeriod field base normal := by
  unfold localScalarRepresentative canonicalLatitudeValue canonicalNormalSlice
  change field (chart.coordinateMap 0) = _
  rw [chart.at_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem localScalarGradient_adapted_zero_normal
    (base : CanonicalLatitudeBase) (normal : Real)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (field : SmoothScalarField period hPeriod) :
    localScalarGradient period hPeriod field
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) 0 0 =
      canonicalLatitudeDerivative period hPeriod field base normal := by
  let patch := chart.toSmoothHolonomicFrameChart4 period hPeriod
  have hField : MDifferentiableAt coverModelWithCorners 𝓘(Real, Real)
      field (chart.coordinateMap 0) :=
    field.contMDiff_toFun.mdifferentiableAt (by simp)
  have hChart : MDifferentiableAt (modelWithCornersSelf Real Vector4)
      coverModelWithCorners chart.coordinateMap 0 :=
    chart.isLocalDiffeomorph.contMDiff.mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply 0 hField hChart (Pi.single (0 : Fin 4) 1)
  have hMap : field ∘ chart.coordinateMap =
      localScalarRepresentative period hPeriod field patch := by
    rfl
  rw [hMap, mfderiv_eq_fderiv] at hChain
  change localScalarGradient period hPeriod field patch 0 0 = _
  rw [canonicalLatitudeDerivative_eq_mvfderiv_normal]
  unfold localScalarGradient
  change (fderiv Real
      (localScalarRepresentative period hPeriod field patch) 0)
      (Pi.single (0 : Fin 4) 1) = _
  exact hChain.trans (by
    rw [chart.derivative_normal, chart.at_zero]
    rfl)

theorem localActualScalarRaisedGradient_adapted_zero_normal
    (base : CanonicalLatitudeBase) (normal : Real)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (field : SmoothScalarField period hPeriod) :
    localActualScalarRaisedGradient period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field 0 0 =
      canonicalLatitudeDerivative period hPeriod field base normal := by
  unfold localActualScalarRaisedGradient
  simp_rw [localInverseMetricMatrix_adapted_zero_row period hPeriod base normal chart]
  simp [localScalarGradient_adapted_zero_normal period hPeriod base normal chart]

theorem localActualScalarGreenCurrent_adapted_zero_normal
    (base : CanonicalLatitudeBase) (normal : Real)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (field test : SmoothScalarField period hPeriod) :
    localActualScalarGreenCurrent period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test 0 0 =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal := by
  unfold localActualScalarGreenCurrent
  rw [localScalarRepresentative_adapted_zero period hPeriod base normal chart field,
    localActualScalarRaisedGradient_adapted_zero_normal
      period hPeriod base normal chart test,
    localScalarRepresentative_adapted_zero period hPeriod base normal chart test,
    localActualScalarRaisedGradient_adapted_zero_normal
      period hPeriod base normal chart field]
  exact (canonicalLatitudeScalarGreenCurrent_eq_normalNoetherPairing
    period hPeriod field test base normal).symm

theorem localActualScalarGreenCurrent_adapted_zero_eq_globalNormalFlux
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Icc (0 : Real) 1)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (field test : SmoothScalarField period hPeriod) :
    localActualScalarGreenCurrent period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test 0 0 =
      let point := canonicalLatitudeCutBulkCollarMap period hPeriod (base, normal)
      (intrinsicCutBulkSmoothGeneralLorentzMetric period hPeriod).musical point
          (intrinsicCutBulkSmoothScalarGreenCurrent period hPeriod field test point)
          ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm
            (canonicalLatitudeNormalVector period hPeriod base normal)) := by
  rw [localActualScalarGreenCurrent_adapted_zero_normal
    period hPeriod base normal chart field test]
  exact (intrinsicCutBulkSmoothScalarGreenCurrent_canonicalNormalFlux
    period hPeriod field test base normal hNormal).symm

end

end P0EFTJanusMappingTorusCanonicalLatitudeAdaptedHolonomicGreenCurrentFlux4D
end JanusFormal
