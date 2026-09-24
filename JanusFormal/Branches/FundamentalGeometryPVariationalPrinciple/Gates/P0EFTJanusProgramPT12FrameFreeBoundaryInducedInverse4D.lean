import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D

/-! C² inverse of the faithful induced lift, using the existing adjugate and
scalar inverse engines. Smooth synthesis solves the genuine relative metric equation. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedInverse4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedLift4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod
local instance : ChartedSpace ThroatCoverModel (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "throatFrame" => finiteSmoothThroatGeneratingFrame
  (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local notation "Index" => NormalBoundaryTangentIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real
local notation "MatrixField" => CandidateANormalBoundaryInducedMetricMatrixField period hPeriod
local notation "Field" => BoundedContinuousFunction Boundary Real
@[reducible] local instance : NormedAddCommGroup MatrixField := Pi.normedAddCommGroup
@[reducible] local instance : NormedSpace Real MatrixField := Pi.normedSpace

def frameFreeBoundaryInducedLiftInverse (current : Input) : MatrixField :=
  (frameFreeBoundaryInducedLift period hPeriod metric current)⁻¹

private theorem determinantInverse_contDiffOn_two :
    ContDiffOn Real 2 (fun current : Input =>
      Ring.inverse (frameFreeBoundaryInducedDeterminant period hPeriod metric current))
      (frameFreeBoundaryInducedDomain period hPeriod metric) := by
  intro current hCurrent
  change IsUnit (frameFreeBoundaryInducedDeterminant period hPeriod metric current) at hCurrent
  have hInverse : ContDiffAt Real 2 Ring.inverse
      (frameFreeBoundaryInducedDeterminant period hPeriod metric current) := by
    simpa using (contDiffAt_ringInverse Real hCurrent.unit :
      ContDiffAt Real 2 Ring.inverse (hCurrent.unit : Field))
  exact hInverse.comp_contDiffWithinAt current
    (frameFreeBoundaryInducedDeterminant_contDiff_two period hPeriod metric).contDiffWithinAt

theorem frameFreeBoundaryInducedLiftInverse_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundaryInducedLiftInverse period hPeriod metric)
      (frameFreeBoundaryInducedDomain period hPeriod metric) := by
  have hAdjugate := ((candidateANormalBoundaryInducedRelativeLiftAdjugate_contDiff period hPeriod).of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp
      (frameFreeBoundaryInducedLift_contDiff_two period hPeriod metric)
  unfold frameFreeBoundaryInducedLiftInverse
  simp_rw [Matrix.inv_def]
  rw [contDiffOn_pi]
  intro row
  rw [contDiffOn_pi]
  intro column
  change ContDiffOn Real 2 (fun current : Input =>
    Ring.inverse (frameFreeBoundaryInducedDeterminant period hPeriod metric current) *
      candidateANormalBoundaryInducedRelativeLiftAdjugate period hPeriod
        (frameFreeBoundaryInducedLift period hPeriod metric current) row column)
      (frameFreeBoundaryInducedDomain period hPeriod metric)
  exact (determinantInverse_contDiffOn_two period hPeriod metric).mul
    (contDiffOn_pi.mp (contDiffOn_pi.mp hAdjugate.contDiffOn row) column)

theorem frameFreeBoundaryInducedLift_mul_inverse (current : Input)
    (hCurrent : current ∈ frameFreeBoundaryInducedDomain period hPeriod metric) :
    frameFreeBoundaryInducedLift period hPeriod metric current *
      frameFreeBoundaryInducedLiftInverse period hPeriod metric current = 1 :=
  Matrix.mul_nonsing_inv _ hCurrent

theorem frameFreeBoundaryInducedLift_inverse_mul (current : Input)
    (hCurrent : current ∈ frameFreeBoundaryInducedDomain period hPeriod metric) :
    frameFreeBoundaryInducedLiftInverse period hPeriod metric current *
      frameFreeBoundaryInducedLift period hPeriod metric current = 1 :=
  Matrix.nonsing_inv_mul _ hCurrent

private theorem evaluated_mul_inverse (current : Input)
    (hCurrent : current ∈ frameFreeBoundaryInducedDomain period hPeriod metric) (boundary : Boundary) :
    (Matrix.of fun row column => frameFreeBoundaryInducedLift period hPeriod metric current row column boundary) *
      (Matrix.of fun row column => frameFreeBoundaryInducedLiftInverse period hPeriod metric current row column boundary) =
      (1 : Matrix Index Index Real) := by
  ext row column
  have h := congrArg (fun matrix : MatrixField => matrix row column boundary)
    (frameFreeBoundaryInducedLift_mul_inverse period hPeriod metric current hCurrent)
  by_cases hrc : row = column <;> simpa [Matrix.mul_apply, Matrix.one_apply, hrc] using h

theorem frameFreeBoundaryInducedLiftInverse_apply (current : Input)
    (hCurrent : current ∈ frameFreeBoundaryInducedDomain period hPeriod metric) (boundary : Boundary) :
    (Matrix.of fun row column => frameFreeBoundaryInducedLiftInverse period hPeriod metric current row column boundary) =
      (Matrix.of fun row column => frameFreeBoundaryInducedLift period hPeriod metric current row column boundary)⁻¹ :=
  (Matrix.inv_eq_right_inv (evaluated_mul_inverse period hPeriod metric current hCurrent boundary)).symm

theorem frameFreeBoundaryInducedLiftInverse_smooth_synthesis
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryInducedDomain period hPeriod metric)
    (boundary : Boundary) (coefficients : Index → Real) :
    normalBoundarySmoothGraphRelativeEndomorphism period hPeriod variedMetric displacement parameter boundary
      (intrinsicThroatFiniteFrameSynthesisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
        (Matrix.mulVec (Matrix.of fun row column => frameFreeBoundaryInducedLiftInverse period hPeriod metric
          (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
          row column boundary) coefficients)) =
      intrinsicThroatFiniteFrameSynthesisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary coefficients := by
  let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
  let relative := normalBoundarySmoothGraphRelativeEndomorphism period hPeriod variedMetric displacement parameter boundary
  let inverse : Matrix Index Index Real := Matrix.of fun row column =>
    frameFreeBoundaryInducedLiftInverse period hPeriod metric current row column boundary
  have hLift : (Matrix.of fun row column => frameFreeBoundaryInducedLift period hPeriod metric current row column boundary) =
      intrinsicThroatFiniteFrameLiftAt (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        throatFrame boundary relative.toLinearMap := by
    ext row column
    exact frameFreeBoundaryInducedLift_smooth_apply period hPeriod metric tensor variedMetric hVaried
      displacement parameter boundary row column
  have hProduct := evaluated_mul_inverse period hPeriod metric current hCurrent boundary
  rw [hLift] at hProduct
  change intrinsicThroatFiniteFrameLiftAt (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    throatFrame boundary relative.toLinearMap * inverse = (1 : Matrix Index Index Real) at hProduct
  have hAction := intrinsicThroatFiniteFrameSynthesisAt_liftAt_mulVec
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) throatFrame boundary
    relative.toLinearMap (inverse.mulVec coefficients)
  rw [Matrix.mulVec_mulVec, hProduct, Matrix.one_mulVec] at hAction
  exact hAction.symm

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedInverse4D
