import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryJointC2Evaluation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryTangentCoefficients4D

/-! C² contraction of graph tangents with the varying covariant metric in the
canonical finite spanning family. No determinant of the redundant Gram matrix
or non-null domain is asserted here. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointC2Evaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryTangentCoefficients4D

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
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
local notation "NormalInput" => NormalBoundaryC2JetCore period hPeriod × Real
local notation "Field" => BoundedContinuousFunction Boundary Real

private theorem cosSquaredLatitude_contMDiff :
    ContMDiff (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ (fun current : Boundary × Real => (Real.cos current.2) ^ 2) :=
  (Real.contDiff_cos.contMDiff.comp contMDiff_snd).pow 2

/-- `arctan'` via the existing smooth compact-latitude substitution engine. -/
def frameFreeBoundaryArctanDerivativeEvaluation (current : NormalInput) : Field :=
  normalBoundarySmoothFiberEvaluation period hPeriod
    (fun point => (Real.cos point.2) ^ 2) (cosSquaredLatitude_contMDiff period hPeriod) current

theorem frameFreeBoundaryArctanDerivativeEvaluation_contDiff_two :
    ContDiff Real 2 (frameFreeBoundaryArctanDerivativeEvaluation period hPeriod) :=
  normalBoundarySmoothFiberEvaluation_contDiff_two period hPeriod _ _

@[simp] theorem frameFreeBoundaryArctanDerivativeEvaluation_apply
    (normal : NormalBoundaryC2JetCore period hPeriod) (parameter : Real) (boundary : Boundary) :
    frameFreeBoundaryArctanDerivativeEvaluation period hPeriod (normal, parameter) boundary =
      1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary normal) ^ 2) := by
  unfold frameFreeBoundaryArctanDerivativeEvaluation
  rw [normalBoundarySmoothFiberEvaluation_apply, Real.cos_sq_arctan]

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod
local notation "Joint" => FrameFreeBoundaryJointCore period hPeriod frame metric
local notation "Input" => Joint × Real

def frameFreeBoundaryNormalInput (current : Input) : NormalInput := (current.1.2, current.2)

theorem frameFreeBoundaryNormalInput_contDiff_two :
    ContDiff Real 2 (frameFreeBoundaryNormalInput period hPeriod metric) :=
  (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd

def frameFreeBoundaryGraphTangentEvaluation (index : TangentIndex) (row : Index)
    (current : Input) : Field :=
  frameFreeBoundaryHorizontalCoefficientEvaluation period hPeriod frame metric index row
      (frameFreeBoundaryNormalInput period hPeriod metric current) +
    (frameFreeBoundaryArctanDerivativeEvaluation period hPeriod
        (frameFreeBoundaryNormalInput period hPeriod metric current) *
      normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
        (frameFreeBoundaryNormalInput period hPeriod metric current)) *
      frameFreeBoundaryVerticalCoefficientEvaluation period hPeriod frame metric row
        (frameFreeBoundaryNormalInput period hPeriod metric current)

theorem frameFreeBoundaryGraphTangentEvaluation_contDiff_two (index : TangentIndex) (row : Index) :
    ContDiff Real 2 (frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row) := by
  have hInput := frameFreeBoundaryNormalInput_contDiff_two period hPeriod metric
  exact ((frameFreeBoundaryHorizontalCoefficientEvaluation_contDiff_two
    period hPeriod frame metric index row).comp hInput).add
      ((((frameFreeBoundaryArctanDerivativeEvaluation_contDiff_two period hPeriod).comp hInput).mul
        ((normalBoundaryC2ScaledRawSpatialFirst_contDiff_two period hPeriod index).comp hInput)).mul
          ((frameFreeBoundaryVerticalCoefficientEvaluation_contDiff_two
            period hPeriod frame metric row).comp hInput))

@[simp] theorem frameFreeBoundaryGraphTangentEvaluation_apply (index : TangentIndex) (row : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row current boundary =
      frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row
        (boundary, Real.arctan (current.2 * normalBoundaryC2JetCoreValueAt period hPeriod boundary current.1.2)) +
      ((1 / (1 + (current.2 * normalBoundaryC2JetCoreValueAt period hPeriod boundary current.1.2) ^ 2)) *
        (current.2 * normalBoundaryC2JetCoreFirstAt period hPeriod boundary current.1.2 index)) *
      frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row
        (boundary, Real.arctan (current.2 * normalBoundaryC2JetCoreValueAt period hPeriod boundary current.1.2)) := by
  simp only [frameFreeBoundaryGraphTangentEvaluation, frameFreeBoundaryNormalInput,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.mul_apply,
    frameFreeBoundaryHorizontalCoefficientEvaluation_apply,
    frameFreeBoundaryVerticalCoefficientEvaluation_apply,
    frameFreeBoundaryArctanDerivativeEvaluation_apply, normalBoundaryC2ScaledRawSpatialFirst_apply]

def frameFreeBoundaryBaseMetricEvaluation (row column : Index) (current : Input) : Field :=
  candidateANormalBoundarySmoothFieldFiberEvaluation period hPeriod metric
    (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column)
    (frameFreeBoundaryNormalInput period hPeriod metric current)

theorem frameFreeBoundaryBaseMetricEvaluation_contDiff_two (row column : Index) :
    ContDiff Real 2 (frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row column) :=
  (candidateANormalBoundarySmoothFieldFiberEvaluation_contDiff_two period hPeriod metric _).comp
    (frameFreeBoundaryNormalInput_contDiff_two period hPeriod metric)

@[simp] theorem frameFreeBoundaryBaseMetricEvaluation_apply (row column : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row column current boundary =
      generalMetricFrameCoefficient period hPeriod frame metric.tensor row column
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary) :=
  candidateANormalBoundarySmoothFieldFiberEvaluation_apply period hPeriod metric _ _ _ _

/-- The covariant coefficient expression `g + g R`, using the faithful relative jet. -/
def frameFreeBoundaryActualMetricEvaluation (row column : Index) (current : Input) : Field :=
  frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row column current +
    ∑ middle : Index, frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row middle current *
      frameFreeBoundaryJointValueEvaluation period hPeriod metric middle column current

theorem frameFreeBoundaryActualMetricEvaluation_contDiff_two (row column : Index) :
    ContDiff Real 2 (frameFreeBoundaryActualMetricEvaluation period hPeriod metric row column) := by
  unfold frameFreeBoundaryActualMetricEvaluation
  apply (frameFreeBoundaryBaseMetricEvaluation_contDiff_two period hPeriod metric row column).add
  apply ContDiff.sum
  intro middle _
  exact (frameFreeBoundaryBaseMetricEvaluation_contDiff_two period hPeriod metric row middle).mul
    (frameFreeBoundaryJointValueEvaluation_contDiff_two period hPeriod metric middle column)

/-- Finite spanning-family contraction; invertibility concerns the faithful lift, not this Gram matrix. -/
def frameFreeBoundaryInducedMetricEvaluation (current : Input) : TangentIndex → TangentIndex → Field :=
  fun first second => ∑ row : Index, ∑ column : Index,
    frameFreeBoundaryGraphTangentEvaluation period hPeriod metric first row current *
      frameFreeBoundaryActualMetricEvaluation period hPeriod metric row column current *
        frameFreeBoundaryGraphTangentEvaluation period hPeriod metric second column current

theorem frameFreeBoundaryInducedMetricEvaluation_contDiff_two :
    ContDiff Real 2 (frameFreeBoundaryInducedMetricEvaluation period hPeriod metric) := by
  rw [contDiff_pi]
  intro first
  rw [contDiff_pi]
  intro second
  unfold frameFreeBoundaryInducedMetricEvaluation
  apply ContDiff.sum
  intro row _
  apply ContDiff.sum
  intro column _
  exact ((frameFreeBoundaryGraphTangentEvaluation_contDiff_two period hPeriod metric first row).mul
    (frameFreeBoundaryActualMetricEvaluation_contDiff_two period hPeriod metric row column)).mul
      (frameFreeBoundaryGraphTangentEvaluation_contDiff_two period hPeriod metric second column)

@[simp] theorem frameFreeBoundaryInducedMetricEvaluation_apply
    (current : Input) (first second : TangentIndex) (boundary : Boundary) :
    frameFreeBoundaryInducedMetricEvaluation period hPeriod metric current first second boundary =
      ∑ row : Index, ∑ column : Index,
        frameFreeBoundaryGraphTangentEvaluation period hPeriod metric first row current boundary *
          frameFreeBoundaryActualMetricEvaluation period hPeriod metric row column current boundary *
            frameFreeBoundaryGraphTangentEvaluation period hPeriod metric second column current boundary := by
  simp only [frameFreeBoundaryInducedMetricEvaluation, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
