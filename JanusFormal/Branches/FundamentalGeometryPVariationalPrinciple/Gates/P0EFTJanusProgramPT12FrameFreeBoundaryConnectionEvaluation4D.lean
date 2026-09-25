import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryMetricFirstEvaluation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryAmbientInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2KoszulConnection4D

/-! Joint C² moving-graph evaluation of the nonholonomic Koszul connection.
Every moving entry uses an established smooth or C³ substitution map. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryConnectionEvaluation4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryMetricFirstEvaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryAmbientInverse4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real

def frameFreeBoundaryStructureEvaluation (first second upper : Index) (current : Input) : Field :=
  candidateANormalBoundarySmoothFieldFiberEvaluation period hPeriod metric
    (finiteFrameStructureCoefficient period hPeriod frame metric first second upper)
    (frameFreeBoundaryNormalInput period hPeriod metric current)

theorem frameFreeBoundaryStructureEvaluation_contDiff_two (first second upper : Index) :
    ContDiff Real 2 (frameFreeBoundaryStructureEvaluation period hPeriod metric first second upper) :=
  (candidateANormalBoundarySmoothFieldFiberEvaluation_contDiff_two period hPeriod metric _).comp
    (frameFreeBoundaryNormalInput_contDiff_two period hPeriod metric)

@[simp] theorem frameFreeBoundaryStructureEvaluation_apply (first second upper : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryStructureEvaluation period hPeriod metric first second upper current boundary =
      finiteFrameStructureCoefficient period hPeriod frame metric first second upper
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary) :=
  candidateANormalBoundarySmoothFieldFiberEvaluation_apply period hPeriod metric _ _ _ _

def frameFreeBoundaryStructureMetricEvaluation (first second row : Index) (current : Input) : Field :=
  ∑ index : Index, frameFreeBoundaryStructureEvaluation period hPeriod metric first second index current *
    frameFreeBoundaryActualMetricEvaluation period hPeriod metric row index current

theorem frameFreeBoundaryStructureMetricEvaluation_contDiff_two (first second row : Index) :
    ContDiff Real 2 (frameFreeBoundaryStructureMetricEvaluation period hPeriod metric first second row) := by
  unfold frameFreeBoundaryStructureMetricEvaluation
  apply ContDiff.sum
  intro index _
  exact (frameFreeBoundaryStructureEvaluation_contDiff_two period hPeriod metric first second index).mul
    (frameFreeBoundaryActualMetricEvaluation_contDiff_two period hPeriod metric row index)

/-- The three derivative terms and three bracket terms of the native Koszul formula. -/
def frameFreeBoundaryKoszulLowerEvaluation (first second lower : Index) (current : Input) : Field :=
  (1 / 2 : Real) •
    (frameFreeBoundaryActualMetricFirstEvaluation period hPeriod metric second lower first current +
      frameFreeBoundaryActualMetricFirstEvaluation period hPeriod metric first lower second current -
      frameFreeBoundaryActualMetricFirstEvaluation period hPeriod metric first second lower current -
      frameFreeBoundaryStructureMetricEvaluation period hPeriod metric second lower first current +
      frameFreeBoundaryStructureMetricEvaluation period hPeriod metric lower first second current +
      frameFreeBoundaryStructureMetricEvaluation period hPeriod metric first second lower current)

theorem frameFreeBoundaryKoszulLowerEvaluation_contDiff_two (first second lower : Index) :
    ContDiff Real 2 (frameFreeBoundaryKoszulLowerEvaluation period hPeriod metric first second lower) := by
  have hDerivative := frameFreeBoundaryActualMetricFirstEvaluation_contDiff_two period hPeriod metric
  have hBracket := frameFreeBoundaryStructureMetricEvaluation_contDiff_two period hPeriod metric
  have hBase := ((hDerivative second lower first).add (hDerivative first lower second)).sub
    (hDerivative first second lower)
  have hResult := ((hBase.sub (hBracket second lower first)).add
    (hBracket lower first second)).add (hBracket first second lower)
  exact ContDiff.const_smul (1 / 2 : Real) hResult

/-- Raise the final Koszul slot with the same genuine inverse metric. -/
def frameFreeBoundaryConnectionEvaluation (upper first second : Index) (current : Input) : Field :=
  ∑ lower : Index, frameFreeBoundaryAmbientInverseEvaluation period hPeriod metric upper lower current *
    frameFreeBoundaryKoszulLowerEvaluation period hPeriod metric first second lower current

theorem frameFreeBoundaryConnectionEvaluation_contDiffOn_two (upper first second : Index) :
    ContDiffOn Real 2 (frameFreeBoundaryConnectionEvaluation period hPeriod metric upper first second)
      (frameFreeBoundaryAmbientDomain period hPeriod metric) := by
  unfold frameFreeBoundaryConnectionEvaluation
  apply ContDiffOn.sum
  intro lower _
  exact (frameFreeBoundaryAmbientInverseEvaluation_contDiffOn_two period hPeriod metric upper lower).mul
    (frameFreeBoundaryKoszulLowerEvaluation_contDiff_two period hPeriod metric first second lower).contDiffOn

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryConnectionEvaluation4D
