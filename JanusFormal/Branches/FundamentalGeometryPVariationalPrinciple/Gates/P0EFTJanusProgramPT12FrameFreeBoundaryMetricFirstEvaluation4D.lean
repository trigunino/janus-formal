import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D

/-! The ambient first derivative of the varying metric, evaluated on the moving
normal graph. It is the first coordinate of the genuine closed C² coefficient
`g₀ + g₀ R`; its moving evaluation is C² by the existing C³ substitution gates.
These are derivatives of frame coefficients, not covariant derivatives. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryMetricFirstEvaluation4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointC2Evaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D

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
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Core" => FrameFreeBoundaryC3Core period hPeriod frame metric
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real
local notation "ScalarCore" => CanonicalPhysicalScalarC2JetCore period hPeriod

/-- The covariant metric coefficient retained in the closed scalar C² core. -/
def frameFreeBoundaryActualMetricCoefficient (row column : Index) (variation : Core) : ScalarCore :=
  smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column) +
    ∑ middle : Index, canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor row middle))
      (frameFreeBoundaryC3RelativeEntry period hPeriod frame metric middle column variation)

/-- The same C² coefficient gives the existing actual metric evaluation. -/
theorem frameFreeBoundaryActualMetricEvaluation_eq_valueJet (row column : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryActualMetricEvaluation period hPeriod metric row column current boundary =
      ((frameFreeBoundaryActualMetricCoefficient period hPeriod metric row column current.1.1).1
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary)).1 := by
  rcases current with ⟨variation, parameter⟩
  let point := normalBoundaryC2Graph period hPeriod variation.2 parameter boundary
  let readValue : ScalarCore →ₗ[Real] Real := {
    toFun := fun field => (field.1 point).1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  change _ = readValue (frameFreeBoundaryActualMetricCoefficient period hPeriod metric row column variation.1)
  rw [frameFreeBoundaryActualMetricCoefficient, map_add, map_sum]
  simp only [frameFreeBoundaryActualMetricEvaluation, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  apply congrArg₂ (fun first second : Real => first + second)
  · rw [frameFreeBoundaryBaseMetricEvaluation_apply]
    rfl
  · apply Finset.sum_congr rfl
    intro middle _
    rw [frameFreeBoundaryBaseMetricEvaluation_apply, frameFreeBoundaryJointValueEvaluation_eq_atGraph]
    rfl

def frameFreeBoundaryBaseMetricFirstEvaluation (row column spatial : Index) (current : Input) : Field :=
  candidateANormalBoundarySmoothFieldFiberEvaluation period hPeriod metric
    (frameDerivativeComponentField period hPeriod frame
      (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column) spatial)
    (frameFreeBoundaryNormalInput period hPeriod metric current)

theorem frameFreeBoundaryBaseMetricFirstEvaluation_contDiff_two (row column spatial : Index) :
    ContDiff Real 2 (frameFreeBoundaryBaseMetricFirstEvaluation period hPeriod metric row column spatial) :=
  (candidateANormalBoundarySmoothFieldFiberEvaluation_contDiff_two period hPeriod metric _).comp
    (frameFreeBoundaryNormalInput_contDiff_two period hPeriod metric)

@[simp] theorem frameFreeBoundaryBaseMetricFirstEvaluation_apply (row column spatial : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryBaseMetricFirstEvaluation period hPeriod metric row column spatial current boundary =
      frameDerivative period hPeriod Real frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column)
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary) spatial :=
  candidateANormalBoundarySmoothFieldFiberEvaluation_apply period hPeriod metric _ _ _ _

/-- `Eᵢ gⱼₖ = Eᵢ g₀ⱼₖ + Σₗ ((Eᵢ g₀ⱼₗ) Rₗₖ + g₀ⱼₗ Eᵢ Rₗₖ)`. -/
def frameFreeBoundaryActualMetricFirstEvaluation (row column spatial : Index) (current : Input) : Field :=
  frameFreeBoundaryBaseMetricFirstEvaluation period hPeriod metric row column spatial current +
    ∑ middle : Index,
      (frameFreeBoundaryBaseMetricFirstEvaluation period hPeriod metric row middle spatial current *
        frameFreeBoundaryJointValueEvaluation period hPeriod metric middle column current +
      frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row middle current *
        frameFreeBoundaryJointFirstEvaluation period hPeriod metric middle column spatial current)

theorem frameFreeBoundaryActualMetricFirstEvaluation_contDiff_two (row column spatial : Index) :
    ContDiff Real 2 (frameFreeBoundaryActualMetricFirstEvaluation period hPeriod metric row column spatial) := by
  unfold frameFreeBoundaryActualMetricFirstEvaluation
  apply (frameFreeBoundaryBaseMetricFirstEvaluation_contDiff_two period hPeriod metric row column spatial).add
  apply ContDiff.sum
  intro middle _
  exact ((frameFreeBoundaryBaseMetricFirstEvaluation_contDiff_two period hPeriod metric row middle spatial).mul
    (frameFreeBoundaryJointValueEvaluation_contDiff_two period hPeriod metric middle column)).add
      ((frameFreeBoundaryBaseMetricEvaluation_contDiff_two period hPeriod metric row middle).mul
        (frameFreeBoundaryJointFirstEvaluation_contDiff_two period hPeriod metric middle column spatial))

private def firstJetAt (point : EffectiveQuotient period hPeriod) (spatial : Index) : ScalarCore →ₗ[Real] Real where
  toFun field := (field.1 point).2.1 spatial
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem firstJetAt_product (point : EffectiveQuotient period hPeriod) (spatial : Index)
    (first second : ScalarCore) :
    firstJetAt period hPeriod point spatial
        (canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second) =
      firstJetAt period hPeriod point spatial first * (second.1 point).1 +
        (first.1 point).1 * firstJetAt period hPeriod point spatial second := by
  change (first.1 point).1 * (second.1 point).2.1 spatial +
      (second.1 point).1 * (first.1 point).2.1 spatial =
    (first.1 point).2.1 spatial * (second.1 point).1 +
      (first.1 point).1 * (second.1 point).2.1 spatial
  ring

private theorem baseFirst_eq_firstJet (row column spatial : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryBaseMetricFirstEvaluation period hPeriod metric row column spatial current boundary =
      firstJetAt period hPeriod (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary) spatial
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column)) := by
  rw [frameFreeBoundaryBaseMetricFirstEvaluation_apply]
  rfl

private theorem base_eq_valueJet (row column : Index) (current : Input) (boundary : Boundary) :
    frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row column current boundary =
      ((smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column)).1
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary)).1 := by
  rw [frameFreeBoundaryBaseMetricEvaluation_apply]
  rfl

private theorem relative_eq_valueJet (row column : Index) (current : Input) (boundary : Boundary) :
    frameFreeBoundaryJointValueEvaluation period hPeriod metric row column current boundary =
      ((frameFreeBoundaryC3RelativeEntry period hPeriod frame metric row column current.1.1).1
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary)).1 := by
  rcases current with ⟨variation, parameter⟩
  rw [frameFreeBoundaryJointValueEvaluation_eq_atGraph]
  rfl

private theorem relativeFirst_eq_firstJet (row column spatial : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryJointFirstEvaluation period hPeriod metric row column spatial current boundary =
      firstJetAt period hPeriod (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary) spatial
        (frameFreeBoundaryC3RelativeEntry period hPeriod frame metric row column current.1.1) := by
  rcases current with ⟨variation, parameter⟩
  rw [frameFreeBoundaryJointFirstEvaluation_eq_atGraph]
  rfl

private theorem productEvaluation_eq_firstJet (row middle column spatial : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryBaseMetricFirstEvaluation period hPeriod metric row middle spatial current boundary *
        frameFreeBoundaryJointValueEvaluation period hPeriod metric middle column current boundary +
      frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row middle current boundary *
        frameFreeBoundaryJointFirstEvaluation period hPeriod metric middle column spatial current boundary =
    firstJetAt period hPeriod (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary) spatial
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor row middle))
        (frameFreeBoundaryC3RelativeEntry period hPeriod frame metric middle column current.1.1)) := by
  rw [firstJetAt_product]
  exact congrArg₂ (fun first second : Real => first + second)
    (congrArg₂ (fun first second : Real => first * second)
      (baseFirst_eq_firstJet period hPeriod metric row middle spatial current boundary)
      (relative_eq_valueJet period hPeriod metric middle column current boundary))
    (congrArg₂ (fun first second : Real => first * second)
      (base_eq_valueJet period hPeriod metric row middle current boundary)
      (relativeFirst_eq_firstJet period hPeriod metric middle column spatial current boundary))

/-- Exact agreement with the first jet, for every completed metric/normal input. -/
theorem frameFreeBoundaryActualMetricFirstEvaluation_eq_firstJet (row column spatial : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryActualMetricFirstEvaluation period hPeriod metric row column spatial current boundary =
      ((frameFreeBoundaryActualMetricCoefficient period hPeriod metric row column current.1.1).1
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary)).2.1 spatial := by
  change _ = firstJetAt period hPeriod
    (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary) spatial
    (frameFreeBoundaryActualMetricCoefficient period hPeriod metric row column current.1.1)
  rw [frameFreeBoundaryActualMetricCoefficient, map_add, map_sum]
  simp only [frameFreeBoundaryActualMetricFirstEvaluation, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  apply congrArg₂ (fun first second : Real => first + second)
    (baseFirst_eq_firstJet period hPeriod metric row column spatial current boundary)
  apply Finset.sum_congr rfl
  intro middle _
  exact productEvaluation_eq_firstJet period hPeriod metric row middle column spatial current boundary

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryMetricFirstEvaluation4D
