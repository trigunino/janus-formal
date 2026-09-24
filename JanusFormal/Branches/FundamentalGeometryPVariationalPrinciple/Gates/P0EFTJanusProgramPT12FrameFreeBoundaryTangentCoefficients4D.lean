import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

/-! Actual collar tangent coefficients in an arbitrary smooth finite spanning family.
They reconstruct the true horizontal and vertical lifts and admit C² normal-graph evaluation. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryTangentCoefficients4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

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
local notation "Input" => NormalBoundaryC2JetCore period hPeriod × Real
local notation "CollarModel" => throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)
local notation "Lift" => Boundary × Real → TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod)
variable (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)

def frameFreeBoundaryLiftCoefficient (lift : Lift) (row : Fin frame.count)
    (current : Boundary × Real) : Real :=
  metric.tensor.tensor (lift current).1 (frame.vectorAt (lift current).1 row)
    (generalMetricFiniteFrameInverseOperator period hPeriod frame metric (lift current).1 (lift current).2)

theorem frameFreeBoundaryLiftCoefficient_contMDiff (lift : Lift)
    (hLift : ContMDiff CollarModel coverModelWithCorners.tangent ∞ lift) (row : Fin frame.count) :
    ContMDiff CollarModel (modelWithCornersSelf Real Real) ∞
      (frameFreeBoundaryLiftCoefficient period hPeriod frame metric lift row) := by
  unfold frameFreeBoundaryLiftCoefficient
  have hProjection : ContMDiff coverModelWithCorners.tangent coverModelWithCorners ∞
      (fun current : TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) => current.1) :=
    Bundle.contMDiff_proj (fun point : EffectiveQuotient period hPeriod => TangentSpace coverModelWithCorners point)
  have hPoint := hProjection.comp hLift
  have hInverse := (generalMetricFiniteFrameInverseOperator period hPeriod frame metric).contMDiff.comp hPoint
  have hSolved := hInverse.clm_bundle_apply hLift
  have hFrame := (frame.contMDiff_vector row).comp hPoint
  have hTensor := metric.tensor.tensor.contMDiff.comp hPoint
  have hApplied := ContMDiff.clm_bundle_apply₂ (F₃ := Real)
    (E₃ := fun _ : EffectiveQuotient period hPeriod => Real) hTensor hFrame hSolved
  intro current
  have hAppliedAt := hApplied current
  rw [Bundle.contMDiffAt_totalSpace] at hAppliedAt
  convert hAppliedAt.2 using 1; rfl

theorem frameFreeBoundaryLiftCoefficient_reconstructs (lift : Lift) (current : Boundary × Real) :
    (lift current).2 = ∑ row : Fin frame.count,
      frameFreeBoundaryLiftCoefficient period hPeriod frame metric lift row current •
        frame.vectorAt (lift current).1 row :=
  generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod frame metric
    (lift current).1 (lift current).2

def frameFreeBoundaryVerticalCoefficient (row : Fin frame.count) : Boundary × Real → Real :=
  frameFreeBoundaryLiftCoefficient period hPeriod frame metric
    (fun current => normalBoundaryLatitudeFiberLift period hPeriod current.1 current.2) row

def frameFreeBoundaryHorizontalCoefficient (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin frame.count) : Boundary × Real → Real :=
  frameFreeBoundaryLiftCoefficient period hPeriod frame metric
    (normalBoundaryLatitudeHorizontalFiberLift period hPeriod index) row

theorem frameFreeBoundaryVerticalCoefficient_contMDiff (row : Fin frame.count) :
    ContMDiff CollarModel (modelWithCornersSelf Real Real) ∞
      (frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row) :=
  frameFreeBoundaryLiftCoefficient_contMDiff period hPeriod frame metric _
    (normalBoundaryLatitudeFiberLift_joint_contMDiff period hPeriod) row

theorem frameFreeBoundaryHorizontalCoefficient_contMDiff
    (index : NormalBoundaryTangentIndex period hPeriod) (row : Fin frame.count) :
    ContMDiff CollarModel (modelWithCornersSelf Real Real) ∞
      (frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row) :=
  frameFreeBoundaryLiftCoefficient_contMDiff period hPeriod frame metric _
    (normalBoundaryLatitudeHorizontalFiberLift_contMDiff period hPeriod index) row

def frameFreeBoundaryVerticalCoefficientEvaluation (row : Fin frame.count) (current : Input) :
    BoundedContinuousFunction Boundary Real :=
  normalBoundarySmoothFiberEvaluation period hPeriod
    (frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row)
    (frameFreeBoundaryVerticalCoefficient_contMDiff period hPeriod frame metric row) current

def frameFreeBoundaryHorizontalCoefficientEvaluation
    (index : NormalBoundaryTangentIndex period hPeriod) (row : Fin frame.count) (current : Input) :
    BoundedContinuousFunction Boundary Real :=
  normalBoundarySmoothFiberEvaluation period hPeriod
    (frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row)
    (frameFreeBoundaryHorizontalCoefficient_contMDiff period hPeriod frame metric index row) current

theorem frameFreeBoundaryVerticalCoefficientEvaluation_contDiff_two (row : Fin frame.count) :
    ContDiff Real 2 (frameFreeBoundaryVerticalCoefficientEvaluation period hPeriod frame metric row) :=
  normalBoundarySmoothFiberEvaluation_contDiff_two period hPeriod _ _

theorem frameFreeBoundaryHorizontalCoefficientEvaluation_contDiff_two
    (index : NormalBoundaryTangentIndex period hPeriod) (row : Fin frame.count) :
    ContDiff Real 2
      (frameFreeBoundaryHorizontalCoefficientEvaluation period hPeriod frame metric index row) :=
  normalBoundarySmoothFiberEvaluation_contDiff_two period hPeriod _ _

@[simp] theorem frameFreeBoundaryVerticalCoefficientEvaluation_apply (row : Fin frame.count)
    (normal : NormalBoundaryC2JetCore period hPeriod) (parameter : Real) (boundary : Boundary) :
    frameFreeBoundaryVerticalCoefficientEvaluation period hPeriod frame metric row (normal, parameter) boundary =
      frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row
        (boundary, Real.arctan (parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary normal)) :=
  normalBoundarySmoothFiberEvaluation_apply period hPeriod _ _ normal parameter boundary

@[simp] theorem frameFreeBoundaryHorizontalCoefficientEvaluation_apply
    (index : NormalBoundaryTangentIndex period hPeriod) (row : Fin frame.count)
    (normal : NormalBoundaryC2JetCore period hPeriod) (parameter : Real) (boundary : Boundary) :
    frameFreeBoundaryHorizontalCoefficientEvaluation period hPeriod frame metric index row
      (normal, parameter) boundary =
      frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row
        (boundary, Real.arctan (parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary normal)) :=
  normalBoundarySmoothFiberEvaluation_apply period hPeriod _ _ normal parameter boundary

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryTangentCoefficients4D
