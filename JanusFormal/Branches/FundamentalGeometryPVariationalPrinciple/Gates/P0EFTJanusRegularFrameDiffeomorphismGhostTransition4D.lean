import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameMetricCartanCoefficients4D

/-! # Bounded changes of regular frame for one diffeomorphism ghost

The transition matrix consists of the target-frame coefficients of each
source-frame vector. Fixed smooth C² multiplication extends this transition
to completed ghost coefficients, with exact smooth geometric agreement.
-/

namespace JanusFormal
namespace P0EFTJanusRegularFrameDiffeomorphismGhostTransition4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

abbrev RegularFrameGhostC2Coefficients := Fin 4 → CanonicalPhysicalScalarC2JetCore period hPeriod

/-- The source vector's coefficient in the target frame: output index precedes input index. -/
def regularFrameGhostTransitionCoefficient
    (source target : RegularGeneralLorentzMetric period hPeriod)
    (output input : Fin 4) : SmoothScalarField period hPeriod :=
  regularFrameCartanGhostCoefficient period hPeriod target (source.frame input) output

/-- Smooth target coefficients of the same geometric ghost. -/
def smoothRegularFrameGhostTransition
    (source target : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    Fin 4 → SmoothScalarField period hPeriod :=
  regularFrameCartanGhostCoefficient period hPeriod target
    (regularFrameGhostFromCoefficients period hPeriod source coefficients)

theorem smoothRegularFrameGhostTransition_eq_sum
    (source target : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) (output : Fin 4) :
    smoothRegularFrameGhostTransition period hPeriod source target coefficients output =
      ∑ input : Fin 4, smoothScalarFieldMul period hPeriod
        (regularFrameGhostTransitionCoefficient period hPeriod source target output input)
        (coefficients input) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  let evaluation : SmoothScalarField period hPeriod →ₗ[Real] Real :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  change generalMetricFiniteFrameCoefficientAt period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod target) target.metric
      point output (regularFrameGhostFromCoefficients period hPeriod source coefficients point) =
    evaluation (∑ input : Fin 4, smoothScalarFieldMul period hPeriod
      (regularFrameGhostTransitionCoefficient period hPeriod source target output input)
      (coefficients input))
  rw [regularFrameGhostFromCoefficients_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [map_smul]
  change coefficients input point *
      regularFrameGhostTransitionCoefficient period hPeriod source target output input point =
    regularFrameGhostTransitionCoefficient period hPeriod source target output input point *
      coefficients input point
  exact mul_comm _ _

/-- Frame transition preserves the entire smooth tangent ghost. -/
theorem smoothRegularFrameGhostTransition_reconstructs
    (source target : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularFrameGhostFromCoefficients period hPeriod target
        (smoothRegularFrameGhostTransition period hPeriod source target coefficients) =
      regularFrameGhostFromCoefficients period hPeriod source coefficients :=
  regularFrameGhostFromCoefficients_reconstructs period hPeriod target _

/-- A fixed smooth matrix acts boundedly on the completed C² ghost coefficients. -/
def regularFrameDiffeomorphismGhostTransition
    (source target : RegularGeneralLorentzMetric period hPeriod) :
    RegularFrameGhostC2Coefficients period hPeriod →L[Real]
      RegularFrameGhostC2Coefficients period hPeriod :=
  ContinuousLinearMap.pi fun output : Fin 4 =>
    ∑ input : Fin 4,
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (regularFrameGhostTransitionCoefficient period hPeriod source target output input))).comp
        (ContinuousLinearMap.proj input)

@[simp] theorem regularFrameDiffeomorphismGhostTransition_apply
    (source target : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : RegularFrameGhostC2Coefficients period hPeriod) (output : Fin 4) :
    regularFrameDiffeomorphismGhostTransition period hPeriod source target coefficients output =
      ∑ input : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
            (regularFrameGhostTransitionCoefficient period hPeriod source target output input))
          (coefficients input) := by
  simp only [regularFrameDiffeomorphismGhostTransition, ContinuousLinearMap.pi_apply,
    sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- Gate 659: the bounded transition agrees with the coefficients of the same smooth ghost. -/
theorem regularFrameDiffeomorphismGhostTransition_smooth
    (source target : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularFrameDiffeomorphismGhostTransition period hPeriod source target
        (fun input => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients input)) =
      fun output => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (smoothRegularFrameGhostTransition period hPeriod source target coefficients output) := by
  funext output
  rw [regularFrameDiffeomorphismGhostTransition_apply, smoothRegularFrameGhostTransition_eq_sum,
    map_sum]
  apply Finset.sum_congr rfl
  intro input _
  exact canonicalPhysicalScalarC2JetCoreProduct_smooth period hPeriod _ _

theorem regularFrameDiffeomorphismGhostTransition_contDiff
    (source target : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real ∞ (regularFrameDiffeomorphismGhostTransition period hPeriod source target) :=
  (regularFrameDiffeomorphismGhostTransition period hPeriod source target).contDiff

/-- One common coefficient ghost supplies the two independently chosen sector frames. -/
def pairedRegularFrameDiffeomorphismGhostTransition
    (source plusReference minusReference : RegularGeneralLorentzMetric period hPeriod) :
    RegularFrameGhostC2Coefficients period hPeriod →L[Real]
      (RegularFrameGhostC2Coefficients period hPeriod ×
        RegularFrameGhostC2Coefficients period hPeriod) :=
  (regularFrameDiffeomorphismGhostTransition period hPeriod source plusReference).prod
    (regularFrameDiffeomorphismGhostTransition period hPeriod source minusReference)

theorem smoothRegularFrameGhostTransition_sameGhost
    (source plusReference minusReference : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularFrameGhostFromCoefficients period hPeriod plusReference
        (smoothRegularFrameGhostTransition period hPeriod source plusReference coefficients) =
      regularFrameGhostFromCoefficients period hPeriod minusReference
        (smoothRegularFrameGhostTransition period hPeriod source minusReference coefficients) :=
  (smoothRegularFrameGhostTransition_reconstructs period hPeriod source plusReference
    coefficients).trans
      (smoothRegularFrameGhostTransition_reconstructs period hPeriod source minusReference
        coefficients).symm

end
end P0EFTJanusRegularFrameDiffeomorphismGhostTransition4D
end JanusFormal
