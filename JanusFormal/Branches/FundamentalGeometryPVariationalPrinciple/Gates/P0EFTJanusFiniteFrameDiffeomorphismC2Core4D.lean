import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameBRSTPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

/-! # Completed diffeomorphism coefficients in finite generating families

An arbitrary smooth Lorentz metric supplies the established redundant dual
coefficients. Fixed smooth transition matrices act boundedly on completed C²
coefficients and preserve the reconstructed smooth vector. No tangent basis
or inverse of a redundant Gram matrix is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameDiffeomorphismC2Core4D

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
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

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

private abbrev TangentSection := ContMDiffSection coverModelWithCorners CoverCoordinates ∞
  (fun point : EffectiveQuotient period hPeriod => TangentSpace coverModelWithCorners point)

abbrev FiniteFrameDiffeomorphismC2Core (frame : SmoothD8Frame period hPeriod) :=
  Fin frame.count → CanonicalPhysicalScalarC2JetCore period hPeriod

abbrev FiniteFrameDiffeomorphismC0Core (frame : SmoothD8Frame period hPeriod) :=
  Fin frame.count → C(EffectiveQuotient period hPeriod, Real)

/-- The unrestricted total B, antighost, and ghost coefficient packets. -/
abbrev FiniteFrameDiffeomorphismNonminimalC2Core (frame : SmoothD8Frame period hPeriod) :=
  FiniteFrameDiffeomorphismC2Core period hPeriod frame ×
    (FiniteFrameDiffeomorphismC2Core period hPeriod frame ×
      FiniteFrameDiffeomorphismC2Core period hPeriod frame)

abbrev FiniteFrameDiffeomorphismNonminimalC0Core (frame : SmoothD8Frame period hPeriod) :=
  FiniteFrameDiffeomorphismC0Core period hPeriod frame ×
    (FiniteFrameDiffeomorphismC0Core period hPeriod frame ×
      FiniteFrameDiffeomorphismC0Core period hPeriod frame)

@[implicit_reducible]
def finiteFrameDiffeomorphismC2CoreCompleteSpace (frame : SmoothD8Frame period hPeriod) :
    CompleteSpace (FiniteFrameDiffeomorphismC2Core period hPeriod frame) := by
  letI : CompleteSpace (C2Scalar period hPeriod) :=
    canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
  infer_instance

def finiteFrameDiffeomorphismC2ToContinuous (frame : SmoothD8Frame period hPeriod) :
    FiniteFrameDiffeomorphismC2Core period hPeriod frame →L[Real]
      FiniteFrameDiffeomorphismC0Core period hPeriod frame :=
  ContinuousLinearMap.pi fun index =>
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp (ContinuousLinearMap.proj index)

@[simp] theorem finiteFrameDiffeomorphismC2ToContinuous_apply
    (frame : SmoothD8Frame period hPeriod)
    (coefficients : FiniteFrameDiffeomorphismC2Core period hPeriod frame) (index : Fin frame.count) :
    finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame coefficients index =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (coefficients index) := rfl

def finiteFrameSmoothDiffeomorphismC2Coefficients
    (frame : SmoothD8Frame period hPeriod) (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : TangentSection period hPeriod) : FiniteFrameDiffeomorphismC2Core period hPeriod frame :=
  fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (generalMetricFiniteFrameCoefficient period hPeriod frame reference vector index)

def finiteFrameSmoothDiffeomorphismC0Coefficients
    (frame : SmoothD8Frame period hPeriod) (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : TangentSection period hPeriod) : FiniteFrameDiffeomorphismC0Core period hPeriod frame :=
  fun index => smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (generalMetricFiniteFrameCoefficient period hPeriod frame reference vector index)

theorem finiteFrameDiffeomorphismC2ToContinuous_smooth
    (frame : SmoothD8Frame period hPeriod) (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : TangentSection period hPeriod) :
    finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame
        (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame reference vector) =
      finiteFrameSmoothDiffeomorphismC0Coefficients period hPeriod frame reference vector := by
  funext index
  exact canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod _

/-- The completed lift retains the actual tangent vector through its continuous coefficients. -/
theorem finiteFrameSmoothDiffeomorphismC2Coefficients_reconstructs
    (frame : SmoothD8Frame period hPeriod) (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : TangentSection period hPeriod) (point : EffectiveQuotient period hPeriod) :
    (∑ index : Fin frame.count,
      finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame
          (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame reference vector)
          index point • frame.vectorAt point index) = vector point := by
  rw [finiteFrameDiffeomorphismC2ToContinuous_smooth]
  exact (generalMetricFiniteFrame_reconstructs period hPeriod frame reference vector point).symm

/-- Smooth assembly uses the finite generators, allowing redundant coefficients. -/
def finiteFrameVectorFromSmoothCoefficients
    (frame : SmoothD8Frame period hPeriod)
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod) : TangentSection period hPeriod :=
  ∑ index : Fin frame.count,
    { toFun := fun point => coefficients index point • frame.vectorAt point index
      contMDiff_toFun :=
        ((coefficients index).contMDiff_toFun.of_le (by simp)).smul_section
          (frame.contMDiff_vector index) }

@[simp] theorem finiteFrameVectorFromSmoothCoefficients_apply
    (frame : SmoothD8Frame period hPeriod)
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameVectorFromSmoothCoefficients period hPeriod frame coefficients point =
      ∑ index : Fin frame.count, coefficients index point • frame.vectorAt point index := by
  let evaluation : TangentSection period hPeriod →ₗ[Real] TangentSpace coverModelWithCorners point :=
    { toFun := fun vector => vector point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact map_sum evaluation _ Finset.univ

theorem finiteFrameVectorFromSmoothCoefficients_reconstructs
    (frame : SmoothD8Frame period hPeriod) (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : TangentSection period hPeriod) :
    finiteFrameVectorFromSmoothCoefficients period hPeriod frame
        (generalMetricFiniteFrameCoefficient period hPeriod frame reference vector) = vector := by
  apply ContMDiffSection.ext
  intro point
  rw [finiteFrameVectorFromSmoothCoefficients_apply]
  exact (generalMetricFiniteFrame_reconstructs period hPeriod frame reference vector point).symm

/-- Target dual coefficients of the source generators form a smooth rectangular transition matrix. -/
def finiteFrameDiffeomorphismTransitionCoefficient
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (output : Fin target.count) (input : Fin source.count) : SmoothScalarField period hPeriod :=
  generalMetricFiniteFrameCoefficient period hPeriod target targetReference
    (smoothFrameVectorSection period hPeriod source input) output

theorem finiteFrameDiffeomorphismTransitionCoefficient_sum
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (coefficients : Fin source.count → SmoothScalarField period hPeriod) (output : Fin target.count) :
    generalMetricFiniteFrameCoefficient period hPeriod target targetReference
        (finiteFrameVectorFromSmoothCoefficients period hPeriod source coefficients) output =
      ∑ input : Fin source.count, smoothScalarFieldMul period hPeriod
        (finiteFrameDiffeomorphismTransitionCoefficient period hPeriod source target targetReference output input)
        (coefficients input) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  let evaluation : SmoothScalarField period hPeriod →ₗ[Real] Real :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  change generalMetricFiniteFrameCoefficientAt period hPeriod target targetReference point output
      (finiteFrameVectorFromSmoothCoefficients period hPeriod source coefficients point) =
    evaluation (∑ input : Fin source.count, smoothScalarFieldMul period hPeriod
      (finiteFrameDiffeomorphismTransitionCoefficient period hPeriod source target targetReference output input)
      (coefficients input))
  rw [finiteFrameVectorFromSmoothCoefficients_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [map_smul]
  change coefficients input point *
      finiteFrameDiffeomorphismTransitionCoefficient period hPeriod source target targetReference output input point =
    finiteFrameDiffeomorphismTransitionCoefficient period hPeriod source target targetReference output input point *
      coefficients input point
  exact mul_comm _ _

def finiteFrameDiffeomorphismC2Transition
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod) :
    FiniteFrameDiffeomorphismC2Core period hPeriod source →L[Real]
      FiniteFrameDiffeomorphismC2Core period hPeriod target :=
  ContinuousLinearMap.pi fun output => ∑ input : Fin source.count,
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (finiteFrameDiffeomorphismTransitionCoefficient period hPeriod source target targetReference output input))).comp
      (ContinuousLinearMap.proj input)

@[simp] theorem finiteFrameDiffeomorphismC2Transition_apply
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (coefficients : FiniteFrameDiffeomorphismC2Core period hPeriod source) (output : Fin target.count) :
    finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference coefficients output =
      ∑ input : Fin source.count, canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (finiteFrameDiffeomorphismTransitionCoefficient period hPeriod source target targetReference output input))
        (coefficients input) := by
  simp only [finiteFrameDiffeomorphismC2Transition, ContinuousLinearMap.pi_apply,
    sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem finiteFrameDiffeomorphismC2Transition_smooth_coefficients
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (coefficients : Fin source.count → SmoothScalarField period hPeriod) :
    finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference
        (fun input => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients input)) =
      finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod target targetReference
        (finiteFrameVectorFromSmoothCoefficients period hPeriod source coefficients) := by
  funext output
  rw [finiteFrameDiffeomorphismC2Transition_apply]
  unfold finiteFrameSmoothDiffeomorphismC2Coefficients
  rw [finiteFrameDiffeomorphismTransitionCoefficient_sum, map_sum]
  apply Finset.sum_congr rfl
  intro input _
  exact canonicalPhysicalScalarC2JetCoreProduct_smooth period hPeriod _ _

/-- Canonical lifts in two finite families represent the same complete smooth vector. -/
theorem finiteFrameDiffeomorphismC2Transition_smooth_vector
    (source target : SmoothD8Frame period hPeriod)
    (sourceReference targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : TangentSection period hPeriod) :
    finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference
        (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod source sourceReference vector) =
      finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod target targetReference vector := by
  change finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference
      (fun input => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (generalMetricFiniteFrameCoefficient period hPeriod source sourceReference vector input)) = _
  rw [finiteFrameDiffeomorphismC2Transition_smooth_coefficients,
    finiteFrameVectorFromSmoothCoefficients_reconstructs]

theorem finiteFrameDiffeomorphismC2Transition_reconstructs
    (source target : SmoothD8Frame period hPeriod)
    (sourceReference targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : TangentSection period hPeriod) (point : EffectiveQuotient period hPeriod) :
    (∑ index : Fin target.count,
      finiteFrameDiffeomorphismC2ToContinuous period hPeriod target
          (finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference
            (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod source sourceReference vector))
          index point • target.vectorAt point index) = vector point := by
  rw [finiteFrameDiffeomorphismC2Transition_smooth_vector]
  exact finiteFrameSmoothDiffeomorphismC2Coefficients_reconstructs period hPeriod target
    targetReference vector point

def finiteFrameSmoothDiffeomorphismNonminimalC2Core
    (frame : SmoothD8Frame period hPeriod) (reference : SmoothGeneralLorentzMetric period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame :=
  (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame reference fields.nakanishiLautrup.field,
    (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame reference fields.antighost.field,
      finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame reference fields.ghost.field))

def finiteFrameDiffeomorphismNonminimalC2ToContinuous (frame : SmoothD8Frame period hPeriod) :
    FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame →L[Real]
      FiniteFrameDiffeomorphismNonminimalC0Core period hPeriod frame :=
  (finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).prodMap
    ((finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).prodMap
      (finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame))

theorem finiteFrameDiffeomorphismNonminimalC2ToContinuous_smooth
    (frame : SmoothD8Frame period hPeriod) (reference : SmoothGeneralLorentzMetric period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFrameDiffeomorphismNonminimalC2ToContinuous period hPeriod frame
        (finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame reference fields) =
      (finiteFrameSmoothDiffeomorphismC0Coefficients period hPeriod frame reference fields.nakanishiLautrup.field,
        (finiteFrameSmoothDiffeomorphismC0Coefficients period hPeriod frame reference fields.antighost.field,
          finiteFrameSmoothDiffeomorphismC0Coefficients period hPeriod frame reference fields.ghost.field)) := by
  simp only [finiteFrameDiffeomorphismNonminimalC2ToContinuous,
    finiteFrameSmoothDiffeomorphismNonminimalC2Core, ContinuousLinearMap.coe_prodMap', Prod.map,
    finiteFrameDiffeomorphismC2ToContinuous_smooth]

def finiteFrameDiffeomorphismNonminimalC2Transition
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod) :
    FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source →L[Real]
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod target :=
  (finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference).prodMap
    ((finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference).prodMap
      (finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference))

theorem finiteFrameDiffeomorphismNonminimalC2Transition_smooth
    (source target : SmoothD8Frame period hPeriod)
    (sourceReference targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source target targetReference
        (finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod source sourceReference fields) =
      finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod target targetReference fields := by
  simp only [finiteFrameDiffeomorphismNonminimalC2Transition,
    finiteFrameSmoothDiffeomorphismNonminimalC2Core, ContinuousLinearMap.coe_prodMap', Prod.map,
    finiteFrameDiffeomorphismC2Transition_smooth_vector]

end
end P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
end JanusFormal
