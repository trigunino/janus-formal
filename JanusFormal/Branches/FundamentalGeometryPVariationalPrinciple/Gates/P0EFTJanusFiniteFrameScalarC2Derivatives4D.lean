import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGradedScalarGhostAction4D

/-! # Bounded scalar C² derivatives along smooth tangent sections

The actual canonical finite-generator jets and fixed smooth reconstruction
coefficients give bounded first and ordered second derivatives into C⁰.
The coefficient derivative in the second formula is retained explicitly.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameScalarC2Derivatives4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev PhysicalFrame := finiteSmoothTangentFrame period hPeriod
private abbrev PhysicalIndex := Fin (PhysicalFrame period hPeriod).count
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

private abbrev SmoothTangentSection := ContMDiffSection coverModelWithCorners CoverCoordinates ∞
  (fun point : EffectiveQuotient period hPeriod => TangentSpace coverModelWithCorners point)

/-- Intrinsic directional differentiation for arbitrary C∞ tangent sections. -/
def smoothVectorScalarLieDerivative
    (vector : SmoothTangentSection period hPeriod) (field : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod :=
  let derivative := cInfinityScalarLieDerivative period hPeriod vector
    ⟨field.toFun, field.contMDiff_toFun⟩
  ⟨derivative, derivative.contMDiff⟩

@[simp] theorem smoothVectorScalarLieDerivative_apply
    (vector : SmoothTangentSection period hPeriod) (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothVectorScalarLieDerivative period hPeriod vector field point =
      mvfderiv coverModelWithCorners field.toFun point (vector point) := rfl

private def physicalFirstProjection (index : PhysicalIndex period hPeriod) :
    ScalarFrameJet2 (PhysicalIndex period hPeriod) →L[Real] Real :=
  (ContinuousLinearMap.proj index).comp
    ((ContinuousLinearMap.fst Real (PhysicalIndex period hPeriod → Real)
      (PhysicalIndex period hPeriod → PhysicalIndex period hPeriod → Real)).comp
      (ContinuousLinearMap.snd Real Real ((PhysicalIndex period hPeriod → Real) ×
        (PhysicalIndex period hPeriod → PhysicalIndex period hPeriod → Real))))

private def physicalSecondProjection (outer inner : PhysicalIndex period hPeriod) :
    ScalarFrameJet2 (PhysicalIndex period hPeriod) →L[Real] Real :=
  (ContinuousLinearMap.proj inner).comp ((ContinuousLinearMap.proj outer).comp
    ((ContinuousLinearMap.snd Real (PhysicalIndex period hPeriod → Real)
      (PhysicalIndex period hPeriod → PhysicalIndex period hPeriod → Real)).comp
      (ContinuousLinearMap.snd Real Real ((PhysicalIndex period hPeriod → Real) ×
        (PhysicalIndex period hPeriod → PhysicalIndex period hPeriod → Real)))))

private def physicalC2FirstComponent (index : PhysicalIndex period hPeriod) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  ((physicalFirstProjection period hPeriod index).compLeftContinuous Real
    (EffectiveQuotient period hPeriod)).comp (canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod)

private def physicalC2SecondComponent (outer inner : PhysicalIndex period hPeriod) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  ((physicalSecondProjection period hPeriod outer inner).compLeftContinuous Real
    (EffectiveQuotient period hPeriod)).comp (canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod)

private theorem physicalC2FirstComponent_smooth
    (field : SmoothScalarField period hPeriod) (index : PhysicalIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    physicalC2FirstComponent period hPeriod index
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      frameDerivative period hPeriod Real (PhysicalFrame period hPeriod) field point index := rfl

private theorem physicalC2SecondComponent_smooth
    (field : SmoothScalarField period hPeriod) (outer inner : PhysicalIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    physicalC2SecondComponent period hPeriod outer inner
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      frameSecondDerivative period hPeriod (PhysicalFrame period hPeriod) field point outer inner := rfl

private def vectorCoefficient
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod) (index : PhysicalIndex period hPeriod) :=
  generalMetricFiniteFrameCoefficient period hPeriod (PhysicalFrame period hPeriod) reference vector index

private def vectorCoefficientC0
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod) (index : PhysicalIndex period hPeriod) :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (vectorCoefficient period hPeriod reference vector index)

private def vectorCoefficientDerivativeC0
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod) (inner outer : PhysicalIndex period hPeriod) :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (frameDerivativeComponentField period hPeriod (PhysicalFrame period hPeriod)
      (vectorCoefficient period hPeriod reference vector inner) outer)

private def scalarEvaluation (point : EffectiveQuotient period hPeriod) :
    SmoothScalarField period hPeriod →ₗ[Real] Real where
  toFun field := field point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem frameDerivativeComponentField_sum
    {ι : Type*} [Fintype ι] (frame : SmoothD8Frame period hPeriod)
    (fields : ι → SmoothScalarField period hPeriod) (index : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame (∑ i, fields i) index =
      ∑ i, frameDerivativeComponentField period hPeriod frame (fields i) index := by
  let derivative : SmoothScalarField period hPeriod →ₗ[Real] SmoothScalarField period hPeriod :=
    { toFun := fun field => frameDerivativeComponentField period hPeriod frame field index
      map_add' := fun first second => frameDerivativeComponentField_add period hPeriod frame first second index
      map_smul' := fun scalar field => frameDerivativeComponentField_smul period hPeriod frame scalar field index }
  exact map_sum derivative _ Finset.univ

private theorem smoothVectorScalarDerivative_eq_sum
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod) (field : SmoothScalarField period hPeriod) :
    smoothVectorScalarLieDerivative period hPeriod vector field =
      ∑ index : PhysicalIndex period hPeriod, smoothScalarFieldMul period hPeriod
        (vectorCoefficient period hPeriod reference vector index)
        (frameDerivativeComponentField period hPeriod (PhysicalFrame period hPeriod) field index) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change mvfderiv coverModelWithCorners field.toFun point (vector point) =
    scalarEvaluation period hPeriod point (∑ index : PhysicalIndex period hPeriod,
      smoothScalarFieldMul period hPeriod (vectorCoefficient period hPeriod reference vector index)
        (frameDerivativeComponentField period hPeriod (PhysicalFrame period hPeriod) field index))
  rw [map_sum]
  have h := congrArg (mvfderiv coverModelWithCorners field.toFun point)
    (generalMetricFiniteFrame_reconstructs period hPeriod (PhysicalFrame period hPeriod)
      reference vector point)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  exact h

private theorem smoothVectorScalarSecondDerivative_eq_sum
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (outer inner : SmoothTangentSection period hPeriod) (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothVectorScalarLieDerivative period hPeriod outer
      (smoothVectorScalarLieDerivative period hPeriod inner field) point =
      ∑ a : PhysicalIndex period hPeriod, vectorCoefficient period hPeriod reference outer a point *
        ∑ b : PhysicalIndex period hPeriod,
          (vectorCoefficient period hPeriod reference inner b point *
              frameSecondDerivative period hPeriod (PhysicalFrame period hPeriod) field point a b +
            frameDerivative period hPeriod Real (PhysicalFrame period hPeriod)
                (vectorCoefficient period hPeriod reference inner b) point a *
              frameDerivative period hPeriod Real (PhysicalFrame period hPeriod) field point b) := by
  have hOuter := congrArg (scalarEvaluation period hPeriod point)
    (smoothVectorScalarDerivative_eq_sum period hPeriod reference outer
      (smoothVectorScalarLieDerivative period hPeriod inner field))
  rw [map_sum] at hOuter
  apply hOuter.trans
  apply Finset.sum_congr rfl
  intro a _
  change vectorCoefficient period hPeriod reference outer a point *
    frameDerivative period hPeriod Real (PhysicalFrame period hPeriod)
      (smoothVectorScalarLieDerivative period hPeriod inner field) point a = _
  congr 1
  have hInner := congrArg
    (fun scalar => frameDerivativeComponentField period hPeriod (PhysicalFrame period hPeriod) scalar a)
    (smoothVectorScalarDerivative_eq_sum period hPeriod reference inner field)
  rw [frameDerivativeComponentField_sum] at hInner
  simp_rw [frameDerivativeComponentField_mul] at hInner
  have hAt := congrArg (scalarEvaluation period hPeriod point) hInner
  simp only [map_sum, map_add] at hAt
  apply hAt.trans
  apply Finset.sum_congr rfl
  intro b _
  change vectorCoefficient period hPeriod reference inner b point *
      frameSecondDerivative period hPeriod (PhysicalFrame period hPeriod) field point a b +
      frameDerivative period hPeriod Real (PhysicalFrame period hPeriod) field point b *
        frameDerivative period hPeriod Real (PhysicalFrame period hPeriod)
          (vectorCoefficient period hPeriod reference inner b) point a = _
  ring

/-- Genuine bounded first derivative along a fixed arbitrary smooth tangent section. -/
def smoothVectorScalarC2FirstDerivative
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  ∑ index : PhysicalIndex period hPeriod,
    (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
      (vectorCoefficientC0 period hPeriod reference vector index)).comp
        (physicalC2FirstComponent period hPeriod index)

/-- Genuine bounded ordered derivative `outer (inner field)`, including the coefficient derivative. -/
def smoothVectorScalarC2SecondDerivative
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (outer inner : SmoothTangentSection period hPeriod) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  ∑ a : PhysicalIndex period hPeriod,
    (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
      (vectorCoefficientC0 period hPeriod reference outer a)).comp
        (∑ b : PhysicalIndex period hPeriod,
          ((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
            (vectorCoefficientC0 period hPeriod reference inner b)).comp
              (physicalC2SecondComponent period hPeriod a b) +
          (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
            (vectorCoefficientDerivativeC0 period hPeriod reference inner b a)).comp
              (physicalC2FirstComponent period hPeriod b)))

@[simp] theorem smoothVectorScalarC2FirstDerivative_smooth
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod) (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothVectorScalarC2FirstDerivative period hPeriod reference vector
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      smoothVectorScalarLieDerivative period hPeriod vector field point := by
  simp only [smoothVectorScalarC2FirstDerivative, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    physicalC2FirstComponent_smooth]
  have h := congrArg (scalarEvaluation period hPeriod point)
    (smoothVectorScalarDerivative_eq_sum period hPeriod reference vector field)
  rw [map_sum] at h
  exact h.symm

@[simp] theorem smoothVectorScalarC2SecondDerivative_smooth
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (outer inner : SmoothTangentSection period hPeriod) (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothVectorScalarC2SecondDerivative period hPeriod reference outer inner
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      smoothVectorScalarLieDerivative period hPeriod outer
        (smoothVectorScalarLieDerivative period hPeriod inner field) point := by
  simp only [smoothVectorScalarC2SecondDerivative, sum_apply, ContinuousLinearMap.comp_apply,
    add_apply, ContinuousLinearMap.mul_apply', ContinuousMap.sum_apply,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, physicalC2FirstComponent_smooth,
    physicalC2SecondComponent_smooth]
  exact (smoothVectorScalarSecondDerivative_eq_sum period hPeriod reference outer inner field point).symm

def finiteFrameScalarC2FirstDerivative
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  smoothVectorScalarC2FirstDerivative period hPeriod reference (smoothFrameVectorSection period hPeriod frame index)

def finiteFrameScalarC2SecondDerivative
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (outer inner : Fin frame.count) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  smoothVectorScalarC2SecondDerivative period hPeriod reference
    (smoothFrameVectorSection period hPeriod frame outer) (smoothFrameVectorSection period hPeriod frame inner)

@[simp] theorem finiteFrameScalarC2FirstDerivative_smooth
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field : SmoothScalarField period hPeriod) (point : EffectiveQuotient period hPeriod) :
    finiteFrameScalarC2FirstDerivative period hPeriod reference frame index
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      frameDerivative period hPeriod Real frame field point index :=
  smoothVectorScalarC2FirstDerivative_smooth period hPeriod reference
    (smoothFrameVectorSection period hPeriod frame index) field point

@[simp] theorem finiteFrameScalarC2SecondDerivative_smooth
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (outer inner : Fin frame.count)
    (field : SmoothScalarField period hPeriod) (point : EffectiveQuotient period hPeriod) :
    finiteFrameScalarC2SecondDerivative period hPeriod reference frame outer inner
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod field) point =
      frameSecondDerivative period hPeriod frame field point outer inner :=
  smoothVectorScalarC2SecondDerivative_smooth period hPeriod reference
    (smoothFrameVectorSection period hPeriod frame outer) (smoothFrameVectorSection period hPeriod frame inner)
    field point

end
end P0EFTJanusFiniteFrameScalarC2Derivatives4D
end JanusFormal
