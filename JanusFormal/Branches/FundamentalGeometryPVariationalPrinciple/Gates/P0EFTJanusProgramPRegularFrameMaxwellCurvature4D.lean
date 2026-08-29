import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D

/-!
# Maxwell curvature coefficients in a regular global frame

For a genuine regular frame, the already implemented smooth potential
coefficients, manifold directional derivative, and intrinsic Lie bracket give
the Cartan expression

`F(e_i,e_j) = e_i(A(e_j)) - e_j(A(e_i)) - A([e_i,e_j])`.

This file proves that these coefficients form a smooth skew matrix and lifts
that exact smooth matrix to the canonical scalar `C²` core.  Identification
with the chartwise exterior derivative `dA` is deliberately kept as a
separate tensorial bridge.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellCurvature4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One genuine frame coefficient `A_component(e_index)`. -/
def regularFramePotentialCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : Fin 4) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    potential.toFun component point (metric.frame index point)
  contMDiff_toFun :=
    (potential.contMDiff_eval component).comp
      (metric.frame index).contMDiff

@[simp]
theorem regularFramePotentialCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFramePotentialCoefficient period hPeriod metric potential
        component index point =
      potential.toFun component point (metric.frame index point) :=
  rfl

/-- Directional derivative `e_direction(A_component(e_index))`. -/
def regularFramePotentialDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (direction index : Fin 4) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    frameDerivative period hPeriod Real (RegularFrame period hPeriod metric)
      (regularFramePotentialCoefficient period hPeriod metric potential
        component index) point direction
  contMDiff_toFun := by
    exact (contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real
        (RegularFrame period hPeriod metric)
        (regularFramePotentialCoefficient period hPeriod metric potential
          component index))) direction

/-- The potential evaluated on the intrinsic bracket `[e_i,e_j]`. -/
def regularFrameBracketPotentialCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    potential.toFun component point
      (smoothGhostLieBracket period hPeriod
        (metric.frame first) (metric.frame second) point)
  contMDiff_toFun :=
    (potential.contMDiff_eval component).comp
      (smoothGhostLieBracket period hPeriod
        (metric.frame first) (metric.frame second)).contMDiff

theorem regularFrameBracketPotentialCoefficient_swap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameBracketPotentialCoefficient period hPeriod metric potential
        component first second =
      -regularFrameBracketPotentialCoefficient period hPeriod metric potential
        component second first := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change potential.toFun component point
      (smoothGhostLieBracket period hPeriod
        (metric.frame first) (metric.frame second) point) =
    -potential.toFun component point
      (smoothGhostLieBracket period hPeriod
        (metric.frame second) (metric.frame first) point)
  rw [smoothGhostLieBracket_swap period hPeriod
    (metric.frame first) (metric.frame second)]
  simp

/-- Cartan curvature coefficient in the genuine regular frame. -/
def regularFrameGaugeCurvatureCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    SmoothScalarField period hPeriod :=
  regularFramePotentialDerivative period hPeriod metric potential
      component first second -
    regularFramePotentialDerivative period hPeriod metric potential
      component second first -
    regularFrameBracketPotentialCoefficient period hPeriod metric potential
      component first second

theorem regularFrameGaugeCurvatureCoefficient_swap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component first second =
      -regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component second first := by
  rw [regularFrameGaugeCurvatureCoefficient,
    regularFrameGaugeCurvatureCoefficient,
    regularFrameBracketPotentialCoefficient_swap period hPeriod metric
      potential component first second]
  abel

@[simp]
theorem regularFrameGaugeCurvatureCoefficient_self
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : Fin 4) :
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component index index = 0 := by
  have hSwap := regularFrameGaugeCurvatureCoefficient_swap period hPeriod
    metric potential component index index
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hPoint := congrArg
    (fun field : SmoothScalarField period hPeriod => field point) hSwap
  change
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component index index point = 0
  change
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component index index point =
      -regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component index index point at hPoint
  linarith

/-- Smooth matrix of Cartan curvature coefficients. -/
def regularFrameGaugeCurvatureMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    SmoothFiniteMatrix period hPeriod 4 :=
  fun first second =>
    regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
      component first second

/-- Exact `C²` lift of the smooth Cartan curvature matrix. -/
def regularFrameGaugeCurvatureC2Matrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    C2FiniteMatrix period hPeriod 4 :=
  smoothFiniteMatrixToC2 period hPeriod 4
    (regularFrameGaugeCurvatureMatrix period hPeriod metric potential
      component)

@[simp]
theorem regularFrameGaugeCurvatureC2Matrix_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameGaugeCurvatureC2Matrix period hPeriod metric potential
        component first second =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component first second) :=
  rfl

/-- Summary gate for the smooth/C² regular-frame Cartan coefficients. -/
theorem regular_frame_maxwell_curvature_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    (∀ component first second,
      regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component first second =
        -regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component second first) ∧
      (∀ component first second,
        regularFrameGaugeCurvatureC2Matrix period hPeriod metric potential
            component first second =
          smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
            (regularFrameGaugeCurvatureCoefficient period hPeriod metric
              potential component first second)) := by
  exact ⟨fun component first second =>
      regularFrameGaugeCurvatureCoefficient_swap period hPeriod metric
        potential component first second,
    fun _ _ _ => rfl⟩

end

end P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
end JanusFormal
