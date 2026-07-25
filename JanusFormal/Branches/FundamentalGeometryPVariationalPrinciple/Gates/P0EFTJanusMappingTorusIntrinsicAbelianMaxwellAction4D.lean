import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

/-!
# Intrinsic abelian Maxwell action on the D8 quotient

The local density is the standard contraction
`-1/4 ∑ₐ Fₐ,μν Fₐ^μν`, formed from the derived curvature `F = dA` and the
actual inverse metric.  A regular global line records only the smooth scalar
descent of the three quadratic contractions; it does not supply a curvature
or an invariance law.  The integrated affine expansion, first derivative and
exact gauge invariance are proved from the local construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private def coordinateBasisVector (index : Index4) : Vector4 :=
  Pi.single index 1

private def coordinateBasisPair
    (first second : Index4) : Fin 2 → Vector4 :=
  ![coordinateBasisVector first, coordinateBasisVector second]

/-- Matrix of the derived abelian curvature in one holonomic chart. -/
def localGaugeCurvatureMatrix
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Matrix4 :=
  fun first second =>
    localGaugeCurvature period hPeriod potential component patch coordinate
      (coordinateBasisPair first second)

/-- The coordinate matrix of `F = dA` is skew-symmetric. -/
theorem localGaugeCurvatureMatrix_transpose
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (localGaugeCurvatureMatrix period hPeriod potential component patch
      coordinate).transpose =
      -(localGaugeCurvatureMatrix period hPeriod potential component patch
        coordinate) := by
  ext first second
  unfold localGaugeCurvatureMatrix coordinateBasisPair
  have hSwap :=
    (localGaugeCurvature period hPeriod potential component patch coordinate).map_swap
      (v := ![coordinateBasisVector first, coordinateBasisVector second])
      (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  have hVector :
      (![coordinateBasisVector first, coordinateBasisVector second] ∘
          Equiv.swap (0 : Fin 2) 1) =
        ![coordinateBasisVector second, coordinateBasisVector first] := by
    funext index
    fin_cases index <;> rfl
  rw [hVector] at hSwap
  exact hSwap

/-- Metric contraction of two abelian field strengths. -/
def localMaxwellPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ component : Fin 2,
    ∑ μ : Index4, ∑ ν : Index4, ∑ ρ : Index4, ∑ σ : Index4,
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ μ ρ *
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ ν σ *
        localGaugeCurvatureMatrix period hPeriod first component patch
          coordinate μ ν *
        localGaugeCurvatureMatrix period hPeriod second component patch
          coordinate ρ σ

/-- Local Maxwell scalar `-1/4 F²`. -/
def localMaxwellLagrangian
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  -(1 / 4 : Real) *
    localMaxwellPairing period hPeriod metric potential potential patch
      coordinate

theorem localGaugeCurvature_add
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localGaugeCurvature period hPeriod (first + second) component patch =
      localGaugeCurvature period hPeriod first component patch +
        localGaugeCurvature period hPeriod second component patch := by
  funext coordinate
  rw [localGaugeCurvature, localGaugeOneForm_add]
  exact extDeriv_add
    ((localGaugeOneForm_contDiff period hPeriod first component patch)
      |>.differentiable (by simp) coordinate)
    ((localGaugeOneForm_contDiff period hPeriod second component patch)
      |>.differentiable (by simp) coordinate)

theorem localGaugeOneForm_smul
    (scalar : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localGaugeOneForm period hPeriod (scalar • potential) component patch =
      scalar • localGaugeOneForm period hPeriod potential component patch := by
  funext coordinate
  simp [localGaugeOneForm, localGaugeCoefficient,
    smoothAbelianGaugePotential_smul_apply, Finset.smul_sum, smul_smul]

theorem localGaugeCurvature_smul
    (scalar : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localGaugeCurvature period hPeriod (scalar • potential) component patch =
      scalar • localGaugeCurvature period hPeriod potential component patch := by
  funext coordinate
  rw [localGaugeCurvature, localGaugeOneForm_smul]
  exact extDeriv_smul scalar
    (localGaugeOneForm period hPeriod potential component patch)

/-- Affine line in the intrinsic gauge-potential space. -/
def gaugePotentialLine
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (epsilon : Real) :
    SmoothAbelianGaugePotential period hPeriod :=
  potential + epsilon • variation

theorem localGaugeCurvatureMatrix_add
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localGaugeCurvatureMatrix period hPeriod (first + second) component patch
        coordinate =
      localGaugeCurvatureMatrix period hPeriod first component patch coordinate +
        localGaugeCurvatureMatrix period hPeriod second component patch
          coordinate := by
  ext μ ν
  change
    localGaugeCurvature period hPeriod (first + second) component patch
        coordinate (coordinateBasisPair μ ν) =
      (localGaugeCurvature period hPeriod first component patch coordinate +
        localGaugeCurvature period hPeriod second component patch coordinate)
        (coordinateBasisPair μ ν)
  rw [localGaugeCurvature_add]
  rfl

theorem localGaugeCurvatureMatrix_smul
    (scalar : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localGaugeCurvatureMatrix period hPeriod (scalar • potential) component
        patch coordinate =
      scalar • localGaugeCurvatureMatrix period hPeriod potential component
        patch coordinate := by
  ext μ ν
  change
    localGaugeCurvature period hPeriod (scalar • potential) component patch
        coordinate (coordinateBasisPair μ ν) =
      (scalar •
        localGaugeCurvature period hPeriod potential component patch coordinate)
        (coordinateBasisPair μ ν)
  rw [localGaugeCurvature_smul]
  rfl

theorem localGaugeCurvatureMatrix_line
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (epsilon : Real)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localGaugeCurvatureMatrix period hPeriod
        (gaugePotentialLine period hPeriod potential variation epsilon)
        component patch coordinate =
      localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate +
        epsilon •
          localGaugeCurvatureMatrix period hPeriod variation component patch
            coordinate := by
  ext first second
  simp only [localGaugeCurvatureMatrix, gaugePotentialLine, Matrix.add_apply,
    Matrix.smul_apply]
  rw [localGaugeCurvature_add, localGaugeCurvature_smul]
  rfl

theorem localMaxwellPairing_add_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellPairing period hPeriod metric (first + second) third patch
        coordinate =
      localMaxwellPairing period hPeriod metric first third patch coordinate +
        localMaxwellPairing period hPeriod metric second third patch
          coordinate := by
  simp only [localMaxwellPairing, localGaugeCurvatureMatrix_add,
    Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem localMaxwellPairing_add_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellPairing period hPeriod metric first (second + third) patch
        coordinate =
      localMaxwellPairing period hPeriod metric first second patch coordinate +
        localMaxwellPairing period hPeriod metric first third patch
          coordinate := by
  simp only [localMaxwellPairing, localGaugeCurvatureMatrix_add,
    Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem localMaxwellPairing_smul_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellPairing period hPeriod metric (scalar • first) second patch
        coordinate =
      scalar *
        localMaxwellPairing period hPeriod metric first second patch
          coordinate := by
  simp only [localMaxwellPairing, localGaugeCurvatureMatrix_smul,
    Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro ρ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem localMaxwellPairing_smul_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellPairing period hPeriod metric first (scalar • second) patch
        coordinate =
      scalar *
        localMaxwellPairing period hPeriod metric first second patch
          coordinate := by
  simp only [localMaxwellPairing, localGaugeCurvatureMatrix_smul,
    Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro ρ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem localMaxwellPairing_line_expansion
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (epsilon : Real) :
    localMaxwellPairing period hPeriod metric
        (gaugePotentialLine period hPeriod potential variation epsilon)
        (gaugePotentialLine period hPeriod potential variation epsilon)
        patch coordinate =
      localMaxwellPairing period hPeriod metric potential potential patch
          coordinate +
        epsilon *
          (localMaxwellPairing period hPeriod metric variation potential patch
              coordinate +
            localMaxwellPairing period hPeriod metric potential variation patch
              coordinate) +
        epsilon ^ 2 *
          localMaxwellPairing period hPeriod metric variation variation patch
            coordinate := by
  unfold gaugePotentialLine
  rw [localMaxwellPairing_add_left, localMaxwellPairing_add_right,
    localMaxwellPairing_add_right, localMaxwellPairing_smul_right,
    localMaxwellPairing_smul_left, localMaxwellPairing_smul_right,
    localMaxwellPairing_smul_left]
  ring

theorem localMaxwellLagrangian_line_expansion
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (epsilon : Real) :
    localMaxwellLagrangian period hPeriod metric
        (gaugePotentialLine period hPeriod potential variation epsilon)
        patch coordinate =
      localMaxwellLagrangian period hPeriod metric potential patch coordinate +
        epsilon * (-(1 / 4 : Real) *
          (localMaxwellPairing period hPeriod metric variation potential patch
              coordinate +
            localMaxwellPairing period hPeriod metric potential variation patch
              coordinate)) +
        epsilon ^ 2 * (-(1 / 4 : Real) *
          localMaxwellPairing period hPeriod metric variation variation patch
            coordinate) := by
  unfold localMaxwellLagrangian
  rw [localMaxwellPairing_line_expansion]
  ring

theorem localMaxwellPairing_gaugeTransform_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (potential second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellPairing period hPeriod metric
        (gaugeTransform period hPeriod parameter potential) second patch
        coordinate =
      localMaxwellPairing period hPeriod metric potential second patch
        coordinate := by
  simp only [localMaxwellPairing]
  apply Finset.sum_congr rfl
  intro component _
  have hMatrix :
      localGaugeCurvatureMatrix period hPeriod
          (gaugeTransform period hPeriod parameter potential) component patch
          coordinate =
        localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate := by
    ext μ ν
    change
      localGaugeCurvature period hPeriod
          (gaugeTransform period hPeriod parameter potential) component patch
          coordinate (coordinateBasisPair μ ν) =
        localGaugeCurvature period hPeriod potential component patch coordinate
          (coordinateBasisPair μ ν)
    rw [localGaugeCurvature_gaugeTransform]
  rw [hMatrix]

theorem localMaxwellPairing_gaugeTransform_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (first potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellPairing period hPeriod metric first
        (gaugeTransform period hPeriod parameter potential) patch coordinate =
      localMaxwellPairing period hPeriod metric first potential patch
        coordinate := by
  simp only [localMaxwellPairing]
  apply Finset.sum_congr rfl
  intro component _
  have hMatrix :
      localGaugeCurvatureMatrix period hPeriod
          (gaugeTransform period hPeriod parameter potential) component patch
          coordinate =
        localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate := by
    ext μ ν
    change
      localGaugeCurvature period hPeriod
          (gaugeTransform period hPeriod parameter potential) component patch
          coordinate (coordinateBasisPair μ ν) =
        localGaugeCurvature period hPeriod potential component patch coordinate
          (coordinateBasisPair μ ν)
    rw [localGaugeCurvature_gaugeTransform]
  rw [hMatrix]

theorem localMaxwellLagrangian_gaugeTransform
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellLagrangian period hPeriod metric
        (gaugeTransform period hPeriod parameter potential) patch coordinate =
      localMaxwellLagrangian period hPeriod metric potential patch coordinate := by
  unfold localMaxwellLagrangian
  rw [localMaxwellPairing_gaugeTransform_left,
    localMaxwellPairing_gaugeTransform_right]

/-- Regular global Maxwell line.  The three smooth scalar fields are the
atlas descent of contractions computed from the already derived `dA`. -/
structure RegularIntrinsicMaxwellLine
    (metric : RegularGeneralLorentzMetric period hPeriod) where
  potential : SmoothAbelianGaugePotential period hPeriod
  variation : SmoothAbelianGaugePotential period hPeriod
  basePairing : SmoothScalarField period hPeriod
  mixedPairing : SmoothScalarField period hPeriod
  variationPairing : SmoothScalarField period hPeriod
  basePairing_eq : ∀
      (patch : SmoothHolonomicFrameChart4 period hPeriod)
      (coordinate : Vector4),
    basePairing (patch.coordinateMap coordinate) =
      localMaxwellPairing period hPeriod metric.metric potential potential
        patch coordinate
  mixedPairing_eq : ∀
      (patch : SmoothHolonomicFrameChart4 period hPeriod)
      (coordinate : Vector4),
    mixedPairing (patch.coordinateMap coordinate) =
      localMaxwellPairing period hPeriod metric.metric variation potential
          patch coordinate +
        localMaxwellPairing period hPeriod metric.metric potential variation
          patch coordinate
  variationPairing_eq : ∀
      (patch : SmoothHolonomicFrameChart4 period hPeriod)
      (coordinate : Vector4),
    variationPairing (patch.coordinateMap coordinate) =
      localMaxwellPairing period hPeriod metric.metric variation variation
        patch coordinate

/-- Global smooth Maxwell density on the regular functional domain. -/
def regularMaxwellDensityField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    metric.volume point * (-(1 / 4 : Real) * data.basePairing point)
  contMDiff_toFun := metric.volume.contMDiff_toFun.mul
    (contMDiff_const.mul data.basePairing.contMDiff_toFun)

/-- Global smooth first-variation density. -/
def regularMaxwellFirstVariationField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    metric.volume point * (-(1 / 4 : Real) * data.mixedPairing point)
  contMDiff_toFun := metric.volume.contMDiff_toFun.mul
    (contMDiff_const.mul data.mixedPairing.contMDiff_toFun)

/-- Global smooth quadratic remainder density. -/
def regularMaxwellQuadraticRemainderField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    metric.volume point * (-(1 / 4 : Real) * data.variationPairing point)
  contMDiff_toFun := metric.volume.contMDiff_toFun.mul
    (contMDiff_const.mul data.variationPairing.contMDiff_toFun)

/-- Intrinsic Maxwell action for a finite reference measure. -/
def intrinsicMaxwellAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (pairing : SmoothScalarField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, metric.volume point * (-(1 / 4 : Real) * pairing point) ∂measure

def intrinsicMaxwellFirstVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, regularMaxwellFirstVariationField period hPeriod metric data point
    ∂measure

def intrinsicMaxwellQuadraticRemainder
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point,
    regularMaxwellQuadraticRemainderField period hPeriod metric data point
      ∂measure

private theorem smoothScalar_integrable
    (field : SmoothScalarField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable field measure :=
  field.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact integrated quadratic expansion of the intrinsic Maxwell action. -/
theorem intrinsicMaxwellAction_line_expansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (epsilon : Real) :
    intrinsicMaxwellAction period hPeriod metric
        { toFun := fun point =>
            data.basePairing point + epsilon * data.mixedPairing point +
              epsilon ^ 2 * data.variationPairing point
          contMDiff_toFun :=
            data.basePairing.contMDiff_toFun.add
              (contMDiff_const.mul data.mixedPairing.contMDiff_toFun) |>.add
              (contMDiff_const.mul data.variationPairing.contMDiff_toFun) }
        measure =
      intrinsicMaxwellAction period hPeriod metric data.basePairing measure +
        epsilon *
          intrinsicMaxwellFirstVariation period hPeriod metric data measure +
        epsilon ^ 2 *
          intrinsicMaxwellQuadraticRemainder period hPeriod metric data
            measure := by
  unfold intrinsicMaxwellAction intrinsicMaxwellFirstVariation
    intrinsicMaxwellQuadraticRemainder regularMaxwellFirstVariationField
    regularMaxwellQuadraticRemainderField
  have hBase := smoothScalar_integrable period hPeriod
    (regularMaxwellDensityField period hPeriod metric data) measure
  have hFirst := (smoothScalar_integrable period hPeriod
    (regularMaxwellFirstVariationField period hPeriod metric data) measure)
      |>.const_mul epsilon
  have hRemainder := (smoothScalar_integrable period hPeriod
    (regularMaxwellQuadraticRemainderField period hPeriod metric data) measure)
      |>.const_mul (epsilon ^ 2)
  rw [show (fun point =>
      metric.volume point *
        (-(1 / 4 : Real) *
          (data.basePairing point + epsilon * data.mixedPairing point +
            epsilon ^ 2 * data.variationPairing point))) =
      fun point =>
        regularMaxwellDensityField period hPeriod metric data point +
          epsilon *
            regularMaxwellFirstVariationField period hPeriod metric data point +
          epsilon ^ 2 *
            regularMaxwellQuadraticRemainderField period hPeriod metric data
              point by
    funext point
    simp only [regularMaxwellDensityField,
      regularMaxwellFirstVariationField,
      regularMaxwellQuadraticRemainderField]
    ring]
  change
    (∫ point,
      regularMaxwellDensityField period hPeriod metric data point +
        epsilon *
          regularMaxwellFirstVariationField period hPeriod metric data point +
        epsilon ^ 2 *
          regularMaxwellQuadraticRemainderField period hPeriod metric data point
      ∂measure) =
      (∫ point, regularMaxwellDensityField period hPeriod metric data point
        ∂measure) +
        epsilon *
          (∫ point,
            regularMaxwellFirstVariationField period hPeriod metric data point
            ∂measure) +
        epsilon ^ 2 *
          (∫ point,
            regularMaxwellQuadraticRemainderField period hPeriod metric data
              point ∂measure)
  calc
    _ = ∫ point,
        regularMaxwellDensityField period hPeriod metric data point +
          (epsilon *
              regularMaxwellFirstVariationField period hPeriod metric data
                point +
            epsilon ^ 2 *
              regularMaxwellQuadraticRemainderField period hPeriod metric data
                point) ∂measure := by
      congr 1
      funext point
      ring
    _ = (∫ point,
          regularMaxwellDensityField period hPeriod metric data point
          ∂measure) +
        ∫ point,
          epsilon *
              regularMaxwellFirstVariationField period hPeriod metric data
                point +
            epsilon ^ 2 *
              regularMaxwellQuadraticRemainderField period hPeriod metric data
                point ∂measure :=
      integral_add hBase (hFirst.add hRemainder)
    _ = _ := by
      rw [integral_add hFirst hRemainder, integral_const_mul,
        integral_const_mul]
      ring

/-- The integrated Maxwell first variation is the actual derivative of its
action along every regular intrinsic gauge line. -/
theorem intrinsicMaxwellAction_line_hasDerivAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasDerivAt
      (fun epsilon : Real =>
        intrinsicMaxwellAction period hPeriod metric
          { toFun := fun point =>
              data.basePairing point + epsilon * data.mixedPairing point +
                epsilon ^ 2 * data.variationPairing point
            contMDiff_toFun :=
              data.basePairing.contMDiff_toFun.add
                (contMDiff_const.mul data.mixedPairing.contMDiff_toFun) |>.add
                (contMDiff_const.mul data.variationPairing.contMDiff_toFun) }
          measure)
      (intrinsicMaxwellFirstVariation period hPeriod metric data measure) 0 := by
  rw [show (fun epsilon : Real =>
      intrinsicMaxwellAction period hPeriod metric
        { toFun := fun point =>
            data.basePairing point + epsilon * data.mixedPairing point +
              epsilon ^ 2 * data.variationPairing point
          contMDiff_toFun :=
            data.basePairing.contMDiff_toFun.add
              (contMDiff_const.mul data.mixedPairing.contMDiff_toFun) |>.add
              (contMDiff_const.mul data.variationPairing.contMDiff_toFun) }
        measure) =
      fun epsilon =>
        intrinsicMaxwellAction period hPeriod metric data.basePairing measure +
          epsilon *
            intrinsicMaxwellFirstVariation period hPeriod metric data measure +
          epsilon ^ 2 *
            intrinsicMaxwellQuadraticRemainder period hPeriod metric data
              measure by
    funext epsilon
    exact intrinsicMaxwellAction_line_expansion period hPeriod metric data
      measure epsilon]
  have hLinear := ((hasDerivAt_id (𝕜 := Real) 0).mul_const
    (intrinsicMaxwellFirstVariation period hPeriod metric data measure))
      |>.const_add
        (intrinsicMaxwellAction period hPeriod metric data.basePairing measure)
  have hQuadratic := ((hasDerivAt_id (𝕜 := Real) 0).pow 2).mul_const
    (intrinsicMaxwellQuadraticRemainder period hPeriod metric data measure)
  change HasDerivAt
    ((fun epsilon : Real =>
        intrinsicMaxwellAction period hPeriod metric data.basePairing measure +
          epsilon *
            intrinsicMaxwellFirstVariation period hPeriod metric data measure) +
      (fun epsilon : Real =>
        epsilon ^ 2 *
          intrinsicMaxwellQuadraticRemainder period hPeriod metric data
            measure)) _ 0
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

/-- Gauge transformation of a regular line reuses the same descended
quadratic scalars because `d(A + dλ) = dA`. -/
def RegularIntrinsicMaxwellLine.gaugeTransform
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    RegularIntrinsicMaxwellLine period hPeriod metric where
  potential := P0EFTJanusMappingTorusAbelianGaugeBRST4D.gaugeTransform
    period hPeriod parameter data.potential
  variation := data.variation
  basePairing := data.basePairing
  mixedPairing := data.mixedPairing
  variationPairing := data.variationPairing
  basePairing_eq patch coordinate := by
    rw [data.basePairing_eq, localMaxwellPairing_gaugeTransform_left,
      localMaxwellPairing_gaugeTransform_right]
  mixedPairing_eq patch coordinate := by
    rw [data.mixedPairing_eq, localMaxwellPairing_gaugeTransform_right,
      localMaxwellPairing_gaugeTransform_left]
  variationPairing_eq := data.variationPairing_eq

@[simp]
theorem intrinsicMaxwellAction_gaugeTransform
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    intrinsicMaxwellAction period hPeriod metric
        (data.gaugeTransform period hPeriod metric parameter).basePairing
        measure =
      intrinsicMaxwellAction period hPeriod metric data.basePairing measure :=
  rfl

end

end P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
end JanusFormal
