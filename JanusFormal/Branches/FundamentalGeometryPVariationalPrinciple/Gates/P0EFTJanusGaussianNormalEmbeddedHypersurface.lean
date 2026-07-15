import Mathlib.Tactic.FinCases
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEHGHYCancellation

/-!
# An embedded hypersurface in an affine Gaussian-normal chart

This file gives an explicit local four-coordinate model with one normal
coordinate `n` and three tangential coordinates.  The hypersurface is the
embedded level set `n = 0`.  Its metric is

`g = epsilon dn^2 + (h_ab + n q_ab) dx^a dx^b`,

with unit lapse and zero shift.  At the hypersurface the inverse, all first
coordinate derivatives, and the Levi--Civita Christoffel symbols are computed
from finite sums.  For the convention

`B_ab = (nabla_a normalFlat)_b`

the result is `B_ab = sigma q_ab / 2`; the opposite convention changes the
sign.  Here `sigma` records the chosen orientation of the unit normal and
`q_ab = partial_n h_ab`.

This is a local affine, pointwise model.  It imposes no inertia condition on
the tangential metric and asserts no global tubular neighborhood, manifold
atlas, boundary integral, junction condition, or evolution theorem.
-/

namespace JanusFormal
namespace P0EFTJanusGaussianNormalEmbeddedHypersurface

set_option autoImplicit false

noncomputable section

open P0EFTJanusGaussianNormalEHGHYCancellation

abbrev Matrix3 := P0EFTJanusGaussianNormalEHGHYCancellation.Matrix3
abbrev Matrix4 := P0EFTJanusGaussianNormalEHGHYCancellation.Matrix4
abbrev Coordinate4 := Fin 4 → ℝ
abbrev TangentCoordinate3 := Fin 3 → ℝ

/-- Whether the Gaussian normal coordinate is spacelike or timelike. -/
inductive NormalSignature where
  | spacelike
  | timelike
  deriving DecidableEq

/-- The squared norm of the coordinate unit normal. -/
def NormalSignature.epsilon : NormalSignature → ℝ
  | .spacelike => 1
  | .timelike => -1

@[simp]
theorem NormalSignature.epsilon_mul_self (signature : NormalSignature) :
    signature.epsilon * signature.epsilon = 1 := by
  cases signature <;> norm_num [NormalSignature.epsilon]

/-- The two orientations of the signed unit normal. -/
inductive NormalOrientation where
  | increasing
  | decreasing
  deriving DecidableEq

def NormalOrientation.sign : NormalOrientation → ℝ
  | .increasing => 1
  | .decreasing => -1

@[simp]
theorem NormalOrientation.sign_mul_self (orientation : NormalOrientation) :
    orientation.sign * orientation.sign = 1 := by
  cases orientation <;> norm_num [NormalOrientation.sign]

/-- Local affine Gaussian-normal data at `n = 0`. -/
structure GaussianAffineData where
  signature : NormalSignature
  inducedMetric : Matrix3
  inducedInverse : Matrix3
  normalDerivative : Matrix3
  inducedMetric_symmetric : inducedMetric.transpose = inducedMetric
  normalDerivative_symmetric : normalDerivative.transpose = normalDerivative
  inverse_mul_induced : inducedInverse * inducedMetric = 1
  induced_mul_inverse : inducedMetric * inducedInverse = 1

/-- Embedding of the three tangential coordinates as the level set `n = 0`. -/
def hypersurfaceEmbedding (tangent : TangentCoordinate3) : Coordinate4 :=
  fun index => Fin.cases 0 tangent index

@[simp]
theorem hypersurfaceEmbedding_normal
    (tangent : TangentCoordinate3) :
    hypersurfaceEmbedding tangent normalIndex = 0 :=
  rfl

@[simp]
theorem hypersurfaceEmbedding_tangent
    (tangent : TangentCoordinate3) (index : Fin 3) :
    hypersurfaceEmbedding tangent (tangentIndex index) = tangent index :=
  rfl

/-- Tangential-coordinate projection from the ambient chart. -/
def tangentProjection (point : Coordinate4) : TangentCoordinate3 :=
  fun index => point (tangentIndex index)

@[simp]
theorem tangentProjection_hypersurfaceEmbedding
    (tangent : TangentCoordinate3) :
    tangentProjection (hypersurfaceEmbedding tangent) = tangent := by
  rfl

/-- The displayed hypersurface parametrization is an actual injection. -/
theorem hypersurfaceEmbedding_injective :
    Function.Injective hypersurfaceEmbedding := by
  intro first second hEqual
  have hProjected := congrArg tangentProjection hEqual
  simpa using hProjected

/-- Retraction onto the displayed hypersurface is exact precisely on `n=0`. -/
theorem hypersurfaceEmbedding_tangentProjection_eq_iff
    (point : Coordinate4) :
    hypersurfaceEmbedding (tangentProjection point) = point ↔
      point normalIndex = 0 := by
  constructor
  · intro hEqual
    have hNormal := congrFun hEqual normalIndex
    simpa using hNormal.symm
  · intro hNormal
    funext index
    refine Fin.cases ?_ (fun _ => rfl) index
    exact hNormal.symm

/-- The range of the embedding is exactly the selected level set. -/
theorem point_mem_hypersurface_range_iff (point : Coordinate4) :
    point ∈ Set.range hypersurfaceEmbedding ↔ point normalIndex = 0 := by
  constructor
  · rintro ⟨tangent, rfl⟩
    rfl
  · intro hNormal
    exact ⟨tangentProjection point,
      (hypersurfaceEmbedding_tangentProjection_eq_iff point).2 hNormal⟩

/-- The explicitly selected hypersurface is exactly contained in `n = 0`. -/
theorem hypersurface_is_normal_zero
    (tangent : TangentCoordinate3) :
    (hypersurfaceEmbedding tangent) 0 = 0 :=
  rfl

/-- Affine family `h_ab(n) = h_ab(0) + n partial_n h_ab`. -/
def inducedMetricAtNormal
    (data : GaussianAffineData) (normal : ℝ) : Matrix3 :=
  data.inducedMetric + normal • data.normalDerivative

@[simp]
theorem inducedMetricAtNormal_zero (data : GaussianAffineData) :
    inducedMetricAtNormal data 0 = data.inducedMetric := by
  simp [inducedMetricAtNormal]

/-- Full Gaussian-normal metric field in the affine chart. -/
def spacetimeMetric
    (data : GaussianAffineData) (point : Coordinate4) : Matrix4 :=
  gaussianMetric data.signature.epsilon
    (inducedMetricAtNormal data (point normalIndex))

/-- Block inverse of the metric at the hypersurface. -/
def surfaceInverse (data : GaussianAffineData) : Matrix4 :=
  gaussianInverse data.signature.epsilon data.inducedInverse

@[simp]
theorem spacetimeMetric_on_hypersurface
    (data : GaussianAffineData) (tangent : TangentCoordinate3) :
    spacetimeMetric data (hypersurfaceEmbedding tangent) =
      gaussianMetric data.signature.epsilon data.inducedMetric := by
  simp [spacetimeMetric]

theorem spacetimeMetric_on_hypersurface_symmetric
    (data : GaussianAffineData) (tangent : TangentCoordinate3) :
    (spacetimeMetric data (hypersurfaceEmbedding tangent)).transpose =
      spacetimeMetric data (hypersurfaceEmbedding tangent) := by
  rw [spacetimeMetric_on_hypersurface]
  ext row column
  refine Fin.cases ?_ (fun tangentRow => ?_) row
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column <;> rfl
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · rfl
    · have hEntry := congrFun
        (congrFun data.inducedMetric_symmetric tangentRow) tangentColumn
      simpa [Matrix.transpose_apply, gaussianMetric,
        normalIndex, tangentIndex] using hEntry

theorem surfaceInverse_mul_metric
    (data : GaussianAffineData) (tangent : TangentCoordinate3) :
    surfaceInverse data * spacetimeMetric data (hypersurfaceEmbedding tangent) = 1 := by
  rw [spacetimeMetric_on_hypersurface]
  ext row column
  refine Fin.cases ?_ (fun tangentRow => ?_) row
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [surfaceInverse, Matrix.mul_apply, sum_fin_four,
        normalIndex, tangentIndex,
        NormalSignature.epsilon_mul_self]
    · simp [surfaceInverse, Matrix.mul_apply, Matrix.one_apply, sum_fin_four,
        normalIndex, tangentIndex]
      exact ne_of_lt (Fin.succ_pos tangentColumn)
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [surfaceInverse, Matrix.mul_apply, sum_fin_four,
        normalIndex, tangentIndex]
    · have hEntry := congrFun
        (congrFun data.inverse_mul_induced tangentRow) tangentColumn
      simpa [surfaceInverse, Matrix.mul_apply, Matrix.one_apply,
        sum_fin_four, normalIndex, tangentIndex] using hEntry

theorem metric_mul_surfaceInverse
    (data : GaussianAffineData) (tangent : TangentCoordinate3) :
    spacetimeMetric data (hypersurfaceEmbedding tangent) * surfaceInverse data = 1 := by
  rw [spacetimeMetric_on_hypersurface]
  ext row column
  refine Fin.cases ?_ (fun tangentRow => ?_) row
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [surfaceInverse, Matrix.mul_apply, sum_fin_four,
        normalIndex, tangentIndex,
        NormalSignature.epsilon_mul_self]
    · simp [surfaceInverse, Matrix.mul_apply, Matrix.one_apply, sum_fin_four,
        normalIndex, tangentIndex]
      exact ne_of_lt (Fin.succ_pos tangentColumn)
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [surfaceInverse, Matrix.mul_apply, sum_fin_four,
        normalIndex, tangentIndex]
    · have hEntry := congrFun
        (congrFun data.induced_mul_inverse tangentRow) tangentColumn
      simpa [surfaceInverse, Matrix.mul_apply, Matrix.one_apply,
        sum_fin_four, normalIndex, tangentIndex] using hEntry

/-- Actual normal coordinate line through a chart point. -/
def normalCoordinateLine (point : Coordinate4) (parameter : ℝ) : Coordinate4 :=
  fun index => Fin.cases (point normalIndex + parameter)
    (fun tangent => point (tangentIndex tangent)) index

/-- Actual tangential coordinate line through a chart point. -/
def tangentCoordinateLine
    (point : Coordinate4) (direction : Fin 3) (parameter : ℝ) : Coordinate4 :=
  fun index => Fin.cases (point normalIndex)
    (fun tangent => point (tangentIndex tangent) +
      if tangent = direction then parameter else 0) index

@[simp]
theorem normalCoordinateLine_normal
    (point : Coordinate4) (parameter : ℝ) :
    normalCoordinateLine point parameter normalIndex =
      point normalIndex + parameter :=
  rfl

@[simp]
theorem tangentCoordinateLine_normal
    (point : Coordinate4) (direction : Fin 3) (parameter : ℝ) :
    tangentCoordinateLine point direction parameter normalIndex =
      point normalIndex :=
  rfl

/-- The affine coefficient is the genuine derivative `partial_n h_ab`. -/
theorem inducedMetric_entry_hasDerivAt
    (data : GaussianAffineData) (row column : Fin 3) :
    HasDerivAt
      (fun normal => inducedMetricAtNormal data normal row column)
      (data.normalDerivative row column) 0 := by
  change HasDerivAt
    (fun normal => data.inducedMetric row column +
      normal * data.normalDerivative row column)
    (data.normalDerivative row column) 0
  have hDerivative :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := data.inducedMetric row column)).add
      ((hasDerivAt_id (x := (0 : ℝ))).mul_const
        (data.normalDerivative row column))
  have hFunction :
      (fun normal : ℝ => data.inducedMetric row column +
        normal * data.normalDerivative row column) =
      ((fun _ : ℝ => data.inducedMetric row column) +
        fun normal : ℝ => normal * data.normalDerivative row column) := by
    funext normal
    rfl
  rw [hFunction]
  simpa only [id_eq, zero_add, one_mul] using hDerivative

/-- All actual first coordinate derivatives of the metric at the hypersurface. -/
def surfaceMetricPartial
    (data : GaussianAffineData)
    (derivative row column : Fin 4) : ℝ :=
  normalMetricVariationJet data.normalDerivative derivative row column

/-- The normal entries of `surfaceMetricPartial` are actual derivatives of
the affine spacetime metric along the normal coordinate line. -/
theorem spacetimeMetric_normalLine_hasDerivAt
    (data : GaussianAffineData) (tangent : TangentCoordinate3)
    (row column : Fin 4) :
    HasDerivAt
      (fun parameter => spacetimeMetric data
        (normalCoordinateLine (hypersurfaceEmbedding tangent) parameter)
        row column)
      (surfaceMetricPartial data normalIndex row column) 0 := by
  refine Fin.cases ?_ (fun tangentRow => ?_) row
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simpa [spacetimeMetric, surfaceMetricPartial, normalIndex,
        normalMetricVariationJet] using
        (hasDerivAt_const (x := (0 : ℝ)) (c := data.signature.epsilon))
    · simpa [spacetimeMetric, surfaceMetricPartial, normalIndex, tangentIndex,
        normalMetricVariationJet] using
        (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simpa [spacetimeMetric, surfaceMetricPartial, normalIndex, tangentIndex,
        normalMetricVariationJet] using
        (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
    · simpa [spacetimeMetric, normalCoordinateLine, hypersurfaceEmbedding,
        surfaceMetricPartial, normalIndex, tangentIndex,
        normalMetricVariationJet] using
        inducedMetric_entry_hasDerivAt data tangentRow tangentColumn

/-- Tangential coordinate derivatives vanish in this affine model, and this
is an actual derivative statement rather than a supplied jet. -/
theorem spacetimeMetric_tangentLine_hasDerivAt
    (data : GaussianAffineData) (tangent : TangentCoordinate3)
    (direction : Fin 3) (row column : Fin 4) :
    HasDerivAt
      (fun parameter => spacetimeMetric data
        (tangentCoordinateLine (hypersurfaceEmbedding tangent) direction parameter)
        row column)
      (surfaceMetricPartial data (tangentIndex direction) row column) 0 := by
  have hConstant :
      (fun parameter => spacetimeMetric data
        (tangentCoordinateLine (hypersurfaceEmbedding tangent) direction parameter)
        row column) =
      fun _ : ℝ => spacetimeMetric data (hypersurfaceEmbedding tangent) row column := by
    funext parameter
    rfl
  rw [hConstant]
  simpa [surfaceMetricPartial, normalMetricVariationJet,
    normalIndex, tangentIndex] using
    (hasDerivAt_const (x := (0 : ℝ))
      (c := spacetimeMetric data (hypersurfaceEmbedding tangent) row column))

/-- Levi--Civita Christoffel formula evaluated at `n = 0` from the actual
surface inverse and the actual coordinate derivatives above. -/
def leviCivitaChristoffelAtSurface
    (data : GaussianAffineData)
    (upper lowerLeft lowerRight : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ contracted : Fin 4,
    surfaceInverse data upper contracted *
      (surfaceMetricPartial data lowerLeft contracted lowerRight +
        surfaceMetricPartial data lowerRight contracted lowerLeft -
        surfaceMetricPartial data contracted lowerLeft lowerRight)

theorem surfaceMetricPartial_symmetric
    (data : GaussianAffineData) (derivative row column : Fin 4) :
    surfaceMetricPartial data derivative row column =
      surfaceMetricPartial data derivative column row := by
  refine Fin.cases ?_ (fun tangentDerivative => ?_) derivative
  · refine Fin.cases ?_ (fun tangentRow => ?_) row
    · refine Fin.cases ?_ (fun tangentColumn => ?_) column <;> rfl
    · refine Fin.cases ?_ (fun tangentColumn => ?_) column
      · simp [surfaceMetricPartial, normalMetricVariationJet]
      · have hEntry := congrFun
          (congrFun data.normalDerivative_symmetric tangentRow) tangentColumn
        simpa [surfaceMetricPartial, normalMetricVariationJet,
          Matrix.transpose_apply, normalIndex, tangentIndex] using hEntry.symm
  · simp [surfaceMetricPartial, normalMetricVariationJet]

theorem leviCivitaChristoffel_eq_explicit
    (data : GaussianAffineData) :
    leviCivitaChristoffelAtSurface data =
      linearizedChristoffel data.signature.epsilon data.inducedInverse
        data.normalDerivative :=
  rfl

/-- Torsion-free symmetry is visible directly in the Christoffel formula. -/
theorem leviCivitaChristoffel_lower_symmetric
    (data : GaussianAffineData) (upper lowerLeft lowerRight : Fin 4) :
    leviCivitaChristoffelAtSurface data upper lowerLeft lowerRight =
      leviCivitaChristoffelAtSurface data upper lowerRight lowerLeft := by
  simp only [leviCivitaChristoffelAtSurface]
  congr 1
  apply Finset.sum_congr rfl
  intro contracted _
  rw [surfaceMetricPartial_symmetric data contracted lowerLeft lowerRight]
  ring

@[simp]
theorem christoffel_normal_tangent_tangent
    (data : GaussianAffineData) (row column : Fin 3) :
    leviCivitaChristoffelAtSurface data normalIndex
        (tangentIndex row) (tangentIndex column) =
      -(data.signature.epsilon / 2) * data.normalDerivative row column := by
  exact linearizedChristoffel_normal_tangent_tangent
    data.signature.epsilon data.inducedInverse data.normalDerivative row column

@[simp]
theorem christoffel_tangent_normal_tangent
    (data : GaussianAffineData) (upper column : Fin 3) :
    leviCivitaChristoffelAtSurface data (tangentIndex upper)
        normalIndex (tangentIndex column) =
      (1 / 2 : ℝ) * ∑ contracted : Fin 3,
        data.inducedInverse upper contracted *
          data.normalDerivative contracted column := by
  exact linearizedChristoffel_tangent_normal_tangent
    data.signature.epsilon data.inducedInverse data.normalDerivative upper column

@[simp]
theorem christoffel_tangent_tangent_normal
    (data : GaussianAffineData) (upper row : Fin 3) :
    leviCivitaChristoffelAtSurface data (tangentIndex upper)
        (tangentIndex row) normalIndex =
      (1 / 2 : ℝ) * ∑ contracted : Fin 3,
        data.inducedInverse upper contracted *
          data.normalDerivative contracted row := by
  rw [leviCivitaChristoffel_lower_symmetric]
  exact christoffel_tangent_normal_tangent data upper row

@[simp]
theorem christoffel_tangent_tangent_tangent
    (data : GaussianAffineData) (upper row column : Fin 3) :
    leviCivitaChristoffelAtSurface data (tangentIndex upper)
        (tangentIndex row) (tangentIndex column) = 0 := by
  simp [leviCivitaChristoffelAtSurface, surfaceInverse,
    surfaceMetricPartial, normalMetricVariationJet, sum_fin_four,
    normalIndex, tangentIndex]

@[simp]
theorem christoffel_normal_normal_any
    (data : GaussianAffineData) (upper : Fin 4) :
    leviCivitaChristoffelAtSurface data upper normalIndex normalIndex = 0 := by
  fin_cases upper <;>
    simp [leviCivitaChristoffelAtSurface, surfaceInverse,
      surfaceMetricPartial, normalMetricVariationJet, sum_fin_four,
      normalIndex, tangentIndex]

@[simp]
theorem christoffel_normal_normal_tangent
    (data : GaussianAffineData) (column : Fin 3) :
    leviCivitaChristoffelAtSurface data normalIndex normalIndex
      (tangentIndex column) = 0 := by
  simp [leviCivitaChristoffelAtSurface, surfaceInverse,
    surfaceMetricPartial, normalMetricVariationJet, sum_fin_four,
    normalIndex, tangentIndex]

@[simp]
theorem christoffel_normal_tangent_normal
    (data : GaussianAffineData) (row : Fin 3) :
    leviCivitaChristoffelAtSurface data normalIndex
      (tangentIndex row) normalIndex = 0 := by
  rw [leviCivitaChristoffel_lower_symmetric]
  exact christoffel_normal_normal_tangent data row

/-- Coordinate components of the signed unit normal `sigma partial_n`. -/
def signedUnitNormal (orientation : NormalOrientation) : Coordinate4 :=
  fun index => Fin.cases orientation.sign (fun _ => 0) index

/-- Tangent lift along the hypersurface embedding. -/
def tangentLift (vector : TangentCoordinate3) : Coordinate4 :=
  fun index => Fin.cases 0 vector index

/-- Bilinear metric pairing in the coordinate basis. -/
def metricPair (metric : Matrix4) (first second : Coordinate4) : ℝ :=
  ∑ row : Fin 4, ∑ column : Fin 4,
    metric row column * first row * second column

/-- The chosen normal has squared norm `epsilon`, including the timelike case. -/
theorem signedUnitNormal_norm_sq
    (data : GaussianAffineData) (tangent : TangentCoordinate3)
    (orientation : NormalOrientation) :
    metricPair (spacetimeMetric data (hypersurfaceEmbedding tangent))
        (signedUnitNormal orientation) (signedUnitNormal orientation) =
      data.signature.epsilon := by
  simp [metricPair, spacetimeMetric, inducedMetricAtNormal,
    hypersurfaceEmbedding, signedUnitNormal, sum_fin_four,
    normalIndex, tangentIndex]
  calc
    data.signature.epsilon * orientation.sign * orientation.sign =
        data.signature.epsilon * (orientation.sign * orientation.sign) := by ring
    _ = data.signature.epsilon := by
      rw [NormalOrientation.sign_mul_self]
      ring

/-- The signed unit normal is orthogonal to every embedded tangent vector. -/
theorem signedUnitNormal_orthogonal_tangent
    (data : GaussianAffineData) (tangent : TangentCoordinate3)
    (orientation : NormalOrientation) (vector : TangentCoordinate3) :
    metricPair (spacetimeMetric data (hypersurfaceEmbedding tangent))
        (signedUnitNormal orientation) (tangentLift vector) = 0 := by
  simp [metricPair, spacetimeMetric, inducedMetricAtNormal,
    hypersurfaceEmbedding, signedUnitNormal, tangentLift, sum_fin_four,
    normalIndex, tangentIndex]

/-- Metric-lowered signed unit normal at the hypersurface. -/
def signedUnitNormalCovector
    (data : GaussianAffineData) (orientation : NormalOrientation) : Fin 4 → ℝ :=
  fun index => Fin.cases
    (orientation.sign * data.signature.epsilon) (fun _ => 0) index

@[simp]
theorem signedUnitNormalCovector_normal
    (data : GaussianAffineData) (orientation : NormalOrientation) :
    signedUnitNormalCovector data orientation normalIndex =
      orientation.sign * data.signature.epsilon :=
  rfl

@[simp]
theorem signedUnitNormalCovector_tangent
    (data : GaussianAffineData) (orientation : NormalOrientation)
    (index : Fin 3) :
    signedUnitNormalCovector data orientation (tangentIndex index) = 0 :=
  rfl

theorem signedUnitNormalCovector_is_metric_dual
    (data : GaussianAffineData) (tangent : TangentCoordinate3)
    (orientation : NormalOrientation) (index : Fin 4) :
    ∑ column : Fin 4,
        spacetimeMetric data (hypersurfaceEmbedding tangent) index column *
          signedUnitNormal orientation column =
      signedUnitNormalCovector data orientation index := by
  refine Fin.cases ?_ (fun tangentIndexValue => ?_) index
  · simp [spacetimeMetric, inducedMetricAtNormal, hypersurfaceEmbedding,
      signedUnitNormal, signedUnitNormalCovector, sum_fin_four,
      normalIndex, tangentIndex]
    ring
  · simp [spacetimeMetric, inducedMetricAtNormal, hypersurfaceEmbedding,
      signedUnitNormal, signedUnitNormalCovector, sum_fin_four,
      normalIndex, tangentIndex]

/-- `nabla_a normalFlat_b` at the surface.  The coordinate components of the
normal covector are constant, so only the Christoffel term remains. -/
def covariantNormalSecondFundamentalForm
    (data : GaussianAffineData) (orientation : NormalOrientation) : Matrix3 :=
  fun row column => -∑ upper : Fin 4,
    leviCivitaChristoffelAtSurface data upper
      (tangentIndex row) (tangentIndex column) *
        signedUnitNormalCovector data orientation upper

/-- Direct derivation of `B_ab = sigma partial_n h_ab / 2`. -/
theorem covariantNormalSecondFundamentalForm_eq
    (data : GaussianAffineData) (orientation : NormalOrientation)
    (row column : Fin 3) :
    covariantNormalSecondFundamentalForm data orientation row column =
      orientation.sign * (1 / 2 : ℝ) * data.normalDerivative row column := by
  rw [covariantNormalSecondFundamentalForm, sum_fin_four]
  simp only [signedUnitNormalCovector_normal,
    signedUnitNormalCovector_tangent, mul_zero, Finset.sum_const_zero,
    add_zero]
  rw [christoffel_normal_tangent_tangent]
  calc
    -(-(data.signature.epsilon / 2) * data.normalDerivative row column *
        (orientation.sign * data.signature.epsilon)) =
      orientation.sign *
        (data.signature.epsilon * data.signature.epsilon) *
        (1 / 2 : ℝ) * data.normalDerivative row column := by ring
    _ = orientation.sign * (1 / 2 : ℝ) *
        data.normalDerivative row column := by
      rw [NormalSignature.epsilon_mul_self]
      ring

/-- The two widespread sign conventions for the second fundamental form. -/
inductive SecondFundamentalConvention where
  | covariantNormal
  | negativeCovariantNormal
  deriving DecidableEq

def SecondFundamentalConvention.sign : SecondFundamentalConvention → ℝ
  | .covariantNormal => 1
  | .negativeCovariantNormal => -1

def secondFundamentalForm
    (convention : SecondFundamentalConvention)
    (data : GaussianAffineData) (orientation : NormalOrientation) : Matrix3 :=
  convention.sign • covariantNormalSecondFundamentalForm data orientation

/-- Convention-aware formula with either sign in front of
`partial_n h_ab / 2`, with the
normal orientation supplying the other possible sign reversal. -/
theorem secondFundamentalForm_eq
    (convention : SecondFundamentalConvention)
    (data : GaussianAffineData) (orientation : NormalOrientation)
    (row column : Fin 3) :
    secondFundamentalForm convention data orientation row column =
      convention.sign * orientation.sign * (1 / 2 : ℝ) *
        data.normalDerivative row column := by
  simp [secondFundamentalForm, covariantNormalSecondFundamentalForm_eq]
  ring

theorem positiveNormal_covariantConvention_eq_half_normalDerivative
    (data : GaussianAffineData) (row column : Fin 3) :
    secondFundamentalForm .covariantNormal data .increasing row column =
      (1 / 2 : ℝ) * data.normalDerivative row column := by
  simp [secondFundamentalForm_eq, SecondFundamentalConvention.sign,
    NormalOrientation.sign]

theorem positiveNormal_negativeConvention_eq_neg_half_normalDerivative
    (data : GaussianAffineData) (row column : Fin 3) :
    secondFundamentalForm .negativeCovariantNormal data .increasing row column =
      -(1 / 2 : ℝ) * data.normalDerivative row column := by
  simp [secondFundamentalForm_eq, SecondFundamentalConvention.sign,
    NormalOrientation.sign]

/-- Contraction of a tangential two-tensor with the inverse induced metric. -/
def inducedTrace (data : GaussianAffineData) (tensor : Matrix3) : ℝ :=
  ∑ row : Fin 3, ∑ column : Fin 3,
    data.inducedInverse row column * tensor row column

/-- Trace `K = h^{ab} B_ab`. -/
def extrinsicTrace
    (convention : SecondFundamentalConvention)
    (data : GaussianAffineData) (orientation : NormalOrientation) : ℝ :=
  inducedTrace data (secondFundamentalForm convention data orientation)

/-- Explicit trace formula in terms of `partial_n h_ab`. -/
theorem extrinsicTrace_eq
    (convention : SecondFundamentalConvention)
    (data : GaussianAffineData) (orientation : NormalOrientation) :
    extrinsicTrace convention data orientation =
      convention.sign * orientation.sign * (1 / 2 : ℝ) *
        inducedTrace data data.normalDerivative := by
  unfold extrinsicTrace inducedTrace
  simp_rw [secondFundamentalForm_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro column _
  ring

end

end P0EFTJanusGaussianNormalEmbeddedHypersurface
end JanusFormal
