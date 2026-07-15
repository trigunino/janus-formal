import Mathlib

namespace JanusFormal
namespace P0EFTJanusImmersionFiberAlgebra

set_option autoImplicit false

/-- Tangent fiber of the three-dimensional throat in a fixed orthonormal frame. -/
@[ext] structure TangentVector3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- Restricted ambient tangent fiber in the four-dimensional candidate. -/
@[ext] structure AmbientVector4 where
  x : ℝ
  y : ℝ
  z : ℝ
  normal : ℝ

/-- Join tangential and normal deformation data. -/
def joinAmbient
    (data : TangentVector3 × ℝ) : AmbientVector4 :=
  { x := data.1.x
    y := data.1.y
    z := data.1.z
    normal := data.2 }

/-- Split an ambient deformation into tangential and normal parts. -/
def splitAmbient
    (vector : AmbientVector4) : TangentVector3 × ℝ :=
  ({ x := vector.x
     y := vector.y
     z := vector.z },
   vector.normal)

@[simp] theorem split_join
    (data : TangentVector3 × ℝ) :
    splitAmbient (joinAmbient data) = data := by
  rcases data with ⟨tangent, normal⟩
  rcases tangent with ⟨x, y, z⟩
  rfl

@[simp] theorem join_split
    (vector : AmbientVector4) :
    joinAmbient (splitAmbient vector) = vector := by
  rcases vector with ⟨x, y, z, normal⟩
  rfl

/-- Fiberwise immersion splitting `i*TM = TΣ ⊕ NΣ`. -/
def ambientSplitEquiv :
    AmbientVector4 ≃ TangentVector3 × ℝ where
  toFun := splitAmbient
  invFun := joinAmbient
  left_inv := join_split
  right_inv := split_join

/-- Tangential reparametrizations inject into ambient deformations. -/
def tangentInclusion
    (vector : TangentVector3) : TangentVector3 × ℝ :=
  (vector, 0)

/-- Quotient map to the physical normal deformation. -/
def normalProjection
    (deformation : TangentVector3 × ℝ) : ℝ :=
  deformation.2

/-- Tangential deformations have no normal component. -/
@[simp] theorem normal_projection_tangent_inclusion
    (vector : TangentVector3) :
    normalProjection (tangentInclusion vector) = 0 := by
  rfl

/-- Exactness at the ambient-deformation term. -/
theorem ambient_kernel_is_tangential_image
    (deformation : TangentVector3 × ℝ)
    (hKernel : normalProjection deformation = 0) :
    ∃ vector : TangentVector3,
      tangentInclusion vector = deformation := by
  rcases deformation with ⟨tangent, normal⟩
  change normal = 0 at hKernel
  subst normal
  exact ⟨tangent, rfl⟩

/-- Every normal scalar is represented by an ambient deformation. -/
theorem normal_projection_surjective
    (normal : ℝ) :
    ∃ deformation : TangentVector3 × ℝ,
      normalProjection deformation = normal := by
  exact ⟨({ x := 0, y := 0, z := 0 }, normal), rfl⟩

/-- Symmetric covariant two-tensor in dimension three. -/
@[ext] structure SymmetricTensor3 where
  xx : ℝ
  yy : ℝ
  zz : ℝ
  xy : ℝ
  xz : ℝ
  yz : ℝ

/-- Five independent coordinates of a traceless symmetric tensor. -/
@[ext] structure TracelessTensor3 where
  xx : ℝ
  yy : ℝ
  xy : ℝ
  xz : ℝ
  yz : ℝ

/-- Scalar trace component, normalized so that `h = τ g + h₀`. -/
noncomputable def traceScalar
    (tensor : SymmetricTensor3) : ℝ :=
  (tensor.xx + tensor.yy + tensor.zz) / 3

/-- Traceless component in five independent coordinates. -/
noncomputable def tracelessPart
    (tensor : SymmetricTensor3) : TracelessTensor3 :=
  let trace := traceScalar tensor
  { xx := tensor.xx - trace
    yy := tensor.yy - trace
    xy := tensor.xy
    xz := tensor.xz
    yz := tensor.yz }

/-- Reconstruct a symmetric tensor from scalar trace and traceless data. -/
def combineTraceTraceless
    (data : ℝ × TracelessTensor3) : SymmetricTensor3 :=
  { xx := data.1 + data.2.xx
    yy := data.1 + data.2.yy
    zz := data.1 - data.2.xx - data.2.yy
    xy := data.2.xy
    xz := data.2.xz
    yz := data.2.yz }

/-- Split a symmetric tensor into trace and traceless parts. -/
noncomputable def splitTraceTraceless
    (tensor : SymmetricTensor3) : ℝ × TracelessTensor3 :=
  (traceScalar tensor, tracelessPart tensor)

@[simp] theorem split_combine_trace_traceless
    (data : ℝ × TracelessTensor3) :
    splitTraceTraceless (combineTraceTraceless data) = data := by
  rcases data with ⟨trace, traceless⟩
  rcases traceless with ⟨xx, yy, xy, xz, yz⟩
  ext <;>
    simp [splitTraceTraceless, combineTraceTraceless,
      traceScalar, tracelessPart] <;>
    ring

set_option linter.unnecessarySeqFocus false in
@[simp] theorem combine_split_trace_traceless
    (tensor : SymmetricTensor3) :
    combineTraceTraceless (splitTraceTraceless tensor) = tensor := by
  rcases tensor with ⟨xx, yy, zz, xy, xz, yz⟩
  ext <;>
    simp [splitTraceTraceless, combineTraceTraceless,
      traceScalar, tracelessPart] <;>
    ring

/-- Canonical fiber decomposition `Sym²(T*Σ) = ℝ·g ⊕ Sym²₀(T*Σ)`. -/
noncomputable def traceTracelessEquiv :
    SymmetricTensor3 ≃ ℝ × TracelessTensor3 where
  toFun := splitTraceTraceless
  invFun := combineTraceTraceless
  left_inv := combine_split_trace_traceless
  right_inv := split_combine_trace_traceless

/-- Addition of symmetric tensors. -/
def addSymmetric
    (first second : SymmetricTensor3) : SymmetricTensor3 :=
  { xx := first.xx + second.xx
    yy := first.yy + second.yy
    zz := first.zz + second.zz
    xy := first.xy + second.xy
    xz := first.xz + second.xz
    yz := first.yz + second.yz }

/-- Scalar multiplication of a symmetric tensor. -/
def scaleSymmetric
    (scalar : ℝ)
    (tensor : SymmetricTensor3) : SymmetricTensor3 :=
  { xx := scalar * tensor.xx
    yy := scalar * tensor.yy
    zz := scalar * tensor.zz
    xy := scalar * tensor.xy
    xz := scalar * tensor.xz
    yz := scalar * tensor.yz }

/-- Zero symmetric tensor. -/
def zeroSymmetric : SymmetricTensor3 :=
  { xx := 0, yy := 0, zz := 0,
    xy := 0, xz := 0, yz := 0 }

/-- Zeroth-order metric variation generated by a normal displacement and second fundamental form. -/
def normalMetricVariation
    (secondFundamentalForm : SymmetricTensor3)
    (normalDisplacement : ℝ) : SymmetricTensor3 :=
  scaleSymmetric (-2 * normalDisplacement) secondFundamentalForm

/-- Fiber-rank formulas. -/
def symmetricTwoTensorRank (dimension : ℕ) : ℕ :=
  dimension * (dimension + 1) / 2


def tracelessSymmetricTwoTensorRank (dimension : ℕ) : ℕ :=
  symmetricTwoTensorRank dimension - 1

@[simp] theorem janus_ambient_rank_split :
    4 = 3 + 1 := by norm_num

@[simp] theorem janus_symmetric_tensor_rank :
    symmetricTwoTensorRank 3 = 6 := by
  norm_num [symmetricTwoTensorRank]

@[simp] theorem janus_traceless_tensor_rank :
    tracelessSymmetricTwoTensorRank 3 = 5 := by
  norm_num [tracelessSymmetricTwoTensorRank,
    symmetricTwoTensorRank]

@[simp] theorem janus_trace_traceless_rank_split :
    6 = 1 + 5 := by norm_num

/--
The short exact fiber sequence

`0 → TΣ → i*TM → NΣ → 0`

is the common origin of tangential diffeomorphism ghosts and the physical
normal deformation. The induced-metric map then lands in the canonical
trace/traceless tensor decomposition.
-/
structure ImmersionFiberGeometricStatus where
  immersionConstructed : Prop
  restrictedAmbientTangentConstructed : Prop
  tangentInjectionConstructed : Prop
  normalQuotientConstructed : Prop
  splittingDerivedFromMetric : Prop
  normalLineIdentifiedWithClutchingModel : Prop
  secondFundamentalFormConstructed : Prop
  inducedMetricVariationDerived : Prop
  traceTracelessBundleSplitGlobalized : Prop


def immersionFiberGeometricClosure
    (s : ImmersionFiberGeometricStatus) : Prop :=
  s.immersionConstructed /\
  s.restrictedAmbientTangentConstructed /\
  s.tangentInjectionConstructed /\
  s.normalQuotientConstructed /\
  s.splittingDerivedFromMetric /\
  s.normalLineIdentifiedWithClutchingModel /\
  s.secondFundamentalFormConstructed /\
  s.inducedMetricVariationDerived /\
  s.traceTracelessBundleSplitGlobalized

end P0EFTJanusImmersionFiberAlgebra
end JanusFormal
