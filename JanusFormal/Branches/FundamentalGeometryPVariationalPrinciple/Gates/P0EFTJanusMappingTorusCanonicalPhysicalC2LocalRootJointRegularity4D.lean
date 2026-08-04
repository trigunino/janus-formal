import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D

/-!
# Joint regularity of the uniform C² local root

A C² target family pulls the uniform local-root branch back to an open
parameter domain.  Its complete scalar second jets are jointly continuous in
the parameter and spacetime point, so value, first derivatives and ordered
second derivatives are controlled simultaneously.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootJointRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Set Topology
open scoped Manifold ContDiff Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup

local instance canonicalMatrixAddCommGroup : AddCommGroup Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toAddCommGroup

local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace

local instance canonicalMatrixTopologicalSpace : TopologicalSpace Matrix4 :=
  canonicalMatrixUniformSpace.toTopologicalSpace

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4

local instance canonicalMatrixModule : Module Real Matrix4 :=
  canonicalMatrixNormedSpace.toModule

local instance canonicalMatrixCompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Continuous C²-core families have jointly continuous complete spacetime
second jets. -/
theorem c2ScalarFamily_jointContinuous
    {Parameter : Type*} [TopologicalSpace Parameter]
    (domain : Set Parameter)
    (family : Parameter → C2Scalar period hPeriod)
    (hFamily : ContinuousOn family domain) :
    Continuous
      (fun input : domain × EffectiveQuotient period hPeriod =>
        canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod
          (family input.1.1) input.2) := by
  have hRestricted : Continuous (domain.restrict family) := hFamily.restrict
  have hAmbientFamily : Continuous
      (fun point : domain =>
        canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod
          (family point.1)) :=
    (canonicalPhysicalScalarC2JetCoreToAmbient
      period hPeriod).continuous.comp hRestricted
  exact (hAmbientFamily.comp continuous_fst).eval continuous_snd

theorem c2FiniteMatrixFamily_jointContinuous
    {Parameter : Type*} [TopologicalSpace Parameter]
    (dimension : Nat) (domain : Set Parameter)
    (family : Parameter → C2FiniteMatrix period hPeriod dimension)
    (hFamily : ContinuousOn family domain)
    (row column : Fin dimension) :
    Continuous
      (fun input : domain × EffectiveQuotient period hPeriod =>
        canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod
          (family input.1.1 row column) input.2) := by
  have hCoefficientOn : ContinuousOn
      (fun point => family point row column) domain := by
    exact ((continuous_apply column).comp (continuous_apply row)).continuousOn.comp
      hFamily (mapsTo_univ _ _)
  exact c2ScalarFamily_jointContinuous period hPeriod domain
    (fun point => family point row column) hCoefficientOn

/-- Pulled-back admissible parameter domain for the uniform C² root. -/
def c2LocalRootPullbackDomain
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (target : Model → C2Matrix period hPeriod) : Set Model :=
  target ⁻¹' c2MatrixRootPerturbationDomain
    period hPeriod root hRegular

theorem c2LocalRootPullbackDomain_isOpen
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (target : Model → C2Matrix period hPeriod)
    (hTarget : ContDiff Real 2 target) :
    IsOpen (c2LocalRootPullbackDomain
      period hPeriod root hRegular target) :=
  (c2MatrixRootPerturbationDomain_isOpen
    period hPeriod root hRegular).preimage hTarget.continuous

theorem c2LocalRootPullbackBranch_contDiffOn
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (target : Model → C2Matrix period hPeriod)
    (hTarget : ContDiff Real 2 target) :
    ContDiffOn Real 2
      (c2MatrixRootPerturbationBranch period hPeriod root hRegular ∘ target)
      (c2LocalRootPullbackDomain period hPeriod root hRegular target) := by
  exact (c2MatrixRootPerturbationBranch_contDiffOn
    period hPeriod root hRegular).comp hTarget.contDiffOn
      (fun _ hPoint => hPoint)

theorem c2LocalRootPullbackBranch_square
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (target : Model → C2Matrix period hPeriod)
    (parameter : Model)
    (hParameter : parameter ∈ c2LocalRootPullbackDomain
      period hPeriod root hRegular target) :
    c2FiniteMatrixSquare period hPeriod 4
        (c2MatrixRootPerturbationBranch period hPeriod root hRegular
          (target parameter)) =
      c2FiniteMatrixSquare period hPeriod 4
          (smoothMatrixFieldToC2 period hPeriod root) + target parameter :=
  c2MatrixRootPerturbationBranch_square period hPeriod hParameter

/-- The entire scalar second jet of every root coefficient is jointly
continuous on the pulled-back parameter--spacetime domain. -/
theorem c2LocalRootPullbackBranch_jointContinuous
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (target : Model → C2Matrix period hPeriod)
    (hTarget : ContDiff Real 2 target)
    (row column : Fin 4) :
    Continuous
      (fun input :
          c2LocalRootPullbackDomain period hPeriod root hRegular target ×
            EffectiveQuotient period hPeriod =>
        canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod
          (c2MatrixRootPerturbationBranch period hPeriod root hRegular
            (target input.1.1) row column) input.2) := by
  exact c2FiniteMatrixFamily_jointContinuous period hPeriod 4
    (c2LocalRootPullbackDomain period hPeriod root hRegular target)
    (c2MatrixRootPerturbationBranch period hPeriod root hRegular ∘ target)
    (c2LocalRootPullbackBranch_contDiffOn
      period hPeriod root hRegular target hTarget).continuousOn
    row column

end

end P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootJointRegularity4D
end JanusFormal
