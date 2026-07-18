import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusGlobalNormalEquivalence

/-!
# Transported topology on the differential normal family

The differential normal quotients already have their canonical quotient
topologies, but their dependent total space previously had no topology or
bundle trivializations.  This gate transports the topology and atlas of the
genuine sign-clutched normal `VectorBundleCore` through the proved global
fiberwise-linear equivalence.

The resulting total-space equivalence is a base-preserving homeomorphism and
is linear on every fiber.  This is a transport of topological bundle
structure.  It does not claim that the previously chosen pointwise algebraic
equivalences are smooth before this transported atlas is installed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance ambientBaseChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- The exact algebraic comparison already chosen in the previous gate is a
continuous linear equivalence on each canonical quotient fiber.  This is
pointwise continuity only. -/
def differentialNormalFiberContinuousEquiv
    (point : ThroatBase period hPeriod) :
    FixedThroatNormalFiber period hPeriod point ≃L[Real]
      DifferentialNormalFiber period hPeriod point := by
  let targetTangent := TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)
  let targetEquiv : targetTangent ≃L[Real] CoverCoordinates :=
    ContinuousLinearEquiv.refl Real CoverCoordinates
  letI : FiniteDimensional Real targetTangent :=
    targetEquiv.toLinearEquiv.symm.finiteDimensional
  letI : T2Space targetTangent := by
    change T2Space CoverCoordinates
    infer_instance
  letI : IsTopologicalAddGroup targetTangent := by
    change IsTopologicalAddGroup CoverCoordinates
    infer_instance
  letI : ContinuousSMul Real targetTangent := by
    change ContinuousSMul Real CoverCoordinates
    infer_instance
  let derivative :=
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap
  letI : IsClosed (LinearMap.range derivative : Set targetTangent) :=
    (LinearMap.range derivative).closed_of_finiteDimensional
  letI : FiniteDimensional Real
      (FixedThroatNormalFiber period hPeriod point) := by
    change FiniteDimensional Real Real
    infer_instance
  letI : IsTopologicalAddGroup
      (FixedThroatNormalFiber period hPeriod point) := by
    change IsTopologicalAddGroup Real
    infer_instance
  letI : ContinuousSMul Real
      (FixedThroatNormalFiber period hPeriod point) := by
    change ContinuousSMul Real Real
    infer_instance
  letI : T2Space (FixedThroatNormalFiber period hPeriod point) := by
    change T2Space Real
    infer_instance
  exact (differentialNormalFiberEquiv period hPeriod point).toContinuousLinearEquiv

@[simp] theorem differentialNormalFiberContinuousEquiv_apply
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    differentialNormalFiberContinuousEquiv period hPeriod point normal =
      differentialNormalFiberEquiv period hPeriod point normal :=
  rfl

@[simp] theorem differentialNormalFiberContinuousEquiv_symm_apply
    (point : ThroatBase period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    (differentialNormalFiberContinuousEquiv period hPeriod point).symm normal =
      (differentialNormalFiberEquiv period hPeriod point).symm normal :=
  rfl

/-- Canonical quotient topology and transported sign-line topology agree on
each individual fiber. -/
def differentialNormalFiberHomeomorph
    (point : ThroatBase period hPeriod) :
    DifferentialNormalFiber period hPeriod point ≃ₜ
      FixedThroatNormalFiber period hPeriod point :=
  (differentialNormalFiberContinuousEquiv period hPeriod point).symm.toHomeomorph

/-- Total topology pulled back from the genuine sign-clutched normal bundle
through the inverse of the global algebraic equivalence. -/
@[implicit_reducible] def differentialNormalTotalTopology :
    TopologicalSpace (DifferentialNormalTotalSpace period hPeriod) :=
  TopologicalSpace.induced
    (differentialNormalTotalEquiv period hPeriod).symm inferInstance

noncomputable instance differentialNormalTotalTopologicalSpace :
    TopologicalSpace (DifferentialNormalTotalSpace period hPeriod) :=
  differentialNormalTotalTopology period hPeriod

/-- The global algebraic comparison becomes a base-preserving homeomorphism
for the transported total topology. -/
def differentialNormalTotalHomeomorph :
    Bundle.TotalSpace Real (FixedThroatNormalFiber period hPeriod) ≃ₜ
      DifferentialNormalTotalSpace period hPeriod where
  toEquiv := differentialNormalTotalEquiv period hPeriod
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    have hInverse :
        ((differentialNormalTotalEquiv period hPeriod).symm ∘
          (differentialNormalTotalEquiv period hPeriod).toFun) = id := by
      funext normal
      exact (differentialNormalTotalEquiv period hPeriod).symm_apply_apply normal
    rw [hInverse]
    exact continuous_id
  continuous_invFun := continuous_induced_dom

@[simp] theorem differentialNormalTotalHomeomorph_base
    (normal : Bundle.TotalSpace Real
      (FixedThroatNormalFiber period hPeriod)) :
    (differentialNormalTotalHomeomorph period hPeriod normal).1 = normal.1 :=
  rfl

@[simp] theorem differentialNormalTotalHomeomorph_fiber
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (differentialNormalTotalHomeomorph period hPeriod ⟨point, normal⟩).2 =
      differentialNormalFiberEquiv period hPeriod point normal :=
  rfl

/-- Local trivialization transported from the genuine normal
`VectorBundleCore`. -/
def differentialNormalLocalTriv
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod)) :
    Bundle.Trivialization Real
      (Bundle.TotalSpace.proj :
        DifferentialNormalTotalSpace period hPeriod →
          ThroatBase period hPeriod) :=
  (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
    |>.compHomeomorph (differentialNormalTotalHomeomorph period hPeriod).symm

@[simp] theorem differentialNormalLocalTriv_baseSet
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod)) :
    (differentialNormalLocalTriv period hPeriod anchor).baseSet =
      normalBundleBaseSet period hPeriod anchor :=
  rfl

@[simp] theorem differentialNormalLocalTriv_apply
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : DifferentialNormalTotalSpace period hPeriod) :
    differentialNormalLocalTriv period hPeriod anchor normal =
      ⟨normal.1,
        (fixedThroatNormalVectorBundleCore period hPeriod).coordChange
          ((fixedThroatNormalVectorBundleCore period hPeriod).indexAt normal.1)
          anchor normal.1
          ((differentialNormalFiberEquiv period hPeriod normal.1).symm normal.2)⟩ :=
  rfl

/-- Transported local trivializations remain linear on every differential
normal fiber. -/
noncomputable instance differentialNormalLocalTrivIsLinear
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod)) :
    (differentialNormalLocalTriv period hPeriod anchor).IsLinear Real where
  linear point _ :=
    { map_add := fun first second => by
        simp only [differentialNormalLocalTriv_apply, map_add]
        exact map_add
          ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
            ((fixedThroatNormalVectorBundleCore period hPeriod).indexAt point)
            anchor point) _ _
      map_smul := fun scalar normal => by
        simp only [differentialNormalLocalTriv_apply, map_smul]
        exact map_smul
          ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
            ((fixedThroatNormalVectorBundleCore period hPeriod).indexAt point)
            anchor point) scalar _ }

@[simp] theorem differentialNormalLocalTriv_symm_fst
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (point : ThroatBase period hPeriod) (normal : Real) :
    (differentialNormalLocalTriv period hPeriod anchor).toOpenPartialHomeomorph.symm
        ⟨point, normal⟩ =
      ⟨point, differentialNormalFiberEquiv period hPeriod point
        ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
          anchor
          ((fixedThroatNormalVectorBundleCore period hPeriod).indexAt point)
          point normal)⟩ :=
  rfl

/-- Transport does not change the sign-clutched transition functions. -/
theorem differentialNormalLocalTriv_coordChange_eq
    (first second : MappingTorusCover (fixedEquatorData period hPeriod))
    {point : ThroatBase period hPeriod}
    (hPoint : point ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second)
    (normal : Real) :
    (differentialNormalLocalTriv period hPeriod first).coordChangeL Real
        (differentialNormalLocalTriv period hPeriod second) point normal =
      (fixedThroatNormalVectorBundleCore period hPeriod).coordChange
        first second point normal := by
  rw [Bundle.Trivialization.coordChangeL_apply']
  · rw [differentialNormalLocalTriv_symm_fst,
      differentialNormalLocalTriv_apply,
      differentialNormalFiberEquiv_symm_apply_apply]
    rw [(fixedThroatNormalVectorBundleCore period hPeriod).coordChange_comp]
    exact ⟨⟨hPoint.1,
      (fixedThroatNormalVectorBundleCore period hPeriod).mem_baseSet_at point⟩,
      hPoint.2⟩
  · exact hPoint

/-- Inclusion of each canonical quotient fiber into the transported total
space induces exactly its quotient topology. -/
theorem differentialNormalTotalSpaceMk_isInducing
    (point : ThroatBase period hPeriod) :
    IsInducing
      (@Bundle.TotalSpace.mk (ThroatBase period hPeriod) Real
        (DifferentialNormalFiber period hPeriod) point) := by
  let totalInverse := (differentialNormalTotalHomeomorph period hPeriod).symm
  let fiberInverse := differentialNormalFiberHomeomorph period hPeriod point
  have hComposition :
      totalInverse ∘
          (@Bundle.TotalSpace.mk (ThroatBase period hPeriod) Real
            (DifferentialNormalFiber period hPeriod) point) =
        (@Bundle.TotalSpace.mk (ThroatBase period hPeriod) Real
            (FixedThroatNormalFiber period hPeriod) point) ∘ fiberInverse := by
    funext normal
    rfl
  apply totalInverse.isInducing.of_comp_iff.mp
  rw [hComposition]
  exact
    (FiberBundle.totalSpaceMk_isInducing Real
      (FixedThroatNormalFiber period hPeriod) point).comp fiberInverse.isInducing

/-- The transported trivializations form a genuine topological fiber bundle
whose fibers retain their canonical quotient topology. -/
noncomputable instance differentialNormalFiberBundle :
    FiberBundle Real (DifferentialNormalFiber period hPeriod) where
  totalSpaceMk_isInducing' :=
    differentialNormalTotalSpaceMk_isInducing period hPeriod
  trivializationAtlas' :=
    Set.range (differentialNormalLocalTriv period hPeriod)
  trivializationAt' point :=
    differentialNormalLocalTriv period hPeriod
      (normalBundleIndexAt period hPeriod point)
  mem_baseSet_trivializationAt' point := by
    change point ∈ normalBundleBaseSet period hPeriod
      (normalBundleIndexAt period hPeriod point)
    exact mem_normalBundleBaseSet_indexAt period hPeriod point
  trivialization_mem_atlas' point := by
    exact ⟨normalBundleIndexAt period hPeriod point, rfl⟩

/-- The transported fiber bundle is a genuine topological real vector bundle;
its transition cocycle is exactly the original sign cocycle. -/
noncomputable instance differentialNormalVectorBundle :
    VectorBundle Real Real (DifferentialNormalFiber period hPeriod) where
  trivialization_linear' := by
    rintro _ ⟨anchor, rfl⟩
    exact differentialNormalLocalTrivIsLinear period hPeriod anchor
  continuousOn_coordChange' := by
    rintro _ _ ⟨first, rfl⟩ ⟨second, rfl⟩
    refine
      ((fixedThroatNormalVectorBundleCore period hPeriod).continuousOn_coordChange
        first second).congr ?_
    intro point hPoint
    apply ContinuousLinearMap.ext
    intro normal
    exact differentialNormalLocalTriv_coordChange_eq period hPeriod
      first second hPoint normal

theorem differentialNormalFiber_isVectorBundle :
    VectorBundle Real Real (DifferentialNormalFiber period hPeriod) :=
  inferInstance

/-- The transported cocycle is analytic, so the differential normal family is
also a genuine analytic vector bundle after the transported atlas is
installed. -/
noncomputable instance differentialNormalContMDiffVectorBundle :
    ContMDiffVectorBundle ω Real
      (DifferentialNormalFiber period hPeriod)
      throatCoverModelWithCorners where
  contMDiffOn_coordChangeL := by
    rintro _ _ ⟨first, rfl⟩ ⟨second, rfl⟩
    letI :
        (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
          throatCoverModelWithCorners ω :=
      fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod
    refine
      ((fixedThroatNormalVectorBundleCore period hPeriod).contMDiffOn_coordChange
        throatCoverModelWithCorners first second).congr ?_
    intro point hPoint
    apply ContinuousLinearMap.ext
    intro normal
    exact differentialNormalLocalTriv_coordChange_eq period hPeriod
      first second hPoint normal

theorem differentialNormalFiber_isContMDiffVectorBundle :
    ContMDiffVectorBundle ω Real
      (DifferentialNormalFiber period hPeriod)
      throatCoverModelWithCorners :=
  inferInstance

end

end P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
end JanusFormal
