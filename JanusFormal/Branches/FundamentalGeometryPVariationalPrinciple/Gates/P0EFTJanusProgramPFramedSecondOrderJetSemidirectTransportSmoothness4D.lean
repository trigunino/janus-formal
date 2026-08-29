import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

/-!
# Smoothness of generic semidirect second-jet transport

A `C^n` family of the five frozen base/fiber coefficients induces a `C^n`
family of continuous linear maps on framed second jets.  The manifold-local
statement is exposed directly for vector-bundle transition maps; the global
normed-space statement is a corollary.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Function Module
open scoped Manifold ContDiff
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D

variable
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]

private abbrev FiberEnd := V →L[Real] V

local instance fiberEndNormedAddCommGroup :
    NormedAddCommGroup (FiberEnd (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberEndNormedSpace :
    NormedSpace Real (FiberEnd (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberFirst := X →L[Real] FiberEnd (V := V)

local instance fiberFirstNormedAddCommGroup :
    NormedAddCommGroup (FiberFirst (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberFirstNormedSpace :
    NormedSpace Real (FiberFirst (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

/-! ## A continuous-linear retraction from arbitrary components -/

private def symmetrizedFramedSecondOrderJet
    (components : FramedSecondOrderJetAmbient X V) :
    FramedSecondOrderJet X V where
  value := components.1
  firstDerivative := components.2.1
  secondDerivative :=
    (2 : Real)⁻¹ • (components.2.2 + components.2.2.flip)
  secondDerivative_symmetric first second := by
    simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply]
    rw [add_comm]

private def symmetrizedFramedSecondOrderJetLinearMap :
    FramedSecondOrderJetAmbient X V →ₗ[Real]
      FramedSecondOrderJet X V where
  toFun := symmetrizedFramedSecondOrderJet
  map_add' first second := by
    apply FramedSecondOrderJet.ext_components X V
    · simp only [symmetrizedFramedSecondOrderJet,
        FramedSecondOrderJet.add_value, Prod.fst_add]
    · simp only [symmetrizedFramedSecondOrderJet,
        FramedSecondOrderJet.add_firstDerivative, Prod.snd_add,
        Prod.fst_add]
    · simp only [symmetrizedFramedSecondOrderJet,
        FramedSecondOrderJet.add_secondDerivative, Prod.snd_add,
        ContinuousLinearMap.flip_add]
      module
  map_smul' scalar components := by
    apply FramedSecondOrderJet.ext_components X V
    · simp only [symmetrizedFramedSecondOrderJet,
        FramedSecondOrderJet.smul_value, Prod.smul_fst,
        RingHom.id_apply]
    · simp only [symmetrizedFramedSecondOrderJet,
        FramedSecondOrderJet.smul_firstDerivative, Prod.smul_snd,
        Prod.smul_fst, RingHom.id_apply]
    · simp only [symmetrizedFramedSecondOrderJet,
        FramedSecondOrderJet.smul_secondDerivative, Prod.smul_snd,
        ContinuousLinearMap.flip_smul, RingHom.id_apply]
      module

private def symmetrizedFramedSecondOrderJetContinuousLinearMap :
    FramedSecondOrderJetAmbient X V →L[Real]
      FramedSecondOrderJet X V :=
  LinearMap.toContinuousLinearMap
    (symmetrizedFramedSecondOrderJetLinearMap (X := X) (V := V))

private theorem symmetrizedFramedSecondOrderJetContinuousLinearMap_components
    (jet : FramedSecondOrderJet X V) :
    symmetrizedFramedSecondOrderJetContinuousLinearMap
        (X := X) (V := V)
        (jet.value, jet.firstDerivative, jet.secondDerivative) = jet := by
  change symmetrizedFramedSecondOrderJet
    (jet.value, jet.firstDerivative, jet.secondDerivative) = jet
  apply FramedSecondOrderJet.ext_components X V
  · rfl
  · rfl
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [symmetrizedFramedSecondOrderJet, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply]
    rw [jet.secondDerivative_symmetric second first]
    module

/-! ## A finite-dimensional application criterion on manifolds -/

private theorem contMDiffOn_clm_apply_of_finiteDimensional
    {E H Parameter A B : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    [TopologicalSpace Parameter] [ChartedSpace H Parameter]
    [NormedAddCommGroup A] [NormedSpace Real A]
    [FiniteDimensional Real A]
    [NormedAddCommGroup B] [NormedSpace Real B]
    {n : WithTop ℕ∞} {s : Set Parameter}
    {family : Parameter → A →L[Real] B}
    (hApply : ∀ value,
      ContMDiffOn I 𝓘(Real, B) n (fun point ↦ family point value) s) :
    ContMDiffOn I 𝓘(Real, A →L[Real] B) n family s := by
  let dimension := finrank Real A
  have hDimension : dimension = finrank Real (Fin dimension → Real) :=
    (finrank_fin_fun Real).symm
  let domainEquiv := ContinuousLinearEquiv.ofFinrankEq hDimension
  let familyEquiv :=
    (domainEquiv.arrowCongr (1 : B ≃L[Real] B)).trans
      (ContinuousLinearEquiv.piRing (Fin dimension))
  rw [← id_comp family, ← familyEquiv.symm_comp_self]
  exact familyEquiv.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn
    (contMDiffOn_pi_space.mpr fun index ↦ hApply _)

/-! ## Smooth semidirect assembly -/

/-- On a manifold subset, `C^n` coefficient fields assemble to a `C^n`
family of semidirect framed-second-jet transports. -/
theorem contMDiffOn_semidirectTransport
    {E H Parameter : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    [TopologicalSpace Parameter] [ChartedSpace H Parameter]
    {n : WithTop ℕ∞} {s : Set Parameter}
    (change : Parameter → FramedSecondOrderJetSemidirectChange X V)
    (hBaseFirst : ContMDiffOn I 𝓘(Real, X →L[Real] X) n
      (fun point ↦ (change point).baseFirst) s)
    (hBaseSecond : ContMDiffOn I
      𝓘(Real, X →L[Real] X →L[Real] X) n
      (fun point ↦ (change point).baseSecond) s)
    (hFiberValue : ContMDiffOn I 𝓘(Real, V →L[Real] V) n
      (fun point ↦ (change point).fiberValue) s)
    (hFiberFirst : ContMDiffOn I
      𝓘(Real, X →L[Real] V →L[Real] V) n
      (fun point ↦ (change point).fiberFirst) s)
    (hFiberSecond : ContMDiffOn I
      𝓘(Real, X →L[Real] X →L[Real] V →L[Real] V) n
      (fun point ↦ (change point).fiberSecond) s) :
    ContMDiffOn I
      𝓘(Real, FramedSecondOrderJet X V →L[Real]
        FramedSecondOrderJet X V) n
      (fun point ↦ (change point).toContinuousLinearMap) s := by
  apply contMDiffOn_clm_apply_of_finiteDimensional
  intro jet
  have hValue : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
      ((change point).toContinuousLinearMap jet).value) s := by
    simpa only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_value] using
      hFiberValue.clm_apply
        (contMDiffOn_const : ContMDiffOn I 𝓘(Real, V) n
          (fun _ : Parameter ↦ jet.value) s)
  have hFirstDerivative : ContMDiffOn I
      𝓘(Real, X →L[Real] V) n (fun point ↦
        ((change point).toContinuousLinearMap jet).firstDerivative) s := by
    apply contMDiffOn_clm_apply_of_finiteDimensional
    intro direction
    have hBaseApply : ContMDiffOn I 𝓘(Real, X) n (fun point ↦
        (change point).baseFirst direction) s :=
      hBaseFirst.clm_apply contMDiffOn_const
    have hSourceDerivative : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        jet.firstDerivative ((change point).baseFirst direction)) s :=
      contMDiffOn_const.clm_apply hBaseApply
    have hTransportedDerivative : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦ (change point).fiberValue
          (jet.firstDerivative ((change point).baseFirst direction))) s :=
      hFiberValue.clm_apply hSourceDerivative
    have hFiberFirstApply : ContMDiffOn I 𝓘(Real, V →L[Real] V) n
        (fun point ↦ (change point).fiberFirst direction) s :=
      hFiberFirst.clm_apply contMDiffOn_const
    have hFiberFirstValue : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦ (change point).fiberFirst direction jet.value) s :=
      hFiberFirstApply.clm_apply contMDiffOn_const
    change ContMDiffOn I 𝓘(Real, V) n (fun point ↦
      (change point).fiberValue
          (jet.firstDerivative ((change point).baseFirst direction)) +
        (change point).fiberFirst direction jet.value) s
    convert hTransportedDerivative.add hFiberFirstValue using 1
    funext point
    rfl
  have hSecondDerivative : ContMDiffOn I
      𝓘(Real, X →L[Real] X →L[Real] V) n (fun point ↦
        ((change point).toContinuousLinearMap jet).secondDerivative) s := by
    apply contMDiffOn_clm_apply_of_finiteDimensional
    intro first
    apply contMDiffOn_clm_apply_of_finiteDimensional
    intro second
    have hBaseFirstApply : ContMDiffOn I 𝓘(Real, X) n (fun point ↦
        (change point).baseFirst first) s :=
      hBaseFirst.clm_apply contMDiffOn_const
    have hBaseSecondApply : ContMDiffOn I 𝓘(Real, X) n (fun point ↦
        (change point).baseFirst second) s :=
      hBaseFirst.clm_apply contMDiffOn_const
    have hJetSecondFirst : ContMDiffOn I 𝓘(Real, X →L[Real] V) n
        (fun point ↦ jet.secondDerivative
          ((change point).baseFirst first)) s :=
      contMDiffOn_const.clm_apply hBaseFirstApply
    have hJetSecond : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        jet.secondDerivative ((change point).baseFirst first)
          ((change point).baseFirst second)) s :=
      hJetSecondFirst.clm_apply hBaseSecondApply
    have hFirstTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberValue
          (jet.secondDerivative ((change point).baseFirst first)
            ((change point).baseFirst second))) s :=
      hFiberValue.clm_apply hJetSecond
    have hBaseSecondFirst : ContMDiffOn I 𝓘(Real, X →L[Real] X) n
        (fun point ↦ (change point).baseSecond first) s :=
      hBaseSecond.clm_apply contMDiffOn_const
    have hBaseSecondBoth : ContMDiffOn I 𝓘(Real, X) n (fun point ↦
        (change point).baseSecond first second) s :=
      hBaseSecondFirst.clm_apply contMDiffOn_const
    have hJetFirstBaseSecond : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦
          jet.firstDerivative ((change point).baseSecond first second)) s :=
      contMDiffOn_const.clm_apply hBaseSecondBoth
    have hSecondTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberValue
          (jet.firstDerivative ((change point).baseSecond first second))) s :=
      hFiberValue.clm_apply hJetFirstBaseSecond
    have hFiberFirstFirst : ContMDiffOn I 𝓘(Real, V →L[Real] V) n
        (fun point ↦ (change point).fiberFirst first) s :=
      hFiberFirst.clm_apply contMDiffOn_const
    have hJetFirstSecond : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        jet.firstDerivative ((change point).baseFirst second)) s :=
      contMDiffOn_const.clm_apply hBaseSecondApply
    have hThirdTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberFirst first
          (jet.firstDerivative ((change point).baseFirst second))) s :=
      hFiberFirstFirst.clm_apply hJetFirstSecond
    have hFiberFirstSecond : ContMDiffOn I 𝓘(Real, V →L[Real] V) n
        (fun point ↦ (change point).fiberFirst second) s :=
      hFiberFirst.clm_apply contMDiffOn_const
    have hJetFirstFirst : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        jet.firstDerivative ((change point).baseFirst first)) s :=
      contMDiffOn_const.clm_apply hBaseFirstApply
    have hFourthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberFirst second
          (jet.firstDerivative ((change point).baseFirst first))) s :=
      hFiberFirstSecond.clm_apply hJetFirstFirst
    have hFiberSecondFirst : ContMDiffOn I
        𝓘(Real, X →L[Real] V →L[Real] V) n
        (fun point ↦ (change point).fiberSecond first) s :=
      hFiberSecond.clm_apply contMDiffOn_const
    have hFiberSecondBoth : ContMDiffOn I 𝓘(Real, V →L[Real] V) n
        (fun point ↦ (change point).fiberSecond first second) s :=
      hFiberSecondFirst.clm_apply contMDiffOn_const
    have hFifthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberSecond first second jet.value) s :=
      hFiberSecondBoth.clm_apply contMDiffOn_const
    change ContMDiffOn I 𝓘(Real, V) n (fun point ↦
      (change point).fiberValue
            (jet.secondDerivative ((change point).baseFirst first)
              ((change point).baseFirst second)) +
          (change point).fiberValue
            (jet.firstDerivative ((change point).baseSecond first second)) +
        (change point).fiberFirst first
            (jet.firstDerivative ((change point).baseFirst second)) +
      (change point).fiberFirst second
          (jet.firstDerivative ((change point).baseFirst first)) +
      (change point).fiberSecond first second jet.value) s
    convert
      ((((hFirstTerm.add hSecondTerm).add hThirdTerm).add hFourthTerm).add
        hFifthTerm) using 1
    funext point
    rfl
  have hComponents : ContMDiffOn I
      𝓘(Real, FramedSecondOrderJetAmbient X V) n (fun point ↦
        (((change point).toContinuousLinearMap jet).value,
          ((change point).toContinuousLinearMap jet).firstDerivative,
          ((change point).toContinuousLinearMap jet).secondDerivative)) s :=
    by
      rw [contMDiffOn_prod_module_iff]
      constructor
      · change ContMDiffOn I _ n (fun point ↦
          ((change point).toContinuousLinearMap jet).value) s
        exact hValue
      · rw [contMDiffOn_prod_module_iff]
        constructor
        · change ContMDiffOn I _ n (fun point ↦
            ((change point).toContinuousLinearMap jet).firstDerivative) s
          exact hFirstDerivative
        · change ContMDiffOn I _ n (fun point ↦
            ((change point).toContinuousLinearMap jet).secondDerivative) s
          exact hSecondDerivative
  have hBack :=
    (symmetrizedFramedSecondOrderJetContinuousLinearMap
      (X := X) (V := V)).contMDiff.comp_contMDiffOn hComponents
  convert hBack using 1
  funext point
  exact
    (symmetrizedFramedSecondOrderJetContinuousLinearMap_components
      (X := X) (V := V)
      ((change point).toContinuousLinearMap jet)).symm

/-- Global normed-space form of smooth semidirect transport. -/
theorem contDiff_semidirectTransport
    {Parameter : Type*}
    [NormedAddCommGroup Parameter] [NormedSpace Real Parameter]
    {n : WithTop ℕ∞}
    (change : Parameter → FramedSecondOrderJetSemidirectChange X V)
    (hBaseFirst : ContDiff Real n (fun point ↦ (change point).baseFirst))
    (hBaseSecond : ContDiff Real n (fun point ↦ (change point).baseSecond))
    (hFiberValue : ContDiff Real n (fun point ↦ (change point).fiberValue))
    (hFiberFirst : ContDiff Real n (fun point ↦ (change point).fiberFirst))
    (hFiberSecond : ContDiff Real n (fun point ↦ (change point).fiberSecond)) :
    ContDiff Real n (fun point ↦
      (change point).toContinuousLinearMap) := by
  rw [← contDiffOn_univ]
  exact (contMDiffOn_semidirectTransport
    (I := 𝓘(Real, Parameter)) (s := Set.univ) change
      hBaseFirst.contMDiff.contMDiffOn
      hBaseSecond.contMDiff.contMDiffOn
      hFiberValue.contMDiff.contMDiffOn
      hFiberFirst.contMDiff.contMDiffOn
      hFiberSecond.contMDiff.contMDiffOn).contDiffOn

end
end P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D
end JanusFormal
