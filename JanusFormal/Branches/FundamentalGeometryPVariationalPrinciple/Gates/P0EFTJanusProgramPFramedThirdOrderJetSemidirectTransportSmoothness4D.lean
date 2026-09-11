import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D

/-!
# Smoothness of generic semidirect third-jet transport

A `C^n` family of the seven frozen base/fiber coefficients induces a `C^n`
family of continuous linear maps on framed third jets.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Function Module
open scoped Manifold ContDiff
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]

private abbrev JetFirstDerivative := X →L[Real] V

local instance jetFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup (JetFirstDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetFirstDerivativeNormedSpace :
    NormedSpace Real (JetFirstDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev JetSecondDerivative :=
  X →L[Real] JetFirstDerivative (X := X) (V := V)

local instance jetSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup (JetSecondDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetSecondDerivativeNormedSpace :
    NormedSpace Real (JetSecondDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev JetThirdDerivative :=
  X →L[Real] JetSecondDerivative (X := X) (V := V)

local instance jetThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup (JetThirdDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetThirdDerivativeNormedSpace :
    NormedSpace Real (JetThirdDerivative (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberEndomorphism := V →L[Real] V

local instance fiberEndomorphismNormedAddCommGroup :
    NormedAddCommGroup (FiberEndomorphism (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberEndomorphismNormedSpace :
    NormedSpace Real (FiberEndomorphism (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberFirstCoefficient :=
  X →L[Real] FiberEndomorphism (V := V)

local instance fiberFirstCoefficientNormedAddCommGroup :
    NormedAddCommGroup (FiberFirstCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberFirstCoefficientNormedSpace :
    NormedSpace Real (FiberFirstCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberSecondCoefficient :=
  X →L[Real] FiberFirstCoefficient (X := X) (V := V)

local instance fiberSecondCoefficientNormedAddCommGroup :
    NormedAddCommGroup (FiberSecondCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberSecondCoefficientNormedSpace :
    NormedSpace Real (FiberSecondCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberThirdCoefficient :=
  X →L[Real] FiberSecondCoefficient (X := X) (V := V)

local instance fiberThirdCoefficientNormedAddCommGroup :
    NormedAddCommGroup (FiberThirdCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberThirdCoefficientNormedSpace :
    NormedSpace Real (FiberThirdCoefficient (X := X) (V := V)) :=
  ContinuousLinearMap.toNormedSpace

/-! ## A continuous-linear retraction from arbitrary components -/

/-- Swap the last two variables of a curried continuous trilinear map. -/
private def flipSecondThird
    (third : JetThirdDerivative (X := X) (V := V)) :
    JetThirdDerivative (X := X) (V := V) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun first ↦ (third first).flip
      map_add' := by
        intro first second
        rw [map_add, ContinuousLinearMap.flip_add]
      map_smul' := by
        intro scalar first
        rw [map_smul, ContinuousLinearMap.flip_smul]
        rfl }

private theorem flipSecondThird_apply
    (third : JetThirdDerivative (X := X) (V := V))
    (first second thirdDirection : X) :
    flipSecondThird third first second thirdDirection =
      third first thirdDirection second := rfl

/-- Average a curried trilinear map over all six permutations. -/
private def symmetrizedThirdDerivative
    (third : JetThirdDerivative (X := X) (V := V)) :
    JetThirdDerivative (X := X) (V := V) :=
  (6 : Real)⁻¹ •
    (third + third.flip + flipSecondThird third +
      (flipSecondThird third).flip + flipSecondThird third.flip +
      (flipSecondThird third.flip).flip)

private theorem symmetrizedThirdDerivative_swap_first_second
    (third : JetThirdDerivative (X := X) (V := V))
    (first second thirdDirection : X) :
    symmetrizedThirdDerivative third first second thirdDirection =
      symmetrizedThirdDerivative third second first thirdDirection := by
  simp only [symmetrizedThirdDerivative, smul_apply, add_apply,
    ContinuousLinearMap.flip_apply, flipSecondThird_apply]
  module

private theorem symmetrizedThirdDerivative_swap_second_third
    (third : JetThirdDerivative (X := X) (V := V))
    (first second thirdDirection : X) :
    symmetrizedThirdDerivative third first second thirdDirection =
      symmetrizedThirdDerivative third first thirdDirection second := by
  simp only [symmetrizedThirdDerivative, smul_apply, add_apply,
    ContinuousLinearMap.flip_apply, flipSecondThird_apply]
  module

private theorem symmetrizedThirdDerivative_add
    (first second : JetThirdDerivative (X := X) (V := V)) :
    symmetrizedThirdDerivative (first + second) =
      symmetrizedThirdDerivative first + symmetrizedThirdDerivative second := by
  ext firstDirection secondDirection thirdDirection
  simp only [symmetrizedThirdDerivative, smul_apply, add_apply,
    ContinuousLinearMap.flip_apply, flipSecondThird_apply]
  module

private theorem symmetrizedThirdDerivative_smul
    (scalar : Real)
    (third : JetThirdDerivative (X := X) (V := V)) :
    symmetrizedThirdDerivative (scalar • third) =
      scalar • symmetrizedThirdDerivative third := by
  ext firstDirection secondDirection thirdDirection
  simp only [symmetrizedThirdDerivative, smul_apply, add_apply,
    ContinuousLinearMap.flip_apply, flipSecondThird_apply]
  module

private def symmetrizedFramedThirdOrderJet
    (components : FramedThirdOrderJetAmbient X V) :
    FramedThirdOrderJet X V where
  toFramedSecondOrderJet :=
    { value := components.1
      firstDerivative := components.2.1
      secondDerivative :=
        (2 : Real)⁻¹ •
          (components.2.2.1 + components.2.2.1.flip)
      secondDerivative_symmetric first second := by
        simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply]
        rw [add_comm] }
  thirdDerivative := symmetrizedThirdDerivative components.2.2.2
  thirdDerivative_swap_first_second :=
    symmetrizedThirdDerivative_swap_first_second components.2.2.2
  thirdDerivative_swap_second_third :=
    symmetrizedThirdDerivative_swap_second_third components.2.2.2

private def symmetrizedFramedThirdOrderJetLinearMap :
    FramedThirdOrderJetAmbient X V →ₗ[Real] FramedThirdOrderJet X V where
  toFun := symmetrizedFramedThirdOrderJet
  map_add' first second := by
    apply FramedThirdOrderJet.ext_components
    · apply FramedSecondOrderJet.ext_components
      · simp only [symmetrizedFramedThirdOrderJet,
          FramedThirdOrderJet.add_value, Prod.fst_add]
      · simp only [symmetrizedFramedThirdOrderJet,
          FramedThirdOrderJet.add_firstDerivative, Prod.snd_add,
          Prod.fst_add]
      · simp only [symmetrizedFramedThirdOrderJet,
          FramedThirdOrderJet.add_secondDerivative, Prod.snd_add,
          Prod.fst_add, ContinuousLinearMap.flip_add]
        module
    · simp only [symmetrizedFramedThirdOrderJet,
        FramedThirdOrderJet.add_thirdDerivative, Prod.snd_add]
      exact symmetrizedThirdDerivative_add first.2.2.2 second.2.2.2
  map_smul' scalar components := by
    apply FramedThirdOrderJet.ext_components
    · apply FramedSecondOrderJet.ext_components
      · simp only [symmetrizedFramedThirdOrderJet,
          FramedThirdOrderJet.smul_value, Prod.smul_fst, RingHom.id_apply]
      · simp only [symmetrizedFramedThirdOrderJet,
          FramedThirdOrderJet.smul_firstDerivative, Prod.smul_snd,
          Prod.smul_fst, RingHom.id_apply]
      · simp only [symmetrizedFramedThirdOrderJet,
          FramedThirdOrderJet.smul_secondDerivative, Prod.smul_snd,
          Prod.smul_fst, ContinuousLinearMap.flip_smul, RingHom.id_apply]
        module
    · simp only [symmetrizedFramedThirdOrderJet,
        FramedThirdOrderJet.smul_thirdDerivative, Prod.smul_snd,
        RingHom.id_apply]
      exact symmetrizedThirdDerivative_smul scalar components.2.2.2

private def symmetrizedFramedThirdOrderJetContinuousLinearMap :
    FramedThirdOrderJetAmbient X V →L[Real] FramedThirdOrderJet X V :=
  LinearMap.toContinuousLinearMap
    (symmetrizedFramedThirdOrderJetLinearMap (X := X) (V := V))

private theorem symmetrizedFramedThirdOrderJetContinuousLinearMap_components
    (jet : FramedThirdOrderJet X V) :
    symmetrizedFramedThirdOrderJetContinuousLinearMap (X := X) (V := V)
        (jet.value, jet.firstDerivative, jet.secondDerivative,
          jet.thirdDerivative) = jet := by
  change symmetrizedFramedThirdOrderJet
    (jet.value, jet.firstDerivative, jet.secondDerivative,
      jet.thirdDerivative) = jet
  apply FramedThirdOrderJet.ext_components
  · apply FramedSecondOrderJet.ext_components
    · rfl
    · rfl
    · apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      simp only [symmetrizedFramedThirdOrderJet, smul_apply, add_apply,
        ContinuousLinearMap.flip_apply]
      rw [jet.secondDerivative_symmetric second first]
      module
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    apply ContinuousLinearMap.ext
    intro third
    have hSecondFirst : jet.thirdDerivative second first third =
        jet.thirdDerivative first second third :=
      (jet.thirdDerivative_swap_first_second first second third).symm
    have hFirstThird : jet.thirdDerivative first third second =
        jet.thirdDerivative first second third :=
      (jet.thirdDerivative_swap_second_third first second third).symm
    have hSecondThirdFirst : jet.thirdDerivative second third first =
        jet.thirdDerivative first second third := by
      calc
        jet.thirdDerivative second third first =
            jet.thirdDerivative second first third :=
          jet.thirdDerivative_swap_second_third second third first
        _ = jet.thirdDerivative first second third := hSecondFirst
    have hThirdFirstSecond : jet.thirdDerivative third first second =
        jet.thirdDerivative first second third := by
      calc
        jet.thirdDerivative third first second =
            jet.thirdDerivative first third second :=
          jet.thirdDerivative_swap_first_second third first second
        _ = jet.thirdDerivative first second third := hFirstThird
    have hThirdSecondFirst : jet.thirdDerivative third second first =
        jet.thirdDerivative first second third := by
      calc
        jet.thirdDerivative third second first =
            jet.thirdDerivative second third first :=
          jet.thirdDerivative_swap_first_second third second first
        _ = jet.thirdDerivative first second third := hSecondThirdFirst
    change symmetrizedThirdDerivative jet.thirdDerivative first second third =
      jet.thirdDerivative first second third
    simp only [symmetrizedThirdDerivative, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, flipSecondThird_apply]
    rw [hSecondFirst, hFirstThird, hSecondThirdFirst, hThirdFirstSecond,
      hThirdSecondFirst]
    module

/-- Reassemble a third jet from an already symmetric lower jet and an
arbitrary third derivative.  This avoids changing the topology carried by the
lower framed jet when smoothness is reconstructed. -/
private def symmetrizedFramedThirdOrderJetFromLower
    (components : FramedSecondOrderJet X V ×
      JetThirdDerivative (X := X) (V := V)) :
    FramedThirdOrderJet X V where
  toFramedSecondOrderJet := components.1
  thirdDerivative := symmetrizedThirdDerivative components.2
  thirdDerivative_swap_first_second :=
    symmetrizedThirdDerivative_swap_first_second components.2
  thirdDerivative_swap_second_third :=
    symmetrizedThirdDerivative_swap_second_third components.2

private def symmetrizedFramedThirdOrderJetFromLowerLinearMap :
    (FramedSecondOrderJet X V × JetThirdDerivative (X := X) (V := V)) →ₗ[Real]
      FramedThirdOrderJet X V where
  toFun := symmetrizedFramedThirdOrderJetFromLower
  map_add' first second := by
    apply FramedThirdOrderJet.ext_components
    · simp only [symmetrizedFramedThirdOrderJetFromLower,
        FramedThirdOrderJet.add_toFramedSecondOrderJet, Prod.fst_add]
    · simp only [symmetrizedFramedThirdOrderJetFromLower,
        FramedThirdOrderJet.add_thirdDerivative, Prod.snd_add]
      exact symmetrizedThirdDerivative_add first.2 second.2
  map_smul' scalar components := by
    apply FramedThirdOrderJet.ext_components
    · simp only [symmetrizedFramedThirdOrderJetFromLower,
        FramedThirdOrderJet.smul_toFramedSecondOrderJet, Prod.smul_fst,
        RingHom.id_apply]
    · simp only [symmetrizedFramedThirdOrderJetFromLower,
        FramedThirdOrderJet.smul_thirdDerivative, Prod.smul_snd,
        RingHom.id_apply]
      exact symmetrizedThirdDerivative_smul scalar components.2

private def symmetrizedFramedThirdOrderJetFromLowerContinuousLinearMap :
    (FramedSecondOrderJet X V × JetThirdDerivative (X := X) (V := V)) →L[Real]
      FramedThirdOrderJet X V :=
  LinearMap.toContinuousLinearMap
    (symmetrizedFramedThirdOrderJetFromLowerLinearMap (X := X) (V := V))

private theorem symmetrizedFramedThirdOrderJetFromLower_components
    (jet : FramedThirdOrderJet X V) :
    symmetrizedFramedThirdOrderJetFromLowerContinuousLinearMap
        (X := X) (V := V)
        (jet.toFramedSecondOrderJet, jet.thirdDerivative) = jet := by
  change symmetrizedFramedThirdOrderJetFromLower
    (jet.toFramedSecondOrderJet, jet.thirdDerivative) = jet
  apply FramedThirdOrderJet.ext_components
  · rfl
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    apply ContinuousLinearMap.ext
    intro third
    have hSecondFirst : jet.thirdDerivative second first third =
        jet.thirdDerivative first second third :=
      (jet.thirdDerivative_swap_first_second first second third).symm
    have hFirstThird : jet.thirdDerivative first third second =
        jet.thirdDerivative first second third :=
      (jet.thirdDerivative_swap_second_third first second third).symm
    have hSecondThirdFirst : jet.thirdDerivative second third first =
        jet.thirdDerivative first second third := by
      calc
        jet.thirdDerivative second third first =
            jet.thirdDerivative second first third :=
          jet.thirdDerivative_swap_second_third second third first
        _ = jet.thirdDerivative first second third := hSecondFirst
    have hThirdFirstSecond : jet.thirdDerivative third first second =
        jet.thirdDerivative first second third := by
      calc
        jet.thirdDerivative third first second =
            jet.thirdDerivative first third second :=
          jet.thirdDerivative_swap_first_second third first second
        _ = jet.thirdDerivative first second third := hFirstThird
    have hThirdSecondFirst : jet.thirdDerivative third second first =
        jet.thirdDerivative first second third := by
      calc
        jet.thirdDerivative third second first =
            jet.thirdDerivative second third first :=
          jet.thirdDerivative_swap_first_second third second first
        _ = jet.thirdDerivative first second third := hSecondThirdFirst
    change symmetrizedThirdDerivative jet.thirdDerivative first second third =
      jet.thirdDerivative first second third
    simp only [symmetrizedThirdDerivative, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, flipSecondThird_apply]
    rw [hSecondFirst, hFirstThird, hSecondThirdFirst, hThirdFirstSecond,
      hThirdSecondFirst]
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
family of semidirect framed-third-jet transports. -/
theorem contMDiffOn_semidirectTransport
    {E H Parameter : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    [TopologicalSpace Parameter] [ChartedSpace H Parameter]
    {n : WithTop ℕ∞} {s : Set Parameter}
    (change : Parameter → FramedThirdOrderJetSemidirectChange X V)
    (hBaseFirst : ContMDiffOn I 𝓘(Real, X →L[Real] X) n
      (fun point ↦ (change point).baseFirst) s)
    (hBaseSecond : ContMDiffOn I
      𝓘(Real, X →L[Real] X →L[Real] X) n
      (fun point ↦ (change point).baseSecond) s)
    (hBaseThird : ContMDiffOn I
      𝓘(Real, X →L[Real] X →L[Real] X →L[Real] X) n
      (fun point ↦ (change point).baseThird) s)
    (hFiberValue : ContMDiffOn I 𝓘(Real, V →L[Real] V) n
      (fun point ↦ (change point).fiberValue) s)
    (hFiberFirst : ContMDiffOn I
      𝓘(Real, X →L[Real] V →L[Real] V) n
      (fun point ↦ (change point).fiberFirst) s)
    (hFiberSecond : ContMDiffOn I
      𝓘(Real, X →L[Real] X →L[Real] V →L[Real] V) n
      (fun point ↦ (change point).fiberSecond) s)
    (hFiberThird : ContMDiffOn I
      𝓘(Real, X →L[Real] X →L[Real] X →L[Real] V →L[Real] V) n
      (fun point ↦ (change point).fiberThird) s) :
    ContMDiffOn I
      𝓘(Real, FramedThirdOrderJet X V →L[Real]
        FramedThirdOrderJet X V) n
      (fun point ↦ (change point).toContinuousLinearMap) s := by
  apply contMDiffOn_clm_apply_of_finiteDimensional
  intro jet
  have hLowerMap : ContMDiffOn I
      𝓘(Real, FramedSecondOrderJet X V →L[Real]
        FramedSecondOrderJet X V) n
      (fun point ↦
        (change point).toFramedSecondOrderJetSemidirectChange.toContinuousLinearMap) s :=
    P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D.contMDiffOn_semidirectTransport
      (fun point ↦ (change point).toFramedSecondOrderJetSemidirectChange)
      hBaseFirst hBaseSecond hFiberValue hFiberFirst hFiberSecond
  have hLowerJet : ContMDiffOn I
      𝓘(Real, FramedSecondOrderJet X V) n (fun point ↦
        ((change point).toContinuousLinearMap jet).toFramedSecondOrderJet) s := by
    simpa only [FramedThirdOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedThirdOrderJetSemidirectChange.transport_toFramedSecondOrderJet,
      FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply] using
      hLowerMap.clm_apply
        (contMDiffOn_const : ContMDiffOn I
          𝓘(Real, FramedSecondOrderJet X V) n
          (fun _ : Parameter ↦ jet.toFramedSecondOrderJet) s)
  have hThirdDerivative : ContMDiffOn I
      𝓘(Real, JetThirdDerivative (X := X) (V := V)) n (fun point ↦
        ((change point).toContinuousLinearMap jet).thirdDerivative) s := by
    apply contMDiffOn_clm_apply_of_finiteDimensional
    intro first
    apply contMDiffOn_clm_apply_of_finiteDimensional
    intro second
    apply contMDiffOn_clm_apply_of_finiteDimensional
    intro third
    have hBaseFirstFirst : ContMDiffOn I 𝓘(Real, X) n (fun point ↦
        (change point).baseFirst first) s :=
      hBaseFirst.clm_apply contMDiffOn_const
    have hBaseFirstSecond : ContMDiffOn I 𝓘(Real, X) n (fun point ↦
        (change point).baseFirst second) s :=
      hBaseFirst.clm_apply contMDiffOn_const
    have hBaseFirstThird : ContMDiffOn I 𝓘(Real, X) n (fun point ↦
        (change point).baseFirst third) s :=
      hBaseFirst.clm_apply contMDiffOn_const
    have hBaseSecondFirst : ContMDiffOn I
        𝓘(Real, X →L[Real] X) n (fun point ↦
          (change point).baseSecond first) s :=
      hBaseSecond.clm_apply contMDiffOn_const
    have hBaseSecondFirstSecond : ContMDiffOn I 𝓘(Real, X) n
        (fun point ↦ (change point).baseSecond first second) s :=
      hBaseSecondFirst.clm_apply contMDiffOn_const
    have hBaseSecondFirstThird : ContMDiffOn I 𝓘(Real, X) n
        (fun point ↦ (change point).baseSecond first third) s :=
      hBaseSecondFirst.clm_apply contMDiffOn_const
    have hBaseSecondSecond : ContMDiffOn I
        𝓘(Real, X →L[Real] X) n (fun point ↦
          (change point).baseSecond second) s :=
      hBaseSecond.clm_apply contMDiffOn_const
    have hBaseSecondSecondThird : ContMDiffOn I 𝓘(Real, X) n
        (fun point ↦ (change point).baseSecond second third) s :=
      hBaseSecondSecond.clm_apply contMDiffOn_const
    have hBaseThirdFirst : ContMDiffOn I
        𝓘(Real, X →L[Real] X →L[Real] X) n (fun point ↦
          (change point).baseThird first) s :=
      hBaseThird.clm_apply contMDiffOn_const
    have hBaseThirdFirstSecond : ContMDiffOn I
        𝓘(Real, X →L[Real] X) n (fun point ↦
          (change point).baseThird first second) s :=
      hBaseThirdFirst.clm_apply contMDiffOn_const
    have hBaseThirdFirstSecondThird : ContMDiffOn I 𝓘(Real, X) n
        (fun point ↦ (change point).baseThird first second third) s :=
      hBaseThirdFirstSecond.clm_apply contMDiffOn_const
    have hFiberFirstFirst : ContMDiffOn I
        𝓘(Real, FiberEndomorphism (V := V)) n (fun point ↦
          (change point).fiberFirst first) s :=
      hFiberFirst.clm_apply contMDiffOn_const
    have hFiberFirstSecond : ContMDiffOn I
        𝓘(Real, FiberEndomorphism (V := V)) n (fun point ↦
          (change point).fiberFirst second) s :=
      hFiberFirst.clm_apply contMDiffOn_const
    have hFiberFirstThird : ContMDiffOn I
        𝓘(Real, FiberEndomorphism (V := V)) n (fun point ↦
          (change point).fiberFirst third) s :=
      hFiberFirst.clm_apply contMDiffOn_const
    have hFiberSecondFirst : ContMDiffOn I
        𝓘(Real, FiberFirstCoefficient (X := X) (V := V)) n (fun point ↦
          (change point).fiberSecond first) s :=
      hFiberSecond.clm_apply contMDiffOn_const
    have hFiberSecondFirstSecond : ContMDiffOn I
        𝓘(Real, FiberEndomorphism (V := V)) n (fun point ↦
          (change point).fiberSecond first second) s :=
      hFiberSecondFirst.clm_apply contMDiffOn_const
    have hFiberSecondFirstThird : ContMDiffOn I
        𝓘(Real, FiberEndomorphism (V := V)) n (fun point ↦
          (change point).fiberSecond first third) s :=
      hFiberSecondFirst.clm_apply contMDiffOn_const
    have hFiberSecondSecond : ContMDiffOn I
        𝓘(Real, FiberFirstCoefficient (X := X) (V := V)) n (fun point ↦
          (change point).fiberSecond second) s :=
      hFiberSecond.clm_apply contMDiffOn_const
    have hFiberSecondSecondThird : ContMDiffOn I
        𝓘(Real, FiberEndomorphism (V := V)) n (fun point ↦
          (change point).fiberSecond second third) s :=
      hFiberSecondSecond.clm_apply contMDiffOn_const
    have hFiberThirdFirst : ContMDiffOn I
        𝓘(Real, FiberSecondCoefficient (X := X) (V := V)) n (fun point ↦
          (change point).fiberThird first) s :=
      hFiberThird.clm_apply contMDiffOn_const
    have hFiberThirdFirstSecond : ContMDiffOn I
        𝓘(Real, FiberFirstCoefficient (X := X) (V := V)) n (fun point ↦
          (change point).fiberThird first second) s :=
      hFiberThirdFirst.clm_apply contMDiffOn_const
    have hFiberThirdFirstSecondThird : ContMDiffOn I
        𝓘(Real, FiberEndomorphism (V := V)) n (fun point ↦
          (change point).fiberThird first second third) s :=
      hFiberThirdFirstSecond.clm_apply contMDiffOn_const
    have hJetThirdFirst : ContMDiffOn I
        𝓘(Real, JetSecondDerivative (X := X) (V := V)) n (fun point ↦
          jet.thirdDerivative ((change point).baseFirst first)) s :=
      contMDiffOn_const.clm_apply hBaseFirstFirst
    have hJetThirdFirstSecond : ContMDiffOn I
        𝓘(Real, JetFirstDerivative (X := X) (V := V)) n (fun point ↦
          jet.thirdDerivative ((change point).baseFirst first)
            ((change point).baseFirst second)) s :=
      hJetThirdFirst.clm_apply hBaseFirstSecond
    have hJetThird : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        jet.thirdDerivative ((change point).baseFirst first)
          ((change point).baseFirst second)
          ((change point).baseFirst third)) s :=
      hJetThirdFirstSecond.clm_apply hBaseFirstThird
    have hFirstTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberValue
          (jet.thirdDerivative ((change point).baseFirst first)
            ((change point).baseFirst second)
            ((change point).baseFirst third))) s :=
      hFiberValue.clm_apply hJetThird
    have hJetSecondBaseSecondFirstSecond : ContMDiffOn I
        𝓘(Real, JetFirstDerivative (X := X) (V := V)) n (fun point ↦
          jet.secondDerivative ((change point).baseSecond first second)) s :=
      contMDiffOn_const.clm_apply hBaseSecondFirstSecond
    have hJetSecondBaseSecondFirstSecondBaseFirstThird : ContMDiffOn I
        𝓘(Real, V) n (fun point ↦
          jet.secondDerivative ((change point).baseSecond first second)
            ((change point).baseFirst third)) s :=
      hJetSecondBaseSecondFirstSecond.clm_apply hBaseFirstThird
    have hSecondTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberValue
          (jet.secondDerivative ((change point).baseSecond first second)
            ((change point).baseFirst third))) s :=
      hFiberValue.clm_apply hJetSecondBaseSecondFirstSecondBaseFirstThird
    have hJetSecondBaseSecondFirstThird : ContMDiffOn I
        𝓘(Real, JetFirstDerivative (X := X) (V := V)) n (fun point ↦
          jet.secondDerivative ((change point).baseSecond first third)) s :=
      contMDiffOn_const.clm_apply hBaseSecondFirstThird
    have hJetSecondBaseSecondFirstThirdBaseFirstSecond : ContMDiffOn I
        𝓘(Real, V) n (fun point ↦
          jet.secondDerivative ((change point).baseSecond first third)
            ((change point).baseFirst second)) s :=
      hJetSecondBaseSecondFirstThird.clm_apply hBaseFirstSecond
    have hThirdTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberValue
          (jet.secondDerivative ((change point).baseSecond first third)
            ((change point).baseFirst second))) s :=
      hFiberValue.clm_apply hJetSecondBaseSecondFirstThirdBaseFirstSecond
    have hJetSecondBaseSecondSecondThird : ContMDiffOn I
        𝓘(Real, JetFirstDerivative (X := X) (V := V)) n (fun point ↦
          jet.secondDerivative ((change point).baseSecond second third)) s :=
      contMDiffOn_const.clm_apply hBaseSecondSecondThird
    have hJetSecondBaseSecondSecondThirdBaseFirstFirst : ContMDiffOn I
        𝓘(Real, V) n (fun point ↦
          jet.secondDerivative ((change point).baseSecond second third)
            ((change point).baseFirst first)) s :=
      hJetSecondBaseSecondSecondThird.clm_apply hBaseFirstFirst
    have hFourthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberValue
          (jet.secondDerivative ((change point).baseSecond second third)
            ((change point).baseFirst first))) s :=
      hFiberValue.clm_apply hJetSecondBaseSecondSecondThirdBaseFirstFirst
    have hJetFirstBaseThird : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        jet.firstDerivative ((change point).baseThird first second third)) s :=
      contMDiffOn_const.clm_apply hBaseThirdFirstSecondThird
    have hFifthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberValue
          (jet.firstDerivative ((change point).baseThird first second third))) s :=
      hFiberValue.clm_apply hJetFirstBaseThird
    have hJetSecondBaseFirstSecond : ContMDiffOn I
        𝓘(Real, JetFirstDerivative (X := X) (V := V)) n (fun point ↦
          jet.secondDerivative ((change point).baseFirst second)) s :=
      contMDiffOn_const.clm_apply hBaseFirstSecond
    have hJetSecondBaseFirstSecondThird : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦ jet.secondDerivative ((change point).baseFirst second)
          ((change point).baseFirst third)) s :=
      hJetSecondBaseFirstSecond.clm_apply hBaseFirstThird
    have hSixthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberFirst first
          (jet.secondDerivative ((change point).baseFirst second)
            ((change point).baseFirst third))) s :=
      hFiberFirstFirst.clm_apply hJetSecondBaseFirstSecondThird
    have hJetSecondBaseFirstFirst : ContMDiffOn I
        𝓘(Real, JetFirstDerivative (X := X) (V := V)) n (fun point ↦
          jet.secondDerivative ((change point).baseFirst first)) s :=
      contMDiffOn_const.clm_apply hBaseFirstFirst
    have hJetSecondBaseFirstFirstThird : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦ jet.secondDerivative ((change point).baseFirst first)
          ((change point).baseFirst third)) s :=
      hJetSecondBaseFirstFirst.clm_apply hBaseFirstThird
    have hSeventhTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberFirst second
          (jet.secondDerivative ((change point).baseFirst first)
            ((change point).baseFirst third))) s :=
      hFiberFirstSecond.clm_apply hJetSecondBaseFirstFirstThird
    have hJetSecondBaseFirstFirstSecond : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦ jet.secondDerivative ((change point).baseFirst first)
          ((change point).baseFirst second)) s :=
      hJetSecondBaseFirstFirst.clm_apply hBaseFirstSecond
    have hEighthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberFirst third
          (jet.secondDerivative ((change point).baseFirst first)
            ((change point).baseFirst second))) s :=
      hFiberFirstThird.clm_apply hJetSecondBaseFirstFirstSecond
    have hJetFirstBaseSecondSecondThird : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦
          jet.firstDerivative ((change point).baseSecond second third)) s :=
      contMDiffOn_const.clm_apply hBaseSecondSecondThird
    have hNinthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberFirst first
          (jet.firstDerivative ((change point).baseSecond second third))) s :=
      hFiberFirstFirst.clm_apply hJetFirstBaseSecondSecondThird
    have hJetFirstBaseSecondFirstThird : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦
          jet.firstDerivative ((change point).baseSecond first third)) s :=
      contMDiffOn_const.clm_apply hBaseSecondFirstThird
    have hTenthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberFirst second
          (jet.firstDerivative ((change point).baseSecond first third))) s :=
      hFiberFirstSecond.clm_apply hJetFirstBaseSecondFirstThird
    have hJetFirstBaseSecondFirstSecond : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦
          jet.firstDerivative ((change point).baseSecond first second)) s :=
      contMDiffOn_const.clm_apply hBaseSecondFirstSecond
    have hEleventhTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberFirst third
          (jet.firstDerivative ((change point).baseSecond first second))) s :=
      hFiberFirstThird.clm_apply hJetFirstBaseSecondFirstSecond
    have hJetFirstBaseFirstThird : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦
          jet.firstDerivative ((change point).baseFirst third)) s :=
      contMDiffOn_const.clm_apply hBaseFirstThird
    have hTwelfthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberSecond first second
          (jet.firstDerivative ((change point).baseFirst third))) s :=
      hFiberSecondFirstSecond.clm_apply hJetFirstBaseFirstThird
    have hJetFirstBaseFirstSecond : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦
          jet.firstDerivative ((change point).baseFirst second)) s :=
      contMDiffOn_const.clm_apply hBaseFirstSecond
    have hThirteenthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberSecond first third
          (jet.firstDerivative ((change point).baseFirst second))) s :=
      hFiberSecondFirstThird.clm_apply hJetFirstBaseFirstSecond
    have hJetFirstBaseFirstFirst : ContMDiffOn I 𝓘(Real, V) n
        (fun point ↦
          jet.firstDerivative ((change point).baseFirst first)) s :=
      contMDiffOn_const.clm_apply hBaseFirstFirst
    have hFourteenthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberSecond second third
          (jet.firstDerivative ((change point).baseFirst first))) s :=
      hFiberSecondSecondThird.clm_apply hJetFirstBaseFirstFirst
    have hFifteenthTerm : ContMDiffOn I 𝓘(Real, V) n (fun point ↦
        (change point).fiberThird first second third jet.value) s :=
      hFiberThirdFirstSecondThird.clm_apply contMDiffOn_const
    change ContMDiffOn I 𝓘(Real, V) n (fun point ↦
      (change point).fiberValue
          (jet.thirdDerivative
            ((change point).baseFirst first)
            ((change point).baseFirst second)
            ((change point).baseFirst third)) +
        (change point).fiberValue
          (jet.secondDerivative
            ((change point).baseSecond first second)
            ((change point).baseFirst third)) +
        (change point).fiberValue
          (jet.secondDerivative
            ((change point).baseSecond first third)
            ((change point).baseFirst second)) +
        (change point).fiberValue
          (jet.secondDerivative
            ((change point).baseSecond second third)
            ((change point).baseFirst first)) +
        (change point).fiberValue
          (jet.firstDerivative
            ((change point).baseThird first second third)) +
        (change point).fiberFirst first
          (jet.secondDerivative
            ((change point).baseFirst second)
            ((change point).baseFirst third)) +
        (change point).fiberFirst second
          (jet.secondDerivative
            ((change point).baseFirst first)
            ((change point).baseFirst third)) +
        (change point).fiberFirst third
          (jet.secondDerivative
            ((change point).baseFirst first)
            ((change point).baseFirst second)) +
        (change point).fiberFirst first
          (jet.firstDerivative
            ((change point).baseSecond second third)) +
        (change point).fiberFirst second
          (jet.firstDerivative
            ((change point).baseSecond first third)) +
        (change point).fiberFirst third
          (jet.firstDerivative
            ((change point).baseSecond first second)) +
        (change point).fiberSecond first second
          (jet.firstDerivative ((change point).baseFirst third)) +
        (change point).fiberSecond first third
          (jet.firstDerivative ((change point).baseFirst second)) +
        (change point).fiberSecond second third
          (jet.firstDerivative ((change point).baseFirst first)) +
        (change point).fiberThird first second third jet.value) s
    exact ((((((((((((((hFirstTerm.add hSecondTerm).add hThirdTerm).add
      hFourthTerm).add hFifthTerm).add hSixthTerm).add hSeventhTerm).add
      hEighthTerm).add hNinthTerm).add hTenthTerm).add hEleventhTerm).add
      hTwelfthTerm).add hThirteenthTerm).add hFourteenthTerm).add
      hFifteenthTerm)
  have hComponents := hLowerJet.prodMk_space hThirdDerivative
  have hBack :=
    (symmetrizedFramedThirdOrderJetFromLowerContinuousLinearMap
      (X := X) (V := V)).contMDiff.comp_contMDiffOn hComponents
  convert hBack using 1
  funext point
  exact
    (symmetrizedFramedThirdOrderJetFromLower_components
      (X := X) (V := V) ((change point).toContinuousLinearMap jet)).symm

/-- Global normed-space form of smooth semidirect third-jet transport. -/
theorem contDiff_semidirectTransport
    {Parameter : Type*}
    [NormedAddCommGroup Parameter] [NormedSpace Real Parameter]
    {n : WithTop ℕ∞}
    (change : Parameter → FramedThirdOrderJetSemidirectChange X V)
    (hBaseFirst : ContDiff Real n (fun point ↦ (change point).baseFirst))
    (hBaseSecond : ContDiff Real n (fun point ↦ (change point).baseSecond))
    (hBaseThird : ContDiff Real n (fun point ↦ (change point).baseThird))
    (hFiberValue : ContDiff Real n (fun point ↦ (change point).fiberValue))
    (hFiberFirst : ContDiff Real n (fun point ↦ (change point).fiberFirst))
    (hFiberSecond : ContDiff Real n (fun point ↦ (change point).fiberSecond))
    (hFiberThird : ContDiff Real n (fun point ↦ (change point).fiberThird)) :
    ContDiff Real n (fun point ↦
      (change point).toContinuousLinearMap) := by
  rw [← contDiffOn_univ]
  exact (contMDiffOn_semidirectTransport
    (I := 𝓘(Real, Parameter)) (s := Set.univ) change
      hBaseFirst.contMDiff.contMDiffOn
      hBaseSecond.contMDiff.contMDiffOn
      hBaseThird.contMDiff.contMDiffOn
      hFiberValue.contMDiff.contMDiffOn
      hFiberFirst.contMDiff.contMDiffOn
      hFiberSecond.contMDiff.contMDiffOn
      hFiberThird.contMDiff.contMDiffOn).contDiffOn

end
end P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D
end JanusFormal
