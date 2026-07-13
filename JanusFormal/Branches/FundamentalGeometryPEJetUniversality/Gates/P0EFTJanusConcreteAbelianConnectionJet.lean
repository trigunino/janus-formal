import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAbelianConnectionJetNormalForm
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusConcreteSecondJetChainRule

namespace JanusFormal
namespace P0EFTJanusConcreteAbelianConnectionJet

set_option autoImplicit false

universe u v

open P0EFTJanusAbelianConnectionJetNormalForm
open P0EFTJanusConcreteSecondJetChainRule

/-- Concrete local first jet of an abelian connection: its value and the first
derivative of that value. -/
@[ext]
structure ConcreteConnectionOneJet (Tangent : Type u) where
  value : Tangent → ℝ
  derivative : Tangent → Tangent → ℝ

/-- Concrete two-jet of an abelian gauge parameter. The Hessian symmetry is the
integrability condition distinguishing a genuine scalar two-jet from an
arbitrary derivative correction. -/
structure ConcreteGaugeTwoJet (Tangent : Type u) where
  gradient : Tangent → ℝ
  hessian : Tangent → Tangent → ℝ
  hessian_symmetric : IsSymmetricTensor hessian

/-- Local abelian gauge transformation `A ↦ A + d chi` on first jets. -/
def applyGauge
    {Tangent : Type u}
    (gauge : ConcreteGaugeTwoJet Tangent)
    (jet : ConcreteConnectionOneJet Tangent) :
    ConcreteConnectionOneJet Tangent where
  value x := jet.value x + gauge.gradient x
  derivative x y := jet.derivative x y + gauge.hessian x y

/-- Curvature two-form extracted from the first derivative of the local
connection one-form. -/
def curvature
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent) :
    Tangent → Tangent → ℝ :=
  fun x y => jet.derivative x y - jet.derivative y x

/-- Symmetric part of an arbitrary two-covariant real tensor. -/
noncomputable def symmetricPart
    {Tangent : Type u}
    (derivative : Tangent → Tangent → ℝ) :
    Tangent → Tangent → ℝ :=
  fun x y => (derivative x y + derivative y x) / 2

/-- Alternating part of an arbitrary two-covariant real tensor. -/
noncomputable def alternatingPart
    {Tangent : Type u}
    (derivative : Tangent → Tangent → ℝ) :
    Tangent → Tangent → ℝ :=
  fun x y => (derivative x y - derivative y x) / 2

/-- The symmetric-part construction is symmetric. -/
theorem symmetricPart_is_symmetric
    {Tangent : Type u}
    (derivative : Tangent → Tangent → ℝ) :
    IsSymmetricTensor (symmetricPart derivative) := by
  intro x y
  simp only [symmetricPart]
  ring

/-- The alternating part changes sign when its arguments are exchanged. -/
theorem alternatingPart_swap
    {Tangent : Type u}
    (derivative : Tangent → Tangent → ℝ)
    (x y : Tangent) :
    alternatingPart derivative y x =
      -alternatingPart derivative x y := by
  simp only [alternatingPart]
  ring

/-- Exact symmetric-plus-alternating decomposition. -/
theorem derivative_eq_symmetric_add_alternating
    {Tangent : Type u}
    (derivative : Tangent → Tangent → ℝ)
    (x y : Tangent) :
    derivative x y =
      symmetricPart derivative x y +
        alternatingPart derivative x y := by
  simp only [symmetricPart, alternatingPart]
  ring

/-- Curvature is twice the alternating part. -/
theorem curvature_eq_two_mul_alternatingPart
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent)
    (x y : Tangent) :
    curvature jet x y =
      2 * alternatingPart jet.derivative x y := by
  simp only [curvature, alternatingPart]
  ring

/-- Curvature is alternating. -/
theorem curvature_swap
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent)
    (x y : Tangent) :
    curvature jet y x = -curvature jet x y := by
  simp only [curvature]
  ring

/-- Abelian curvature is unchanged by a genuine gauge two-jet because its
Hessian is symmetric. -/
theorem curvature_applyGauge
    {Tangent : Type u}
    (gauge : ConcreteGaugeTwoJet Tangent)
    (jet : ConcreteConnectionOneJet Tangent) :
    curvature (applyGauge gauge jet) = curvature jet := by
  funext x y
  have hSymmetric := gauge.hessian_symmetric x y
  simp only [curvature, applyGauge]
  rw [hSymmetric]
  ring

/-- Gauge parameter that kills the connection value and the symmetric part of
its first derivative. -/
noncomputable def concreteNormalizingGauge
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent) :
    ConcreteGaugeTwoJet Tangent where
  gradient x := -jet.value x
  hessian x y := -symmetricPart jet.derivative x y
  hessian_symmetric := by
    intro x y
    have hSymmetric := symmetricPart_is_symmetric jet.derivative x y
    exact congrArg Neg.neg hSymmetric

/-- Concrete curvature gauge slice. Its derivative is the alternating part, hence
is uniquely determined by curvature. -/
noncomputable def concreteCurvatureNormalForm
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent) :
    ConcreteConnectionOneJet Tangent where
  value := 0
  derivative := alternatingPart jet.derivative

/-- The explicit gradient/Hessian gauge reaches the curvature slice. -/
theorem concrete_normalizing_gauge_reaches_curvature_form
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent) :
    applyGauge (concreteNormalizingGauge jet) jet =
      concreteCurvatureNormalForm jet := by
  apply ConcreteConnectionOneJet.ext
  · funext x
    simp [applyGauge, concreteNormalizingGauge,
      concreteCurvatureNormalForm]
  · funext x y
    simp only [applyGauge, concreteNormalizingGauge,
      concreteCurvatureNormalForm, symmetricPart, alternatingPart]
    ring

/-- The concrete curvature representative has the same curvature. -/
theorem curvature_concrete_normal_form
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent) :
    curvature (concreteCurvatureNormalForm jet) = curvature jet := by
  calc
    curvature (concreteCurvatureNormalForm jet) =
        curvature (applyGauge (concreteNormalizingGauge jet) jet) := by
      rw [concrete_normalizing_gauge_reaches_curvature_form]
    _ = curvature jet := curvature_applyGauge _ _

/-- Concrete gauge-equivalence relation. -/
def ConcreteGaugeEquivalent
    {Tangent : Type u}
    (first second : ConcreteConnectionOneJet Tangent) : Prop :=
  ∃ gauge : ConcreteGaugeTwoJet Tangent,
    applyGauge gauge first = second

/-- If two concrete connection jets have the same curvature, their derivative
difference is symmetric and therefore is the Hessian of a formal gauge two-jet. -/
def gaugeBetweenEqualCurvatures
    {Tangent : Type u}
    (first second : ConcreteConnectionOneJet Tangent)
    (hCurvature : curvature first = curvature second) :
    ConcreteGaugeTwoJet Tangent where
  gradient x := -first.value x + second.value x
  hessian x y := -first.derivative x y + second.derivative x y
  hessian_symmetric := by
    intro x y
    have hAt := congrFun (congrFun hCurvature x) y
    simp only [curvature] at hAt
    linarith

/-- The gauge constructed from equal curvatures maps the first jet to the second. -/
theorem gaugeBetweenEqualCurvatures_maps
    {Tangent : Type u}
    (first second : ConcreteConnectionOneJet Tangent)
    (hCurvature : curvature first = curvature second) :
    applyGauge (gaugeBetweenEqualCurvatures first second hCurvature) first =
      second := by
  apply ConcreteConnectionOneJet.ext
  · funext x
    simp only [applyGauge, gaugeBetweenEqualCurvatures]
    ring
  · funext x y
    simp only [applyGauge, gaugeBetweenEqualCurvatures]
    ring

/-- Exact concrete one-jet quotient theorem: abelian connection first jets are
gauge equivalent exactly when their curvature two-forms agree. -/
theorem concrete_gauge_equivalent_iff_curvature_eq
    {Tangent : Type u}
    (first second : ConcreteConnectionOneJet Tangent) :
    ConcreteGaugeEquivalent first second ↔
      curvature first = curvature second := by
  constructor
  · rintro ⟨gauge, hGauge⟩
    calc
      curvature first = curvature (applyGauge gauge first) :=
        (curvature_applyGauge gauge first).symm
      _ = curvature second := congrArg curvature hGauge
  · intro hCurvature
    exact ⟨gaugeBetweenEqualCurvatures first second hCurvature,
      gaugeBetweenEqualCurvatures_maps first second hCurvature⟩

/-- Decomposition into the three components used by the abstract normal-form
gate. -/
noncomputable def decomposeConnectionJet
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent) :
    ConnectionOneJet
      (Tangent → ℝ)
      (Tangent → Tangent → ℝ)
      (Tangent → Tangent → ℝ) where
  value := jet.value
  symmetricDerivative := symmetricPart jet.derivative
  curvature := curvature jet

/-- Forgetful map from a genuine scalar gauge two-jet to the additive abstract
gauge correction. -/
def abstractGaugeOfConcrete
    {Tangent : Type u}
    (gauge : ConcreteGaugeTwoJet Tangent) :
    GaugeTwoJet (Tangent → ℝ) (Tangent → Tangent → ℝ) where
  gradient := gauge.gradient
  hessian := gauge.hessian

/-- The concrete gauge formula is exactly compatible with the decomposed
abstract action. In particular, the symmetric/alternating split used in the
previous gate is now derived from the concrete derivative formula. -/
theorem decomposition_commutes_with_gauge
    {Tangent : Type u}
    (gauge : ConcreteGaugeTwoJet Tangent)
    (jet : ConcreteConnectionOneJet Tangent) :
    decomposeConnectionJet (applyGauge gauge jet) =
      gaugeChange (abstractGaugeOfConcrete gauge)
        (decomposeConnectionJet jet) := by
  apply ConnectionOneJet.ext
  · rfl
  · funext x y
    have hSymmetric := gauge.hessian_symmetric x y
    change
      ((jet.derivative x y + gauge.hessian x y) +
          (jet.derivative y x + gauge.hessian y x)) / 2 =
        (jet.derivative x y + jet.derivative y x) / 2 +
          gauge.hessian x y
    rw [hSymmetric]
    ring
  · exact curvature_applyGauge gauge jet

/-- The concrete normalizing gauge maps under decomposition to the abstract
normalizing gauge. -/
theorem abstractGaugeOfConcrete_normalizing
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent) :
    abstractGaugeOfConcrete (concreteNormalizingGauge jet) =
      P0EFTJanusAbelianConnectionJetNormalForm.normalizingGauge
        (decomposeConnectionJet jet) := by
  apply GaugeTwoJet.ext <;> rfl

/-- The concrete normalization theorem refines the earlier decomposed theorem. -/
theorem decomposed_concrete_normalization_is_abstract_curvature_form
    {Tangent : Type u}
    (jet : ConcreteConnectionOneJet Tangent) :
    decomposeConnectionJet
        (applyGauge (concreteNormalizingGauge jet) jet) =
      P0EFTJanusAbelianConnectionJetNormalForm.curvatureNormalForm
        (decomposeConnectionJet jet) := by
  calc
    decomposeConnectionJet
        (applyGauge (concreteNormalizingGauge jet) jet) =
      gaugeChange
        (abstractGaugeOfConcrete (concreteNormalizingGauge jet))
        (decomposeConnectionJet jet) :=
      decomposition_commutes_with_gauge _ _
    _ = gaugeChange
        (P0EFTJanusAbelianConnectionJetNormalForm.normalizingGauge
          (decomposeConnectionJet jet))
        (decomposeConnectionJet jet) := by
      rw [abstractGaugeOfConcrete_normalizing]
    _ = P0EFTJanusAbelianConnectionJetNormalForm.curvatureNormalForm
        (decomposeConnectionJet jet) :=
      chosen_gauge_reaches_curvature_normal_form _

section ResidualTangentFrame

variable {Frame : Type v}
variable {Tangent : Type u}
variable [Group Frame]
variable [MulAction Frame Tangent]

/-- Pullback of a connection one-jet by a residual tangent-frame transformation. -/
def pullbackConnectionJet
    (frame : Frame)
    (jet : ConcreteConnectionOneJet Tangent) :
    ConcreteConnectionOneJet Tangent where
  value x := jet.value (frame⁻¹ • x)
  derivative x y := jet.derivative (frame⁻¹ • x) (frame⁻¹ • y)

/-- Contravariant residual frame action on a two-form. -/
def pullbackTwoForm
    (frame : Frame)
    (form : Tangent → Tangent → ℝ) :
    Tangent → Tangent → ℝ :=
  fun x y => form (frame⁻¹ • x) (frame⁻¹ • y)

@[simp]
theorem pullbackTwoForm_one
    (form : Tangent → Tangent → ℝ) :
    pullbackTwoForm (1 : Frame) form = form := by
  funext x y
  simp [pullbackTwoForm]

@[simp]
theorem pullbackTwoForm_mul
    (first second : Frame)
    (form : Tangent → Tangent → ℝ) :
    pullbackTwoForm (first * second) form =
      pullbackTwoForm first (pullbackTwoForm second form) := by
  funext x y
  simp [pullbackTwoForm, mul_smul]

/-- Curvature transforms as a residual two-form. -/
theorem curvature_pullbackConnectionJet
    (frame : Frame)
    (jet : ConcreteConnectionOneJet Tangent) :
    curvature (pullbackConnectionJet frame jet) =
      pullbackTwoForm frame (curvature jet) := by
  funext x y
  rfl

end ResidualTangentFrame

/-- Boundary between the concrete local gauge-jet theorem and the full SpinC
connection reduction. -/
structure ConcreteAbelianConnectionGeometricStatus where
  concreteGaugeActionDerived : Prop
  symmetricAlternatingDecompositionProved : Prop
  curvatureGaugeInvarianceProved : Prop
  concreteGaugeOrbitsClassifiedByCurvature : Prop
  compatibilityWithAbstractQuotientProved : Prop
  residualFrameActionOnCurvatureConstructed : Prop
  localU1TrivializationsConstructed : Prop
  smoothJetBundleAndGaugeGroupConstructed : Prop
  spinCDeterminantConnectionInserted : Prop
  globalHolonomyDataSeparated : Prop

/-- Closure of the geometric abelian/SpinC connection one-jet theorem. -/
def concreteAbelianConnectionGeometricClosed
    (s : ConcreteAbelianConnectionGeometricStatus) : Prop :=
  s.concreteGaugeActionDerived /\
  s.symmetricAlternatingDecompositionProved /\
  s.curvatureGaugeInvarianceProved /\
  s.concreteGaugeOrbitsClassifiedByCurvature /\
  s.compatibilityWithAbstractQuotientProved /\
  s.residualFrameActionOnCurvatureConstructed /\
  s.localU1TrivializationsConstructed /\
  s.smoothJetBundleAndGaugeGroupConstructed /\
  s.spinCDeterminantConnectionInserted /\
  s.globalHolonomyDataSeparated

/-- The concrete Taylor-coefficient theorem does not by itself construct the
local trivializations of the actual determinant line bundle. -/
theorem missing_local_trivializations_blocks_spinC_connection_reduction
    (s : ConcreteAbelianConnectionGeometricStatus)
    (hMissing : Not s.localU1TrivializationsConstructed) :
    Not (concreteAbelianConnectionGeometricClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end P0EFTJanusConcreteAbelianConnectionJet
end JanusFormal
