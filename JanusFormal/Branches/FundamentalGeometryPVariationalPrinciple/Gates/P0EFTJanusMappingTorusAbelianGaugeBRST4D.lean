import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

/-!
# Intrinsic abelian gauge connection and BRST differential on the D8 quotient

The existing `GhostFiber = R^2` is used as the Lie algebra of a global
`U(1)^2` coefficient sector.  A gauge potential is an intrinsic smooth
Lie-algebra-valued one-form on the actual effective mapping torus, not four
coefficients in an assumed global frame.  Exact gauge transformations,
diffeomorphism pullback and their naturality are constructed on those same
global objects.  The resulting linear abelian BRST differential is genuinely
nilpotent.  Nonabelian brackets and diffeomorphism BRST remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAbelianGaugeBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The existing two-component ghost fiber, interpreted as the Lie algebra of
the concrete abelian `U(1)^2` gauge sector. -/
abbrev GaugeLieAlgebra := GhostFiber

/-- An intrinsic smooth `R^2`-valued one-form on the actual D8 quotient.
Smoothness is imposed on evaluation over the genuine tangent bundle. -/
structure SmoothAbelianGaugePotential where
  toFun : Fin 2 → ∀ point : EffectiveQuotient period hPeriod,
    TangentSpace coverModelWithCorners point →L[Real] Real
  contMDiff_eval : ∀ component : Fin 2,
    ContMDiff coverModelWithCorners.tangent
      (modelWithCornersSelf Real Real) ∞
      (fun vector : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) =>
        toFun component vector.1 vector.2)

@[ext]
theorem SmoothAbelianGaugePotential.ext
    {first second : SmoothAbelianGaugePotential period hPeriod}
    (hEqual : ∀ component point tangent,
      first.toFun component point tangent =
        second.toFun component point tangent) :
    first = second := by
  cases first with
  | mk firstFun firstSmooth =>
    cases second with
    | mk secondFun secondSmooth =>
      have hFun : firstFun = secondFun := by
        funext component
        funext point
        apply ContinuousLinearMap.ext
        intro tangent
        exact hEqual component point tangent
      subst secondFun
      rfl

instance : Zero (SmoothAbelianGaugePotential period hPeriod) where
  zero :=
    { toFun := fun _ _ => 0
      contMDiff_eval := fun component => by
        simpa using
          (contMDiff_const :
            ContMDiff coverModelWithCorners.tangent
              (modelWithCornersSelf Real Real) ∞
              (fun _ : TangentBundle coverModelWithCorners
                (EffectiveQuotient period hPeriod) =>
                  (0 : Real))) }

instance : Add (SmoothAbelianGaugePotential period hPeriod) where
  add first second :=
    { toFun := fun component point =>
        first.toFun component point + second.toFun component point
      contMDiff_eval := fun component => by
        exact (first.contMDiff_eval component).add
          (second.contMDiff_eval component) }

instance : Neg (SmoothAbelianGaugePotential period hPeriod) where
  neg potential :=
    { toFun := fun component point => -potential.toFun component point
      contMDiff_eval := fun component => by
        exact (potential.contMDiff_eval component).neg }

instance : AddCommGroup (SmoothAbelianGaugePotential period hPeriod) where
  add_assoc := by
    intros
    apply SmoothAbelianGaugePotential.ext
    intros component point tangent
    exact add_assoc _ _ _
  zero_add := by
    intros
    apply SmoothAbelianGaugePotential.ext
    intros component point tangent
    exact zero_add _
  add_zero := by
    intros
    apply SmoothAbelianGaugePotential.ext
    intros component point tangent
    exact add_zero _
  nsmul := nsmulRec
  add_comm := by
    intros
    apply SmoothAbelianGaugePotential.ext
    intros component point tangent
    exact add_comm _ _
  neg_add_cancel := by
    intros
    apply SmoothAbelianGaugePotential.ext
    intros component point tangent
    exact neg_add_cancel _
  zsmul := zsmulRec

/-- A scalar component of one of the existing Euclidean two-component ghost
fields remains a smooth field on the same quotient. -/
def ghostComponent
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) : SmoothQuotientField period hPeriod Real where
  toFun := fun point => EuclideanSpace.proj component (ghost point)
  contMDiff_toFun :=
    (EuclideanSpace.proj component).contDiff.contMDiff.comp
      ghost.contMDiff_toFun

@[simp]
theorem ghostComponent_zero (component : Fin 2) :
    ghostComponent period hPeriod
        (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) component = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

theorem ghostComponent_add
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    ghostComponent period hPeriod (first + second) component =
      ghostComponent period hPeriod first component +
        ghostComponent period hPeriod second component := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact (EuclideanSpace.proj component).map_add _ _

theorem ghostComponent_neg
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    ghostComponent period hPeriod (-ghost) component =
      -ghostComponent period hPeriod ghost component := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

/-- The exterior derivative of one of the already constructed smooth global
ghost fields, packaged as an intrinsic smooth gauge one-form. -/
def exactGaugePotential
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    SmoothAbelianGaugePotential period hPeriod where
  toFun := fun component => mvfderiv coverModelWithCorners
    (ghostComponent period hPeriod ghost component).toFun
  contMDiff_eval := fun component => by
    have hDerivative :=
      (contMDiff_snd_tangentBundle_modelSpace Real
        (modelWithCornersSelf Real Real) (n := ∞)).comp
        ((ghostComponent period hPeriod ghost component).contMDiff_toFun.contMDiff_tangentMap
          (m := ∞) (by simp))
    convert hDerivative using 1
    rfl

@[simp]
theorem exactGaugePotential_zero :
    exactGaugePotential period hPeriod
        (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) = 0 := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  change mvfderiv coverModelWithCorners
      (ghostComponent period hPeriod
        (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) component).toFun
      point tangent = 0
  rw [ghostComponent_zero period hPeriod component]
  change mvfderiv coverModelWithCorners
      (0 : EffectiveQuotient period hPeriod → Real) point tangent = 0
  rw [mvfderiv_zero]
  rfl

theorem exactGaugePotential_add
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    exactGaugePotential period hPeriod (first + second) =
      exactGaugePotential period hPeriod first +
        exactGaugePotential period hPeriod second := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  change mvfderiv coverModelWithCorners
      (ghostComponent period hPeriod (first + second) component).toFun
        point tangent =
    mvfderiv coverModelWithCorners
        (ghostComponent period hPeriod first component).toFun point tangent +
      mvfderiv coverModelWithCorners
        (ghostComponent period hPeriod second component).toFun point tangent
  rw [ghostComponent_add period hPeriod first second component]
  change mvfderiv coverModelWithCorners
      ((ghostComponent period hPeriod first component).toFun +
        (ghostComponent period hPeriod second component).toFun) point tangent = _
  rw [mvfderiv_add
    ((ghostComponent period hPeriod first component).contMDiff_toFun.mdifferentiableAt
      (by simp))
    ((ghostComponent period hPeriod second component).contMDiff_toFun.mdifferentiableAt
      (by simp))]
  rfl

theorem exactGaugePotential_neg
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    exactGaugePotential period hPeriod (-ghost) =
      -exactGaugePotential period hPeriod ghost := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  change mvfderiv coverModelWithCorners
      (ghostComponent period hPeriod (-ghost) component).toFun point tangent =
    -mvfderiv coverModelWithCorners
      (ghostComponent period hPeriod ghost component).toFun point tangent
  rw [ghostComponent_neg period hPeriod ghost component]
  change mvfderiv coverModelWithCorners
      (-(ghostComponent period hPeriod ghost component).toFun) point tangent = _
  rw [mvfderiv_neg]
  rfl

/-- The genuine abelian gauge transformation `A ↦ A + dλ`. -/
def gaugeTransform
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod :=
  potential + exactGaugePotential period hPeriod parameter

@[simp]
theorem gaugeTransform_zero
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    gaugeTransform period hPeriod 0 potential = potential := by
  simp [gaugeTransform]

theorem gaugeTransform_add
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    gaugeTransform period hPeriod second
        (gaugeTransform period hPeriod first potential) =
      gaugeTransform period hPeriod (first + second) potential := by
  rw [gaugeTransform, gaugeTransform, gaugeTransform,
    exactGaugePotential_add]
  abel

/-- Gauge transformations are exact equivalences; the inverse parameter is
`-λ`. -/
def gaugeTransformEquiv
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    SmoothAbelianGaugePotential period hPeriod ≃
      SmoothAbelianGaugePotential period hPeriod where
  toFun := gaugeTransform period hPeriod parameter
  invFun := gaugeTransform period hPeriod (-parameter)
  left_inv potential := by
    rw [gaugeTransform_add, add_neg_cancel, gaugeTransform_zero]
  right_inv potential := by
    rw [gaugeTransform_add, neg_add_cancel, gaugeTransform_zero]

/-- Tensorial pullback of an intrinsic gauge potential by an arbitrary smooth
diffeomorphism of the actual quotient. -/
def pullbackGaugePotential
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod where
  toFun := fun component point =>
    (potential.toFun component (diffeomorphism point)).comp
      (mfderiv coverModelWithCorners coverModelWithCorners
        diffeomorphism point)
  contMDiff_eval := fun component => by
    have hTangent :=
      diffeomorphism.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)
    exact (potential.contMDiff_eval component).comp hTangent

theorem pullbackGaugePotential_add
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    pullbackGaugePotential period hPeriod diffeomorphism (first + second) =
      pullbackGaugePotential period hPeriod diffeomorphism first +
        pullbackGaugePotential period hPeriod diffeomorphism second := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  rfl

theorem ghostComponent_pullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    ghostComponent period hPeriod
        (pullbackSmoothField period hPeriod GaugeLieAlgebra
          diffeomorphism ghost) component =
      pullbackSmoothField period hPeriod Real diffeomorphism
        (ghostComponent period hPeriod ghost component) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

/-- Exterior differentiation is natural under every global D8
diffeomorphism. -/
theorem pullback_exactGaugePotential
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    pullbackGaugePotential period hPeriod diffeomorphism
        (exactGaugePotential period hPeriod ghost) =
      exactGaugePotential period hPeriod
        (pullbackSmoothField period hPeriod GaugeLieAlgebra
          diffeomorphism ghost) := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  change mvfderiv coverModelWithCorners
      (ghostComponent period hPeriod ghost component).toFun
        (diffeomorphism point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          diffeomorphism point tangent) =
    mvfderiv coverModelWithCorners
      (ghostComponent period hPeriod
        (pullbackSmoothField period hPeriod GaugeLieAlgebra
          diffeomorphism ghost) component).toFun point tangent
  rw [ghostComponent_pullback period hPeriod diffeomorphism ghost component]
  have hOuter :=
    (ghostComponent period hPeriod ghost component).contMDiff_toFun.mdifferentiableAt
    (x := diffeomorphism point) (by simp)
  have hInner := diffeomorphism.contMDiff.mdifferentiableAt
    (x := point) (by simp)
  change mvfderiv coverModelWithCorners
      (ghostComponent period hPeriod ghost component).toFun
      (diffeomorphism point)
      (mfderiv coverModelWithCorners coverModelWithCorners
        diffeomorphism point tangent) =
    mvfderiv coverModelWithCorners
      ((ghostComponent period hPeriod ghost component).toFun ∘
        diffeomorphism) point tangent
  unfold mvfderiv
  rw [mfderiv_comp point hOuter hInner]
  rfl

/-- Gauge transformations commute with tensorial diffeomorphism pullback. -/
theorem pullback_gaugeTransform
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    pullbackGaugePotential period hPeriod diffeomorphism
        (gaugeTransform period hPeriod parameter potential) =
      gaugeTransform period hPeriod
        (pullbackSmoothField period hPeriod GaugeLieAlgebra
          diffeomorphism parameter)
        (pullbackGaugePotential period hPeriod diffeomorphism potential) := by
  rw [gaugeTransform, gaugeTransform, pullbackGaugePotential_add,
    pullback_exactGaugePotential]

/-- Global linear abelian BRST state on the same D8 quotient. -/
@[ext]
structure AbelianBRSTState where
  potential : SmoothAbelianGaugePotential period hPeriod
  ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra

def zeroBRSTState : AbelianBRSTState period hPeriod where
  potential := 0
  ghost := 0

/-- The linear abelian BRST differential `s(A,c) = (dc,0)`. -/
def brstDifferential
    (state : AbelianBRSTState period hPeriod) :
    AbelianBRSTState period hPeriod where
  potential := exactGaugePotential period hPeriod state.ghost
  ghost := 0

/-- Nilpotence is proved for the actual exterior derivative on the global D8
quotient, rather than postulated through an abstract gauge-action record. -/
theorem brstDifferential_square_zero
    (state : AbelianBRSTState period hPeriod) :
    brstDifferential period hPeriod
        (brstDifferential period hPeriod state) =
      zeroBRSTState period hPeriod := by
  apply AbelianBRSTState.ext
  · exact exactGaugePotential_zero period hPeriod
  · rfl

/-- Diffeomorphism pullback on the complete abelian BRST state. -/
def pullbackBRSTState
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (state : AbelianBRSTState period hPeriod) :
    AbelianBRSTState period hPeriod where
  potential := pullbackGaugePotential period hPeriod diffeomorphism state.potential
  ghost := pullbackSmoothField period hPeriod GaugeLieAlgebra
    diffeomorphism state.ghost

/-- The global BRST differential is diffeomorphism-covariant. -/
theorem pullback_brstDifferential
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (state : AbelianBRSTState period hPeriod) :
    pullbackBRSTState period hPeriod diffeomorphism
        (brstDifferential period hPeriod state) =
      brstDifferential period hPeriod
        (pullbackBRSTState period hPeriod diffeomorphism state) := by
  apply AbelianBRSTState.ext
  · exact pullback_exactGaugePotential period hPeriod
      diffeomorphism state.ghost
  · apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
    intro point
    rfl

/-- Each already constructed independent field package canonically supplies
the two global BRST states with zero background potentials and its existing
plus/minus ghosts. -/
def independentFieldsBRSTPair
    (fields : IndependentFields period hPeriod) :
    AbelianBRSTState period hPeriod × AbelianBRSTState period hPeriod :=
  ({ potential := 0, ghost := fields.ghosts.1 },
    { potential := 0, ghost := fields.ghosts.2 })

theorem independentFieldsBRSTPair_differential
    (fields : IndependentFields period hPeriod) :
    ((brstDifferential period hPeriod
        (independentFieldsBRSTPair period hPeriod fields).1).potential,
      (brstDifferential period hPeriod
        (independentFieldsBRSTPair period hPeriod fields).2).potential) =
    (exactGaugePotential period hPeriod fields.ghosts.1,
      exactGaugePotential period hPeriod fields.ghosts.2) :=
  rfl

end

end P0EFTJanusMappingTorusAbelianGaugeBRST4D
end JanusFormal
