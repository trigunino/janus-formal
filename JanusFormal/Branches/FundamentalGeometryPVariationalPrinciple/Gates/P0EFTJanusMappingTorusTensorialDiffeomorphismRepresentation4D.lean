import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGhostCEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationModuleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D

/-!
# Tensorial diffeomorphism representations on the D8 quotient

The scalar pullback action was already functorial.  This gate proves the same
finite composition law for the genuine intrinsic gauge one-forms and
covariant two-tensors.  These are the finite geometric representation laws
whose infinitesimal bracket identity is required by nonlinear BRST.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

@[simp]
theorem pullbackGaugePotential_zero
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod) :
    pullbackGaugePotential period hPeriod diffeomorphism 0 = 0 := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  rfl

theorem pullbackGaugePotential_smul
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (coefficient : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    pullbackGaugePotential period hPeriod diffeomorphism
        (coefficient • potential) =
      coefficient •
        pullbackGaugePotential period hPeriod diffeomorphism potential := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  rfl

/-- Pullback of intrinsic one-forms is a contravariant group action. -/
theorem pullbackGaugePotential_trans
    (first second : SpacetimeDiffeomorphism period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    pullbackGaugePotential period hPeriod first
        (pullbackGaugePotential period hPeriod second potential) =
      pullbackGaugePotential period hPeriod (first.trans second) potential := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  change
    potential.toFun component (second (first point))
        (mfderiv coverModelWithCorners coverModelWithCorners second
          (first point)
          (mfderiv coverModelWithCorners coverModelWithCorners first
            point tangent)) =
      potential.toFun component ((first.trans second) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (first.trans second) point tangent)
  rw [show (first.trans second : EffectiveQuotient period hPeriod →
      EffectiveQuotient period hPeriod) = second ∘ first by rfl]
  rw [mfderiv_comp point
    (second.contMDiff.mdifferentiableAt (x := first point) (by simp))
    (first.contMDiff.mdifferentiableAt (x := point) (by simp))]
  rfl

/-- Pointwise pullback of a covariant two-tensor is functorial. -/
theorem pullbackTensorValue_trans
    (first second : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    pullbackTensorValue period hPeriod first
        (fun current =>
          pullbackTensorValue period hPeriod second tensor current) point =
      pullbackTensorValue period hPeriod (first.trans second) tensor point := by
  apply ContinuousLinearMap.ext
  intro firstVector
  apply ContinuousLinearMap.ext
  intro secondVector
  simp only [pullbackTensorValue_apply]
  rw [show (first.trans second : EffectiveQuotient period hPeriod →
      EffectiveQuotient period hPeriod) = second ∘ first by rfl]
  rw [mfderiv_comp point
    (second.contMDiff.mdifferentiableAt (x := first point) (by simp))
    (first.contMDiff.mdifferentiableAt (x := point) (by simp))]
  rfl

/-- The two concrete tensorial pullbacks satisfy the finite representation
laws needed before differentiating to Lie derivatives. -/
structure TensorialDiffeomorphismRepresentationCertificate4D : Prop where
  gaugeTrans :
    ∀ first second potential,
      pullbackGaugePotential period hPeriod first
          (pullbackGaugePotential period hPeriod second potential) =
        pullbackGaugePotential period hPeriod (first.trans second) potential
  tensorTrans :
    ∀ first second tensor point,
      pullbackTensorValue period hPeriod first
          (fun current =>
            pullbackTensorValue period hPeriod second tensor current) point =
        pullbackTensorValue period hPeriod (first.trans second) tensor point

def tensorialDiffeomorphismRepresentationCertificate4D :
    TensorialDiffeomorphismRepresentationCertificate4D period hPeriod where
  gaugeTrans := pullbackGaugePotential_trans period hPeriod
  tensorTrans := pullbackTensorValue_trans period hPeriod

/-! ## Infinitesimal representation contract -/

private abbrev Ghost :=
  CInfinityDiffeomorphismGhost period hPeriod

/-- A genuine linear Lie action of smooth D8 ghosts on a geometric field
module. -/
structure SmoothGhostLieRepresentation
    (Field : Type*) [AddCommGroup Field] [Module Real Field] where
  action : Ghost period hPeriod →ₗ[Real] Field →ₗ[Real] Field
  bracket_action :
    ∀ first second field,
      action (smoothGhostLieBracket period hPeriod first second) field =
        action first (action second field) -
          action second (action first field)

/-- The precise pairwise obstruction occurring in the nonlinear BRST
square for any geometric representation. -/
def lieRepresentationBRSTPairObstruction
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field)
    (first second : Ghost period hPeriod)
    (field : Field) : Field :=
  representation.action first (representation.action second field) -
    representation.action second (representation.action first field) -
      representation.action
        (smoothGhostLieBracket period hPeriod first second) field

@[simp]
theorem lieRepresentationBRSTPairObstruction_zero
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field)
    (first second : Ghost period hPeriod)
    (field : Field) :
    lieRepresentationBRSTPairObstruction period hPeriod
      representation first second field = 0 := by
  rw [lieRepresentationBRSTPairObstruction,
    representation.bracket_action]
  abel

/-- The already proved scalar Lie derivative is the first unconditional
geometric instance of the common representation interface. -/
def smoothScalarGhostLieRepresentation :
    SmoothGhostLieRepresentation period hPeriod
      (CInfinityScalarField period hPeriod) where
  action :=
    { toFun := fun ghost =>
        { toFun := cInfinityScalarLieDerivative period hPeriod ghost
          map_add' :=
            cInfinityScalarLieDerivative_addScalar period hPeriod ghost
          map_smul' := fun coefficient scalar =>
            cInfinityScalarLieDerivative_smulScalar
              period hPeriod ghost coefficient scalar }
      map_add' := fun first second => by
        apply LinearMap.ext
        intro scalar
        exact cInfinityScalarLieDerivative_addGhost
          period hPeriod first second scalar
      map_smul' := fun coefficient ghost => by
        apply LinearMap.ext
        intro scalar
        exact cInfinityScalarLieDerivative_smulGhost
          period hPeriod coefficient ghost scalar }
  bracket_action :=
    cInfinityScalarLieDerivative_bracket period hPeriod

/-! ## Maxwell Cartan reduction -/

/-- Smooth scalar contraction of one Maxwell component with a smooth ghost. -/
def gaugePotentialGhostContraction
    (ghost : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    CInfinityScalarField period hPeriod :=
  ⟨fun point => potential.toFun component point (ghost point),
    (potential.contMDiff_eval component).comp ghost.contMDiff⟩

@[simp]
theorem gaugePotentialGhostContraction_apply
    (ghost : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    gaugePotentialGhostContraction period hPeriod ghost potential component
        point =
      potential.toFun component point (ghost point) :=
  rfl

theorem gaugePotentialGhostContraction_addGhost
    (first second : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    gaugePotentialGhostContraction period hPeriod (first + second) potential =
      gaugePotentialGhostContraction period hPeriod first potential +
        gaugePotentialGhostContraction period hPeriod second potential := by
  funext component
  apply ContMDiffMap.ext
  intro point
  change potential.toFun component point (first point + second point) = _
  exact map_add (potential.toFun component point) (first point) (second point)

theorem gaugePotentialGhostContraction_smulGhost
    (coefficient : Real)
    (ghost : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    gaugePotentialGhostContraction period hPeriod
        (coefficient • ghost) potential =
      coefficient •
        gaugePotentialGhostContraction period hPeriod ghost potential := by
  funext component
  apply ContMDiffMap.ext
  intro point
  change potential.toFun component point (coefficient • ghost point) = _
  exact map_smul (potential.toFun component point) coefficient (ghost point)

theorem gaugePotentialGhostContraction_addPotential
    (ghost : Ghost period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    gaugePotentialGhostContraction period hPeriod ghost (first + second) =
      gaugePotentialGhostContraction period hPeriod ghost first +
        gaugePotentialGhostContraction period hPeriod ghost second := by
  funext component
  apply ContMDiffMap.ext
  intro point
  rfl

theorem gaugePotentialGhostContraction_smulPotential
    (ghost : Ghost period hPeriod)
    (coefficient : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    gaugePotentialGhostContraction period hPeriod ghost
        (coefficient • potential) =
      coefficient •
        gaugePotentialGhostContraction period hPeriod ghost potential := by
  funext component
  apply ContMDiffMap.ext
  intro point
  rfl

/-- Contraction is bilinear in the smooth ghost and Maxwell potential. -/
def gaugePotentialGhostContractionBilinear :
    Ghost period hPeriod →ₗ[Real]
      SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
        (Fin 2 → CInfinityScalarField period hPeriod) where
  toFun ghost :=
    { toFun := gaugePotentialGhostContraction period hPeriod ghost
      map_add' :=
        gaugePotentialGhostContraction_addPotential period hPeriod ghost
      map_smul' :=
        gaugePotentialGhostContraction_smulPotential period hPeriod ghost }
  map_add' := fun first second => by
    apply LinearMap.ext
    intro potential
    exact gaugePotentialGhostContraction_addGhost
      period hPeriod first second potential
  map_smul' := fun coefficient ghost => by
    apply LinearMap.ext
    intro potential
    exact gaugePotentialGhostContraction_smulGhost
      period hPeriod coefficient ghost potential

theorem gaugePotentialGhostContraction_subPotential
    (ghost : Ghost period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    gaugePotentialGhostContraction period hPeriod ghost (first - second) =
      gaugePotentialGhostContraction period hPeriod ghost first -
        gaugePotentialGhostContraction period hPeriod ghost second :=
  (gaugePotentialGhostContractionBilinear period hPeriod ghost).map_sub
    first second

/-- Smooth ghost contractions separate intrinsic Maxwell one-forms. -/
theorem gaugePotential_eq_of_ghostContraction_eq
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (hEqual : ∀ ghost,
      gaugePotentialGhostContraction period hPeriod ghost first =
        gaugePotentialGhostContraction period hPeriod ghost second) :
    first = second := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  have hLinear :
      first.toFun component point = second.toFun component point := by
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.ext_on
      ((finiteSmoothTangentFrame period hPeriod).spansAt point)
    intro vector hVector
    rcases hVector with ⟨index, rfl⟩
    have hComponent := congrFun
      (hEqual (finiteGeneratorCInfinityGhost period hPeriod index)) component
    exact DFunLike.congr_fun hComponent point
  exact DFunLike.congr_fun hLinear tangent

/-- A bilinear Maxwell action satisfying the intrinsic Cartan evaluation
formula. The formula alone forces the Lie bracket law. -/
structure GaugePotentialCartanActionData where
  action :
    Ghost period hPeriod →ₗ[Real]
      SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
        SmoothAbelianGaugePotential period hPeriod
  cartan :
    ∀ first potential second component,
      gaugePotentialGhostContraction period hPeriod second
          (action first potential) component =
        cInfinityScalarLieDerivative period hPeriod first
            (gaugePotentialGhostContraction period hPeriod second potential
              component) -
          gaugePotentialGhostContraction period hPeriod
            (smoothGhostLieBracket period hPeriod first second)
            potential component

theorem GaugePotentialCartanActionData.bracket_action
    (data : GaugePotentialCartanActionData period hPeriod)
    (first second : Ghost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    data.action (smoothGhostLieBracket period hPeriod first second) potential =
      data.action first (data.action second potential) -
        data.action second (data.action first potential) := by
  apply gaugePotential_eq_of_ghostContraction_eq period hPeriod
  intro third
  funext component
  rw [data.cartan]
  rw [gaugePotentialGhostContraction_subPotential]
  simp only [Pi.sub_apply]
  rw [data.cartan first (data.action second potential) third component,
    data.cartan second (data.action first potential) third component]
  rw [data.cartan second potential third component,
    data.cartan second potential
      (smoothGhostLieBracket period hPeriod first third) component,
    data.cartan first potential third component,
    data.cartan first potential
      (smoothGhostLieBracket period hPeriod second third) component]
  have hLieSub :
      ∀ (ghost : Ghost period hPeriod)
          (left right : CInfinityScalarField period hPeriod),
        cInfinityScalarLieDerivative period hPeriod ghost (left - right) =
          cInfinityScalarLieDerivative period hPeriod ghost left -
            cInfinityScalarLieDerivative period hPeriod ghost right := by
    intro ghost left right
    change (cInfinityScalarGhostAction period hPeriod ghost)
        (left - right) = _
    exact (cInfinityScalarGhostAction period hPeriod ghost).map_sub left right
  rw [hLieSub, hLieSub]
  rw [cInfinityScalarLieDerivative_bracket period hPeriod first second
    (gaugePotentialGhostContraction period hPeriod third potential component)]
  rw [smoothGhostLieBracket_jacobi period hPeriod first second third]
  rw [gaugePotentialGhostContraction_addGhost]
  simp only [Pi.add_apply]
  abel

/-- Cartan evaluation upgrades a bilinear Maxwell action to the common smooth
ghost Lie-representation interface. -/
def GaugePotentialCartanActionData.toSmoothGhostLieRepresentation
    (data : GaugePotentialCartanActionData period hPeriod) :
    SmoothGhostLieRepresentation period hPeriod
      (SmoothAbelianGaugePotential period hPeriod) where
  action := data.action
  bracket_action := data.bracket_action period hPeriod

/-! ## Symmetric-tensor Cartan reduction -/

private def tensorContractionBackground :
    EffectiveD8Background where
  period := period
  period_ne_zero := hPeriod

/-- The existing smooth tensor/vector contraction, specialized to two
smooth diffeomorphism ghosts and promoted to the common `C∞` scalar type. -/
def symmetricTensorGhostContraction
    (first second : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    CInfinityScalarField period hPeriod :=
  analyticScalarToCInfinity period hPeriod
    (effectiveD8SmoothTensorVectorContraction
      (tensorContractionBackground period hPeriod) tensor first second)

@[simp]
theorem symmetricTensorGhostContraction_apply
    (first second : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    symmetricTensorGhostContraction period hPeriod first second tensor point =
      tensor.tensor point (first point) (second point) :=
  rfl

theorem symmetricTensorGhostContraction_addTensor
    (first second : Ghost period hPeriod)
    (left right : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    symmetricTensorGhostContraction period hPeriod first second
        (left + right) =
      symmetricTensorGhostContraction period hPeriod first second left +
        symmetricTensorGhostContraction period hPeriod first second right := by
  apply ContMDiffMap.ext
  intro point
  rfl

theorem symmetricTensorGhostContraction_smulTensor
    (first second : Ghost period hPeriod)
    (coefficient : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    symmetricTensorGhostContraction period hPeriod first second
        (coefficient • tensor) =
      coefficient •
        symmetricTensorGhostContraction period hPeriod first second tensor := by
  apply ContMDiffMap.ext
  intro point
  rfl

theorem symmetricTensorGhostContraction_subTensor
    (first second : Ghost period hPeriod)
    (left right : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    symmetricTensorGhostContraction period hPeriod first second
        (left - right) =
      symmetricTensorGhostContraction period hPeriod first second left -
        symmetricTensorGhostContraction period hPeriod first second right := by
  apply ContMDiffMap.ext
  intro point
  rfl

theorem symmetricTensorGhostContraction_addFirstGhost
    (first second third : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    symmetricTensorGhostContraction period hPeriod
        (first + second) third tensor =
      symmetricTensorGhostContraction period hPeriod first third tensor +
        symmetricTensorGhostContraction period hPeriod second third tensor := by
  apply ContMDiffMap.ext
  intro point
  change tensor.tensor point (first point + second point) (third point) = _
  rw [map_add]
  rfl

theorem symmetricTensorGhostContraction_smulFirstGhost
    (coefficient : Real)
    (first second : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    symmetricTensorGhostContraction period hPeriod
        (coefficient • first) second tensor =
      coefficient •
        symmetricTensorGhostContraction period hPeriod first second tensor := by
  apply ContMDiffMap.ext
  intro point
  change tensor.tensor point (coefficient • first point) (second point) = _
  rw [map_smul]
  rfl

theorem symmetricTensorGhostContraction_addSecondGhost
    (first second third : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    symmetricTensorGhostContraction period hPeriod
        first (second + third) tensor =
      symmetricTensorGhostContraction period hPeriod first second tensor +
        symmetricTensorGhostContraction period hPeriod first third tensor := by
  apply ContMDiffMap.ext
  intro point
  change tensor.tensor point (first point) (second point + third point) = _
  rw [map_add]
  rfl

theorem symmetricTensorGhostContraction_smulSecondGhost
    (coefficient : Real)
    (first second : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    symmetricTensorGhostContraction period hPeriod
        first (coefficient • second) tensor =
      coefficient •
        symmetricTensorGhostContraction period hPeriod first second tensor := by
  apply ContMDiffMap.ext
  intro point
  change tensor.tensor point (first point) (coefficient • second point) = _
  rw [map_smul]
  rfl

/-- Evaluation on smooth ghosts separates intrinsic symmetric two-tensors,
using the already constructed finite smooth spanning family. -/
theorem symmetricTensor_eq_of_ghostContraction_eq
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hEqual : ∀ left right,
      symmetricTensorGhostContraction period hPeriod left right first =
        symmetricTensorGhostContraction period hPeriod left right second) :
    first = second := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  have hOuter :
      (first.tensor point).toLinearMap =
        (second.tensor point).toLinearMap := by
    apply LinearMap.ext_on_range
      ((finiteSmoothTangentFrame period hPeriod).spansAt point)
    intro leftIndex
    have hInner :
        (first.tensor point
            ((finiteSmoothTangentFrame period hPeriod).vectorAt
              point leftIndex)).toLinearMap =
          (second.tensor point
            ((finiteSmoothTangentFrame period hPeriod).vectorAt
              point leftIndex)).toLinearMap := by
      apply LinearMap.ext_on_range
        ((finiteSmoothTangentFrame period hPeriod).spansAt point)
      intro rightIndex
      have hReading := DFunLike.congr_fun
        (hEqual
          (finiteGeneratorCInfinityGhost period hPeriod leftIndex)
          (finiteGeneratorCInfinityGhost period hPeriod rightIndex)) point
      exact hReading
    apply ContinuousLinearMap.ext
    intro tangent
    exact LinearMap.congr_fun hInner tangent
  apply ContinuousLinearMap.ext
  intro tangent
  exact LinearMap.congr_fun hOuter tangent

/-- A bilinear symmetric-tensor action satisfying the intrinsic Cartan
evaluation formula. This formula forces the Lie bracket law. -/
structure SymmetricTensorCartanActionData where
  action :
    Ghost period hPeriod →ₗ[Real]
      SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
        SmoothSymmetricCovariantTwoTensor period hPeriod
  cartan :
    ∀ acting tensor first second,
      symmetricTensorGhostContraction period hPeriod first second
          (action acting tensor) =
        cInfinityScalarLieDerivative period hPeriod acting
            (symmetricTensorGhostContraction period hPeriod
              first second tensor) -
          symmetricTensorGhostContraction period hPeriod
            (smoothGhostLieBracket period hPeriod acting first)
            second tensor -
          symmetricTensorGhostContraction period hPeriod first
            (smoothGhostLieBracket period hPeriod acting second) tensor

theorem SymmetricTensorCartanActionData.bracket_action
    (data : SymmetricTensorCartanActionData period hPeriod)
    (first second : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    data.action (smoothGhostLieBracket period hPeriod first second) tensor =
      data.action first (data.action second tensor) -
        data.action second (data.action first tensor) := by
  apply symmetricTensor_eq_of_ghostContraction_eq period hPeriod
  intro third fourth
  rw [data.cartan]
  rw [symmetricTensorGhostContraction_subTensor]
  rw [data.cartan first (data.action second tensor) third fourth,
    data.cartan second (data.action first tensor) third fourth]
  rw [data.cartan second tensor third fourth,
    data.cartan second tensor
      (smoothGhostLieBracket period hPeriod first third) fourth,
    data.cartan second tensor third
      (smoothGhostLieBracket period hPeriod first fourth),
    data.cartan first tensor third fourth,
    data.cartan first tensor
      (smoothGhostLieBracket period hPeriod second third) fourth,
    data.cartan first tensor third
      (smoothGhostLieBracket period hPeriod second fourth)]
  have hLieSub :
      ∀ (ghost : Ghost period hPeriod)
          (left right : CInfinityScalarField period hPeriod),
        cInfinityScalarLieDerivative period hPeriod ghost (left - right) =
          cInfinityScalarLieDerivative period hPeriod ghost left -
            cInfinityScalarLieDerivative period hPeriod ghost right := by
    intro ghost left right
    change (cInfinityScalarGhostAction period hPeriod ghost)
        (left - right) = _
    exact (cInfinityScalarGhostAction period hPeriod ghost).map_sub left right
  simp only [hLieSub]
  rw [cInfinityScalarLieDerivative_bracket period hPeriod first second
    (symmetricTensorGhostContraction period hPeriod third fourth tensor)]
  rw [smoothGhostLieBracket_jacobi period hPeriod first second third,
    smoothGhostLieBracket_jacobi period hPeriod first second fourth]
  rw [symmetricTensorGhostContraction_addFirstGhost,
    symmetricTensorGhostContraction_addSecondGhost]
  abel

/-- Cartan evaluation upgrades a bilinear symmetric-tensor action to the
common smooth ghost Lie-representation interface. -/
def SymmetricTensorCartanActionData.toSmoothGhostLieRepresentation
    (data : SymmetricTensorCartanActionData period hPeriod) :
    SmoothGhostLieRepresentation period hPeriod
      (SmoothSymmetricCovariantTwoTensor period hPeriod) where
  action := data.action
  bracket_action := data.bracket_action period hPeriod

/-- Cartan data for both intrinsic tensorial sectors. -/
structure TensorialCartanActionData where
  gauge : GaugePotentialCartanActionData period hPeriod
  metric : SymmetricTensorCartanActionData period hPeriod

/-- Abstract package for globally smooth, ghost-linear infinitesimal actions
on the intrinsic Maxwell one-form and symmetric metric tensor.  The canonical
geometric instance is supplied downstream; bracket laws follow from the
Cartan contracts above. -/
structure TensorialInfinitesimalLieActionData where
  gauge :
    SmoothGhostLieRepresentation period hPeriod
      (SmoothAbelianGaugePotential period hPeriod)
  metric :
    SmoothGhostLieRepresentation period hPeriod
      (SmoothSymmetricCovariantTwoTensor period hPeriod)

/-- Both tensorial bracket laws are automatic once the two Cartan formulas
are realized by globally smooth actions. -/
def TensorialCartanActionData.toTensorialInfinitesimalLieActionData
    (data : TensorialCartanActionData period hPeriod) :
    TensorialInfinitesimalLieActionData period hPeriod where
  gauge := data.gauge.toSmoothGhostLieRepresentation period hPeriod
  metric := data.metric.toSmoothGhostLieRepresentation period hPeriod

theorem scalar_geometric_nonlinear_brst_pair_square_zero
    (first second : Ghost period hPeriod)
    (scalar : CInfinityScalarField period hPeriod) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (smoothScalarGhostLieRepresentation period hPeriod)
      first second scalar = 0 :=
  lieRepresentationBRSTPairObstruction_zero period hPeriod
    (smoothScalarGhostLieRepresentation period hPeriod)
    first second scalar

end
end P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
end JanusFormal
