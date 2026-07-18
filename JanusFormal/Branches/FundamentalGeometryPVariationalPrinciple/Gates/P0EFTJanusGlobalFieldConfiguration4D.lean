import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLLBraneAuxiliaryActionVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInducedScalarStressVariation4D

/-!
# Parametrized global four-dimensional field configuration

This gate fixes a single typed home for the independent and induced fields of
Programme P.  The spacetime, throat, matter, gauge, ghost and auxiliary
fibres, their functional spaces, and all boundary conditions remain explicit
parameters.  Thus the construction can be instantiated on the eventual
mapping-torus/throat geometry without pretending that the required global
regularity or boundary-value theorems have already been proved.

The two Lorentzian metrics and all doubled bulk fields are independent record
components.  Inverse metrics, measures, the relative root, throat geometry
and concrete LL point data occur only as outputs of a structured induction
map.  PT/exchange is defined on every slot; its involutivity is proved, as is
the covariance of a PT-compatible induction map and of the resulting
admissible configuration.

No global manifold, PDE, Sobolev/Holder regularity theorem, boundary
condition, root existence theorem or LL solution is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalFieldConfiguration4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusLLBraneAuxiliaryActionVariation

abbrev Matrix4 :=
  P0EFTJanusMetricInducedScalarStressVariation4D.Matrix4

/-- Concrete signature condition: a symmetric matrix is Lorentzian when it
is congruent to `diag(-1,1,1,1)` through an invertible frame. -/
def minkowskiMetric4 : Matrix4 :=
  Matrix.diagonal (fun index : Fin 4 => if index = 0 then (-1 : Real) else 1)

def IsLorentzianMatrix4 (metric : Matrix4) : Prop :=
  Exists fun frame : Matrix4 =>
    Exists fun inverseFrame : Matrix4 =>
      P0EFTJanusMatrixSquareRootInteractionDensity.FrameInverseWitness
          frame inverseFrame ∧
        metric = frame.transpose * minkowskiMetric4 * frame

/-- Pointwise metric data share the exact fixed-determinant-sign type already
used by the scalar stress gate, with an additional genuine Lorentz-signature
witness. -/
@[ext]
structure LorentzMetricPoint4 extends FixedSignMetric4 where
  lorentzian : IsLorentzianMatrix4 metric

abbrev LorentzMetricField4 (Spacetime : Type*) :=
  Spacetime -> LorentzMetricPoint4

/-- An algebraic involution.  It packages the transformations that later
geometric gates must construct as actual pullbacks or fibre actions. -/
structure AlgebraicInvolution (Field : Type*) where
  act : Field -> Field
  act_involutive : Function.Involutive act

namespace AlgebraicInvolution

@[simp]
theorem act_act {Field : Type*} (symmetry : AlgebraicInvolution Field)
    (field : Field) : symmetry.act (symmetry.act field) = field :=
  symmetry.act_involutive field

def identity (Field : Type*) : AlgebraicInvolution Field where
  act := id
  act_involutive := by
    intro field
    rfl

end AlgebraicInvolution

/-- Pullback on a field, including the supplied fibre PT action. -/
def transformField
    {Base Fibre : Type*}
    (basePT : AlgebraicInvolution Base)
    (fibrePT : AlgebraicInvolution Fibre)
    (field : Base -> Fibre) : Base -> Fibre :=
  fun point => fibrePT.act (field (basePT.act point))

@[simp]
theorem transformField_twice
    {Base Fibre : Type*}
    (basePT : AlgebraicInvolution Base)
    (fibrePT : AlgebraicInvolution Fibre)
    (field : Base -> Fibre) :
    transformField basePT fibrePT
        (transformField basePT fibrePT field) = field := by
  funext point
  simp [transformField]

/-- Independent variables.  There is deliberately no equation relating the
plus and minus components: PT identifies their types and exchanges them, but
does not collapse them into one variable. -/
@[ext]
structure IndependentFields
    (Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*) where
  plusMetric : LorentzMetricField4 Spacetime
  minusMetric : LorentzMetricField4 Spacetime
  plusMatter : Spacetime -> Matter
  minusMatter : Spacetime -> Matter
  plusGauge : Spacetime -> Gauge
  minusGauge : Spacetime -> Gauge
  plusGhost : Spacetime -> Ghost
  minusGhost : Spacetime -> Ghost
  plusAuxiliary : Spacetime -> Auxiliary
  minusAuxiliary : Spacetime -> Auxiliary
  throatEmbedding : Throat -> Spacetime
  llIndependent : Throat -> LLIndependent

/-- The plus metric can be replaced without changing the independent minus
metric.  This is the formal independence statement needed by variation. -/
def IndependentFields.replacePlusMetric
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*}
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent)
    (metric : LorentzMetricField4 Spacetime) :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent :=
  { fields with plusMetric := metric }

@[simp]
theorem IndependentFields.replacePlusMetric_minusMetric
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*}
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent)
    (metric : LorentzMetricField4 Spacetime) :
    (fields.replacePlusMetric metric).minusMetric = fields.minusMetric :=
  rfl

/-- Symmetric independence statement for the minus metric. -/
def IndependentFields.replaceMinusMetric
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*}
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent)
    (metric : LorentzMetricField4 Spacetime) :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent :=
  { fields with minusMetric := metric }

@[simp]
theorem IndependentFields.replaceMinusMetric_plusMetric
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*}
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent)
    (metric : LorentzMetricField4 Spacetime) :
    (fields.replaceMinusMetric metric).plusMetric = fields.plusMetric :=
  rfl

/-- PT data on every independent fibre and on the two bases. -/
structure IndependentPTData
    (Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*) where
  spacetime : AlgebraicInvolution Spacetime
  throat : AlgebraicInvolution Throat
  metric : AlgebraicInvolution LorentzMetricPoint4
  matter : AlgebraicInvolution Matter
  gauge : AlgebraicInvolution Gauge
  ghost : AlgebraicInvolution Ghost
  auxiliary : AlgebraicInvolution Auxiliary
  llIndependent : AlgebraicInvolution LLIndependent

/-- Exact PT/exchange action on all independent variables.  The common
embedding transforms on both its source and target. -/
def independentPTExchange
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*}
    (symmetry : IndependentPTData Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent)
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent where
  plusMetric := transformField symmetry.spacetime symmetry.metric fields.minusMetric
  minusMetric := transformField symmetry.spacetime symmetry.metric fields.plusMetric
  plusMatter := transformField symmetry.spacetime symmetry.matter fields.minusMatter
  minusMatter := transformField symmetry.spacetime symmetry.matter fields.plusMatter
  plusGauge := transformField symmetry.spacetime symmetry.gauge fields.minusGauge
  minusGauge := transformField symmetry.spacetime symmetry.gauge fields.plusGauge
  plusGhost := transformField symmetry.spacetime symmetry.ghost fields.minusGhost
  minusGhost := transformField symmetry.spacetime symmetry.ghost fields.plusGhost
  plusAuxiliary :=
    transformField symmetry.spacetime symmetry.auxiliary fields.minusAuxiliary
  minusAuxiliary :=
    transformField symmetry.spacetime symmetry.auxiliary fields.plusAuxiliary
  throatEmbedding := fun point =>
    symmetry.spacetime.act (fields.throatEmbedding (symmetry.throat.act point))
  llIndependent :=
    transformField symmetry.throat symmetry.llIndependent fields.llIndependent

@[simp]
theorem independentPTExchange_involutive
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*}
    (symmetry : IndependentPTData Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent)
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) :
    independentPTExchange symmetry (independentPTExchange symmetry fields) =
      fields := by
  ext point <;> simp [independentPTExchange]

/-- Induced fields.  They are intentionally absent from `IndependentFields`.
The concrete LL output reuses the point data of the LL variation gate. -/
@[ext]
structure InducedFields
    (Spacetime Throat ThroatGeometry : Type*) where
  plusInverseMetric : Spacetime -> Matrix4
  minusInverseMetric : Spacetime -> Matrix4
  plusVolumeDensity : Spacetime -> Real
  minusVolumeDensity : Spacetime -> Real
  relativeRoot : Spacetime -> Matrix4
  throatGeometry : Throat -> ThroatGeometry
  llPointData : Throat -> LLBraneAuxiliaryPointData

/-- Structured, rather than opaque, induction map.  Its proof fields force
the inverse metrics and volume densities to come from the same two independent
metrics.  Root, throat and LL construction remain explicit model parameters. -/
structure FieldInduction
    (Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*) where
  plusInverseMetric :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Spacetime -> Matrix4
  minusInverseMetric :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Spacetime -> Matrix4
  plusVolumeDensity :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Spacetime -> Real
  minusVolumeDensity :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Spacetime -> Real
  relativeRoot :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Spacetime -> Matrix4
  throatGeometry :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Throat -> ThroatGeometry
  llPointData :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Throat -> LLBraneAuxiliaryPointData
  plusInverse_exact : forall fields point,
    plusInverseMetric fields point =
      (fields.plusMetric point).metric⁻¹
  minusInverse_exact : forall fields point,
    minusInverseMetric fields point =
      (fields.minusMetric point).metric⁻¹
  plusVolume_exact : forall fields point,
    plusVolumeDensity fields point =
      Real.sqrt |Matrix.det (fields.plusMetric point).metric|
  minusVolume_exact : forall fields point,
    minusVolumeDensity fields point =
      Real.sqrt |Matrix.det (fields.minusMetric point).metric|
  relativeRoot_square : forall fields point,
    relativeRoot fields point * relativeRoot fields point =
      plusInverseMetric fields point * (fields.minusMetric point).metric

def induce
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (induction : FieldInduction Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry)
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) :
    InducedFields Spacetime Throat ThroatGeometry where
  plusInverseMetric := induction.plusInverseMetric fields
  minusInverseMetric := induction.minusInverseMetric fields
  plusVolumeDensity := induction.plusVolumeDensity fields
  minusVolumeDensity := induction.minusVolumeDensity fields
  relativeRoot := induction.relativeRoot fields
  throatGeometry := induction.throatGeometry fields
  llPointData := induction.llPointData fields

@[simp]
theorem induce_plusInverse_exact
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (induction : FieldInduction Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry)
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) (point : Spacetime) :
    (induce induction fields).plusInverseMetric point =
      (fields.plusMetric point).metric⁻¹ :=
  induction.plusInverse_exact fields point

/-- PT data on every induced fibre. -/
structure InducedPTData
    (Spacetime Throat ThroatGeometry : Type*) where
  spacetime : AlgebraicInvolution Spacetime
  throat : AlgebraicInvolution Throat
  inverseMetric : AlgebraicInvolution Matrix4
  volumeDensity : AlgebraicInvolution Real
  relativeRoot : AlgebraicInvolution Matrix4
  throatGeometry : AlgebraicInvolution ThroatGeometry
  llPointData : AlgebraicInvolution LLBraneAuxiliaryPointData

def inducedPTExchange
    {Spacetime Throat ThroatGeometry : Type*}
    (symmetry : InducedPTData Spacetime Throat ThroatGeometry)
    (fields : InducedFields Spacetime Throat ThroatGeometry) :
    InducedFields Spacetime Throat ThroatGeometry where
  plusInverseMetric :=
    transformField symmetry.spacetime symmetry.inverseMetric
      fields.minusInverseMetric
  minusInverseMetric :=
    transformField symmetry.spacetime symmetry.inverseMetric
      fields.plusInverseMetric
  plusVolumeDensity :=
    transformField symmetry.spacetime symmetry.volumeDensity
      fields.minusVolumeDensity
  minusVolumeDensity :=
    transformField symmetry.spacetime symmetry.volumeDensity
      fields.plusVolumeDensity
  relativeRoot :=
    transformField symmetry.spacetime symmetry.relativeRoot fields.relativeRoot
  throatGeometry :=
    transformField symmetry.throat symmetry.throatGeometry fields.throatGeometry
  llPointData :=
    transformField symmetry.throat symmetry.llPointData fields.llPointData

@[simp]
theorem inducedPTExchange_involutive
    {Spacetime Throat ThroatGeometry : Type*}
    (symmetry : InducedPTData Spacetime Throat ThroatGeometry)
    (fields : InducedFields Spacetime Throat ThroatGeometry) :
    inducedPTExchange symmetry (inducedPTExchange symmetry fields) = fields := by
  ext point <;> simp [inducedPTExchange]

/-- Functional spaces are predicates, so Sobolev, Holder, smooth, compactly
supported or weighted choices can be installed without changing field types. -/
structure FunctionalSpaces
    (Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*) where
  metric : LorentzMetricField4 Spacetime -> Prop
  matter : (Spacetime -> Matter) -> Prop
  gauge : (Spacetime -> Gauge) -> Prop
  ghost : (Spacetime -> Ghost) -> Prop
  auxiliary : (Spacetime -> Auxiliary) -> Prop
  throatEmbedding : (Throat -> Spacetime) -> Prop
  llIndependent : (Throat -> LLIndependent) -> Prop
  induced : InducedFields Spacetime Throat ThroatGeometry -> Prop

/-- Boundary conditions are kept in three named contracts: bulk faces,
throat/worldvolume, and the PT matching condition. -/
structure BoundaryConditions
    (Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent : Type*) where
  bulkFaces :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Prop
  throatWorldvolume :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Prop
  ptMatching :
    IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent -> Prop

def IndependentAdmissible
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (spaces : FunctionalSpaces Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry)
    (boundary : BoundaryConditions Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent)
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) : Prop :=
  spaces.metric fields.plusMetric ∧
  spaces.metric fields.minusMetric ∧
  spaces.matter fields.plusMatter ∧
  spaces.matter fields.minusMatter ∧
  spaces.gauge fields.plusGauge ∧
  spaces.gauge fields.minusGauge ∧
  spaces.ghost fields.plusGhost ∧
  spaces.ghost fields.minusGhost ∧
  spaces.auxiliary fields.plusAuxiliary ∧
  spaces.auxiliary fields.minusAuxiliary ∧
  spaces.throatEmbedding fields.throatEmbedding ∧
  spaces.llIndependent fields.llIndependent ∧
  boundary.bulkFaces fields ∧
  boundary.throatWorldvolume fields ∧
  boundary.ptMatching fields

/-- Compatibility assumptions required of the chosen functional spaces and
boundary conditions.  These are obligations of a concrete global geometry,
not hidden conclusions of this abstract gate. -/
structure PTCompatibleContracts
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (independentPT : IndependentPTData Spacetime Throat Matter Gauge Ghost
      Auxiliary LLIndependent)
    (inducedPT : InducedPTData Spacetime Throat ThroatGeometry)
    (spaces : FunctionalSpaces Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry)
    (boundary : BoundaryConditions Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) : Prop where
  independent_preserved : forall fields,
    IndependentAdmissible spaces boundary fields ->
      IndependentAdmissible spaces boundary
        (independentPTExchange independentPT fields)
  induced_preserved : forall fields,
    spaces.induced fields -> spaces.induced (inducedPTExchange inducedPT fields)

/-- A structured induction map is PT-covariant when inducing after exchange
equals exchanging the already induced fields. -/
def InductionPTCovariant
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (independentPT : IndependentPTData Spacetime Throat Matter Gauge Ghost
      Auxiliary LLIndependent)
    (inducedPT : InducedPTData Spacetime Throat ThroatGeometry)
    (induction : FieldInduction Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry) : Prop :=
  forall fields,
    induce induction (independentPTExchange independentPT fields) =
      inducedPTExchange inducedPT (induce induction fields)

/-- Realized fields retain the independent variables and attach exactly one
induced output.  There is no second variational copy of the induced slots. -/
@[ext]
structure RealizedFields
    (Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*) where
  independent : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
    LLIndependent
  induced : InducedFields Spacetime Throat ThroatGeometry

def realize
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (induction : FieldInduction Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry)
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) :
    RealizedFields Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry where
  independent := fields
  induced := induce induction fields

def realizedPTExchange
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (independentPT : IndependentPTData Spacetime Throat Matter Gauge Ghost
      Auxiliary LLIndependent)
    (inducedPT : InducedPTData Spacetime Throat ThroatGeometry)
    (fields : RealizedFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry) :
    RealizedFields Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry where
  independent := independentPTExchange independentPT fields.independent
  induced := inducedPTExchange inducedPT fields.induced

@[simp]
theorem realizedPTExchange_involutive
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (independentPT : IndependentPTData Spacetime Throat Matter Gauge Ghost
      Auxiliary LLIndependent)
    (inducedPT : InducedPTData Spacetime Throat ThroatGeometry)
    (fields : RealizedFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry) :
    realizedPTExchange independentPT inducedPT
        (realizedPTExchange independentPT inducedPT fields) = fields := by
  ext <;> simp [realizedPTExchange]

/-- Algebraic covariance of the full realization. -/
theorem realize_pt_covariant
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (independentPT : IndependentPTData Spacetime Throat Matter Gauge Ghost
      Auxiliary LLIndependent)
    (inducedPT : InducedPTData Spacetime Throat ThroatGeometry)
    (induction : FieldInduction Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry)
    (hCovariant : InductionPTCovariant independentPT inducedPT induction)
    (fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent) :
    realize induction (independentPTExchange independentPT fields) =
      realizedPTExchange independentPT inducedPT (realize induction fields) := by
  unfold realize realizedPTExchange
  rw [hCovariant fields]

/-- An admissible global configuration uses the same independent object for
functional/boundary conditions and for induction. -/
@[ext]
structure GlobalConfiguration
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    (spaces : FunctionalSpaces Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry)
    (boundary : BoundaryConditions Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent)
    (induction : FieldInduction Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry) where
  fields : IndependentFields Spacetime Throat Matter Gauge Ghost Auxiliary
    LLIndependent
  fields_admissible : IndependentAdmissible spaces boundary fields
  induced_admissible : spaces.induced (induce induction fields)

def globalConfigurationPTExchange
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    {spaces : FunctionalSpaces Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry}
    {boundary : BoundaryConditions Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent}
    {induction : FieldInduction Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry}
    (independentPT : IndependentPTData Spacetime Throat Matter Gauge Ghost
      Auxiliary LLIndependent)
    (inducedPT : InducedPTData Spacetime Throat ThroatGeometry)
    (contracts : PTCompatibleContracts independentPT inducedPT spaces boundary)
    (hCovariant : InductionPTCovariant independentPT inducedPT induction)
    (configuration : GlobalConfiguration spaces boundary induction) :
    GlobalConfiguration spaces boundary induction where
  fields := independentPTExchange independentPT configuration.fields
  fields_admissible :=
    contracts.independent_preserved configuration.fields
      configuration.fields_admissible
  induced_admissible := by
    rw [hCovariant configuration.fields]
    exact contracts.induced_preserved (induce induction configuration.fields)
      configuration.induced_admissible

@[simp]
theorem globalConfigurationPTExchange_involutive
    {Spacetime Throat Matter Gauge Ghost Auxiliary LLIndependent
      ThroatGeometry : Type*}
    {spaces : FunctionalSpaces Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry}
    {boundary : BoundaryConditions Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent}
    {induction : FieldInduction Spacetime Throat Matter Gauge Ghost Auxiliary
      LLIndependent ThroatGeometry}
    (independentPT : IndependentPTData Spacetime Throat Matter Gauge Ghost
      Auxiliary LLIndependent)
    (inducedPT : InducedPTData Spacetime Throat ThroatGeometry)
    (contracts : PTCompatibleContracts independentPT inducedPT spaces boundary)
    (hCovariant : InductionPTCovariant independentPT inducedPT induction)
    (configuration : GlobalConfiguration spaces boundary induction) :
    globalConfigurationPTExchange independentPT inducedPT contracts hCovariant
        (globalConfigurationPTExchange independentPT inducedPT contracts
          hCovariant configuration) = configuration := by
  apply GlobalConfiguration.ext
  simp [globalConfigurationPTExchange]

end

end P0EFTJanusGlobalFieldConfiguration4D
end JanusFormal
