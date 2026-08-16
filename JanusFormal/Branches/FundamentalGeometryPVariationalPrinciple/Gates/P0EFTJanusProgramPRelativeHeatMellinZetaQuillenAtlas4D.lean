import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaAnchoredFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D

/-!
# Quillen circle and determinant-line atlas from one anchored Mellin family

An anchored Mellin family already fixes the complex determinant coordinate and
the positive finite-part metric at the physical basepoint.  This file adds the
two genuine global gluing inputs:

* agreement of the family connection with the explicit circle Quillen
  connection and endpoint clutching;
* a multi-chart zeta atlas whose selected chart is exactly the same Mellin
  family.

All line-bundle transition laws, local parallelism, metric variation and phase
unitarity are then consequences.  In particular the circle, the general atlas
and the scalar heat determinant cannot refer to three unrelated zeta germs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaQuillenAtlas4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaAnchoredFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D
open P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

/-- One anchored Mellin family together with the circle and multi-chart
Quillen gluing data. -/
structure RelativeHeatMellinZetaQuillenAtlasData
    {baseHeatTrace : HeatTime → Real}
    (baseFinitePart : RelativeHeatFinitePartData baseHeatTrace)
    (baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart)
    (fold : Fold) (Index : Type*) where
  anchored : RelativeHeatMellinZetaAnchoredFamilyData
    baseFinitePart baseContinuation
  circleBridge : RelativeZetaCircleConnectionBridgeData fold
    anchored.family.toZetaFamily
  atlas : RelativeZetaLocalFamilyAtlasData Index
  baseIndex : Index
  atlas_zetaPrime_eq :
    atlas.zetaPrimeAtZero baseIndex =
      anchored.family.toZetaFamily.zetaPrimeAtZero
  atlas_parameterDerivative_eq :
    atlas.parameterDerivative baseIndex =
      anchored.family.toZetaFamily.parameterDerivative

namespace RelativeHeatMellinZetaQuillenAtlasData

/-- The selected atlas coordinate is the Mellin-family determinant coordinate
at every parameter. -/
theorem atlas_base_determinant_eq_family
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    {fold : Fold} {Index : Type*}
    (data : RelativeHeatMellinZetaQuillenAtlasData baseFinitePart
      baseContinuation fold Index)
    (parameter : Real) :
    relativeZetaLocalDeterminant data.atlas data.baseIndex parameter =
      relativeHeatMellinZetaFamilyDeterminant data.anchored.family parameter := by
  change
    Complex.exp (-data.atlas.zetaPrimeAtZero data.baseIndex parameter) =
      Complex.exp
        (-data.anchored.family.toZetaFamily.zetaPrimeAtZero parameter)
  rw [congrFun data.atlas_zetaPrime_eq parameter]

/-- The selected atlas connection coefficient is the Mellin/zeta connection
coefficient. -/
theorem atlas_base_connection_eq_family
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    {fold : Fold} {Index : Type*}
    (data : RelativeHeatMellinZetaQuillenAtlasData baseFinitePart
      baseContinuation fold Index)
    (parameter : Real) :
    relativeZetaLocalConnectionCoefficient data.atlas data.baseIndex parameter =
      relativeZetaConnectionCoefficient
        data.anchored.family.toZetaFamily parameter := by
  unfold relativeZetaLocalConnectionCoefficient
    relativeZetaConnectionCoefficient
  rw [congrFun data.atlas_parameterDerivative_eq parameter]

/-- The physical scalar Mellin determinant is the selected atlas coordinate at
parameter zero. -/
theorem atlas_basepoint_eq_scalar
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    {fold : Fold} {Index : Type*}
    (data : RelativeHeatMellinZetaQuillenAtlasData baseFinitePart
      baseContinuation fold Index) :
    relativeZetaLocalDeterminant data.atlas data.baseIndex 0 =
      relativeHeatMellinZetaDeterminant baseContinuation := by
  rw [data.atlas_base_determinant_eq_family]
  exact data.anchored.determinant_zero_eq_base

/-- The selected atlas base coordinate has the original finite-part norm. -/
theorem norm_atlas_basepoint_eq_finitePart
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    {fold : Fold} {Index : Type*}
    (data : RelativeHeatMellinZetaQuillenAtlasData baseFinitePart
      baseContinuation fold Index) :
    ‖relativeZetaLocalDeterminant data.atlas data.baseIndex 0‖ =
      relativeHeatFinitePartDeterminant baseFinitePart := by
  rw [data.atlas_basepoint_eq_scalar]
  exact norm_relativeZetaDeterminant baseContinuation.toZetaComparison

/-- Coherent circle/atlas/metric certificate generated by the one anchored
Mellin family. -/
structure RelativeHeatMellinZetaQuillenAtlasCertificate
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    {fold : Fold} {Index : Type*}
    (data : RelativeHeatMellinZetaQuillenAtlasData baseFinitePart
      baseContinuation fold Index) : Prop where
  atlasCertificate : RelativeZetaDeterminantLineAtlasCertificate data.atlas
  basepoint :
    relativeZetaLocalDeterminant data.atlas data.baseIndex 0 =
      relativeHeatMellinZetaDeterminant baseContinuation
  basepointNorm :
    ‖relativeZetaLocalDeterminant data.atlas data.baseIndex 0‖ =
      relativeHeatFinitePartDeterminant baseFinitePart
  selectedConnection : ∀ parameter,
    relativeZetaLocalConnectionCoefficient data.atlas data.baseIndex parameter =
      relativeZetaConnectionCoefficient
        data.anchored.family.toZetaFamily parameter
  circleParallel : ∀ parameter,
    circleQuillenConnectionAt fold
        (relativeZetaDeterminantCoordinate
          data.anchored.family.toZetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          data.anchored.family.toZetaFamily parameter) = 0
  endpointClutching :
    circleLargeGaugeFrameCoordinateTransition fold
        (relativeZetaDeterminantCoordinate
          data.anchored.family.toZetaFamily 1) =
      relativeZetaDeterminantCoordinate
        data.anchored.family.toZetaFamily 0
  metricVariation : ∀ parameter,
    relativeHeatFinitePartMetricWeightDerivative
        data.anchored.family.finitePartFamily parameter =
      -2 *
        (relativeZetaConnectionCoefficient
          data.anchored.family.toZetaFamily parameter).re *
        relativeHeatFinitePartMetricWeight
          data.anchored.family.finitePartFamily parameter
  phaseUnitary : ∀ parameter,
    ‖relativeZetaFinitePartPhase
      data.anchored.family.toFinitePartComparison parameter‖ = 1

/-- Build the coherent Quillen atlas certificate. -/
def certificate
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    {fold : Fold} {Index : Type*}
    (data : RelativeHeatMellinZetaQuillenAtlasData baseFinitePart
      baseContinuation fold Index) :
    RelativeHeatMellinZetaQuillenAtlasCertificate data where
  atlasCertificate := relativeZetaDeterminantLineAtlasCertificate data.atlas
  basepoint := data.atlas_basepoint_eq_scalar
  basepointNorm := data.norm_atlas_basepoint_eq_finitePart
  selectedConnection := data.atlas_base_connection_eq_family
  circleParallel := data.circleBridge.circle_parallel
  endpointClutching := data.circleBridge.endpoint_clutching
  metricVariation :=
    relativeHeatMellinZetaFamily_metricVariation data.anchored.family
  phaseUnitary :=
    relativeHeatMellinZetaFamily_phase_norm_one data.anchored.family

/-- Public coherent Quillen-atlas checkpoint. -/
theorem relative_heat_mellin_zeta_quillen_atlas_gate
    {baseHeatTrace : HeatTime → Real}
    {baseFinitePart : RelativeHeatFinitePartData baseHeatTrace}
    {baseContinuation : RelativeHeatMellinZetaContinuationData baseFinitePart}
    {fold : Fold} {Index : Type*}
    (data : RelativeHeatMellinZetaQuillenAtlasData baseFinitePart
      baseContinuation fold Index) :
    RelativeHeatMellinZetaQuillenAtlasCertificate data :=
  data.certificate

end RelativeHeatMellinZetaQuillenAtlasData

end
end P0EFTJanusProgramPRelativeHeatMellinZetaQuillenAtlas4D
end JanusFormal
