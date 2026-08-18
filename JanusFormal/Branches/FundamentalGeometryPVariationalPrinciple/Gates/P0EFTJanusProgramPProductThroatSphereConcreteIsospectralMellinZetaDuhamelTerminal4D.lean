import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinAnalyticGerm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinConnectedAnalyticContinuation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereSpectralMellinZetaHalfPlane4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereIsospectralMellinZetaDuhamelAssembly4D

/-!
# Concrete isospectral reduced-sphere Mellin--Duhamel terminal

The explicit reduced-sphere Mellin continuation supplies the continuation and
the reality of its derivative at zero required by the isospectral Duhamel
assembly.  Thus the terminal packet below has no analytic continuation or
phase-reality hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereConcreteIsospectralMellinZetaDuhamelTerminal4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPConstantRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatSphereIsospectralMellinZetaDuhamelAssembly4D
open P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
open P0EFTJanusProgramPProductThroatSphereMellinAnalyticGerm4D
open P0EFTJanusProgramPProductThroatSphereMellinConnectedAnalyticContinuation4D
open P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D
open P0EFTJanusProgramPProductThroatSphereSpectralMellinZetaHalfPlane4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermSubtractedFinitePartAssembly4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- The explicit sphere continuation, named at the concrete terminal layer. -/
def reducedSphereIsospectralMellinZetaContinuation
    (sphereData : ProductThroatSpectralData) :=
  reducedSphereMellinZetaContinuationData sphereData

/-- The explicit sphere continuation viewed as a constant isospectral family. -/
def reducedSphereIsospectralMellinZetaFamily
    (sphereData : ProductThroatSpectralData) :=
  constantRelativeHeatMellinZetaFamily
    (reducedSphereIsospectralMellinZetaContinuation sphereData)

@[simp]
theorem reducedSphereIsospectralMellinZetaContinuation_derivativeAtZero_im
    (sphereData : ProductThroatSpectralData) :
    (reducedSphereIsospectralMellinZetaContinuation sphereData).derivativeAtZero.im = 0 := by
  exact reducedSphereMellinZetaContinuationData_derivativeAtZero_im sphereData

/-- The fully instantiated finite-part Duhamel assembly. -/
def reducedSphereIsospectralFinitePartAssembly
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :=
  toFinitePartAssembly sphereData nuclear data
    (reducedSphereIsospectralMellinZetaContinuation sphereData)
    (reducedSphereIsospectralMellinZetaContinuation_derivativeAtZero_im sphereData)

/-- The concrete continuation agrees with the heat Mellin transform on its
natural half-plane. -/
theorem reducedSphereIsospectralMellinZeta_eq_candidate
    (sphereData : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    (reducedSphereIsospectralMellinZetaContinuation sphereData).zeta spectral =
      relativeHeatMellinZetaCandidate
        (dimensionlessReducedSphereHeatTrace sphereData) spectral := by
  exact reducedSphereMellinZeta_eq_candidate sphereData spectral hSpectral

/-- On the convergence half-plane, the concrete continuation is the
absolutely convergent reduced-sphere spectral zeta series. -/
theorem reducedSphereIsospectralMellinZeta_eq_spectralZeta
    (sphereData : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    (reducedSphereIsospectralMellinZetaContinuation sphereData).zeta spectral =
      reducedSphereSpectralZeta sphereData spectral := by
  rw [reducedSphereIsospectralMellinZeta_eq_candidate
      sphereData spectral hSpectral,
    relativeHeatMellinZetaCandidate_eq_reducedSphereSpectralZeta
      sphereData spectral hSpectral]

/-- The concrete continuation is genuinely holomorphic at the Mellin origin. -/
theorem reducedSphereIsospectralMellinZeta_analyticAt_zero
    (sphereData : ProductThroatSpectralData) :
    AnalyticAt Complex
      (reducedSphereIsospectralMellinZetaContinuation sphereData).zeta 0 :=
  reducedSphereMellinZeta_analyticAt_zero sphereData

/-- The zero germ and the convergent spectral Mellin germ belong to one
connected analytic continuation, so the concrete terminal is not spliced. -/
theorem reducedSphereIsospectralMellinZeta_connectedAnalyticContinuation_gate
    (sphereData : ProductThroatSpectralData) :
    IsOpen reducedSphereMellinConnectedDomain ∧
      IsPreconnected reducedSphereMellinConnectedDomain ∧
      (0 : Complex) ∈ reducedSphereMellinConnectedDomain ∧
      ((5 : Complex) / 4) ∈ reducedSphereMellinConnectedDomain ∧
      AnalyticOnNhd Complex (reducedSphereMellinZeta sphereData)
        reducedSphereMellinConnectedDomain ∧
      reducedSphereMellinZeta sphereData =ᶠ[𝓝 ((5 : Complex) / 4)]
        relativeHeatMellinZetaCandidate
          (dimensionlessReducedSphereHeatTrace sphereData) :=
  product_throat_sphere_mellin_connected_analytic_continuation_gate sphereData

/-- Schwarz reflection is a consequence of the connected analytic
continuation and its real Mellin seed. -/
theorem reducedSphereIsospectralMellinZeta_schwarz_gate
    (sphereData : ProductThroatSpectralData) :
    Set.EqOn (reducedSphereMellinZeta sphereData)
        (schwarzReflect (reducedSphereMellinZeta sphereData))
        reducedSphereMellinConnectedDomain ∧
      (reducedSphereIsospectralMellinZetaContinuation sphereData).derivativeAtZero.im = 0 := by
  simpa [reducedSphereIsospectralMellinZetaContinuation] using
    reducedSphereMellinZeta_schwarz_gate sphereData

/-- The concrete derivative at zero is the negative finite-part logarithm. -/
theorem reducedSphereIsospectralMellinZetaDerivativeAtZero_eq
    (sphereData : ProductThroatSpectralData) :
    (reducedSphereIsospectralMellinZetaContinuation sphereData).derivativeAtZero =
      ((-relativeHeatFinitePartLogDeterminant
        (reducedSphereMellinFinitePartData sphereData) : Real) : Complex) :=
  rfl

/-- Public fully concrete sphere terminal.  Its only inputs are the geometric
sphere packet and the already constructed nuclear short-time packet. -/
theorem product_throat_sphere_concrete_isospectral_mellin_zeta_duhamel_terminal_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    (IsOpen reducedSphereMellinConnectedDomain ∧
      IsPreconnected reducedSphereMellinConnectedDomain ∧
      (0 : Complex) ∈ reducedSphereMellinConnectedDomain ∧
      ((5 : Complex) / 4) ∈ reducedSphereMellinConnectedDomain ∧
      AnalyticOnNhd Complex (reducedSphereMellinZeta sphereData)
        reducedSphereMellinConnectedDomain ∧
      reducedSphereMellinZeta sphereData =ᶠ[𝓝 ((5 : Complex) / 4)]
        relativeHeatMellinZetaCandidate
          (dimensionlessReducedSphereHeatTrace sphereData)) ∧
    Set.EqOn (reducedSphereMellinZeta sphereData)
        (schwarzReflect (reducedSphereMellinZeta sphereData))
        reducedSphereMellinConnectedDomain ∧
    ((∀ spectral : Complex, 1 < spectral.re →
        reducedSphereMellinZeta sphereData spectral =
          relativeHeatMellinZetaCandidate
            (dimensionlessReducedSphereHeatTrace sphereData) spectral) ∧
      HasDerivAt (reducedSphereMellinZeta sphereData)
        (reducedSphereMellinZetaDerivativeAtZero sphereData) 0 ∧
      (reducedSphereIsospectralMellinZetaContinuation sphereData).derivativeAtZero.im = 0 ∧
      relativeHeatMellinZetaDeterminant
          (reducedSphereIsospectralMellinZetaContinuation sphereData) ≠ 0 ∧
      ‖relativeHeatMellinZetaDeterminant
          (reducedSphereIsospectralMellinZetaContinuation sphereData)‖ =
        relativeHeatFinitePartDeterminant
          (reducedSphereMellinFinitePartData sphereData)) ∧
    relativeHeatFinitePartLogDeterminant
        (reducedSphereMellinFinitePartData sphereData) =
      -(reducedSphereIsospectralMellinZetaContinuation sphereData).derivativeAtZero.re ∧
    (let family := reducedSphereIsospectralMellinZetaFamily sphereData
     let assembly := reducedSphereIsospectralFinitePartAssembly
       sphereData nuclear data
     (∀ parameter, HasDerivAt
        (fun current =>
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        0 parameter) ∧
      (∀ parameter, family.finitePartFamily.logDerivative parameter = 0) ∧
      (∀ parameter,
        family.finitePartFamily.logDerivative parameter =
          -finitePartDerivative assembly.finiteCounterterm parameter +
            (∫ time in Set.Ioo (0 : Real) 1,
              assembly.shortTime.renormalizedDuhamelTrace parameter time) +
            (∫ time in Set.Ioi (1 : Real),
              extendedDuhamelTrace nuclear parameter time)) ∧
      (∀ parameter,
        relativeZetaConnectionCoefficient family.toZetaFamily parameter = 0) ∧
      (∀ parameter,
        ‖relativeHeatMellinZetaFamilyDeterminant family parameter‖ =
          relativeHeatFinitePartDeterminant
            (reducedSphereMellinFinitePartData sphereData))) := by
  refine ⟨reducedSphereIsospectralMellinZeta_connectedAnalyticContinuation_gate sphereData,
    (reducedSphereIsospectralMellinZeta_schwarz_gate sphereData).1,
    product_throat_sphere_mellin_zeta_continuation_gate sphereData,
    (reducedSphereIsospectralMellinZetaContinuation sphereData).finitePart_realPart,
    ?_⟩
  simpa only [reducedSphereIsospectralMellinZetaFamily,
      reducedSphereIsospectralFinitePartAssembly] using
    product_throat_sphere_isospectral_mellin_zeta_duhamel_assembly_gate
      sphereData nuclear data
      (reducedSphereIsospectralMellinZetaContinuation sphereData)
      (reducedSphereIsospectralMellinZetaContinuation_derivativeAtZero_im sphereData)

end
end P0EFTJanusProgramPProductThroatSphereConcreteIsospectralMellinZetaDuhamelTerminal4D
end JanusFormal
