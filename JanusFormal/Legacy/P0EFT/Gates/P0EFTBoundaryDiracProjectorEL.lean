import JanusFormal.Legacy.P0EFT.Gates.P0EFTCayleyShellNormalization

namespace JanusFormal
namespace P0EFTBoundaryDiracProjectorEL

set_option autoImplicit false

structure BoundaryDiracEL where
  bulkSurfaceFluxTerm : Prop
  diracBoundaryTermIncluded : Prop
  janusPinShellTermsIncluded : Prop
  boundaryEulerLagrangeEquation : Prop
  factorizesAsChiralBoundaryEquation : Prop
  chiralProjectorDerived : Prop
  apsDomainEquivalent : Prop

def boundaryELCanDeriveProjector (b : BoundaryDiracEL) : Prop :=
  b.bulkSurfaceFluxTerm /\
  b.diracBoundaryTermIncluded /\
  b.janusPinShellTermsIncluded /\
  b.boundaryEulerLagrangeEquation /\
  b.factorizesAsChiralBoundaryEquation /\
  b.chiralProjectorDerived

def boundaryELClosesAPSProjector (b : BoundaryDiracEL) : Prop :=
  boundaryELCanDeriveProjector b /\ b.apsDomainEquivalent

theorem boundary_el_factorization_gives_chiral_projector
    (b : BoundaryDiracEL)
    (hFlux : b.bulkSurfaceFluxTerm)
    (hBoundary : b.diracBoundaryTermIncluded)
    (hShell : b.janusPinShellTermsIncluded)
    (hEL : b.boundaryEulerLagrangeEquation)
    (hFactor : b.factorizesAsChiralBoundaryEquation)
    (hProjector : b.chiralProjectorDerived) :
    boundaryELCanDeriveProjector b := by
  exact And.intro hFlux
    (And.intro hBoundary
      (And.intro hShell
        (And.intro hEL
          (And.intro hFactor hProjector))))

theorem missing_factorization_blocks_boundary_projector
    (b : BoundaryDiracEL)
    (hMissing : Not b.factorizesAsChiralBoundaryEquation) :
    Not (boundaryELCanDeriveProjector b) := by
  intro h
  exact hMissing h.right.right.right.right.left

theorem boundary_projector_needs_aps_equivalence_for_spectral_closure
    (b : BoundaryDiracEL)
    (hMissing : Not b.apsDomainEquivalent) :
    Not (boundaryELClosesAPSProjector b) := by
  intro h
  exact hMissing h.right

theorem boundary_el_closes_aps_projector_conditionally
    (b : BoundaryDiracEL)
    (hProjector : boundaryELCanDeriveProjector b)
    (hAPS : b.apsDomainEquivalent) :
    boundaryELClosesAPSProjector b := by
  exact And.intro hProjector hAPS

end P0EFTBoundaryDiracProjectorEL
end JanusFormal
