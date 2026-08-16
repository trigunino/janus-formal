# HESSIAN-GLOBAL-01 — orbites de symétrie non linéaires

Date : **9 août 2026**.

La route affine traite les directions pour lesquelles l’action quadratique
augmentée est invariante sous `x ↦ x + t v`. Les véritables actions de jauge et
de difféomorphisme peuvent cependant tracer des courbes non linéaires dans le
chart des configurations.

## Donnée géométrique

Une orbite est un objet

```lean
SymmetryCurveAt point generator
```

contenant :

- une courbe `γ : ℝ → E` ;
- `γ 0 = point` ;
- sa dérivée de Fréchet en zéro ;
- l’identification de cette dérivée avec `generator`.

## Identité de Noether

Le module

```text
P0EFTJanusProgramPSymmetryCurveHessianKernel4D
```

part de

\[
\nabla S(\gamma(t))=\nabla S(\gamma(0))
\]

pour `t` assez petit. La règle de chaîne donne :

\[
D(\nabla S)_{\gamma(0)}\,\gamma'(0)=0.
\]

Le générateur tangent est donc un zéro-mode du Hessien véritable.

## Candidate-A

Le module

```text
P0EFTJanusProgramPGlobalCandidateASymmetryCurveZeroModes4D
```

applique ce calcul à :

```lean
globalCandidateACommonAugmentedAction
globalCandidateAActualKernelOperator
```

et utilise ensuite l’indépendance des générateurs et la Gårding globale pour
prouver qu’ils épuisent tout le noyau.

La façade terminale est :

```lean
global_candidateA_hessian_canonicalSix_symmetryCurve_frontier_gate
```

Elle assemble les six Hessiennes physiques canoniques, le Robin H10, les
orbites de symétrie, H11, H12 et H14.

## Frontière restante

Pour chaque générateur physique concret, il reste à construire :

```text
1. l’orbite de jauge/difféomorphisme dans le chart réel ;
2. sa dérivée en zéro ;
3. l’invariance du gradient de l’action augmentée le long de l’orbite ;
4. l’indépendance des générateurs et l’estimation de Gårding.
```

Cette route est plus générale que la translation affine et n’introduit aucune
direction D10, seconde action, seconde complétion ou projection de défaut.
