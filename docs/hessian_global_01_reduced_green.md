# HESSIAN-GLOBAL-01 — scindage exact et Green réduit

Date : **8 août 2026**.

Ce document complète `hessian_global_01_concrete_frontier.md`. La même frontière
à trois paquets produit désormais non seulement le certificat H14, mais aussi
la réalisation du Hessien après retrait exact des zéro-modes.

## Entrées inchangées

```text
1. famille locale physique avec projection de bord H10
2. accords denses des sept prolongements physiques H11
3. obstruction finie orthogonale et coercivité hors défaut H12
```

Aucun quatrième paquet n’est ajouté.

## Scindage exact

Pour l’opérateur augmenté `H` et le projecteur fini `P`, les relations

```text
P² = P,
HP = 0,
PH = 0,
```

et la coercivité sur `ker P` impliquent :

```text
ker H = range P.
```

En effet, si `Hx = 0`, alors `x - Px` appartient à `ker P`, est encore annulé
par `H`, et la coercivité force `x - Px = 0`.

La surjectivité construite de `H + P` donne l’autre moitié :

```text
range H = ker P.
```

Si `y ∈ ker P`, une solution de `Hx + Px = y` vérifie nécessairement `Px = 0`,
donc `Hx = y`.

Modules :

```text
P0EFTJanusProgramPFiniteDefectKernelIdentification4D
P0EFTJanusProgramPFiniteDefectRangeIdentification4D
P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSplitting4D
```

## Hessien réduit

Le véritable opérateur réduit est la restriction :

```text
H_red : ker P → ker P.
```

Il s’agit du même opérateur augmenté, sans changement de formule ni de domaine
ambiant. Le module

```text
P0EFTJanusProgramPFiniteDefectReducedOperator4D
```

prouve :

```text
H_red injectif,
H_red surjectif,
c ‖x‖ ≤ ‖H_red x‖.
```

La spécialisation Candidate-A est :

```text
P0EFTJanusProgramPGlobalCandidateAAugmentedReducedOperator4D
```

## Green réduit

Le bounded inverse theorem transforme `H_red` en équivalence linéaire continue.
Son inverse est :

```text
G_red = H_red⁻¹.
```

Les identités exactes sont :

```text
H_red G_red = id,
G_red H_red = id.
```

La coercivité fournit la borne quantitative :

\[
\|G_{\mathrm{red}}\| \le c^{-1}.
\]

Modules :

```text
P0EFTJanusProgramPFiniteDefectReducedInverse4D
P0EFTJanusProgramPGlobalCandidateAAugmentedReducedInverse4D
```

## Certificat terminal enrichi

```text
P0EFTJanusProgramPGlobalHessianReducedGreenCertificate4D
P0EFTJanusProgramPGlobalHessianReducedGreenFrontier4D
```

Gate :

```lean
global_candidateA_hessian_reducedGreen_certificate_gate
```

La sortie contient simultanément :

- H10 same-action et second Fréchet ;
- H13 et les sept blocs physiques ;
- H11 fermé et auto-adjoint ;
- H12 Fredholm et indice zéro ;
- `ker H = range P` ;
- `range H = ker P` ;
- le Green réduit et sa borne.

## Robustesse perturbative

Le module

```text
P0EFTJanusProgramPSelfAdjointSmallPerturbation4D
```

considère un opérateur auto-adjoint `H` avec gap normique `c > 0` et une
perturbation auto-adjointe `K` telle que :

\[
\|Kx\| \le \delta\|x\|,
\qquad 0\le\delta<c.
\]

Il prouve :

\[
(c-\delta)\|x\|
\le
\|(H+K)x\|.
\]

Ainsi `H + K` reste injectif, surjectif et quantitativement séparé de zéro.
Cette brique donne un voisinage ouvert de stabilité autour du Hessien réduit.

## Usage suivant

La prochaine couche peut travailler directement sur `ker P` :

- quotient stable sans zéro-modes ;
- résolvante et perturbations ;
- déterminant réduit ;
- comparaison avec le régulateur nucléaire de référence ;
- famille de Quillen/Bismut–Freed après contrôle paramétrique.

La certification Lean complète reste requise avant de déclarer ce paquet
formellement fermé.
