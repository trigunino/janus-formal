# HESSIAN-GLOBAL-01 — perturbation physique stable et noyau exact

Date : **9 août 2026**.

Cette couche remplace la route perturbative précédente, qui demandait déjà un
certificat disant que les modes nommés engendraient tout le noyau du Hessien
final. Cette hypothèse était trop forte : l’exclusion des modes cachés doit être
une conséquence de l’estimation de Gårding.

## Décomposition canonique

Le véritable opérateur augmenté Candidate-A est fixé comme

\[
H=A+K,
\]

où :

- `A` est le représentant de Riesz diagonal BRST--SpinC--LL déjà construit ;
- `K` est le représentant de Riesz des sept blocs physiques H10/H11.

Dans Lean, ces objets sont :

```lean
globalCandidateACanonicalStableReferenceOperator
globalCandidateACanonicalStablePhysicalPerturbation
```

et l’égalité avec l’opérateur affiché est :

```lean
globalCandidateAActualKernelOperator_eq_canonicalStableSum
```

Elle n’est pas une nouvelle hypothèse physique.

## Données analytiques restantes

Pour un type fini `ZeroMode`, on fournit des vecteurs `vᵢ` tels que :

\[
A v_i=0,
\qquad
K v_i=0,
\]

avec :

- `vᵢ ≠ 0` ;
- orthogonalité deux à deux ;
- une estimation de Gårding pour `A` :

\[
c\|x\|^2
\le
\langle x,Ax\rangle
+D\sum_i \langle x,v_i\rangle^2;
\]

- la petitesse perturbative :

\[
\|K\|<c.
\]

Le Hessien complet hérite alors de :

\[
(c-\|K\|)\|x\|^2
\le
\langle x,Hx\rangle
+D\sum_i \langle x,v_i\rangle^2.
\]

## Exclusion des modes cachés

Les vecteurs non nuls et orthogonaux sont indépendants. Leur span dans
`ker H` est de dimension finie et possède donc une projection orthogonale.
Pour un vecteur du noyau orthogonal à tous les `vᵢ`, le défaut fini disparaît et
l’estimation précédente force sa norme à être nulle.

On obtient ainsi, sans hypothèse de spanning :

\[
\ker H=\operatorname{span}\{v_i\},
\qquad
\dim\ker H=\#\mathrm{ZeroMode}.
\]

Le paquet construit ensuite le gap sur `(ker H)ᗮ`, l’image fermée, le caractère
Fredholm, l’indice zéro, le Green réduit, la résolvante et la stabilité sous
petites perturbations.

## Gates terminaux

La spécialisation Candidate-A est :

```lean
global_candidateA_actual_kernel_stable_perturbation_gate
```

La fermeture H10--H14 avec une décomposition arbitraire identifiée à `H` est :

```lean
global_candidateA_hessian_canonicalSix_stablePerturbation_frontier_gate
```

La route préférée, où `A` et `K` sont fixés canoniquement, est :

```lean
global_candidateA_hessian_canonicalSix_physicalPerturbation_frontier_gate
```

La version classifiée par secteurs est :

```lean
global_candidateA_hessian_canonicalSix_physicalPerturbation_sector_gate
```

## Frontière restante

Après la famille locale H10-réduite, la route préférée ne demande que deux
paquets analytiques :

1. la borne du vrai morphisme du cœur lisse vers le chart physique D10-free ;
2. les modes nommés préservés par `A` et `K`, l’estimation de Gårding de `A` et
   la borne stricte `‖K‖ < c`.

Elle ne demande plus :

- une base ou une équivalence de coordonnées de `ker H` ;
- une preuve de spanning du noyau final ;
- un gap spectral déjà construit ;
- un projecteur de défaut ;
- un paramétrix ;
- un choix arbitraire de `A` et `K`.

La branche reste en brouillon tant qu’un build Lean complet n’est pas vert.
Aucun nouvel axiome, `sorry`, `admit`, opérateur de remplacement ou direction
physique D10 n’est introduit par cette réduction.
