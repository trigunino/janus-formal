# HESSIAN-GLOBAL-01 — frontière de Noether des zéro-modes

Date : **9 août 2026**.

Cette note prolonge :

```text
docs/hessian_global_01_named_zero_modes.md
docs/hessian_global_01_no_hidden_modes.md
docs/hessian_global_01_stable_physical_perturbation.md
```

La frontière précédente demandait encore, pour chaque mode physique nommé, une
preuve séparée de l’équation opératorielle

\[
H v=0.
\]

La nouvelle route dérive cette équation de l’action elle-même.

## 1. Identité de Noether sur un germe

Pour une action scalaire `C²`

\[
\mathcal S:E\to\mathbb R
\]

et une direction constante `v`, on suppose que la première variation dans la
direction `v` s’annule sur un voisinage du point de base :

\[
D\mathcal S(x)[v]=0.
\]

Le module

```text
P0EFTJanusProgramPNoetherHessianKernel4D
```

différentie cette identité et démontre :

\[
D^2\mathcal S(x_0)[w,v]=0
\]

pour toute direction `w`. Si le Hessien est symétrique, alors aussi :

\[
D^2\mathcal S(x_0)[v,w]=0.
\]

Par représentation de Riesz, le mode appartient au noyau de l’opérateur du
Hessien :

\[
H v=0.
\]

Le gate générique est :

```lean
noether_hessian_kernel_gate
```

## 2. Spécialisation à l’action augmentée Candidate-A

Le module

```text
P0EFTJanusProgramPGlobalCandidateAActualNoetherModes4D
```

utilise l’action quadratique augmentée déjà construite sur l’unique complétion
D10-free :

```lean
globalCandidateACommonAugmentedAction
```

Sa seconde dérivée est exactement :

```lean
globalCandidateACommonAugmentedHessian
```

et son représentant de Riesz est exactement l’opérateur H12 affiché :

```lean
globalCandidateAActualKernelOperator
```

Une famille finie

```lean
GlobalCandidateAActualNoetherModeFamily4D
```

ne contient donc plus de champ `operator (vector mode) = 0`. Elle contient les
vecteurs et leurs identités de Noether au niveau de la première variation.
L’annulation par le Hessien est un théorème.

## 3. Orthogonalité et absence de modes cachés

Le module

```text
P0EFTJanusProgramPGlobalCandidateAActualNoetherOrthogonalGarding4D
```

ajoute seulement :

```text
modes non nuls
modes deux à deux orthogonaux
une estimation de Gårding globale
stationnarité LL
```

L’orthogonalité donne l’indépendance linéaire. La projection orthogonale sur le
sous-espace engendré par les modes est construite automatiquement. L’estimation
de Gårding annule tout vecteur du noyau orthogonal à ce sous-espace. On obtient
ainsi :

\[
\ker H=\operatorname{span}\{v_i\},
\qquad
\dim\ker H=\#\{i\}.
\]

La finitude du noyau, le gap sur son orthogonal, l’image fermée, Fredholm,
l’indice zéro, le Green réduit et la résolvante sont ensuite dérivés par les
gates déjà installés.

## 4. Gårding du total héritée du principal

L’opérateur Candidate-A possède la décomposition canonique :

\[
H=A_{\mathrm{BRST-SpinC-LL}}+K_{\mathrm{phys}}.
\]

Le module

```text
P0EFTJanusProgramPGlobalCandidateAActualNoetherStablePhysicalForm4D
```

ne demande pas une estimation de Gårding indépendante pour `H`. Il utilise :

1. une estimation de Gårding pour l’opérateur principal `A` ;
2. la petite norme de la forme physique H11 :
   \[
   \|B_{\mathrm{phys}}\|<c;
   \]
3. la borne de Riesz déjà démontrée :
   \[
   \|K_{\mathrm{phys}}\|\leq\|B_{\mathrm{phys}}\|.
   \]

Il en déduit :

\[
(c-\|K_{\mathrm{phys}}\|)\|x\|^2
\leq
\langle x,Hx\rangle+
C\sum_i\langle x,v_i\rangle^2.
\]

Le coefficient restant est strictement positif. Les modes n’ont pas besoin
d’être annulés séparément par `A` et `K` : leur identité de Noether concerne
directement l’action totale et fournit `H v_i=0`.

## 5. Façades terminales

Trois niveaux sont exportés.

### Noether + indépendance

```lean
global_candidateA_hessian_canonicalSix_noether_frontier_gate
```

### Noether + orthogonalité

```lean
global_candidateA_hessian_canonicalSix_noetherOrthogonal_frontier_gate
```

### Noether + Gårding du principal + petite forme physique

```lean
global_candidateA_hessian_canonicalSix_noetherStable_frontier_gate
```

Le dernier gate est la route préférée. Après la famille locale H10-réduite, il
ne demande que :

```text
1. la borne du cœur lisse vers le chart physique ;
2. les modes de Noether orthogonaux ;
3. Gårding pour le principal ;
4. ‖physical.form‖ < constante de Gårding ;
5. la stationnarité LL.
```

Il retourne la fermeture H10–H14, le noyau exact, son nombre de modes, le gap,
Fredholm, l’indice zéro, le Green et la résolvante.

## 6. Travail physique restant

Cette réduction isole désormais les tâches suivantes :

```text
1. écrire les transformations infinitésimales physiques dans le Hilbert commun ;
2. démontrer l’invariance de première variation de l’action augmentée le long
   de ces directions ;
3. vérifier leur non-annulation et leur orthogonalité par secteur ;
4. prouver Gårding pour l’opérateur principal BRST–SpinC–LL ;
5. démontrer que la norme de la forme physique H11 est plus petite que la
   constante coercive du principal.
```

La preuve `H v = 0`, l’indépendance, la projection finie, l’absence de modes
cachés, le gap et les conclusions Fredholm ne sont plus des obligations
indépendantes.

La chaîne reste à certifier par un build Lean complet.
