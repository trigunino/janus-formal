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

La nouvelle route dérive cette équation de l’invariance de l’action elle-même.

## 1. Invariance de l’action et identité de Noether

La prémisse physique la plus primitive utilisée ici est l’invariance locale de
l’action scalaire `C²` sous la translation engendrée par un mode `v` :

\[
\mathcal S(x+t v)=\mathcal S(x)
\]

pour les paramètres `t` suffisamment petits et les configurations `x` dans un
germe autour du point de base.

Le module

```text
P0EFTJanusProgramPActionTranslationSymmetryHessianKernel4D
```

différentie d’abord cette identité et obtient l’invariance de la première
variation le long de l’orbite affine. Le module

```text
P0EFTJanusProgramPNoetherHessianKernel4D
```

différentie ensuite l’identité directionnelle

\[
D\mathcal S(x)[v]=0
\]

et démontre :

\[
D^2\mathcal S(x_0)[w,v]=0
\]

pour toute direction `w`. Si le Hessien est symétrique, alors également :

\[
D^2\mathcal S(x_0)[v,w]=0.
\]

Par représentation de Riesz :

\[
H v=0.
\]

Les gates génériques sont :

```lean
action_translation_symmetry_hessian_kernel_gate
noether_hessian_kernel_gate
```

## 2. Spécialisation à l’action augmentée Candidate-A

Le module

```text
P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D
```

applique cette chaîne à l’unique action augmentée Candidate-A sur la complétion
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

Une famille

```lean
GlobalCandidateAActionTranslationSymmetryModes4D
```

contient seulement les vecteurs et leurs identités d’invariance de l’action.
L’équation `H v = 0` est construite par différentiation ; elle n’est plus un
champ indépendant du paquet analytique.

La route plus générale fondée directement sur la première variation reste
exportée par :

```text
P0EFTJanusProgramPGlobalCandidateAActualNoetherModes4D
```

## 3. Orthogonalité et absence de modes cachés

Les modes physiques peuvent être présentés comme des vecteurs non nuls et deux
à deux orthogonaux. Le module

```text
P0EFTJanusProgramPGlobalCandidateAActualNoetherOrthogonalGarding4D
```

utilise cette orthogonalité pour dériver leur indépendance linéaire.

Le sous-espace engendré est fini-dimensional ; sa projection orthogonale est
donc construite automatiquement. Une estimation de Gårding avec défaut porté
par les coefficients de ces modes force ensuite à zéro tout élément du noyau
orthogonal à leur span. Il en résulte :

\[
\ker H=\operatorname{span}\{v_i\},
\qquad
\dim\ker H=\#\{i\}.
\]

Il n’est donc plus nécessaire de fournir :

```text
une équivalence choisie avec ker H
une projection de défaut
une preuve séparée qu’il n’existe pas de mode caché
```

## 4. Gårding du Hessien total héritée de l’opérateur principal

L’opérateur Candidate-A possède la décomposition canonique :

\[
H=A_{\mathrm{BRST-SpinC-LL}}+K_{\mathrm{phys}}.
\]

Le module

```text
P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
```

ne demande pas une estimation de Gårding indépendante pour `H`. Il utilise :

1. une estimation de Gårding pour l’opérateur principal `A` ;
2. la petite norme de la véritable forme physique H11 :
   \[
   \|B_{\mathrm{phys}}\|<c;
   \]
3. la borne de Riesz déjà démontrée :
   \[
   \|K_{\mathrm{phys}}\|\leq\|B_{\mathrm{phys}}\|.
   \]

La borne inférieure universelle d’une perturbation bornée donne alors :

\[
(c-\|K_{\mathrm{phys}}\|)\|x\|^2
\leq
\langle x,Hx\rangle+
C\sum_i\langle x,v_i\rangle^2.
\]

Le coefficient de gauche est strictement positif. Les modes n’ont pas besoin
d’être annulés séparément par `A` et `K` : leur invariance concerne directement
l’action totale et fournit `H v_i=0`.

## 5. Façades terminales

Plusieurs niveaux compatibles sont exportés.

### Identité directionnelle de Noether

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

### Invariance de l’action + Gårding du principal + petite forme physique

```lean
global_candidateA_hessian_canonicalSix_actionSymmetryStable_frontier_gate
```

Le dernier gate est la route préférée. Après la famille locale H10-réduite, il
ne demande que deux paquets analytiques :

```text
1. la borne du cœur lisse vers le véritable chart physique ;
2. un paquet contenant :
   - les translations qui préservent l’action augmentée ;
   - leur non-annulation et leur orthogonalité ;
   - Gårding pour le principal BRST–SpinC–LL ;
   - ‖physical.form‖ < constante de Gårding ;
   - la stationnarité LL.
```

Il construit ensuite :

```text
H10 same-action Robin
H13 vrai Hessien Candidate-A
H11 extension canonique des sept blocs
noyau exact et nombre de zéro-modes
H12 Fredholm et indice zéro
gap sur (ker H)ᗮ
Green réduit
résolvante réelle et stabilité quantitative
H14 certificat terminal
```

## 6. Travail physique restant

La frontière analytique est désormais ramenée à :

```text
1. écrire les transformations infinitésimales physiques dans le Hilbert commun ;
2. démontrer S(x+t·v)=S(x) sur le germe admissible pour chacune d’elles ;
3. vérifier qu’elles sont non nulles et orthogonales par secteur ;
4. prouver Gårding pour l’opérateur principal BRST–SpinC–LL ;
5. démontrer que la norme de la forme physique H11 est plus petite que la
   constante coercive du principal ;
6. établir la borne du cœur lisse vers le chart physique.
```

La preuve `H v = 0`, l’indépendance, la projection finie, l’absence de modes
cachés, la Gårding du total, le gap et les conclusions Fredholm ne sont plus des
obligations indépendantes.

La chaîne reste à certifier par un build Lean complet.
