# HESSIAN-GLOBAL-01 — frontière d’invariance de l’action

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
D^2\mathcal S(x_0)[w,v]=0,
\qquad
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

et son représentant de Riesz est l’opérateur H12 affiché :

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

## 3. Orthogonalité et absence de modes cachés

Les modes physiques sont présentés comme des vecteurs non nuls et deux à deux
orthogonaux. Cette orthogonalité dérive leur indépendance linéaire.

Le sous-espace engendré est fini-dimensional ; sa projection orthogonale est
donc construite automatiquement. Une estimation de Gårding avec défaut porté
par les coefficients de ces modes force ensuite à zéro tout élément du noyau
orthogonal à leur span. Il en résulte :

\[
\ker H=\operatorname{span}\{v_i\},
\qquad
\dim\ker H=\#\{i\}.
\]

Il n’est plus nécessaire de fournir :

```text
une équivalence choisie avec ker H
une projection de défaut
une preuve séparée d’absence de mode caché
```

## 4. Gårding du Hessien total héritée du principal

L’opérateur Candidate-A possède la décomposition canonique :

\[
H=A_{\mathrm{BRST-SpinC-LL}}+K_{\mathrm{phys}}.
\]

Le module

```text
P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
```

utilise :

1. une estimation de Gårding pour le principal `A` ;
2. la petite norme de la véritable forme physique H11 ;
3. la borne de Riesz
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

Les modes n’ont pas besoin d’être annulés séparément par `A` et `K` : leur
invariance concerne l’action totale et fournit directement `H v_i=0`.

## 5. Petite norme H11 calculée sur le cœur dense

L’extension H11 est construite canoniquement depuis une estimation bilinéaire
sur le cœur lisse dense. Le module

```text
P0EFTJanusProgramPDenseBilinearOpNorm4D
```

démontre le principe général : si

\[
|B(\iota x,\iota y)|
\leq C\|\iota x\|\|\iota y\|
\]

sur une image dense, alors la forme bilinéaire continue complétée vérifie :

\[
\|B\|\leq C.
\]

La spécialisation Candidate-A est :

```text
P0EFTJanusProgramPGlobalCandidateASevenPhysicalExtensionNorm4D
```

La constante canonique

```lean
globalCandidateACanonicalSevenPhysicalConstant
```

est celle du vrai Hessien physique à sept blocs. Elle est calculée à partir :

```text
borne cœur → chart
normes des six Hessiennes locales canoniques
projection de bord construite depuis la même borne
norme du Hessien Robin H10
```

Le module

```text
P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D
```

remplace donc l’hypothèse abstraite

```text
‖physical.form‖ < c
```

par l’inégalité scalaire explicite

```text
globalCandidateACanonicalSevenPhysicalConstant ... < c.
```

L’ancienne inégalité sur la forme complétée est une conséquence.

## 6. Façades terminales

Les routes intermédiaires restent exportées :

```lean
global_candidateA_hessian_canonicalSix_noether_frontier_gate
global_candidateA_hessian_canonicalSix_noetherOrthogonal_frontier_gate
global_candidateA_hessian_canonicalSix_noetherStable_frontier_gate
global_candidateA_hessian_canonicalSix_actionSymmetryStable_frontier_gate
```

La route préférée est maintenant :

```lean
global_candidateA_hessian_canonicalSix_actionSymmetryExplicitSmallness_frontier_gate
```

Après la famille locale H10-réduite, elle ne demande que deux paquets :

```text
1. la borne du cœur lisse vers le véritable chart physique ;
2. un paquet contenant :
   - les translations qui préservent l’action augmentée ;
   - leur non-annulation et leur orthogonalité ;
   - Gårding pour le principal BRST–SpinC–LL ;
   - constante physique dense-core < constante de Gårding ;
   - la stationnarité LL.
```

Elle construit :

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

## 7. Travail physique restant

La frontière analytique est désormais ramenée à :

```text
1. écrire les transformations infinitésimales physiques dans le Hilbert commun ;
2. démontrer S(x+t·v)=S(x) sur le germe admissible ;
3. vérifier qu’elles sont non nulles et orthogonales par secteur ;
4. prouver Gårding pour le principal BRST–SpinC–LL ;
5. calculer la constante dense-core des sept blocs et montrer qu’elle est
   strictement plus petite que la constante coercive du principal ;
6. établir la borne du cœur lisse vers le chart physique.
```

La preuve `H v = 0`, l’indépendance, la projection finie, l’absence de modes
cachés, la Gårding du total, la norme de l’extension H11, le gap et les
conclusions Fredholm ne sont plus des obligations indépendantes.

La chaîne reste à certifier par un build Lean complet.
