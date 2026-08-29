# HESSIAN-GLOBAL-01 — zéro-modes générés par symétrie

Date : **9 août 2026**.

Cette couche retire de la frontière terminale la donnée explicite

```text
H v = 0
```

pour chaque zéro-mode physique nommé.

## 1. Orbite affine

Pour un point de base `x₀` et une direction `v`, on considère

\[
x(t)=x_0+t v.
\]

Le module

```text
P0EFTJanusProgramPSymmetryOrbitHessianKernel4D
```

prouve que l’invariance locale du gradient de l’action le long de cette orbite,

\[
\nabla S(x_0+t v)=\nabla S(x_0),
\]

implique

\[
D(\nabla S)_{x_0}(v)=0.
\]

C’est exactement l’annulation de la seconde dérivée de Fréchet sur `v`.
Sur un espace de Hilbert réel, le représentant de Riesz du Hessien annule donc
également `v`.

## 2. L’entrée primitive est l’invariance de l’action

Le module

```text
P0EFTJanusProgramPActionTranslationSymmetryHessianKernel4D
```

part de l’identité plus physique

\[
S(x+t v)=S(x)
\]

valable localement pour `t` petit et `x` proche du point de base.

En différentiant cette identité par rapport à `x`, il reconstruit
l’invariance du gradient. La chaîne devient donc :

```text
invariance locale de l’action
→ invariance locale du gradient
→ Hessian(v, ·) = 0
→ Riesz(Hessian) v = 0.
```

## 3. Spécialisation Candidate-A

Les modules

```text
P0EFTJanusProgramPGlobalCandidateAInfinitesimalSymmetryZeroModes4D
P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D
```

appliquent cette chaîne à la véritable action quadratique augmentée

```lean
globalCandidateACommonAugmentedAction
```

et à son véritable opérateur

```lean
globalCandidateAActualKernelOperator.
```

L’équation de noyau n’est plus un champ du paquet analytique. Elle est un
théorème dérivé de l’identité de symétrie.

## 4. Absence de modes cachés

Les données terminales conservent :

- l’indépendance des modes nommés ;
- une estimation globale de Gårding avec défaut fini porté par ces modes ;
- la stationnarité LL.

La projection orthogonale sur leur span est construite automatiquement. Si un
vecteur du noyau est orthogonal à tous les modes nommés, le terme de défaut de
Gårding disparaît et la coercivité force ce vecteur à être nul.

On obtient donc :

\[
\ker H=\operatorname{span}\{v_m\},
\qquad
\dim\ker H=\#\mathrm{ZeroMode}.
\]

## 5. Fermeture H10--H14

La façade

```lean
global_candidateA_hessian_canonicalSix_actionSymmetry_frontier_gate
```

combine :

1. la famille locale H10-réduite ;
2. l’identité d’action Robin et la borne du vrai morphisme cœur-vers-chart ;
3. l’invariance locale de l’action selon les modes nommés et la Gårding.

Elle construit ensuite H10, H13, H11, H12 et H14 sur l’unique complétion
D10-free.

La variante

```lean
global_candidateA_action_symmetry_sector_gate
```

classe le noyau exact dans les cinq secteurs :

```text
metricDiffeomorphism
abelianGauge
primitiveSpinCMatter
longitudinalLL
boundaryFiniteBV
```

et démontre que la dimension du noyau est la somme de leurs multiplicités.

## 6. Frontière analytique restante

La nouvelle interface ne demande plus une preuve séparée d’annulation par le
Hessien. Il reste à fournir, pour les symétries physiques concrètes :

```text
1. leurs vecteurs dans le véritable espace de Hilbert commun ;
2. l’identité locale de l’action sous leurs translations ;
3. leur indépendance ;
4. la Gårding globale avec défaut porté par ces modes.
```

Cette route n’ajoute ni projecteur artificiel, ni paramétrix, ni seconde action,
ni seconde complétion, ni direction physique D10. La PR reste en brouillon tant
que la chaîne complète n’est pas certifiée par un build Lean vert.
