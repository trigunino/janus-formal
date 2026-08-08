# HESSIAN-GLOBAL-01 — frontière de Schur des zéro-modes

Date : **8 août 2026**.

Cette note prolonge `hessian_global_01_actual_kernel_frontier.md`. La fermeture
H10–H14 utilise désormais le noyau réel du Hessien augmenté et calcule ce noyau
par élimination de Schur, sans demander directement une base dans l’espace de
Hilbert complet.

La chaîne reste à certifier par un build Lean complet.

## 1. Décomposition finie/complement

On choisit une décomposition continue

\[
\mathcal H \simeq F\oplus G,
\]

où `F = Mode → ℝ` est de dimension finie. Dans ces coordonnées, le véritable
Hessien augmenté est écrit

\[
H=\begin{pmatrix}A&B\\C&D\end{pmatrix}.
\]

Le paquet terminal

```lean
FiniteModeContinuousSchurBlockData H Mode Complement
```

contient :

- la décomposition linéaire continue ;
- les quatre blocs bornés `A`, `B`, `C`, `D` ;
- une équivalence linéaire continue représentant l’inverse du bloc
  complémentaire `D` ;
- l’identité affirmant que ces quatre blocs sont exactement ceux de `H`.

## 2. Élimination gaussienne

Le module

```text
P0EFTJanusProgramPFiniteModeSchurBlockElimination4D
```

construit automatiquement :

\[
S=A-BD^{-1}C,
\]

ainsi que les transformations triangulaires

\[
R(x,y)=(x,y-D^{-1}Cx),
\]

\[
L(u,v)=(u-BD^{-1}v,v).
\]

Il démontre l’identité exacte

\[
LHR=\operatorname{diag}(S,D).
\]

Aucune transformation triangulaire n’est donc fournie comme hypothèse
indépendante.

## 3. Noyau réel du Hessien

Le module

```text
P0EFTJanusProgramPFiniteModeSchurKernel4D
```

construit une équivalence linéaire

\[
\ker H\simeq\ker S.
\]

Il en déduit :

\[
\dim\ker H=\dim\ker S\leq\#Mode.
\]

Le modèle fini produit par

```lean
finiteModeSchurKernelModel
```

utilise une base du noyau de l’opérateur fini `S`, et non une base choisie
directement dans le noyau de l’opérateur infini.

## 4. Image fermée construite automatiquement

À partir des blocs bornés, le module

```text
P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D
```

construit lui-même la coordonnée réduite continue

\[
\Phi=L\circ\mathrm{decomposition}.
\]

Le module de fermeture de l’image démontre ensuite :

\[
\operatorname{Ran}H
=
\Phi^{-1}(\operatorname{Ran}S\times G).
\]

Comme `S` agit en dimension finie, son image est fermée. La continuité de
`Φ` donne automatiquement la fermeture de l’image de `H`.

Le paquet terminal ne demande donc plus séparément :

```text
une coordonnée réduite Φ
range H is closed
kernel H is finite-dimensional
une base du noyau complet
```

## 5. Spécialisation Candidate-A

Les modules

```text
P0EFTJanusProgramPGlobalCandidateAActualSchurZeroMode4D
P0EFTJanusProgramPGlobalCandidateAActualSchurClosedRange4D
P0EFTJanusProgramPGlobalCandidateAActualContinuousSchurBlock4D
P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D
```

transportent la construction vers le véritable opérateur augmenté Candidate-A.
Ils produisent automatiquement :

- le modèle fini des zéro-modes ;
- l’image fermée ;
- le gap sur l’orthogonal du noyau réel ;
- le certificat H12 ;
- le Green réduit ;
- la résolvante réelle dans le gap.

## 6. Façade terminale générale

Le point d’entrée général est :

```lean
global_candidateA_hessian_bounded_schur_frontier_gate
```

Il consomme trois paquets analytiques :

1. la famille locale H10-réduite ;
2. la réalisation H11 dans le véritable chart physique ;
3. la décomposition **bornée** en quatre blocs `A,B,C,D`, avec `D` inversible.

Il retourne la fermeture H10–H14, le comptage des zéro-modes par `ker S`, le
Green réduit et la résolvante. Le gate

```lean
global_candidateA_hessian_bounded_schur_stability_gate
```

ajoute la stabilité quantitative sous petite perturbation auto-adjointe.

## 7. Strate non dégénérée et déterminant fini

Le module

```text
P0EFTJanusProgramPFiniteModeSchurDeterminant4D
```

associe à `S` sa matrice dans la base standard de `Mode → ℝ` :

\[
M_S=\operatorname{Mat}(S).
\]

La condition finie

\[
\Delta_{\mathrm{Schur}}=\det M_S\neq0
\]

construit l’inverse matriciel, donc la bijectivité de `S`. L’identité
`LHR = diag(S,D)` donne alors :

\[
H\text{ bijectif},
\qquad
\ker H=0,
\qquad
\dim\ker H=0.
\]

Le Green n’est plus seulement défini sur `(ker H)ᗮ` : il devient l’inverse
borné du Hessien sur tout l’espace de Hilbert commun.

La façade Candidate-A correspondante est :

```lean
global_candidateA_hessian_schur_determinant_frontier_gate
```

et le scalaire public est :

```lean
globalCandidateAHessianFiniteSchurDeterminant
```

Le module intermédiaire

```text
P0EFTJanusProgramPGlobalHessianNondegenerateSchurFrontier4D
```

reste disponible lorsque la bijectivité de `S` est connue autrement qu’au
moyen de son déterminant.

## 8. Travail analytique restant

La classification globale du noyau est maintenant remplacée par les tâches
naturelles suivantes :

```text
1. choisir les modes de référence F ;
2. calculer les quatre blocs bornés réels du Hessien Candidate-A ;
3. démontrer l’inversibilité du bloc complémentaire D ;
4. calculer le noyau du Schur fini S = A - B D⁻¹ C ;
5. sur la strate sans zéro-mode, calculer et montrer non nul
   Δ_Schur = det(Mat(S)).
```

La coordonnée réduite, l’image fermée, la finitude du noyau, le gap, le Green et
la résolvante ne sont plus des obligations indépendantes.

Cette route est compatible avec les symétries physiques : les modes candidats
peuvent être choisis parmi les directions de stabilisateur, les modes
harmoniques, les paramètres de module et les éventuels zéro-modes de bord. Le
calcul final est fini-dimensional, tandis que toute l’analyse elliptique
infinie est concentrée dans l’inversibilité du bloc `D`.
