# HESSIAN-GLOBAL-01 — frontière de Schur orthogonale

Date : **9 août 2026**.

Cette note décrit la réduction H10–H14 fondée sur un véritable sous-espace fini
de modes physiques du Hessien Candidate-A.

La chaîne reste en brouillon tant que la compilation Lean complète n’est pas
verte.

## 1. Données H11

Le bord mobile H10 fournit le véritable bloc Robin. Les six autres Hessiennes
sont les seconds Fréchet des six actions Candidate-A :

1. interaction Candidate-A ;
2. Einstein–Hilbert `+` ;
3. Einstein–Hilbert `-` ;
4. Maxwell `+` ;
5. Maxwell `-` ;
6. finite/null-BV.

Une seule estimation du morphisme réel du cœur lisse vers le chart physique,

\[
\|Tx\|_{\mathrm{chart}}
\le C_T\|\iota x\|_{\mathrm{graphe}},
\]

construit leurs bornes, la projection H10 complétée et l’extension physique H11.

## 2. Modes de référence concrets

On choisit un type fini `Mode` et de vrais vecteurs

```lean
vector : Mode → ℋ
```

dans l’unique Hilbert commun, avec une preuve de leur indépendance linéaire.
Le module

```text
P0EFTJanusProgramPFiniteModeOrthogonalSchurNamedVectors4D
```

construit automatiquement :

- le sous-espace `K = span(range vector)` ;
- la base de `K` indexée par `Mode` ;
- les coordonnées continues `K ≃L (Mode → ℝ)` ;
- la décomposition canonique
  \[
  \mathcal H\simeq (Mode\to\mathbb R)\times K^\perp.
  \]

Aucun complément, projecteur ou isomorphisme global n’est choisi séparément.

## 3. Blocs de Schur canoniques

Après conjugaison du véritable Hessien augmenté par la décomposition
orthogonale, les quatre blocs

\[
A, B, C, D
\]

sont extraits automatiquement. La seule hypothèse analytique infinie restante
est l’inversibilité du bloc complémentaire canonique

\[
D:K^\perp\to K^\perp.
\]

Le Schur fini est alors

\[
S=A-BD^{-1}C.
\]

Les gates existantes en déduisent :

- l’image fermée du Hessien complet ;
- l’équivalence `ker H ≃ ker S` ;
- la finitude du noyau ;
- le gap sur `(ker H)ᗮ` ;
- Fredholm et indice zéro ;
- le Green réduit et la résolvante réelle.

Le point d’entrée général est :

```lean
global_candidateA_hessian_canonicalSix_orthogonalSchurNamedVectors_frontier_gate
```

## 4. Strate sans zéro-mode

Le Schur fini possède une matrice dans la base standard de `Mode → ℝ`. Le
scalaire public est :

```lean
globalCandidateAHessianNamedOrthogonalSchurDeterminant
```

Si

\[
\det S\neq0,
\]

alors `S` est bijectif, donc le Hessien complet est bijectif et

\[
\ker H=0.
\]

Le Green agit alors sur tout l’espace de Hilbert commun. Le gate terminal est :

```lean
global_candidateA_hessian_canonicalSix_namedOrthogonalSchurDeterminant_frontier_gate
```

## 5. Frontière mathématique

Hors corrections Lean, les travaux concrets sont maintenant :

1. construire la famille locale Candidate-A et ses six régularités `C²` ;
2. prouver l’unique estimation cœur-vers-chart ;
3. choisir et écrire les vecteurs physiques de référence ;
4. prouver leur indépendance linéaire ;
5. démontrer l’inversibilité de `D` sur leur orthogonal ;
6. calculer le Schur fini et son noyau, ou son déterminant sur la strate
   non dégénérée.

Il n’est plus nécessaire de fournir :

- une décomposition arbitraire de l’espace complet ;
- quatre blocs choisis manuellement ;
- un projecteur de défaut ;
- un paramétrix ;
- une base du noyau infini ;
- l’image fermée ;
- un gap spectral abstrait.

## 6. Validation

Audit statique :

```text
scripts/audit_hessian_orthogonal_schur.py
```

Workflow ciblé :

```text
.github/workflows/program-p-hessian-orthogonal-schur.yml
```

L’audit refuse `sorry`, `admit`, les nouveaux axiomes et les déclarations
`unsafe`. Il ne remplace pas la certification par le noyau Lean.
