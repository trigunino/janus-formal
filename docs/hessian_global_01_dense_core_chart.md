# HESSIAN-GLOBAL-01 — chart physique depuis le cœur dense

Date : **8 août 2026**.

Cette note précise la direction fonctionnelle correcte pour construire la borne
H11 des six blocs physiques non‑Robin.

## 1. Pas de régularisation inverse supposée

Le modèle local est un tangent de champs lisses, tandis que l'espace commun est
une complétion de type graphe/Hilbert. En général, il n'existe pas d'application
bornée canonique :

```text
complétion Hilbert → champs lisses.
```

La construction préférée n'utilise donc pas une telle application.

## 2. La vraie application du cœur

On utilise seulement :

```lean
embedding : Core →ₗ Hilbert
chartMap  : Core →ₗ Chart
```

avec l'estimation :

\[
\|T x\|_{\mathrm{chart}}
\leq C\,\|\iota x\|_{\mathrm{graphe}}.
\]

Le module

```text
P0EFTJanusProgramPDenseCoreChartBilinearBound4D
```

montre alors, pour toute forme bilinéaire continue `B` sur le chart :

\[
\|B(Tx,Ty)\|
\leq
\|B\|C^2\,\|\iota x\|\,\|\iota y\|.
\]

## 3. Somme des six Hessiennes

Le module

```text
P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D
```

traite une famille finie de Hessiennes. Pour Candidate‑A, l'index fini est :

```text
interaction
Einstein–Hilbert +
Einstein–Hilbert −
Maxwell +
Maxwell −
finite/null-BV
```

La constante est construite automatiquement :

\[
C_6=
\left(\sum_j\|B_j\|\right)C^2.
\]

Le Robin n'appartient pas à cette somme : il est déjà le véritable second
Fréchet de l'action GHY H10.

## 4. Accord avec le Hessien affiché

Le module

```text
P0EFTJanusProgramPDenseCoreChartHessianAgreement4D
```

exige l'égalité exacte :

\[
B_6^{\mathrm{Candidate-A}}
=
\sum_j T^*B_jT
\]

sur le cœur lisse typé. Cette égalité empêche qu'une forme bornée sans rapport
avec l'action soit introduite.

Le résultat est l'unique estimation produit consommée par le prolongement H11
par densité.

## 5. Frontière combinée

La façade :

```text
P0EFTJanusProgramPGlobalHessianDenseCoreChartFrontier4D
```

expose trois entrées :

```text
borne cœur→chart
accord exact des six Hessiennes
base finie du noyau + coercivité quadratique
```

Elles alimentent respectivement H11 et H12, tandis que H10 fournit Robin et
H13 conserve l'action Candidate‑A originale.

La certification Lean complète reste nécessaire.
