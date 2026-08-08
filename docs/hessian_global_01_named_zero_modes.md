# HESSIAN-GLOBAL-01 — zéro-modes nommés et coercivité

Date : **8 août 2026**.

Cette note complète `hessian_global_01_actual_kernel_frontier.md`. La réduction
sur le véritable complément du noyau était déjà construite. La présente couche
remplace le simple énoncé « noyau de dimension finie » par une classification
finie de vecteurs physiques explicitement nommés.

## 1. Famille finie nommée

Le module

```text
P0EFTJanusProgramPFiniteKernelNamedModes4D
```

introduit :

```lean
FiniteKernelNamedModeFamily operator ZeroMode
```

avec :

```text
vector : ZeroMode → E
operator (vector index) = 0
(ZeroMode → ℝ) ≃ₗ ker operator
coordonnée unité index ↦ vector index
```

Ainsi, les labels peuvent réellement représenter des générateurs résiduels,
des moduli, des modes de bord ou des secteurs physiques. Ils ne servent pas
seulement à compter une dimension abstraite.

Les opérations :

```lean
synthesize
analyze
```

sont inverses exactes. En particulier :

```text
dim ker H = card ZeroMode.
```

## 2. Opérateur de synthèse ambiant

Le module

```text
P0EFTJanusProgramPFiniteKernelNamedModeOperators4D
```

construit :

```lean
finiteKernelNamedModeSynthesisLinearMap :
  (ZeroMode → ℝ) →ₗ E
```

et démontre :

```text
synthèse injective
range synthèse = ker H
représentation unique de chaque zéro-mode
```

Le sous-espace d'obstruction utilisé par H12 est donc exactement le noyau de
l'opérateur affiché.

## 3. Coercivité quadratique

Le module

```text
P0EFTJanusProgramPSelfAdjointKernelComplementCoercivity4D
```

prend l'estimation PDE naturelle sur le complément orthogonal du noyau :

\[
c\|x\|^2\leq\langle x,Hx\rangle,
\qquad c>0.
\]

Par Cauchy–Schwarz, il construit automatiquement :

\[
c\|x\|\leq\|Hx\|.
\]

Cette dernière borne est exactement le paquet consommé par les gates déjà
présents pour :

```text
image fermée
Fredholm
indice zéro
Green réduit
résolvante dans |λ| < c
stabilité sous petites perturbations
```

## 4. Frontière physique restante

Pour le Hessien Candidate-A concret, il reste à fournir :

1. le type fini `ZeroMode` réellement choisi ;
2. les vecteurs correspondants dans le tangent physique D10-free ;
3. la preuve qu'ils forment exactement le noyau ;
4. l'estimation quadratique de coercivité sur leur orthogonal.

Toutes les conversions vers les anciens paquets `FiniteKernelModel` et
`SelfAdjointKernelComplementGapWithModel` sont automatiques. Aucun projecteur
de défaut auxiliaire n'est requis.

La certification Lean complète de ces nouveaux modules reste à effectuer.
