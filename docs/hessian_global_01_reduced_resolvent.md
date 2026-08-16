# HESSIAN-GLOBAL-01 — résolvante réduite et exponentielle bornée

Date du lot : **8 août 2026**.

Ce document décrit la couche construite après le certificat H10–H14, le
scindage exact des zéro-modes et l’opérateur de Green réduit.

Les nouveaux modules restent à valider par Lean. Le texte décrit donc la portée
mathématique de l’implémentation, pas une certification du noyau.

## 1. Espace réduit exact

La projection finie orthogonale `P` vérifie déjà :

```text
ker(H)   = range(P),
range(H) = ker(P).
```

L’opérateur réduit agit sur :

```text
ker(P).
```

Sur cet espace, le paquet coercif fournit :

```text
c > 0,
‖Hred x‖ ≥ c ‖x‖.
```

Le Green réduit `Hred⁻¹` est donc borné par `c⁻¹`.

## 2. Intervalle réel de résolvante

Le module :

```text
P0EFTJanusProgramPFiniteDefectReducedResolvent4D
```

construit, pour tout réel `λ` tel que :

```text
|λ| < c,
```

l’opérateur :

```text
R(λ) = (Hred - λ I)⁻¹.
```

Il prouve :

```text
(Hred - λ I) R(λ) = I,
R(λ) (Hred - λ I) = I,
‖R(λ)‖ ≤ (c - |λ|)⁻¹.
```

La spécialisation Candidate-A est :

```text
P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolvent4D
```

et le certificat terminal :

```text
P0EFTJanusProgramPGlobalHessianReducedResolventCertificate4D.
```

L’intervalle certifié est exactement :

```text
(-c, c).
```

À `λ = 0`, la résolvante coïncide avec le Green réduit déjà construit.

## 3. Identité de résolvante

Le module :

```text
P0EFTJanusProgramPFiniteDefectReducedResolventIdentity4D
```

prouve :

```text
R(λ) - R(μ) = (λ - μ) R(λ) R(μ).
```

Il en déduit la borne :

```text
‖R(λ) - R(μ)‖
  ≤ |λ - μ|
    (c - |λ|)⁻¹
    (c - |μ|)⁻¹.
```

La famille est donc quantitativement continue en norme d’opérateur à
l’intérieur de l’intervalle coercif.

## 4. Exponentielle bornée exacte

Comme `Hred` est un opérateur borné sur l’espace de graphe réduit, son
exponentielle de Banach existe sans hypothèse supplémentaire :

```text
U(t) = exp(-t Hred).
```

Le module :

```text
P0EFTJanusProgramPFiniteDefectReducedExponential4D
```

prouve :

```text
U(0) = I,
U(s+t) = U(s) U(t),
U(t) U(-t) = I,
Hred U(t) = U(t) Hred.
```

La version Candidate-A est :

```text
P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponential4D.
```

## 5. No-go compact absolu

L’exponentielle bornée est inversible pour tout temps réel. Si `U(t)` était
compact pour un seul temps, alors :

```text
I = U(-t) U(t)
```

serait compact. L’espace réduit serait donc fini-dimensionnel.

Ce résultat est formalisé dans :

```text
P0EFTJanusProgramPFiniteDefectReducedExponentialCompactNoGo4D
P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponentialCompactNoGo4D.
```

Conséquence : dans une réalisation réellement infinie-dimensionnelle, il est
incorrect d’identifier `exp(-t Hred)` à un heat kernel nucléaire elliptique.

## 6. Portée exacte

Cette couche construit réellement :

- le Green réduit ;
- un intervalle réel de résolvante ;
- l’identité de résolvante ;
- la continuité quantitative ;
- l’exponentielle bornée exacte ;
- le no-go compact absolu.

Elle ne construit pas encore :

- un opérateur elliptique non borné à résolvante compacte ;
- une trace canonique de chaleur ;
- un déterminant zêta ;
- une ligne de Quillen/Bismut–Freed pour le Hessien global.

Ces derniers objets appartiennent à la frontière relative décrite dans
`docs/hessian_global_01_relative_trace_frontier.md`.
