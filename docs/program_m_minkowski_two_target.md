# MF-MAN-004 — Cible témoin Minkowski 1+1

## Rôle

Cette cible rend MF-MAN-003 concrètement instanciable. Elle est **externe** au
programme d'émergence : la réussir montrerait qu'un candidat ressemble à cette
géométrie aux échelles testées, pas que Minkowski a été dérivé sans hypothèse.

## Conventions déclarées

Un point est une paire réelle `(u,v)` de coordonnées nulles futures. L'ordre
causal est l'ordre produit : `(u₁,v₁) ≤ (u₂,v₂)` lorsque les deux coordonnées
croissent. Un diamant fermé est donné par deux extrémités ainsi ordonnées.

Nous fixons

```text
ds² = -du dv,
volume(diamant) = Δu Δv / 2,
temps_propre(x,y) = sqrt(Δu Δv)
```

pour des points ordonnés ; le temps vaut zéro sinon. Le facteur `1/2` vient de
la convention `u=t-x`, `v=t+x`, donc `dt dx = du dv / 2`.

Lean prouve :

- volume positif ou nul ;
- temps propre positif ou nul ;
- temps nul pour une paire non ordonnée ;
- `2 × volume = temps_propre²` pour chaque diamant causal.

## Bibliothèque et littérature

La formalisation réutilise l'ordre produit de Mathlib et `Real.sqrt`. Les
méthodes d'embedding causal dans Minkowski à partir de volumes sont notamment
étudiées par [Johnston (2021)](https://arxiv.org/abs/2111.09331).

## Limites

Il s'agit d'un modèle analytique 1+1 fixé manuellement, pas d'une variété
lorentzienne générale formalisée. Aucun candidat de Program M ne possède encore
de certificat MF-MAN-003 vers cette cible. La dimension 2, l'orientation et la
métrique sont des propriétés de ce banc d'essai, jamais des conclusions sur la
structure primitive. Janus et la gorge n'interviennent pas.

