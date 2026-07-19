# MF-DESC-001 — Descente primitive et portée globale

## La bifurcation

Les relations primitives et la portée globale ne doivent pas obéir à la même
règle locale-vers-global.

Pour une famille de morceaux plongés dans un global, une relation primitive
satisfait la descente lorsqu'elle existe globalement exactement si elle possède
un témoin complet dans au moins un morceau.

Lean formalise :

- les atlas de morceaux relationnels induits ;
- la propriété `PrimitiveDescent` ;
- l'unicité de la relation primitive globale pour un prédicat de témoins locaux
  fixé.

## Exemple exhaustif

Deux morceaux portent `0→1` et `1→2`. Leurs restrictions locales laissent les
paires orientées `0→2` et `2→0` invisibles. Quatre relations globales primitives
sont donc compatibles avec les seules restrictions.

La descente primitive impose l'absence de toute relation sans témoin local et
sélectionne un unique global minimal : seulement `0→1` et `1→2`.

## Reachabilité

Après le collage, la fermeture réflexive-transitive reconstruit pourtant
`0→2`. Cette relation globale traverse les deux morceaux et ne possède aucun
témoin primitif dans un seul morceau.

La bonne architecture est donc :

```text
relations primitives locales compatibles
→ collage libre / descente primitive
→ relation primitive globale minimale
→ fermeture réflexive-transitive globale
→ reachabilité potentiellement non locale
```

Imposer la descente directement à la reachabilité supprimerait des conséquences
globales légitimes des chaînes locales.

## Statut

La distinction, l'unicité primitive et le contre-exemple de reachabilité sont
prouvés en Lean. L'audit énumère exhaustivement les quatre extensions globales
du petit exemple.

Le module est `JanusFormal/Foundations/ProgramMPrimitiveDescent.lean`. Le script
est `scripts/audit_program_m_primitive_descent.py`; la sortie est
`outputs/program_m/mf_desc_001_primitive_descent.json`.
