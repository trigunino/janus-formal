# MF-SIGN-001 — Extension signée par involution

## Structure ajoutée

On ajoute explicitement une involution `σ` et une charge réelle `q` satisfaisant

```text
q(σx) = -q(x).
```

Lean prouve que chaque paire échangée a une charge totale nulle et que tout
point fixe porte nécessairement la charge zéro.

## Frontière anti-triche

Une charge non nulle ne peut pas être simultanément invariante
`q(σx)=q(x)` et impaire `q(σx)=-q(x)`. Les deux conditions forcent `q=0`.
Ainsi, obtenir deux secteurs opposés exige une loi de transformation signée,
distincte de l'invariance ordinaire de la mesure de comptage.

Sur deux objets échangés, les charges `(1,-1)`, `(2,-2)` et `(3,-3)` satisfont
toutes la règle. L'involution impose l'opposition et l'annulation totale, mais
ne sélectionne pas la magnitude.

## Interprétation

Cette construction fournit une **charge abstraite signée**, pas une masse
négative. L'involution, le choix de la représentation impaire et l'échelle sont
des données supplémentaires. Une interprétation en masse inertielle ou
gravitationnelle appartient seulement à un futur adaptateur vers P.

Mathlib traite séparément les mesures positives et les mesures signées
([SignedMeasure](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/VectorMeasure/Decomposition/Lebesgue.html)),
ce qui correspond à cette séparation conceptuelle.

Le module formel est `JanusFormal/Foundations/ProgramMSignedInvolution.lean`.
Le script est `scripts/audit_program_m_signed_involution.py`; la sortie est
`outputs/program_m/mf_sign_001_signed_involution.json`.
